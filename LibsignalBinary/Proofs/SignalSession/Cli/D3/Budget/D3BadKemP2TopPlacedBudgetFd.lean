/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudgetFd
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Store-Kit `withFds` Lifts and 6-Kit Poll Bundles for Untyped `decrypt_prekey`

Provides `withFds` lifts (`sessKitFds_toWithFds`, `idKitFds_toWithFds`) for the Stage-P1 store-kit
bundles, defines the 6-kit `decrypt_prekey` poll bundles `CliDecPkPollKitsPlacedOk` (`fds = false`)
and `CliDecPkPollKitsPlacedOkFds` (`fds = true`), and bridges `fds = true` at `A` to `fds = false`
at `withFds A`.
-/

public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudgetFd

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (PublicKey)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles IdentityStoreSpec SessionStoreSpec extract_withLsRoCl
  withEnvPre withLsLogOff withLsRoCl
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (futDropBudgetSpec)
open CryptoVerification.LibsignalPublicApiRepr (directionByte sessionRecordAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  cliKitStk cliPollIdKitPlaced cliPollKpkKitPlaced cliPollPkKitPlaced
  cliPollSelfKitPlaced cliPollSessKitPlaced cliPollSpkKitPlaced
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudgetFd (
  kpkKitFds_toWithFds
  pkKitFds_toWithFds
  selfKitFds_toWithFds
  spkKitFds_toWithFds
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (
  IdentityStoreBudgetEnv kitSaveShimSpec kitTrustShimSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentitySelfStoreKitPlacedOkI IdentitySelfStoreKitPlacedOkIFds
  IdentityStoreKitPlacedOkI IdentityStoreKitPlacedOkIFds
  KyberPreKeyStoreKitPlacedOk KyberPreKeyStoreKitPlacedOkFds
  PreKeyStoreKitPlacedOk PreKeyStoreKitPlacedOkFds
  SessionOnlyKitPlacedOkSE SessionOnlyKitPlacedOkSEFds
  SignedPreKeyStoreKitPlacedOk SignedPreKeyStoreKitPlacedOkFds
  kitLoadPollPlacedSpecS kitLoadPollPlacedSpecSE
  kitSavePollPlacedSpec kitSavePollPlacedSpecE kitSavePollPlacedSpecI
  kitStorePollPlacedSpec kitStorePollPlacedSpecE
  kitTrustPollPlacedSpec kitTrustPollPlacedSpecE kitTrustPollPlacedSpecI
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (
  SessionStoreBudgetEnv kitLoadShimSpec kitStoreShimSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (
  withFds withFds_live withFds_pool_enforced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget (
  cliPollSelfBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (
  cliPollIdBudgetEnv cliPollSessBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux (
  cliPollKpkFullBudgetEnv cliPollPkFullBudgetEnv cliPollSpkFullBudgetEnv
)

/-! ## 1. Stage-P1 Store-Kit `withFds` Lifts -/

private theorem subroutine_ok_withLsRoCl_mono [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec₁ spec₂ : Spec α}
    (h : subroutine_ok prog entry (withLsRoCl lsmpl spec₁))
    (hpre : ∀ x R s, (s.mem ⊨ spec₂.pre x s ∗ R) → (s.mem ⊨ spec₁.pre x s ∗ R))
    (hpost : ∀ x R s0 sf, (sf.mem ⊨ spec₁.post x s0 sf ∗ R) → (sf.mem ⊨ spec₂.post x s0 sf ∗ R))
    (hexit : spec₁.onExit = spec₂.onExit := by rfl)
    (hpan : spec₁.onPanic = spec₂.onPanic := by rfl)
    (hoom : spec₁.onOom = spec₂.onOom := by rfl) :
    subroutine_ok prog entry (withLsRoCl lsmpl spec₂) := by
  refine subroutine_ok_mono h
    (fun x R s hp => ?_)
    (fun x R s0 sf hq => ?_)
    (fun x R s0 sf hq => hpan ▸ hq)
    (fun x code R s0 sf hq => hexit ▸ hq)
    (fun x R s0 sf hq => hoom ▸ hq)
  · obtain ⟨hcrl, hp'⟩ := extract_withLsRoCl hp
    dsimp only [withLsRoCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcrl, hpre x R s hp'⟩
  · dsimp only [withLsRoCl] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨hq.1, hpost x R s0 sf hq.2⟩

private theorem subroutine_ok_futDrop_false_of_true [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {fdsOk : FsState → Prop}
    (h : subroutine_ok prog entry (withLsRoCl lsmpl (futDropBudgetSpec fdsOk true))) :
    subroutine_ok prog entry (withLsRoCl lsmpl (futDropBudgetSpec fdsOk false)) := by
  refine subroutine_ok_withLsRoCl_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [futDropBudgetSpec] at hq ⊢
  rw [satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1, hq.1.2.1⟩, hq.2⟩

private theorem satisfies_insert_pure {m : Memory} {φ : Prop} {P Q : SepProp}
    (hφ : φ) (hm : m ⊨ P) (hEq : ⌜φ⌝ ∗ P = Q) : m ⊨ Q := by
  rw [← hEq, satisfies_pure_sepConj]
  exact ⟨hφ, hm⟩

/-- Lift `SessionOnlyKitPlacedOkSEFds A lim` (`fds = true`) to
`SessionOnlyKitPlacedOkSE (withFds A) lim ... false` under `lim.enforced = true` and
`kit.fdsOk = FdsGe3Closed`. -/
theorem sessKitFds_toWithFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks} (hkit : kit.fdsOk = FdsGe3Closed)
    (h : SessionOnlyKitPlacedOkSEFds A lim kit kitEnv Scope encRecord H) :
    SessionOnlyKitPlacedOkSE (withFds A) lim kit kitEnv Scope encRecord H false where
  loadShim hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.loadShim hblk) (fun ⟨x, st⟩ R s hp => ?_)
      (fun ⟨x, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitLoadShimSpec] at hp ⊢
      rw [withFds_pool_enforced A henf] at hp
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      rcases hp with ⟨⟨hx0, hx1, hfits⟩, hfds, hmem⟩
      exact ⟨⟨hx0, hx1, hfits, hkit ▸ hfds⟩, hmem⟩
    · dsimp only [kitLoadShimSpec, withFds_live] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      refine ⟨evs, ?_⟩
      rw [withFds_pool_enforced A henf]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hr1, hr0, hal, htr, hbox, hfds⟩, hmem⟩
      refine ⟨⟨hr1, hr0, hal, htr, hbox⟩, ?_⟩
      exact satisfies_insert_pure (hkit ▸ hfds) hmem (by sep_ac_rfl)
  loadPoll hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.loadPoll hblk)
      (fun ⟨x, self, st0, st⟩ R s hp => ?_)
      (fun ⟨x, self, st0, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitLoadPollPlacedSpecSE, withEnvPre, kitLoadPollPlacedSpecS] at hp ⊢
      rw [withFds_pool_enforced A henf] at hp
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      rcases hp with ⟨henv, hpure, hmem⟩
      have hmem' : s.mem ⊨ ⌜FdsGe3Closed s.fs⌝ ∗
          (kit.loadBoxAt x.fut self x.addrA 0#8 ∗ kit.storeAt self st0 ∗ memRegion x.out 368 ∗
            protocolAddressAt A.repAlloc x.addr x.addrA ∗
            A.pool lim st s ∗ stackAt s.sp kit.loadPollStack ∗ R) :=
        Satisfies.of_eq hmem (by sep_ac_rfl)
      rw [satisfies_pure_sepConj] at hmem'
      exact ⟨⟨henv, hkit ▸ hmem'.1⟩, hpure, hmem'.2⟩
    · dsimp only [kitLoadPollPlacedSpecSE, withEnvPre, kitLoadPollPlacedSpecS] at hq ⊢
      simp only [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨ans, evs, hq⟩
      refine ⟨ans, evs, ?_⟩
      rw [withFds_pool_enforced A henf]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hrel, htr, henv, hfds⟩, hmem⟩
      refine ⟨⟨hrel, htr, henv⟩, ?_⟩
      exact satisfies_insert_pure (hkit ▸ hfds) hmem (by sep_ac_rfl)
  loadFutDrop hblk := subroutine_ok_futDrop_false_of_true (h.loadFutDrop hblk)
  storeShim hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.storeShim hblk) (fun ⟨x, st⟩ R s hp => ?_)
      (fun ⟨x, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitStoreShimSpec] at hp ⊢
      rw [withFds_pool_enforced A henf] at hp
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      rcases hp with ⟨⟨hx0, hx1, hx2, hfits⟩, hfds, hmem⟩
      exact ⟨⟨hx0, hx1, hx2, hfits, hkit ▸ hfds⟩, hmem⟩
    · dsimp only [kitStoreShimSpec, withFds_live] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      refine ⟨evs, ?_⟩
      rw [withFds_pool_enforced A henf]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hr1, hr0, hal, htr, hbox, hfds⟩, hmem⟩
      refine ⟨⟨hr1, hr0, hal, htr, hbox⟩, ?_⟩
      exact satisfies_insert_pure (hkit ▸ hfds) hmem (by sep_ac_rfl)
  storePoll hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.storePoll hblk)
      (fun ⟨x, self, st0, st⟩ R s hp => ?_)
      (fun ⟨x, self, st0, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitStorePollPlacedSpecE, withEnvPre, kitStorePollPlacedSpec] at hp ⊢
      rw [withFds_pool_enforced A henf] at hp
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      rcases hp with ⟨henv, hpure, hmem⟩
      have hmem' : s.mem ⊨ ⌜FdsGe3Closed s.fs⌝ ∗
          (kit.storeBoxAt x.fut self x.call.addrA x.call.recA 0#8 ∗
            kit.storeAt self st0 ∗ memRegion x.out 48 ∗
            protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
            sessionRecordAt A.repAlloc x.call.recA x.call.g x.call.record ∗
            A.pool lim st s ∗ stackAt s.sp kit.storePollStack ∗ R) :=
        Satisfies.of_eq hmem (by sep_ac_rfl)
      rw [satisfies_pure_sepConj] at hmem'
      exact ⟨⟨henv, hkit ▸ hmem'.1⟩, hpure, hmem'.2⟩
    · dsimp only [kitStorePollPlacedSpecE, withEnvPre, kitStorePollPlacedSpec] at hq ⊢
      simp only [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨ans, evs, hq⟩
      refine ⟨ans, evs, ?_⟩
      rw [withFds_pool_enforced A henf]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hrel, htr, henv, hfds⟩, hmem⟩
      refine ⟨⟨hrel, htr, henv⟩, ?_⟩
      exact satisfies_insert_pure (hkit ▸ hfds) hmem (by sep_ac_rfl)
  storeFutDrop hblk := subroutine_ok_futDrop_false_of_true (h.storeFutDrop hblk)

/-- Lift `IdentityStoreKitPlacedOkIFds A lim` (`fds = true`) to
`IdentityStoreKitPlacedOkI (withFds A) lim ... false` under `lim.enforced = true` and
`ikit.fdsOk = FdsGe3Closed`. -/
theorem idKitFds_toWithFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {H : LibsignalHooks} (hkit : ikit.fdsOk = FdsGe3Closed)
    (h : IdentityStoreKitPlacedOkIFds A lim ikit ikitEnv H) :
    IdentityStoreKitPlacedOkI (withFds A) lim ikit ikitEnv H false where
  trustShim hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.trustShim hblk) (fun ⟨x, d, st⟩ R s hp => ?_)
      (fun ⟨x, d, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitTrustShimSpec] at hp ⊢
      rw [withFds_pool_enforced A henf] at hp
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      rcases hp with ⟨⟨hx0, hx1, hx2, hx3, hfits⟩, hfds, hmem⟩
      exact ⟨⟨hx0, hx1, hx2, hx3, hfits, hkit ▸ hfds⟩, hmem⟩
    · dsimp only [kitTrustShimSpec, withFds_live] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      refine ⟨evs, ?_⟩
      rw [withFds_pool_enforced A henf]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hr1, hr0, hal, htr, hbox, hfds⟩, hmem⟩
      refine ⟨⟨hr1, hr0, hal, htr, hbox⟩, ?_⟩
      exact satisfies_insert_pure (hkit ▸ hfds) hmem (by sep_ac_rfl)
  trustPoll hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.trustPoll hblk)
      (fun ⟨x, d, self, ist0, st⟩ R s hp => ?_)
      (fun ⟨x, d, self, ist0, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitTrustPollPlacedSpecI, withLsLogOff, kitTrustPollPlacedSpecE,
        withEnvPre, kitTrustPollPlacedSpec] at hp ⊢
      rw [withFds_pool_enforced A henf] at hp
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      rcases hp with ⟨henv, hpure, hmem⟩
      have hmem' : s.mem ⊨ ⌜FdsGe3Closed s.fs⌝ ∗
          (ikit.trustBoxAt x.fut self x.call.addrA x.call.keyA 0#8 (directionByte d) ∗
            ikit.identityAt self ist0 ∗ memRegion x.out 48 ∗
            protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
            (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗
            A.pool lim st s ∗ stackAt s.sp ikit.trustPollStack ∗
            lsLogOff ∗ R) :=
        Satisfies.of_eq hmem (by sep_ac_rfl)
      rw [satisfies_pure_sepConj] at hmem'
      exact ⟨⟨henv, hkit ▸ hmem'.1⟩, hpure, hmem'.2⟩
    · dsimp only [kitTrustPollPlacedSpecI, withLsLogOff, kitTrustPollPlacedSpecE,
        withEnvPre, kitTrustPollPlacedSpec] at hq ⊢
      simp only [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨ans, evs, hq⟩
      refine ⟨ans, evs, ?_⟩
      rw [withFds_pool_enforced A henf]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hrel, htr, henv, hfds⟩, hmem⟩
      refine ⟨⟨hrel, htr, henv⟩, ?_⟩
      exact satisfies_insert_pure (hkit ▸ hfds) hmem (by sep_ac_rfl)
  trustFutDrop hblk := subroutine_ok_futDrop_false_of_true (h.trustFutDrop hblk)
  saveShim hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.saveShim hblk) (fun ⟨x, st⟩ R s hp => ?_)
      (fun ⟨x, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitSaveShimSpec] at hp ⊢
      rw [withFds_pool_enforced A henf] at hp
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      rcases hp with ⟨⟨hx0, hx1, hx2, hfits⟩, hfds, hmem⟩
      exact ⟨⟨hx0, hx1, hx2, hfits, hkit ▸ hfds⟩, hmem⟩
    · dsimp only [kitSaveShimSpec, withFds_live] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      refine ⟨evs, ?_⟩
      rw [withFds_pool_enforced A henf]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hr1, hr0, hal, htr, hbox, hfds⟩, hmem⟩
      refine ⟨⟨hr1, hr0, hal, htr, hbox⟩, ?_⟩
      exact satisfies_insert_pure (hkit ▸ hfds) hmem (by sep_ac_rfl)
  savePoll hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.savePoll hblk)
      (fun ⟨x, self, ist0, st⟩ R s hp => ?_)
      (fun ⟨x, self, ist0, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitSavePollPlacedSpecI, withLsLogOff, kitSavePollPlacedSpecE,
        withEnvPre, kitSavePollPlacedSpec] at hp ⊢
      rw [withFds_pool_enforced A henf] at hp
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      rcases hp with ⟨henv, hpure, hmem⟩
      have hmem' : s.mem ⊨ ⌜FdsGe3Closed s.fs⌝ ∗
          (ikit.saveBoxAt x.fut self x.call.addrA x.call.keyA 0#8 ∗
            ikit.identityAt self ist0 ∗ memRegion x.out 48 ∗
            protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
            (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗
            A.pool lim st s ∗ stackAt s.sp ikit.savePollStack ∗
            lsLogOff ∗ R) :=
        Satisfies.of_eq hmem (by sep_ac_rfl)
      rw [satisfies_pure_sepConj] at hmem'
      exact ⟨⟨henv, hkit ▸ hmem'.1⟩, hpure, hmem'.2⟩
    · dsimp only [kitSavePollPlacedSpecI, withLsLogOff, kitSavePollPlacedSpecE,
        withEnvPre, kitSavePollPlacedSpec] at hq ⊢
      simp only [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨ans, evs, hq⟩
      refine ⟨ans, evs, ?_⟩
      rw [withFds_pool_enforced A henf]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hrel, htr, henv, hfds⟩, hmem⟩
      refine ⟨⟨hrel, htr, henv⟩, ?_⟩
      exact satisfies_insert_pure (hkit ▸ hfds) hmem (by sep_ac_rfl)
  saveFutDrop hblk := subroutine_ok_futDrop_false_of_true (h.saveFutDrop hblk)

/-! ## 2. 6-Kit CLI `decrypt_prekey` Poll Seam (`fds = false` & `fds = true`, `toWithFds`, `ofKitInst`) -/

/-- Plain (`fds = false`) bundle of the 6 CLI store-kit `PlacedOk*` contracts consumed across
Stage P1 and Stage P2 of `decrypt_prekey` poll (`dpPollProgPlaced ext`). -/
structure CliDecPkPollKitsPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (ext : LibsignalHooks) : Prop where
  sessOk : ∀ (F0 : FsFiles) (peer : AddrGhost),
    SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      (cliPollSessBudgetEnv A.repAlloc F0 peer B ReadEnv DeserEnv)
      scopeKit encodeRecord ext
  idOk : ∀ (F0 : FsFiles) (peer : AddrGhost),
    IdentityStoreKitPlacedOkI A lim
      (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollIdBudgetEnv A.repAlloc F0 peer B ReadEnv) ext
  selfOk : ∀ (F0 : FsFiles) (peer : AddrGhost),
    IdentitySelfStoreKitPlacedOkI A lim
      (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk B) ReadEnv) ext
  spkOk : ∀ (F0 : FsFiles) (sid : BitVec 32),
    SignedPreKeyStoreKitPlacedOk A lim
      (cliPollSpkKitPlaced A.repAlloc F0 sid (cliKitStk B))
      (cliPollSpkFullBudgetEnv A.repAlloc F0 sid (cliKitStk B) ReadEnv) ext
  kpkOk : ∀ (F0 : FsFiles) (kid sid : BitVec 32) (kbk : PublicKey),
    KyberPreKeyStoreKitPlacedOk A lim
      (cliPollKpkKitPlaced A.repAlloc F0 kid sid kbk (cliKitStk B))
      (cliPollKpkFullBudgetEnv A.repAlloc F0 kid sid kbk (cliKitStk B) ReadEnv) ext
  pkOk : ∀ (F0 : FsFiles) (pid : BitVec 32),
    PreKeyStoreKitPlacedOk A lim
      (cliPollPkKitPlaced A.repAlloc F0 pid (cliKitStk B))
      (cliPollPkFullBudgetEnv A.repAlloc F0 pid (cliKitStk B) ReadEnv) ext

/-- Descriptor-threaded (`fds = true`, `.fdsOk = FdsGe3Closed`) bundle of the 6 CLI store-kit
`PlacedOk*Fds` contracts for `decrypt_prekey` poll. -/
structure CliDecPkPollKitsPlacedOkFds [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (ext : LibsignalHooks) : Prop where
  sessFdsEq : ∀ (F0 : FsFiles) (peer : AddrGhost),
    (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B)).fdsOk = FdsGe3Closed
  sessOk : ∀ (F0 : FsFiles) (peer : AddrGhost),
    SessionOnlyKitPlacedOkSEFds A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      (cliPollSessBudgetEnv A.repAlloc F0 peer B ReadEnv DeserEnv)
      scopeKit encodeRecord ext
  idFdsEq : ∀ (F0 : FsFiles) (peer : AddrGhost),
    (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B)).fdsOk = FdsGe3Closed
  idOk : ∀ (F0 : FsFiles) (peer : AddrGhost),
    IdentityStoreKitPlacedOkIFds A lim
      (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollIdBudgetEnv A.repAlloc F0 peer B ReadEnv) ext
  selfFdsEq : ∀ (F0 : FsFiles) (peer : AddrGhost),
    (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B)).fdsOk = FdsGe3Closed
  selfOk : ∀ (F0 : FsFiles) (peer : AddrGhost),
    IdentitySelfStoreKitPlacedOkIFds A lim
      (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk B) ReadEnv) ext
  spkFdsEq : ∀ (F0 : FsFiles) (sid : BitVec 32),
    (cliPollSpkKitPlaced A.repAlloc F0 sid (cliKitStk B)).fdsOk = FdsGe3Closed
  spkOk : ∀ (F0 : FsFiles) (sid : BitVec 32),
    SignedPreKeyStoreKitPlacedOkFds A lim
      (cliPollSpkKitPlaced A.repAlloc F0 sid (cliKitStk B))
      (cliPollSpkFullBudgetEnv A.repAlloc F0 sid (cliKitStk B) ReadEnv) ext
  kpkFdsEq : ∀ (F0 : FsFiles) (kid sid : BitVec 32) (kbk : PublicKey),
    (cliPollKpkKitPlaced A.repAlloc F0 kid sid kbk (cliKitStk B)).fdsOk = FdsGe3Closed
  kpkOk : ∀ (F0 : FsFiles) (kid sid : BitVec 32) (kbk : PublicKey),
    KyberPreKeyStoreKitPlacedOkFds A lim
      (cliPollKpkKitPlaced A.repAlloc F0 kid sid kbk (cliKitStk B))
      (cliPollKpkFullBudgetEnv A.repAlloc F0 kid sid kbk (cliKitStk B) ReadEnv) ext
  pkFdsEq : ∀ (F0 : FsFiles) (pid : BitVec 32),
    (cliPollPkKitPlaced A.repAlloc F0 pid (cliKitStk B)).fdsOk = FdsGe3Closed
  pkOk : ∀ (F0 : FsFiles) (pid : BitVec 32),
    PreKeyStoreKitPlacedOkFds A lim
      (cliPollPkKitPlaced A.repAlloc F0 pid (cliKitStk B))
      (cliPollPkFullBudgetEnv A.repAlloc F0 pid (cliKitStk B) ReadEnv) ext

theorem CliDecPkPollKitsPlacedOk.ofKitInst [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {B : RunBudgets}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ext : LibsignalHooks}
    (h : LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget.CliDecPkPollKitsPlacedOk
      A lim B ReadEnv DeserEnv ext) :
    CliDecPkPollKitsPlacedOk A lim B ReadEnv DeserEnv ext where
  sessOk := h.sessOk
  idOk := h.idOk
  selfOk := h.selfOk
  spkOk := h.spkOk
  kpkOk := h.kpkOk
  pkOk := h.pkOk

theorem CliDecPkPollKitsPlacedOk.toKitInst [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {B : RunBudgets}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ext : LibsignalHooks}
    (h : CliDecPkPollKitsPlacedOk A lim B ReadEnv DeserEnv ext) :
    LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget.CliDecPkPollKitsPlacedOk
      A lim B ReadEnv DeserEnv ext where
  sessOk := h.sessOk
  idOk := h.idOk
  selfOk := h.selfOk
  spkOk := h.spkOk
  kpkOk := h.kpkOk
  pkOk := h.pkOk

theorem CliDecPkPollKitsPlacedOkFds.ofKitInst [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {B : RunBudgets}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ext : LibsignalHooks}
    (h : LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget.CliDecPkPollKitsPlacedOkFds
      A lim B ReadEnv DeserEnv ext) :
    CliDecPkPollKitsPlacedOkFds A lim B ReadEnv DeserEnv ext where
  sessFdsEq := h.sessFdsEq
  sessOk := h.sessOk
  idFdsEq := h.idFdsEq
  idOk := h.idOk
  selfFdsEq := h.selfFdsEq
  selfOk := h.selfOk
  spkFdsEq := h.spkFdsEq
  spkOk := h.spkOk
  kpkFdsEq := h.kpkFdsEq
  kpkOk := h.kpkOk
  pkFdsEq := h.pkFdsEq
  pkOk := h.pkOk

theorem CliDecPkPollKitsPlacedOkFds.toKitInst [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {B : RunBudgets}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ext : LibsignalHooks}
    (h : CliDecPkPollKitsPlacedOkFds A lim B ReadEnv DeserEnv ext) :
    LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget.CliDecPkPollKitsPlacedOkFds
      A lim B ReadEnv DeserEnv ext where
  sessFdsEq := h.sessFdsEq
  sessOk := h.sessOk
  idFdsEq := h.idFdsEq
  idOk := h.idOk
  selfFdsEq := h.selfFdsEq
  selfOk := h.selfOk
  spkFdsEq := h.spkFdsEq
  spkOk := h.spkOk
  kpkFdsEq := h.kpkFdsEq
  kpkOk := h.kpkOk
  pkFdsEq := h.pkFdsEq
  pkOk := h.pkOk

/-- Lift the 6-kit `fds = true` bundle at `A, lim` to the plain `fds = false` bundle at `withFds A, lim`
under `lim.enforced = true`. -/
theorem CliDecPkPollKitsPlacedOkFds.toWithFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {B : RunBudgets}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ext : LibsignalHooks}
    (h : CliDecPkPollKitsPlacedOkFds A lim B ReadEnv DeserEnv ext) :
    CliDecPkPollKitsPlacedOk (withFds A) lim B ReadEnv DeserEnv ext where
  sessOk F0 peer := sessKitFds_toWithFds henf (h.sessFdsEq F0 peer) (h.sessOk F0 peer)
  idOk F0 peer := idKitFds_toWithFds henf (h.idFdsEq F0 peer) (h.idOk F0 peer)
  selfOk F0 peer := selfKitFds_toWithFds henf (h.selfFdsEq F0 peer) (h.selfOk F0 peer)
  spkOk F0 sid := spkKitFds_toWithFds henf (h.spkFdsEq F0 sid) (h.spkOk F0 sid)
  kpkOk F0 kid sid kbk := kpkKitFds_toWithFds henf (h.kpkFdsEq F0 kid sid kbk) (h.kpkOk F0 kid sid kbk)
  pkOk F0 pid := pkKitFds_toWithFds henf (h.pkFdsEq F0 pid) (h.pkOk F0 pid)

theorem cliDecPkPollKitsFds_toWithFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {B : RunBudgets}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ext : LibsignalHooks}
    (h : CliDecPkPollKitsPlacedOkFds A lim B ReadEnv DeserEnv ext) :
    CliDecPkPollKitsPlacedOk (withFds A) lim B ReadEnv DeserEnv ext :=
  h.toWithFds henf

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudgetFd
