/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosureFrozenPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Inner Store-Kit Transfer for `decrypt_signal` (Placed)

Budget-pool counterparts of `w2_inner_placed_at_block` and `w2_inner_full_placed_at_block`,
transferring `InnerDecryptPlacedOk` and `InnerDecryptFrozenPlacedOk` from Block `463`
(`signal_session_ratchet::decrypt_signal`) to any caller block `i < 619`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerGluePlacedBudget

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.CliRatchet.DecPlaced
open CryptoVerification.LibsignalSpqrV1 hiding Bytes
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  lsLogOff withLsCodeRoLoaded LibsignalCodeRoLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (SessionStoreBudgetEnv retagSessionStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv retagIdentityStore)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
  (InnerDecryptPlacedOk decIdKitPlaced decSessKitPlaced withStoresDecPlacedSpecVTP)

private theorem withStoresDecPlacedSpecVTP_rocl [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {EnvP : State → Prop} {xs : DecryptGhost × M.σ} {R : SepProp} {s : State}
    (h : s.mem ⊨ (withEnvPre
      (withStoresDecPlacedSpecVTP C A lim ctl parse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope) EnvP).pre xs s ∗ R) :
    LibsignalCodeRoLoaded lsmpl s.mem := by
  obtain ⟨x, st_init⟩ := xs
  dsimp only [withEnvPre, withStoresDecPlacedSpecVTP,
    LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudget.withStoresDecPlacedSpecVX,
    LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlacedBudget.withStoresDecPlacedSpecV] at h
  have h1 : s.mem ⊨
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecV
        C (A.atState lim st_init s) ctl parse S encRecord
        (retagSessionStore kit) (retagIdentityStore ikit) st0 ist0 Scope).pre x s ∗
      (⌜EnvP s⌝ ∗
        ⌜Slots.DistinctSid parse x.loc.name.bytes x.rem.name.bytes⌝ ∗
        CryptoVerification.SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        ⌜LibsignalBinary.Heap.FitsEnv M lim st_init
          (LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget.WithStoresDecEnv
            kit kitEnv st0 ikit ikitEnv ist0 C S parse tdEnv Scope x)⌝ ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) h
  exact (StoreKit.extract_withLsCodeRoLoaded h1).1

/-- Transfers budget-threaded `InnerDecryptPlacedOk` from Block `463` (`lsProg_463 H`) to any caller block `i < 619`. -/
theorem w2_inner_placed_at_block [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} (P : PEParams)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) [hcaller : IsLsBlockProg callerProg i H]
    (B : RunBudgets)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B))
    (hInner463 : InnerDecryptPlacedOk P A lim H B tdEnv kitEnv ikitEnv)
    (hi : i < 619 := by decide)
    (F0 : FsFiles) (peer : AddrGhost) (hok : Slots.FilesOkPeer Slots.scopeIn F0 peer.val) :
    let kit := decSessKitPlaced A.repAlloc F0 peer B
    let ikit := decIdKitPlaced A.repAlloc F0 peer B
    subroutine_ok callerProg (lsmpl.base 463)
      (withEnvPre
        (withStoresDecPlacedSpecVTP P.C A lim 0#64 uuidTryParse
          (pqxdhSpqrModel P) tdEnv E2E.Record.encodeRecord
          kit (kitEnv F0 peer) ikit (ikitEnv F0 peer)
          StoresGhost.opened.sessions StoresGhost.opened.identity Slots.scopeKit)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  intro kit ikit
  have hsub := hInner463 F0 peer hok
  have hwrap := StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain (pl := lsmpl) hsub
  have htr := @ls_subroutine_ok_rocl_of_block _ _ callerProg (lsProg_463 H)
    i 463 H hcaller
    (instIsLsBlockProg_463 H)
    (lsmpl.base 463) _ hwrap _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono htr (fun xs R s0 hpre => ?_) (fun xs R s0 sf hpost => ?_)
  · have hrocl := withStoresDecPlacedSpecVTP_rocl hpre
    dsimp only [StoreKit.withLsRoCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hrocl, hpre⟩
  · dsimp only [StoreKit.withLsRoCl] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2

private theorem withStoresDecFrozenPlacedSpecVTP_frozen [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {EnvP : State → Prop} {xs : DecryptGhost × M.σ} {R : SepProp} {s : State}
    (h : s.mem ⊨ (withEnvPre
      (SpecPlacedBudget.withStoresDecFrozenPlacedSpecVTP C A lim ctl parse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope) EnvP).pre xs s ∗ R) :
    LibsignalFrozen lsmpl s.mem := by
  dsimp only [withEnvPre, SpecPlacedBudget.withStoresDecFrozenPlacedSpecVTP, withLsFrozen] at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at h
  exact h.2.1

/-- Transfers budget-threaded `InnerDecryptFrozenPlacedOk` from Block `463` (`lsProg_463 H`) to any
caller block `i < 619` under `[LibsignalFullPlacement]`. -/
theorem w2_inner_full_placed_at_block [LibsignalFullPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} (P : PEParams)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) [hcaller : IsLsBlockProg callerProg i H]
    (B : RunBudgets)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B))
    (hInner463 : SpecPlacedBudget.InnerDecryptFrozenPlacedOk P A lim H B tdEnv kitEnv ikitEnv)
    (hi : i < 624 := by decide)
    (F0 : FsFiles) (peer : AddrGhost) (hok : Slots.FilesOkPeer Slots.scopeIn F0 peer.val) :
    let kit := decSessKitPlaced A.repAlloc F0 peer B
    let ikit := decIdKitPlaced A.repAlloc F0 peer B
    subroutine_ok callerProg (lsmpl.base 463)
      (withEnvPre
        (SpecPlacedBudget.withStoresDecFrozenPlacedSpecVTP P.C A lim 0#64 uuidTryParse
          (pqxdhSpqrModel P) tdEnv E2E.Record.encodeRecord
          kit (kitEnv F0 peer) ikit (ikitEnv F0 peer)
          StoresGhost.opened.sessions StoresGhost.opened.identity Slots.scopeKit)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  intro kit ikit
  let _ := hi
  have hsub := hInner463 F0 peer hok
  have hwrap :=
    LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.subroutine_ok_withLsFrozen_of_plain
      (pl := lsmpl) hsub
  have htr :=
    @LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.ls_subroutine_ok_withLsFrozen_of_block_frc
      _ _ callerProg (lsProg_463 H) i 463 H hcaller (instIsLsBlockProg_463 H)
      (lsmpl.base 463) _ hwrap (by decide)
  refine subroutine_ok_mono htr (fun xs R s0 hpre => ?_) (fun _ _ _ _ hpost => hpost)
  have hfroz := withStoresDecFrozenPlacedSpecVTP_frozen hpre
  dsimp only [withLsFrozen]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hfroz, hpre⟩

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerGluePlacedBudget
