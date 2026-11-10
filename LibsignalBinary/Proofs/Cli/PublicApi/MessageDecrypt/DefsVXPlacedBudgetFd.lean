/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudget

/-!
# File-Descriptor-Threaded `withStoresDecPlacedSpecVXFd`

Adds `⌜FdsGe3Closed s.fs⌝` to the precondition of `DefsVXPlacedBudget.withStoresDecPlacedSpecVX`
on `lsProg_463` via `StoreKit.withEnvPre`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudgetFd

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.LibsignalSessionApi (SessionRecord StoreAnswers)
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.CliRatchet.DecPlaced (lsProg_463)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (SessionStoreSpec reaches_outcome_withEnvPre withEnvPre withEnvPre_pre_elim)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlacedBudgetFd
  (withStoresDecPlacedSpecVFd)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudget
  (DecSegVXPlaced withStoresDecPlacedSpecVX)

/-- `DefsVXPlacedBudget.withStoresDecPlacedSpecVX` with `⌜FdsGe3Closed s.fs⌝` added to `.pre`. -/
abbrev withStoresDecPlacedSpecVXFd [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop) :
    Spec (DecryptGhost × M.σ) :=
  withEnvPre
    (withStoresDecPlacedSpecVX C A lim ctl parse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope Extra)
    (fun s => FdsGe3Closed s.fs)

theorem withStoresDecPlacedSpecVFd_eq_VXFd [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) :
    withStoresDecPlacedSpecVFd C A lim ctl parse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope =
      withStoresDecPlacedSpecVXFd C A lim ctl parse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope (fun x a => x.recvPanics S a) := rfl

theorem withStoresDecPlacedSpecVXFd_pre_elim [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    {x : DecryptGhost} {st_init : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (withStoresDecPlacedSpecVXFd C A lim ctl parse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope Extra).pre (x, st_init) s0 ∗ R) :
    FdsGe3Closed s0.fs ∧
      (s0.mem ⊨
        (withStoresDecPlacedSpecVX C A lim ctl parse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope Extra).pre (x, st_init) s0 ∗ R) :=
  withEnvPre_pre_elim hpre

theorem reaches_outcome_withStoresDecPlacedSpecVXFd [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    {x : DecryptGhost} {st_init : M.σ} {R : SepProp} {s0 s : State} :
    reaches_outcome (lsProg_463 H)
        (withStoresDecPlacedSpecVXFd C A lim ctl parse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope Extra)
        (x, st_init) R s0 s ↔
      reaches_outcome (lsProg_463 H)
        (withStoresDecPlacedSpecVX C A lim ctl parse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope Extra)
        (x, st_init) R s0 s :=
  reaches_outcome_withEnvPre

end LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudgetFd
