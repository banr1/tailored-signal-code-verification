/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced

/-!
# File-Descriptor-Threaded CLI `MessageDecrypt` Seam States and Specifications

Extends `DefsPlacedBudget` on `lsProg_463` with `FdsGe3Closed s.fs` across all seams preceding the
final `read_file` call (`IdSavePoll` in `SegSave`), and defines `withStoresDecPlacedSpecVFd` with
`⌜FdsGe3Closed s.fs⌝` in its precondition.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlacedBudgetFd

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.LibsignalSessionApi (SessionRecord StoreAnswers)
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.CliRatchet.DecPlaced (lsProg_463)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsCtx SessionStoreSpec withEnvPre withEnvPre_pre_elim)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlacedBudget
  (KeyReadyStateVPlaced LoadPolledStateVPlaced PostSomeStateVPlaced RegionSomeStateVPlaced
   TrustedStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk)

/-! ## Filesystem invariant carrier with `FdsGe3Closed` -/

/-- Filesystem invariant carrier over `lsProg_463 H` maintaining `FdsGe3Closed` alongside `envOk`. -/
abbrev DecFsCtxPlacedFd [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (H : LibsignalHooks) (s0 s : State) : Prop :=
  FsCtx (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
    (lsProg_463 H) s0 s

/-! ## Pre-`save_identity` seam states carrying `FdsGe3Closed` -/

/-- `LoadPolledStateVPlaced` (`+0x8c`) extended with `FdsGe3Closed s.fs`. -/
def LoadPolledStateVPlacedFd [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (R : SepProp) (s0 s : State) : Prop :=
  LoadPolledStateVPlaced C A lim ctl parse S tdEnv encRecord
    kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s ∧
  FdsGe3Closed s.fs

/-- `RegionSomeStateVPlaced` (`+0x1a8`) extended with `FdsGe3Closed s.fs`. -/
def RegionSomeStateVPlacedFd [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (R : SepProp) (s0 s : State) : Prop :=
  RegionSomeStateVPlaced C A lim ctl parse S tdEnv encRecord
    kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s ∧
  FdsGe3Closed s.fs

/-- `PostSomeStateVPlaced` (`+0x1f50`) extended with `FdsGe3Closed s.fs`. -/
def PostSomeStateVPlacedFd [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (R : SepProp) (s0 s : State) : Prop :=
  PostSomeStateVPlaced C A lim ctl parse S tdEnv encRecord
    kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s ∧
  FdsGe3Closed s.fs

/-- `KeyReadyStateVPlaced` (`+0x1fcc`) extended with `FdsGe3Closed s.fs`. -/
def KeyReadyStateVPlacedFd [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (R : SepProp) (s0 s : State) : Prop :=
  KeyReadyStateVPlaced C A lim ctl parse S tdEnv encRecord
    kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s ∧
  FdsGe3Closed s.fs

/-- `TrustedStateVPlaced` (`trustedPCPlaced t`) extended with `FdsGe3Closed s.fs`. -/
def TrustedStateVPlacedFd [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (t : Bool)
    (R : SepProp) (s0 s : State) : Prop :=
  TrustedStateVPlaced C A lim ctl parse S tdEnv encRecord
    kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans t R s0 s ∧
  FdsGe3Closed s.fs

/-! ## Top-level `withStoresDecPlacedSpecVFd` -/

/-- `DefsPlacedBudget.withStoresDecPlacedSpecV` with `⌜FdsGe3Closed s.fs⌝` added to `.pre`. -/
abbrev withStoresDecPlacedSpecVFd [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Spec (DecryptGhost × M.σ) :=
  withEnvPre
    (withStoresDecPlacedSpecV C A lim ctl parse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope)
    (fun s => FdsGe3Closed s.fs)

theorem withStoresDecPlacedSpecVFd_pre_elim [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {st_init : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (withStoresDecPlacedSpecVFd C A lim ctl parse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope).pre (x, st_init) s0 ∗ R) :
    FdsGe3Closed s0.fs ∧
      (s0.mem ⊨
        (withStoresDecPlacedSpecV C A lim ctl parse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope).pre (x, st_init) s0 ∗ R) :=
  withEnvPre_pre_elim hpre

theorem withStoresDecPlacedSpecVFd_pre_addrOk [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {st_init : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (withStoresDecPlacedSpecVFd C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope).pre (x, st_init) s0 ∗ R) :
    kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val :=
  withStoresDecPlacedSpecV_pre_addrOk (withStoresDecPlacedSpecVFd_pre_elim hpre).2

end LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlacedBudgetFd
