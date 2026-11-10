/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.PublicApiCodeSym
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsVX

/-!
# Budget-Threaded `withStoresDecPlacedSpecVX`

Generalizes the `x.recvPanics S answers` panic disjunct of `DefsBudget.withStoresDecPlacedSpecV` to
an arbitrary parameter `Extra x answers`, lifting `DefsBudget.DecSegVPlaced` to `DecSegVXPlaced` and
`decSegVXPlaced_chain` under `[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsVXBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.LibsignalSessionApi (SessionRecord StoreAnswers)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.Placed (lsProg_197)
open CryptoVerification.LibsignalPublicApi.StoreKit (SessionStoreSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (DecSegVPlaced withStoresDecPlacedSpecV)

/-- `DefsBudget.withStoresDecPlacedSpecV` with `x.recvPanics S answers` generalized to `Extra x answers`. -/
def withStoresDecPlacedSpecVX [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop) :
    Spec (DecryptGhost × M.σ) where
  pre := (withStoresDecPlacedSpecV C A lim ctl parse S tdEnv encRecord
    kit kitEnv ikit ikitEnv st0 ist0 Scope).pre
  post := (withStoresDecPlacedSpecV C A lim ctl parse S tdEnv encRecord
    kit kitEnv ikit ikitEnv st0 ist0 Scope).post
  onPanic := fun (x, _) s0 sf =>
    ⌜s0.trace <+: sf.trace ∧
      (∃ answers : StoreAnswers (List (BitVec 8)) Unit,
        kit.loadRel st0 x.rem.val answers.loadSession ∧
        s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
        ((x.model C S parse answers).1 = .error .panic ∨ Extra x answers))⌝ ∗
      anyHeap

theorem withStoresDecPlacedSpecV_eq_VX [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) :
    withStoresDecPlacedSpecV C A lim ctl parse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope =
      withStoresDecPlacedSpecVX C A lim ctl parse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope (fun x a => x.recvPanics S a) := rfl

def DecSegVXPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop)
    (x : DecryptGhost) (st_init : M.σ) (R : SepProp) (s0 s : State)
    (Out : State → Prop) : Prop :=
  (lsProg_197 H).CodeLoaded s.mem →
  ∃ s', Steps (lsProg_197 H) s s' ∧
    (Out s' ∨
      SubroutineOutcome
        (withStoresDecPlacedSpecVX C A lim ctl parse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope Extra)
        (x, st_init) R s0 s')

theorem DecSegVPlaced_eq_VX [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (R : SepProp) (s0 s : State) (Out : State → Prop) :
    DecSegVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
        x st_init R s0 s Out =
      DecSegVXPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
        (fun x a => x.recvPanics S a) x st_init R s0 s Out := rfl

theorem decSegVXPlaced_chain [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    {x : DecryptGhost} {st_init : M.σ} {R : SepProp} {s0 s : State} {next : State → Prop}
    (h1 : DecSegVXPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv
      st0 ist0 Scope Extra x st_init R s0 s next)
    (h2 : ∀ s', next s' → reaches_outcome (lsProg_197 H)
      (withStoresDecPlacedSpecVX C A lim ctl parse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope Extra)
      (x, st_init) R s0 s') :
    reaches_outcome (lsProg_197 H)
      (withStoresDecPlacedSpecVX C A lim ctl parse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope Extra)
      (x, st_init) R s0 s := by
  refine Arm64.reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf hnext)
  · exact Arm64.reaches_outcome_steps hst (Arm64.reaches_outcome.of_outcome hout)

end LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsVXBudget
