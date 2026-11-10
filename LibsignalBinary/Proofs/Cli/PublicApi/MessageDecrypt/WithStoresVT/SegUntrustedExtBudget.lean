/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegUntrustedExt
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegUntrustedPlaced
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts

/-!
# Budget-Threaded `SegUntrusted` Helpers and Weak-Precondition Record Spec

Defines budget-threaded `recordDecryptPlacedSpecP` and proves the scope-free model equation
`model_of_trust_false_noScope` along with allocator-representation invariance lemmas for
`SegUntrustedExtPlacedBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegUntrustedExtBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoGames.LibsignalSession (Crypto IdentityKey)
open CryptoGames.LibsignalSessionApi (
  Session SessionRecord StoreAnswers StoreCall messageDecryptSignal_eq_flat decryptFlat
)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalSessionRepr (VecGhost vecGhostAt)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser protocolAddressAt uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (RecordDecryptGhost SpqrModel)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.StoreKit (SessionStoreSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (decryptRecord)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt (decStoreExtraPlaced)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted
  (wsUntrustedFramePlaced)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (RecordDecryptEnv TryDecryptEnvArgs)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (retagSessionStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (retagIdentityStore)

/-- Budget-threaded `recordDecryptPlacedSpec` with the identity guard weakened to
`remoteIdentity ≠ some localIdentity ∨ DistinctSid uuidParse loc rem`. -/
def recordDecryptPlacedSpecP [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (RecordDecryptGhost × M.σ) :=
  { LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.recordDecryptPlacedSpec
      C A lim ctl uuidParse S tdEnv with
    pre := fun (x, st) s => ⌜FitsEnv M lim st (RecordDecryptEnv tdEnv x)⌝ ∗
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT.recordDecryptPlacedSpecP
        C (A.atState lim st s) ctl uuidParse S).pre x s }

attribute [local irreducible] protocolAddressAt vecGhostAt

/-- Scope-free model evaluation equation on the `isTrustedIdentity = .ok false` branch. -/
theorem model_of_trust_false_noScope (C : Crypto) (S : SpqrModel) (x : DecryptGhost)
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (rec rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8))
    (ses : Session (List (BitVec 8))) (k : IdentityKey)
    (hload : ans.loadSession = .ok (some rec))
    (hdec : decryptRecord C S uuidTryParse x rec = .ok (pt, rec'))
    (hcur : rec'.currentSession = some ses)
    (hik : ses.state.remoteIdentity = some k)
    (htrust : ans.isTrustedIdentity = .ok false) :
    (x.model C S uuidTryParse ans).1 = .error (.untrustedIdentity x.rem.val) ∧
    (x.model C S uuidTryParse ans).2 =
      [.loadSession x.rem.val, .isTrustedIdentity x.rem.val k .receiving] := by
  have h : x.model C S uuidTryParse ans =
      (.error (.untrustedIdentity x.rem.val),
        [.loadSession x.rem.val, .isTrustedIdentity x.rem.val k .receiving]) := by
    unfold DecryptGhost.model
    unfold decryptRecord at hdec
    rw [messageDecryptSignal_eq_flat]
    simp [decryptFlat, hload, hdec, hcur, hik, htrust]
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

attribute [local semireducible] protocolAddressAt vecGhostAt in
theorem rep_decStoreExtra_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (P : SepProp)
    (kit : SessionStoreSpec A.repAlloc 0#64) (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (st : kit.StoreState) (ist : ikit.IdState) (s0 : State) :
    decStoreExtraPlaced (retagSessionStore (A' := { pool := P, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P, live := A.live }) ikit) st ist s0 =
    decStoreExtraPlaced kit ikit st ist s0 := rfl

attribute [local semireducible] protocolAddressAt vecGhostAt in
theorem rep_vecGhostAt_eq {M : AllocCostModel}
    (A : RustCliAllocBudget M) (P : SepProp) (v : VecGhost) (a : BitVec 64) :
    vecGhostAt ({ pool := P, live := A.live } : RustAlloc) v a =
    vecGhostAt A.repAlloc v a := rfl

attribute [local semireducible] protocolAddressAt vecGhostAt in
theorem rep_vecU8Buf_eq {M : AllocCostModel}
    (A : RustCliAllocBudget M) (P : SepProp) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf
      ({ pool := P, live := A.live } : RustAlloc) cap ptr bs =
    CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf
      A.repAlloc cap ptr bs := rfl

attribute [local semireducible] protocolAddressAt vecGhostAt in
theorem rep_wsUntrustedFrame_eq [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (P1 P2 : SepProp) (ctl : BitVec 64)
    (kit : SessionStoreSpec A.repAlloc 0#64) (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (k : IdentityKey) (e4 : BitVec 64) :
    wsUntrustedFramePlaced C ({ pool := P1, live := A.live }) ctl
      (retagSessionStore (A' := { pool := P1, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P1, live := A.live }) ikit)
      x ans s0 sp rec' pt k e4 =
    wsUntrustedFramePlaced C ({ pool := P2, live := A.live }) ctl
      (retagSessionStore (A' := { pool := P2, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P2, live := A.live }) ikit)
      x ans s0 sp rec' pt k e4 := rfl

theorem rep_storeFinal_eq {A A' : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (retagSessionStore (A' := A') kit).storeFinal st0 ans calls = kit.storeFinal st0 ans calls := by
  induction calls generalizing st0 with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [SessionStoreSpec.storeFinal, retagSessionStore, ih]

theorem rep_idFinal_eq {A A' : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ist0 : ikit.IdState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (retagIdentityStore (A' := A') ikit).idFinal ist0 ans calls = ikit.idFinal ist0 ans calls := by
  induction calls generalizing ist0 with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [IdentityStoreSpec.idFinal, retagIdentityStore, ih]

theorem rep_callsRel_eq {A A' : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (retagSessionStore (A' := A') kit).callsRel st0 ans calls = kit.callsRel st0 ans calls := by
  induction calls generalizing st0 with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [SessionStoreSpec.callsRel, retagSessionStore, ih]

theorem rep_idCallsRel_eq {A A' : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ist0 : ikit.IdState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (retagIdentityStore (A' := A') ikit).idCallsRel ist0 ans calls = ikit.idCallsRel ist0 ans calls := by
  induction calls generalizing ist0 with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [IdentityStoreSpec.idCallsRel, retagIdentityStore, ih]

private theorem rep_callEvs_eq {A A' : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (kit : SessionStoreSpec A b)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    (retagIdentityStore (A' := A') ikit).callEvs (retagSessionStore (A' := A') kit) encRecord ans =
      ikit.callEvs kit encRecord ans := by
  ext c; cases c <;> rfl

theorem rep_traceOfWith_eq {A A' : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (kit : SessionStoreSpec A b)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (retagIdentityStore (A' := A') ikit).traceOfWith (retagSessionStore (A' := A') kit) encRecord ans calls =
      ikit.traceOfWith kit encRecord ans calls := by
  simp only [IdentityStoreSpec.traceOfWith, rep_callEvs_eq]

end LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegUntrustedExtBudget
