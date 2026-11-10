/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalMem
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Callees
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seams

/-!
# Panic Bridge for `segSignal`

Bridges an `OTR::encrypt` panic on the `pendingPreKey = none` path to `withStoresEncSpecV`'s
`onPanic` postcondition.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalPublicApi.MessageEncrypt

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedSimpArgs false

/-! ## Model -/

open CryptoVerification.LibsignalPublicApi.StoreKit

/-- **Panic bridge**: `OTR::encrypt`'s panic (model panic, `spqr::send` panic, or allocation
failure after the load) is `CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV`'s panic (answers `okAnswers r _`). -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_panic_bridge {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {img : Obj.Image} {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {sp pqCap pqPtr : BitVec 64}
    {F X R0 : SepProp} {s0 s1 sf : State}
    (hcur : r.currentSession = some sess) (hsc : kit.ScopeAt Scope st0 x.rem.val r)
    (hnone : sess.pendingPreKey = none)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (htr1 : s1.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)))
    (hpost : sf.mem ⊨ ((CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptSpecQ Q C A ctl uuidTryParse S img).onPanic
      (segSignalEncGhost sp pqCap pqPtr otr x) s1 sf ∗ F) ∗ (X ∗ R0)) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R0 := by
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptSpecQ CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec Spec.inImage at hpost
  dsimp only at hpost
  have h1 : sf.mem ⊨ ⌜(((segSignalEncGhost sp pqCap pqPtr otr x).model C S uuidTryParse).1 = .error .panic ∨
        S.sendPanics otr.pqrState x.rest ∨ allocFailedIn s1 sf) ∧ s1.trace <+: sf.trace⌝ ∗
      ((anyHeap ∗ F ∗ X) ∗ R0) :=
    Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hpost
  rw [satisfies_pure_sepConj] at h1
  rcases h1 with ⟨⟨hpan_or, hpref1⟩, hmem⟩
  have hany : anyHeap ∗ F ∗ X ⊢ anyHeap := entails_anyHeap _
  have hmem' : sf.mem ⊨ anyHeap ∗ R0 := Satisfies.mono (sepConj_mono_left hany) hmem
  have hpref01 : s0.trace <+: s1.trace := by
    rw [htr1]
    exact List.prefix_append _ _
  have hpref0f : s0.trace <+: sf.trace := hpref01.trans hpref1
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV Spec.inImage
  dsimp only
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hpref0f, ?_⟩, hmem'⟩
  have hload : s0.trace ++ kit.loadEvs encRecord x.rem.val
      (okAnswers r IdentityChange.newOrUnchanged).loadSession <+: sf.trace := by
    have : s0.trace ++ kit.loadEvs encRecord x.rem.val
        (okAnswers r IdentityChange.newOrUnchanged).loadSession = s1.trace := by
      rw [htr1]
      rfl
    rw [this]
    exact hpref1
  rcases hpan_or with herr | hsp | halloc
  · refine Or.inr ⟨okAnswers r .newOrUnchanged, hsc.2, hload, Or.inl ?_⟩
    rw [segSignalEncGhost_model] at herr
    rw [segSignal_model_err hcur hnone hfrom hrem (execOk_of_exec_error herr)]
    rfl
  · refine Or.inr ⟨okAnswers r .newOrUnchanged, hsc.2, hload, Or.inr ?_⟩
    exact ⟨otr.pqrState, (segSignal_sendState (S := S) (x := x) hcur hnone hfrom hrem).1, hsp⟩
  · exact Or.inl (allocFailedIn_trans hpref01 halloc)

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
