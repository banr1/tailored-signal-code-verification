/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.SegmentProofs
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local2
import LibsignalBinary.Proofs.TripleRatchet.Getters.Identity
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Statements

/-!
# `MessageDecrypt` Segment Assembly

Assembles the twelve segment specifications (`DecSegs` / `DecSegsV`), shared hypotheses (`DecHyps`),
and callee contracts (`DecCallees`) into `withStoresDecSpec` and `withStoresDecSpecV` for
`session_message_decrypt_signal_with_stores` (`0x3a4a8`), together with their relocatable
`[LibsignalPlacement]` counterparts on block `197`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt

open Arm64 ProofLib CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity

variable {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {abs : String → Option (State → State)}

/-- The twelve segment specifications parameterized by `kit`, `ikit`, `st0`, `ist0`, and `Scope`. -/
structure DecSegsV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop where
  load : SegLoadSpecV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope
  dispatch : SegDispatchSpecV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope
  regionSome : SegRegionSomeSpecV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope
  regionNone : SegRegionNoneSpecV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope
  postSome : SegPostSomeSpecV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope
  postNone : SegPostNoneSpecV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope
  trust : SegTrustSpecV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope
  untrusted : SegUntrustedSpecV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope
  save : SegSaveSpecV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope
  store : SegStoreSpecV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope
  errTeardown : SegErrTeardownSpecV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope
  write : SegWriteSpecV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope

/-- The twelve segment specifications. -/
structure DecSegs (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop where
  load : SegLoadSpec img C A ctl parse S encRecord abs
  dispatch : SegDispatchSpec img C A ctl parse S encRecord abs
  regionSome : SegRegionSomeSpec img C A ctl parse S encRecord abs
  regionNone : SegRegionNoneSpec img C A ctl parse S encRecord abs
  postSome : SegPostSomeSpec img C A ctl parse S encRecord abs
  postNone : SegPostNoneSpec img C A ctl parse S encRecord abs
  trust : SegTrustSpec img C A ctl parse S encRecord abs
  untrusted : SegUntrustedSpec img C A ctl parse S encRecord abs
  save : SegSaveSpec img C A ctl parse S encRecord abs
  store : SegStoreSpec img C A ctl parse S encRecord abs
  errTeardown : SegErrTeardownSpec img C A ctl parse S encRecord abs
  write : SegWriteSpec img C A ctl parse S encRecord abs

/-- The callee facts the segments take besides `DecHyps`: the record-level region (its contract
restricted to a predicate `Q` on the current session's pq state), the remote identity key getter
and the SS drop glue. `Q := fun _ => True` comes from `RecordDecryptRunStmt` (`SpqrRecvOk`),
`Q := (· = [])` from `RecordDecryptEmptyRunStmt` (`SpqrModel.RecvEmptyOk`). -/
structure DecCallees (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (Q : List (BitVec 8) → Prop) :
    Prop where
  region : region_ok (tripleRatchetProgAt img.base C ctl abs) (recordRegionEntry img) (recordRegionExit img)
    ((recordDecryptSpec C A ctl uuidTryParse S img).withVRegs.restrictPre (Q ·.st.pqRatchetState))
  remoteIk : OutgoingRatchet.RemoteIdentityKeyOk img C A ctl abs
  dropSs : FromRecordCallees.DropSessionStructureLocal2Ok img.base C A ctl abs

/-- Chain a store-kit-parameterized segment into the rest of the run. -/
theorem decSegV_chain
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {next : State → Prop}
    (h1 : DecSegV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope x R s0 s next)
    (h2 : ∀ s', next s' → reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
      (withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope) x R s0 s') :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
      (withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope) x R s0 s := by
  refine Arm64.reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf hnext)
  · exact Arm64.reaches_outcome_steps hst (Arm64.reaches_outcome.of_outcome hout)

/-- `decSegV_chain` carrying the fs carrier `DecFsCtx … s0` to the next seam. -/
theorem decSegV_chainFs
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {next : State → Prop}
    (hfs : DecFsCtx kit ikit C ctl abs s0 s)
    (h1 : DecSegV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope x R s0 s next)
    (h2 : ∀ s', DecFsCtx kit ikit C ctl abs s0 s' → next s' →
      reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
        (withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope) x R s0 s') :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
      (withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope) x R s0 s := by
  refine Arm64.reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf (hfs.of_steps hst) hnext)
  · exact Arm64.reaches_outcome_steps hst (Arm64.reaches_outcome.of_outcome hout)

/-- Convert a `SubroutineOutcome` for `withStoresDecSpecV` at the `E₀` hook kits into one for
`withStoresDecSpec`. -/
theorem subroutineOutcome_withStoresDecSpec_of_V {x : DecryptGhost} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome
      (withStoresDecSpecV C A ctl uuidTryParse S encRecord img
        (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope)
      x R s0 sf) :
    SubroutineOutcome (withStoresDecSpec C A ctl uuidTryParse S encRecord img) x R s0 sf := by
  rcases h with ⟨hret, hcs, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hpost
    have hstk : wsStackV (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) = wsStack := rfl
    dsimp only [withStoresDecSpecV, withStoresDecSpec, Spec.inImage]
    rw [hstk, ← decVtablesAt_eq_decVtablesAtV A img.base]
    apply Entails.sepExists_elim; intro answers
    apply Entails.sepExists_right answers
    rw [show (hookSessionStoreSpec A img.base).storeAt (s0.readReg64 .x3)
          ((hookSessionStoreSpec A img.base).storeFinal () answers (x.model C S uuidTryParse answers).2) = emp from rfl,
        show (hookIdentityStoreSpec A img.base).identityAt (s0.readReg64 .x5)
          ((hookIdentityStoreSpec A img.base).idFinal () answers (x.model C S uuidTryParse answers).2) = emp from rfl,
        emp_sepConj, emp_sepConj]
    exact sepConj_mono_left (Entails.pure_mono fun ⟨h1, _, _, _, h5⟩ =>
      ⟨h1, h5.trans (congrArg (s0.trace ++ ·)
        (hookIdentityStoreSpecAt_traceOfWith_eq_hook encRecord answers (x.model C S uuidTryParse answers).2))⟩)
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    refine Satisfies.mono (sepConj_mono_left ?_) hpost
    dsimp only [withStoresDecSpecV, withStoresDecSpec, Spec.inImage]
    exact sepConj_mono_left (Entails.pure_mono fun ⟨htr, hdisj⟩ =>
      ⟨htr, hdisj.imp id fun ⟨ans, _, hpref, hp⟩ => ⟨ans, hpref, hp⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hpost⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hpost⟩))

/-- Chain a segment into the rest of the run: its seam exit continues, its outcome exit is done. -/
theorem decSeg_chain {x : DecryptGhost} {R : SepProp} {s0 s : State} {next : State → Prop}
    (h1 : DecSeg img C A ctl uuidTryParse S encRecord abs x R s0 s next)
    (h2 : ∀ s', next s' → reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
      (withStoresDecSpec C A ctl uuidTryParse S encRecord img) x R s0 s') :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs) (withStoresDecSpec C A ctl uuidTryParse S encRecord img)
      x R s0 s := by
  refine Arm64.reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf hnext)
  · exact Arm64.reaches_outcome_steps hst (Arm64.reaches_outcome.of_outcome (subroutineOutcome_withStoresDecSpec_of_V hout))

section ChainV

variable {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
  {st0 : kit.StoreState} {ist0 : ikit.IdState}
  {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
  (hH : DecHypsV img C A ctl uuidTryParse S encRecord abs kit ikit Scope)
  (hC : DecCallees img C A ctl S abs Q)
  (hS : DecSegsV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope)
  (x : DecryptGhost) (R : SepProp) (s0 : State)
  (hAddr : kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val)

include hH hS in
theorem reachV_resultFinal (s : State)
    (h : ResultFinalStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x R s0 s) :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
      (withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegV_chain (hS.write hH x R s0 s h) (fun _ hf => hf.elim)

include hH hC hS in
theorem reachV_errJoin (pt : Bool) (s : State)
    (h : ErrJoinStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x pt R s0 s) :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
      (withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegV_chain (hS.errTeardown hH hC.dropSs x pt R s0 s h)
    (reachV_resultFinal hH hS x R s0)

include hH hC hS hAddr in
theorem reachV_storeCall (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtx kit ikit C ctl abs s0 s)
    (h : StoreCallStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s) :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
      (withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegV_chain (hS.store hH hC.dropSs x ans R s0 s hAddr.1 hfs h) (fun s' h' => h'.elim
    (reachV_resultFinal hH hS x R s0 s') (reachV_errJoin hH hC hS x R s0 true s'))

include hH hC hS hAddr in
theorem reachV_trusted (ans : StoreAnswers (List (BitVec 8)) Unit) (t : Bool) (s : State)
    (hfs : DecFsCtx kit ikit C ctl abs s0 s)
    (h : TrustedStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans t R s0 s) :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
      (withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
      x R s0 s := by
  cases t with
  | true =>
    exact decSegV_chainFs hfs (hS.save hH x ans R s0 s hAddr.2 hfs h) (fun s' hfs' h' => h'.elim
      (fun ⟨ans', hsc⟩ => reachV_storeCall hH hC hS x R s0 hAddr ans' s' hfs' hsc)
      (reachV_errJoin hH hC hS x R s0 true s'))
  | false =>
    exact decSegV_chain (hS.untrusted hH x ans R s0 s h) (reachV_errJoin hH hC hS x R s0 true)

include hH hC hS hAddr in
theorem reachV_keyReady (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtx kit ikit C ctl abs s0 s)
    (h : KeyReadyStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s) :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
      (withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegV_chainFs hfs (hS.trust hH x ans R s0 s hAddr.2 hfs h) (fun s' hfs' h' => h'.elim
    (fun ⟨ans', t, ht⟩ => reachV_trusted hH hC hS x R s0 hAddr ans' t s' hfs' ht)
    (reachV_errJoin hH hC hS x R s0 true s'))

include hH hC hS hAddr in
theorem reachV_loadPolled (hQ : ScopePq kit st0 Scope Q)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtx kit ikit C ctl abs s0 s)
    (h : LoadPolledStateV ctl encRecord img kit ikit st0 ist0 Scope x ans R s0 s) :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
      (withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
      x R s0 s := by
  refine decSegV_chainFs hfs (hS.dispatch hH x ans R s0 s h) ?_
  rintro s' hfs' (hSome | hNone | hFin)
  · refine decSegV_chainFs hfs' (hS.regionSome hH Q hC.region hQ x ans R s0 s' hSome) ?_
    intro s'' hfs'' hPost
    exact decSegV_chainFs hfs'' (hS.postSome hH hC.remoteIk x ans R s0 s'' hPost)
      (fun s3 hfs3 h3 => h3.elim
        (reachV_keyReady hH hC hS x R s0 hAddr ans s3 hfs3)
        (reachV_errJoin hH hC hS x R s0 false s3))
  · refine decSegV_chain (hS.regionNone hH x ans R s0 s' hNone) ?_
    intro s'' hPost
    exact decSegV_chain (hS.postNone hH x ans R s0 s'' hPost) (reachV_errJoin hH hC hS x R s0 false)
  · exact reachV_resultFinal hH hS x R s0 s' hFin

end ChainV

section Chain

variable (hH : DecHyps img C A ctl uuidTryParse S encRecord abs)
  (hC : DecCallees img C A ctl S abs (fun _ => True))
  (hS : DecSegs img C A ctl uuidTryParse S encRecord abs)
  (x : DecryptGhost) (R : SepProp) (s0 : State)

include hH hS in
theorem reach_resultFinal (s : State)
    (h : ResultFinalState C A ctl uuidTryParse S encRecord img x R s0 s) :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs) (withStoresDecSpec C A ctl uuidTryParse S encRecord img)
    x R s0 s :=
  decSeg_chain (hS.write hH.toV x R s0 s h) (fun _ hf => hf.elim)

include hH hC hS in
theorem reach_errJoin (pt : Bool) (s : State)
    (h : ErrJoinState C A ctl uuidTryParse S encRecord img x pt R s0 s) :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs) (withStoresDecSpec C A ctl uuidTryParse S encRecord img)
      x R s0 s :=
  decSeg_chain (hS.errTeardown hH.toV hC.dropSs x pt R s0 s h)
    (reach_resultFinal hH hS x R s0)

include hH hC hS in
theorem reach_storeCall (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (h : StoreCallState C A ctl uuidTryParse S encRecord img x ans R s0 s) :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs) (withStoresDecSpec C A ctl uuidTryParse S encRecord img)
      x R s0 s :=
  decSeg_chain (hS.store hH.toV hC.dropSs x ans R s0 s trivial
      (.inl fun _ => ⟨trivial, trivial⟩) h) (fun s' h' => h'.elim
    (reach_resultFinal hH hS x R s0 s') (reach_errJoin hH hC hS x R s0 true s'))

include hH hC hS in
theorem reach_trusted (ans : StoreAnswers (List (BitVec 8)) Unit) (t : Bool) (s : State)
    (h : TrustedState C A ctl uuidTryParse S encRecord img x ans t R s0 s) :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs) (withStoresDecSpec C A ctl uuidTryParse S encRecord img)
      x R s0 s := by
  cases t with
  | true =>
    exact decSeg_chain (hS.save hH.toV x ans R s0 s trivial
        (.inl fun _ => ⟨trivial, trivial⟩) h) (fun s' h' => h'.elim
      (fun ⟨ans', hsc⟩ => reach_storeCall hH hC hS x R s0 ans' s' hsc)
      (reach_errJoin hH hC hS x R s0 true s'))
  | false =>
    exact decSeg_chain (hS.untrusted hH.toV x ans R s0 s h) (reach_errJoin hH hC hS x R s0 true)

include hH hC hS in
theorem reach_keyReady (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (h : KeyReadyState C A ctl uuidTryParse S encRecord img x ans R s0 s) :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs) (withStoresDecSpec C A ctl uuidTryParse S encRecord img)
      x R s0 s :=
  decSeg_chain (hS.trust hH.toV x ans R s0 s trivial
      (.inl fun _ => ⟨trivial, trivial⟩) h) (fun s' h' => h'.elim
    (fun ⟨ans', t, ht⟩ => reach_trusted hH hC hS x R s0 ans' t s' ht)
    (reach_errJoin hH hC hS x R s0 true s'))

include hH hC hS in
theorem reach_loadPolled (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (h : LoadPolledState A ctl encRecord img x ans R s0 s) :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs) (withStoresDecSpec C A ctl uuidTryParse S encRecord img)
      x R s0 s := by
  refine decSeg_chain (hS.dispatch hH.toV x ans R s0 s h) ?_
  rintro s' (hSome | hNone | hFin)
  · refine decSeg_chain (hS.regionSome hH.toV _ hC.region (scopePq_true _ _ _) x ans R s0 s'
      hSome) ?_
    intro s'' hPost
    exact decSeg_chain (hS.postSome hH.toV hC.remoteIk x ans R s0 s'' hPost) (fun s3 h3 => h3.elim
      (reach_keyReady hH hC hS x R s0 ans s3) (reach_errJoin hH hC hS x R s0 false s3))
  · refine decSeg_chain (hS.regionNone hH.toV x ans R s0 s' hNone) ?_
    intro s'' hPost
    exact decSeg_chain (hS.postNone hH.toV x ans R s0 s'' hPost) (reach_errJoin hH hC hS x R s0 false)
  · exact reach_resultFinal hH hS x R s0 s' hFin

end Chain

/-- `session_message_decrypt_signal_with_stores` satisfies `withStoresDecSpecV` with `withEnvPre`
from the twelve `V` segments under `KitFsOk`. -/
theorem withStoresDec_ok_of_segsV_fs
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsV img C A ctl uuidTryParse S encRecord abs kit ikit Scope)
    (hC : DecCallees img C A ctl S abs Q) (hQ : ScopePq kit st0 Scope Q)
    (hS : DecSegsV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope)
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAt img.base C ctl abs)) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (wsEntryPC img)
      (withEnvPre (withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  refine Arm64.subroutine_ok_outcome_intro ?_
  intro x R s0 hpc hrun hpre0 hal
  obtain ⟨h0, hpre⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  have hAddr := withStoresDecSpecV_pre_addrOk hpre
  have hfs0 : DecFsCtx kit ikit C ctl abs s0 s0 := FsCtx.of_entry hKitFs h0
  exact decSegV_chainFs hfs0 (hS.load hH x R s0 hfs0 hpc hrun hal hpre)
    (fun s hfs ⟨ans, h⟩ => reachV_loadPolled hH hC hS x R s0 hAddr hQ ans s hfs h)

/-- `session_message_decrypt_signal_with_stores` satisfies `withStoresDecSpecV` from the twelve `V`
segments for kits with trivial `envOk`. -/
theorem withStoresDec_ok_of_segsV
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsV img C A ctl uuidTryParse S encRecord abs kit ikit Scope)
    (hC : DecCallees img C A ctl S abs Q) (hQ : ScopePq kit st0 Scope Q)
    (hS : DecSegsV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope)
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (wsEntryPC img)
      (withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope) :=
  subroutine_ok_of_withEnvPre (withStoresDec_ok_of_segsV_fs hH hC hQ hS (.inl htriv))
    fun s => htriv s.fs.files

/-- `session_message_decrypt_signal_with_stores` satisfies `withStoresDecSpec` from the twelve segments. -/
theorem withStoresDec_ok_of_segs (hH : DecHyps img C A ctl uuidTryParse S encRecord abs)
    (hC : DecCallees img C A ctl S abs (fun _ => True)) (hS : DecSegs img C A ctl uuidTryParse S encRecord abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (wsEntryPC img)
      (withStoresDecSpec C A ctl uuidTryParse S encRecord img) := by
  refine Arm64.subroutine_ok_outcome_intro ?_
  intro x R s0 hpc hrun hpre hal
  have hpreV : s0.mem ⊨
      (withStoresDecSpecV C A ctl uuidTryParse S encRecord img
        (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope).pre x s0 ∗ R := by
    refine Satisfies.mono (sepConj_mono_left ?_) hpre
    have hstk : wsStackV (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) = wsStack := rfl
    dsimp only [withStoresDecSpec, withStoresDecSpecV, Spec.inImage]
    rw [hstk, ← decVtablesAt_eq_decVtablesAtV A img.base]
    dsimp only [hookSessionStoreSpec, hookIdentityStoreSpec, hookIdentityStoreSpecAt]
    simp only [and_true, emp_sepConj]
    exact Entails.refl _
  exact decSeg_chain (hS.load hH.toV x R s0 (.inl fun _ => ⟨trivial, trivial⟩) hpc hrun hal hpreV)
    (fun s ⟨ans, h⟩ => reach_loadPolled hH hC hS x R s0 ans s h)

/-- Bundle `DecCallees` from `PublicApiHooksNoStores` and `SpqrRecvOk`. -/
theorem decCallees_ok_noStores (h3 : PublicApiHooksNoStores C A S abs)
    (hrecv : SpqrRecvOk C A ctl S abs img)
    (himg : Obj.Loads libsignalSessionImage img) : DecCallees img C A ctl S abs (fun _ => True) :=
  ⟨Statements.recordDecrypt_vregs_run C A ctl S abs img h3.toTripleRatchetHooks hrecv himg,
    Glue.remoteIdentityKeyOk img C A ctl abs himg,
    FromRecordCallees.drop_session_structure_local2_ok h3.alloc (Glue.drop_chain_ok_of_tripleRatchetHooks h3.toTripleRatchetHooks)⟩

/-- Bundle `DecCallees` for an empty current-session PQ state from `PublicApiHooksNoStores` and `SpqrModel.RecvEmptyOk`. -/
theorem decCallees_ok_empty (h3 : PublicApiHooksNoStores C A S abs) (hRE : S.RecvEmptyOk)
    (himg : Obj.Loads libsignalSessionImage img) : DecCallees img C A ctl S abs (· = []) :=
  ⟨Statements.recordDecryptEmpty_vregs_run C A ctl S abs img h3.toTripleRatchetHooks hRE himg,
    Glue.remoteIdentityKeyOk img C A ctl abs himg,
    FromRecordCallees.drop_session_structure_local2_ok h3.alloc (Glue.drop_chain_ok_of_tripleRatchetHooks h3.toTripleRatchetHooks)⟩

/-- Bundle `DecCallees` from `PublicApiHooks` and `SpqrRecvOk`. -/
theorem decCallees_ok (h3 : PublicApiHooks C A S encRecord abs)
    (hrecv : SpqrRecvOk C A ctl S abs img)
    (himg : Obj.Loads libsignalSessionImage img) : DecCallees img C A ctl S abs (fun _ => True) :=
  decCallees_ok_noStores (PublicApiHooks.toNoStores h3) hrecv himg

/-- The twelve store-kit-parameterized segment proofs bundled into `DecSegsV`. -/
theorem decSegsV_ok {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    DecSegsV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope :=
  ⟨segLoadV_ok, segDispatchV_ok, segRegionSomeV_ok, segRegionNoneV_ok, segPostSomeV_ok,
    segPostNoneV_ok, segTrustV_ok, segUntrustedV_ok, segSaveV_ok, segStoreV_ok, segErrTeardownV_ok,
    segWriteV_ok⟩

/-- Store-kit-parameterized correctness of `session_message_decrypt_signal_with_stores` for arbitrary
`kit`, `ikit`, initial store states `st0` / `ist0`, and `Scope`. -/
theorem decryptSignalWithStores_ok_of_kit
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hH : DecHypsV img C A ctl uuidTryParse S encRecord abs kit ikit Scope)
    (hrecv : SpqrRecvOk C A ctl S abs img)
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (wsEntryPC img)
      (withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope) :=
  withStoresDec_ok_of_segsV hH (decCallees_ok_noStores hH.hooks hrecv hH.loads)
    (scopePq_true kit st0 Scope) decSegsV_ok htriv

/-- Store-kit-parameterized correctness of `session_message_decrypt_signal_with_stores` for an empty
current-session PQ state (`ScopePq … (· = [])`) under `SpqrModel.RecvEmptyOk`. -/
theorem decryptSignalWithStoresEmpty_ok_of_kit
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hH : DecHypsV img C A ctl uuidTryParse S encRecord abs kit ikit Scope)
    (hRE : S.RecvEmptyOk) (hQ : ScopePq kit st0 Scope (· = []))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (wsEntryPC img)
      (withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope) :=
  withStoresDec_ok_of_segsV hH (decCallees_ok_empty hH.hooks hRE hH.loads) hQ decSegsV_ok htriv

-- Statement checks matching the exact hypotheses expected by the store-call callee proofs.
theorem guard_decryptSignalWithStores_ok_of_kit
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hH : DecHypsV img C A ctl uuidTryParse S encRecord abs kit ikit Scope)
    (hrecv : SpqrRecvOk C A ctl S abs img)
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (wsEntryPC img)
      (withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope) :=
  decryptSignalWithStores_ok_of_kit hH hrecv htriv

theorem guard_decryptSignalWithStoresEmpty_ok_of_kit
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hH : DecHypsV img C A ctl uuidTryParse S encRecord abs kit ikit Scope)
    (hRE : S.RecvEmptyOk) (hQ : ScopePq kit st0 Scope (· = []))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (wsEntryPC img)
      (withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope) :=
  decryptSignalWithStoresEmpty_ok_of_kit hH hRE hQ htriv

theorem guard_withStoresDec_ok_of_segsV
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsV img C A ctl uuidTryParse S encRecord abs kit ikit Scope)
    (hC : DecCallees img C A ctl S abs Q) (hQ : ScopePq kit st0 Scope Q)
    (hS : DecSegsV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope)
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (wsEntryPC img)
      (withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope) :=
  withStoresDec_ok_of_segsV hH hC hQ hS htriv

/-! ## Relocatable `[LibsignalPlacement]` Assembly -/

section Placed

open CryptoVerification CryptoVerification.LibsignalPublicApi.Placed

/-- The callee facts the `[LibsignalPlacement]` segments take besides `DecHypsVPlaced`:
the record-level region (restricted to `Q` on `pqRatchetState`), the remote identity key getter
(Block `29`), and the `SessionStructure` drop glue (Block `139`). -/
structure DecCalleesPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : LibsignalHooks) (Q : List (BitVec 8) → Prop) : Prop where
  region : region_ok (lsProg_197 H) Record.recEntryPlaced Record.recExitPlaced
    ((Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).withVRegs.restrictPre
      (Q ·.st.pqRatchetState))
  remoteIk : RemoteIdentityKeyPlacedOk A H
  dropSs : DropSessionStructureLocal2PlacedOk A H

/-- Chain a `[LibsignalPlacement]` store-kit-parameterized segment into the rest of the run. -/
theorem decSegVPlaced_chain [LibsignalPlacement] {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {next : State → Prop}
    (h1 : DecSegVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope x R s0 s next)
    (h2 : ∀ s', next s' → reaches_outcome (lsProg_197 H)
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) x R s0 s') :
    reaches_outcome (lsProg_197 H)
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) x R s0 s := by
  refine Arm64.reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf hnext)
  · exact Arm64.reaches_outcome_steps hst (Arm64.reaches_outcome.of_outcome hout)

/-- `decSegVPlaced_chain` carrying the fs carrier `DecFsCtxPlaced … s0` to the next seam. -/
theorem decSegVPlaced_chainFs [LibsignalPlacement] {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {next : State → Prop}
    (hfs : DecFsCtxPlaced kit ikit H s0 s)
    (h1 : DecSegVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope x R s0 s next)
    (h2 : ∀ s', DecFsCtxPlaced kit ikit H s0 s' → next s' →
      reaches_outcome (lsProg_197 H)
        (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) x R s0 s') :
    reaches_outcome (lsProg_197 H)
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) x R s0 s := by
  refine Arm64.reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf (hfs.of_steps hst) hnext)
  · exact Arm64.reaches_outcome_steps hst (Arm64.reaches_outcome.of_outcome hout)

section ChainVPlaced

variable [LibsignalPlacement] {H : LibsignalHooks}
  {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
  {st0 : kit.StoreState} {ist0 : ikit.IdState}
  {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
  (hH : DecHypsVPlaced C A uuidTryParse S encRecord H kit ikit Scope)
  (hC : DecCalleesPlaced C A ctl S H Q)
  (hS : DecSegsVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope)
  (x : DecryptGhost) (R : SepProp) (s0 : State)
  (hAddr : kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val)

include hH hS in
theorem reachVPlaced_resultFinal (s : State)
    (h : ResultFinalStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x R s0 s) :
    reaches_outcome (lsProg_197 H)
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegVPlaced_chain (hS.write hH x R s0 s h) (fun _ hf => hf.elim)

include hH hC hS in
theorem reachVPlaced_errJoin (pt : Bool) (s : State)
    (h : ErrJoinStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x pt R s0 s) :
    reaches_outcome (lsProg_197 H)
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegVPlaced_chain (hS.errTeardown hH hC.dropSs x pt R s0 s h)
    (reachVPlaced_resultFinal hH hS x R s0)

include hH hC hS hAddr in
theorem reachVPlaced_storeCall (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxPlaced kit ikit H s0 s)
    (h : StoreCallStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x ans R s0 s) :
    reaches_outcome (lsProg_197 H)
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegVPlaced_chain (hS.store hH hC.dropSs x ans R s0 s hAddr.1 hfs h) (fun s' h' => h'.elim
    (reachVPlaced_resultFinal hH hS x R s0 s') (reachVPlaced_errJoin hH hC hS x R s0 true s'))

include hH hC hS hAddr in
theorem reachVPlaced_trusted (ans : StoreAnswers (List (BitVec 8)) Unit) (t : Bool) (s : State)
    (hfs : DecFsCtxPlaced kit ikit H s0 s)
    (h : TrustedStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x ans t R s0 s) :
    reaches_outcome (lsProg_197 H)
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s := by
  cases t with
  | true =>
    exact decSegVPlaced_chainFs hfs (hS.save hH x ans R s0 s hAddr.2 hfs h) (fun s' hfs' h' => h'.elim
      (fun ⟨ans', hsc⟩ => reachVPlaced_storeCall hH hC hS x R s0 hAddr ans' s' hfs' hsc)
      (reachVPlaced_errJoin hH hC hS x R s0 true s'))
  | false =>
    exact decSegVPlaced_chain (hS.untrusted hH x ans R s0 s h)
      (reachVPlaced_errJoin hH hC hS x R s0 true)

include hH hC hS hAddr in
theorem reachVPlaced_keyReady (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxPlaced kit ikit H s0 s)
    (h : KeyReadyStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x ans R s0 s) :
    reaches_outcome (lsProg_197 H)
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegVPlaced_chainFs hfs (hS.trust hH x ans R s0 s hAddr.2 hfs h) (fun s' hfs' h' => h'.elim
    (fun ⟨ans', t, ht⟩ => reachVPlaced_trusted hH hC hS x R s0 hAddr ans' t s' hfs' ht)
    (reachVPlaced_errJoin hH hC hS x R s0 true s'))

include hH hC hS hAddr in
theorem reachVPlaced_loadPolled (hQ : ScopePq kit st0 Scope Q)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxPlaced kit ikit H s0 s)
    (h : LoadPolledStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans R s0 s) :
    reaches_outcome (lsProg_197 H)
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s := by
  refine decSegVPlaced_chainFs hfs (hS.dispatch hH x ans R s0 s h) ?_
  rintro s' hfs' (hSome | hNone | hFin)
  · refine decSegVPlaced_chainFs hfs' (hS.regionSome hH Q hC.region hQ x ans R s0 s' hSome) ?_
    intro s'' hfs'' hPost
    exact decSegVPlaced_chainFs hfs'' (hS.postSome hH hC.remoteIk x ans R s0 s'' hPost)
      (fun s3 hfs3 h3 => h3.elim
        (reachVPlaced_keyReady hH hC hS x R s0 hAddr ans s3 hfs3)
        (reachVPlaced_errJoin hH hC hS x R s0 false s3))
  · refine decSegVPlaced_chain (hS.regionNone hH x ans R s0 s' hNone) ?_
    intro s'' hPost
    exact decSegVPlaced_chain (hS.postNone hH x ans R s0 s'' hPost)
      (reachVPlaced_errJoin hH hC hS x R s0 false)
  · exact reachVPlaced_resultFinal hH hS x R s0 s' hFin

end ChainVPlaced

/-- `session_message_decrypt_signal_with_stores` satisfies `withStoresDecPlacedSpecV` with `withEnvPre`
from the twelve `[LibsignalPlacement]` `V` segments under `KitFsOk`. -/
theorem withStoresDec_placed_ok_of_segsV_fs [LibsignalPlacement] {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsVPlaced C A uuidTryParse S encRecord H kit ikit Scope)
    (hC : DecCalleesPlaced C A ctl S H Q) (hQ : ScopePq kit st0 Scope Q)
    (hS : DecSegsVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope)
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_197 H)) :
    subroutine_ok (lsProg_197 H) wsEntryPCPlaced
      (withEnvPre (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  refine Arm64.subroutine_ok_outcome_intro ?_
  intro x R s0 hpc hrun hpre0 hal
  obtain ⟨h0, hpre⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  have hAddr := withStoresDecPlacedSpecV_pre_addrOk hpre
  have hfs0 : DecFsCtxPlaced kit ikit H s0 s0 := FsCtx.of_entry hKitFs h0
  exact decSegVPlaced_chainFs hfs0 (hS.load hH x R s0 hfs0 hpc hrun hal hpre)
    (fun s hfs ⟨ans, h⟩ => reachVPlaced_loadPolled hH hC hS x R s0 hAddr hQ ans s hfs h)

/-- `session_message_decrypt_signal_with_stores` satisfies `withStoresDecPlacedSpecV` from the twelve
`[LibsignalPlacement]` `V` segments for kits with trivial `envOk`. -/
theorem withStoresDec_placed_ok_of_segsV [LibsignalPlacement] {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsVPlaced C A uuidTryParse S encRecord H kit ikit Scope)
    (hC : DecCalleesPlaced C A ctl S H Q) (hQ : ScopePq kit st0 Scope Q)
    (hS : DecSegsVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope)
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_197 H) wsEntryPCPlaced
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) :=
  subroutine_ok_of_withEnvPre (withStoresDec_placed_ok_of_segsV_fs hH hC hQ hS (.inl htriv))
    fun s => htriv s.fs.files

theorem remoteIdentityKeyPlacedOk [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) :
    RemoteIdentityKeyPlacedOk A H := by
  have _ := Getters.instIsLsBlockProg_29 H
  exact StoreKit.ls_subroutine_ok_rocl_of_cl (callerProg := lsProg_197 H)
    (Getters.remote_identity_key_placed_ok A H)

theorem dropSessionStructureLocal2PlacedOk [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hDealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    DropSessionStructureLocal2PlacedOk A H := by
  have _ := CryptoVerification.instIsLsBlockProg_139 H
  exact StoreKit.ls_subroutine_ok_rocl_of_cl (callerProg := lsProg_197 H)
    (FromRecordCallees.drop_session_structure_local2_placed_ok hDealloc)

/-- Assemble `DecCalleesPlaced` from the record-decrypt region contract on `lsProg_197 H` and
the proved Block `29` / Block `139` callees. -/
theorem decCalleesPlaced_of_region [LibsignalPlacement] {H : LibsignalHooks}
    {Q : List (BitVec 8) → Prop}
    (hDealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hRegion : region_ok (lsProg_197 H) Record.recEntryPlaced Record.recExitPlaced
      ((Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).withVRegs.restrictPre
        (Q ·.st.pqRatchetState))) :
    DecCalleesPlaced C A ctl S H Q :=
  ⟨hRegion, remoteIdentityKeyPlacedOk A H, dropSessionStructureLocal2PlacedOk hDealloc⟩

/-- Convenience bridge when `hRegion` is stated over `Record.lsProg_197 H`. -/
theorem decCalleesPlaced_of_recordRegion [LibsignalPlacement] {H : LibsignalHooks}
    {Q : List (BitVec 8) → Prop}
    (hDealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hRegion : region_ok (Record.lsProg_197 H) Record.recEntryPlaced Record.recExitPlaced
      ((Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).withVRegs.restrictPre
        (Q ·.st.pqRatchetState))) :
    DecCalleesPlaced C A ctl S H Q :=
  decCalleesPlaced_of_region hDealloc (lsProg_197_eq_record_lsProg_197 H ▸ hRegion)

/-- Relocatable store-kit-parameterized `_with_stores` decrypt with `withEnvPre`. -/
theorem decryptSignalWithStores_placed_ok_of_kit_fs [LibsignalPlacement] {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hH : DecHypsVPlaced C A uuidTryParse S encRecord H kit ikit Scope)
    (hRegion : region_ok (lsProg_197 H) Record.recEntryPlaced Record.recExitPlaced
      ((Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).withVRegs.restrictPre
        (fun _ => True)))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_197 H)) :
    subroutine_ok (lsProg_197 H) wsEntryPCPlaced
      (withEnvPre (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_placed_ok_of_segsV_fs hH
    (decCalleesPlaced_of_region hH.hooks.dealloc hRegion)
    (scopePq_true kit st0 Scope) decSegsVPlaced_ok hKitFs

/-- Relocatable store-kit-parameterized `_with_stores` decrypt for arbitrary `kit`, `ikit`,
initial store states `st0` / `ist0`, and `Scope` under `[LibsignalPlacement]`. -/
theorem decryptSignalWithStores_placed_ok_of_kit [LibsignalPlacement] {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hH : DecHypsVPlaced C A uuidTryParse S encRecord H kit ikit Scope)
    (hRegion : region_ok (lsProg_197 H) Record.recEntryPlaced Record.recExitPlaced
      ((Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).withVRegs.restrictPre
        (fun _ => True)))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_197 H) wsEntryPCPlaced
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) :=
  withStoresDec_placed_ok_of_segsV hH
    (decCalleesPlaced_of_region hH.hooks.dealloc hRegion)
    (scopePq_true kit st0 Scope) decSegsVPlaced_ok htriv

/-- Relocatable store-kit-parameterized `_with_stores` decrypt for an empty PQ state with `withEnvPre`. -/
theorem decryptSignalWithStoresEmpty_placed_ok_of_kit_fs [LibsignalPlacement] {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hH : DecHypsVPlaced C A uuidTryParse S encRecord H kit ikit Scope)
    (hRegion : region_ok (lsProg_197 H) Record.recEntryPlaced Record.recExitPlaced
      ((Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).withVRegs.restrictPre
        (·.st.pqRatchetState = [])))
    (hQ : ScopePq kit st0 Scope (· = []))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_197 H)) :
    subroutine_ok (lsProg_197 H) wsEntryPCPlaced
      (withEnvPre (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_placed_ok_of_segsV_fs hH
    (decCalleesPlaced_of_region hH.hooks.dealloc hRegion)
    hQ decSegsVPlaced_ok hKitFs

/-- Relocatable store-kit-parameterized `_with_stores` decrypt for an empty PQ state under `[LibsignalPlacement]`. -/
theorem decryptSignalWithStoresEmpty_placed_ok_of_kit [LibsignalPlacement] {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hH : DecHypsVPlaced C A uuidTryParse S encRecord H kit ikit Scope)
    (hRegion : region_ok (lsProg_197 H) Record.recEntryPlaced Record.recExitPlaced
      ((Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).withVRegs.restrictPre
        (·.st.pqRatchetState = [])))
    (hQ : ScopePq kit st0 Scope (· = []))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_197 H) wsEntryPCPlaced
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) :=
  withStoresDec_placed_ok_of_segsV hH
    (decCalleesPlaced_of_region hH.hooks.dealloc hRegion)
    hQ decSegsVPlaced_ok htriv

end Placed

end CryptoVerification.LibsignalPublicApi.MessageDecrypt
