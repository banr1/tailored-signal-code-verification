/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordDecryptPV1
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegDispatchExt
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegBatch1
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegErrTeardownExt
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegPostSomeExt
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegRegionNoneExt
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegSaveExt
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegStoreExt
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegTrustExt
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegUntrustedExt
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegRegionSome
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridge

/-!
# Ext-Generic Token-Framed `MessageDecrypt` Assembly (`WithStoresVT.Core`)

Assembles the twelve `MessageDecrypt` segments at `tripleRatchetProgAtExt img.base ext` for:
- `withStoresDecSpecVTP`: tight-panic (`Extra := fun _ _ => False`), weak-precondition
  (`RecordInScopeP` and `IdOrDistinctSid`) specification with `TokenInit img` framed across
  `recordDecryptSpecTPTight`;
- `withStoresDecSpecVT`: `TokenInit img` framed over `withStoresDecSpecV` across `recordDecryptSpecT`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT

open Arm64 ProofLib ProofLib.Variant CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalSpqrV1 (TokenInit)

/-! ## `TrapsOnly` transfer for `region_ok` -/

theorem region_ok_of_trapsOnly {α : Type} {P₁ P₂ : Program} {entry exit : BitVec 64}
    {spec : Spec α} (htr : TrapsOnly P₁ P₂)
    (h : region_ok P₁ entry exit spec) :
    region_ok P₂ entry exit spec := by
  intro x R s0 hpc hrun hpre hL₂
  have hL₁ : P₁.CodeLoaded s0.mem := CodeLoaded_of_trapsOnly htr hL₂
  obtain ⟨sf, hsteps, hout⟩ := h x R s0 hpc hrun hpre hL₁
  rcases hout with ⟨hpc_sf, hrun_sf, hpost⟩ | ⟨hpan_sf, honp⟩
  · exact ⟨sf, Steps.of_trapsOnly htr hsteps (.of_running hrun_sf),
      Or.inl ⟨hpc_sf, hrun_sf, hpost⟩⟩
  · exact ⟨sf, Steps.of_trapsOnly htr hsteps (.of_panicked hpan_sf),
      Or.inr ⟨hpan_sf, honp⟩⟩

/-! ## `IdOrDistinctSid`, `withStoresDecSpecVT`, and `withStoresDecSpecVTP` -/

/-- Identity/service-ID guard required by `recordDecryptSpecP`: every loaded in-scope current
session has `remoteIdentity ≠ some localIdentity`, or `loc` and `rem` satisfy `DistinctSid parse`. -/
def IdOrDistinctSid {A : RustAlloc} {b : BitVec 64}
    (parse : UuidParser) (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (x : DecryptGhost) : Prop :=
  ∀ r ses, kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some ses →
    ses.state.remoteIdentity ≠ some ses.state.localIdentity ∨
      CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid parse x.loc.name.bytes x.rem.name.bytes

theorem idOrDistinctSid_of_distinctSid {A : RustAlloc} {b : BitVec 64}
    {parse : UuidParser} {kit : SessionStoreSpec A b} {st0 : kit.StoreState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {x : DecryptGhost}
    (hdist : CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid parse x.loc.name.bytes x.rem.name.bytes) :
    IdOrDistinctSid parse kit st0 Scope x :=
  fun _ _ _ _ => Or.inr hdist

theorem idOrDistinctSid_of_scopeIn {A : RustAlloc} {b : BitVec 64}
    {parse : UuidParser} {kit : SessionStoreSpec A b} {st0 : kit.StoreState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {x : DecryptGhost}
    (hscopeIn : ∀ r, Scope r → RecordInScope r) :
    IdOrDistinctSid parse kit st0 Scope x :=
  fun r ses hsc hcur => Or.inl (hscopeIn r hsc.1 ses hcur).1

/-- `withStoresDecSpecV` with `TokenInit img` framed in `pre` and `post`. -/
def withStoresDecSpecVT (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Spec DecryptGhost :=
  { CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecV
      C A ctl parse S encRecord img kit ikit st0 ist0 Scope with
    pre := fun x s =>
      TokenInit img ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecV
          C A ctl parse S encRecord img kit ikit st0 ist0 Scope).pre x s
    post := fun x s0 sf =>
      TokenInit img ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecV
          C A ctl parse S encRecord img kit ikit st0 ist0 Scope).post x s0 sf }

/-- Tight-panic `withStoresDecSpecVX` (`Extra := fun _ _ => False`) with `TokenInit img` framed in `pre` and `post`. -/
def withStoresDecSpecVTP (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Spec DecryptGhost :=
  { CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecVX
      C A ctl parse S encRecord img kit ikit st0 ist0 Scope (fun _ _ => False) with
    pre := fun x s =>
      TokenInit img ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecVX
          C A ctl parse S encRecord img kit ikit st0 ist0 Scope (fun _ _ => False)).pre x s
    post := fun x s0 sf =>
      TokenInit img ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecVX
          C A ctl parse S encRecord img kit ikit st0 ist0 Scope (fun _ _ => False)).post x s0 sf }

/-! ## Weak-precondition `RegionSomeStatePV` and `segDispatchVP_ok_ext` -/

/-- `RegionSomeStateV` weakened to `recordDecryptSpecP` (`remote ≠ local ∨ DistinctSid`). -/
def RegionSomeStatePV (C : Crypto) {A : RustAlloc} (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (R : SepProp) (s0 s : State) : Prop :=
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img ∧
  wsMeta img x s0 s ∧
  ∃ (rec : SessionRecord (List (BitVec 8))) (ses : Session (List (BitVec 8))) (G : SessionGhost)
    (prevCap prevPtr : BitVec 64),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    rec.currentSession = some ses ∧ sessionModelRel G ses ∧
    s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
    (s.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpecP C A ctl parse S img).pre
      (recGhostOf x prevPtr G ses.state) s ∗
      wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗ decStoreExtra kit ikit st0 ist0 s0 ∗ R)

theorem regionSomePV_of_common_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (x : DecryptGhost) (s0 sf : State) (sp : BitVec 64) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8))) (ses : Session (List (BitVec 8)))
    (hsp0 : s0.sp - 0xee0#64 = sp) (hsp : sf.sp = sp)
    (hscopeP : CryptoVerification.E2E.RecordX.RecordInScopeP rec)
    (hcur : rec.currentSession = some ses)
    (hid : ses.state.remoteIdentity ≠ some ses.state.localIdentity ∨
      CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid uuidTryParse x.loc.name.bytes x.rem.name.bytes)
    (hpure : img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧ sf.spAligned = true ∧
      sf.readReg64 .x27 = x.ret ∧ sf.readReg64 .x19 = x.remA ∧
      sf.readReg64 .x23 = sp + 0x5f0#64 ∧ sf.readReg64 .x24 = sp + 0xca0#64 ∧
      rootStack ≤ sp.toNat) :
    sessionRecordAt A (sp + 0x120#64) g rec ∗
      regionCommonBodyExt A img x sp ∗
      Pf.SegDispatch.wsRegionFrameRest img kit ikit st0 ist0 x s0 sp ⊢
    ∃∗ G : SessionGhost,
      ⌜sessionModelRel G ses⌝ ∗
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpecP C A ctl uuidTryParse S img).pre
        (recGhostOf x g.prevPtr G ses.state) sf ∗
      wsRegionFrameV img kit ikit x s0 g.prevCap g.prevPtr ∗
      decStoreExtra kit ikit st0 ist0 s0 := by
  have hsplit := Pf.SegDispatch.recordSome_split A (sp + 0x120#64) g rec ses hcur
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsplit
  refine Entails.trans (sepConj_mono_left hsplit) ?_
  simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro G
  refine Entails.sepExists_right G ?_
  rw [sepConj_assoc (⌜_⌝)]
  apply Entails.pure_left; intro hw0
  apply Entails.pure_right hw0
  have hsc := hscopeP ses hcur
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpecP, Spec.inImage, recGhostOf]
  unfold regionCommonBodyExt wsRegionFrameV Pf.SegDispatch.wsRegionFrameRest wsFixedV
  rw [hsp0, hsp]
  simp only [sepConj_assoc]
  apply Entails.pure_right ⟨hpure.1, hpure.2.1⟩
  apply Entails.pure_right ⟨hpure.2.2.1, hpure.2.2.2.1, hpure.2.2.2.2.1,
    hpure.2.2.2.2.2.1, hpure.2.2.2.2.2.2.1, hid, hsc.1, hsc.2.1, hpure.2.2.2.2.2.2.2⟩
  exact Entails.of_eq (by ac_rfl)

theorem segDispatchVP_ok_ext4K {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hH : DecHypsExt4K img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State)
    (hid : IdOrDistinctSid uuidTryParse kit st0 Scope x)
    (hLP : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.LoadPolledStateV
      ctl encRecord img kit ikit st0 ist0 Scope x ans R s0 s) :
    DecSegVXExt img C A ctl uuidTryParse S encRecord ext kit ikit st0 ist0 Scope Extra x R s0 s
      (fun s' =>
        RegionSomeStatePV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s' ∨
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.RegionNoneStateV
          ctl encRecord img kit ikit st0 ist0 Scope x ans R s0 s' ∨
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ResultFinalStateV
          C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x R s0 s') := by
  refine segDispatchGen_ok_ext4K hH x ans R s0 s hLP ?_
  intro sf_3 g rec ses hpc3 hmeta3 hload hscope hscopeAt hcur htr3 hsp' hsp3 hpure3 hmf3'
  have hmf3'' := Satisfies.mono
    (sepConj_mono_left (regionSomePV_of_common_ext C A ctl S img kit ikit st0 ist0 x s0 sf_3
      s.sp g rec ses hsp' hsp3
      (hH.scopeInP rec hscope) hcur (hid rec ses hscopeAt hcur) hpure3)) hmf3'
  rw [sepExists_sepConj_left, satisfies_sepExists] at hmf3''
  obtain ⟨G, hmf3''⟩ := hmf3''
  rw [sepConj_assoc (⌜_⌝), satisfies_pure_sepConj] at hmf3''
  obtain ⟨hw0, hmf3''⟩ := hmf3''
  simp only [sepConj_assoc] at hmf3''
  exact ⟨hpc3, hmeta3, rec, ses, G, g.prevCap, g.prevPtr, hload, hscopeAt, hcur, hw0, htr3, hmf3''⟩

theorem segDispatchVP_ok_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hH : DecHypsExt img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State)
    (hid : IdOrDistinctSid uuidTryParse kit st0 Scope x)
    (hLP : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.LoadPolledStateV
      ctl encRecord img kit ikit st0 ist0 Scope x ans R s0 s) :
    DecSegVXExt img C A ctl uuidTryParse S encRecord ext kit ikit st0 ist0 Scope Extra x R s0 s
      (fun s' =>
        RegionSomeStatePV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s' ∨
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.RegionNoneStateV
          ctl encRecord img kit ikit st0 ist0 Scope x ans R s0 s' ∨
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ResultFinalStateV
          C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x R s0 s') :=
  segDispatchVP_ok_ext4K hH.toDecHypsExt4K x ans R s0 s hid hLP

/-! ## Outcome lifting and region crossing -/

private theorem subroutineOutcome_vx_to_framed
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecVX
        C A ctl parse S encRecord img kit ikit st0 ist0 Scope Extra)
      x (TokenInit img ∗ R) s0 sf) :
    SubroutineOutcome
      { CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecVX
          C A ctl parse S encRecord img kit ikit st0 ist0 Scope Extra with
        pre := fun x s =>
          TokenInit img ∗
            (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecVX
              C A ctl parse S encRecord img kit ikit st0 ist0 Scope Extra).pre x s
        post := fun x s0 sf =>
          TokenInit img ∗
            (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecVX
              C A ctl parse S encRecord img kit ikit st0 ist0 Scope Extra).post x s0 sf }
      x R s0 sf := by
  rcases h with ⟨h1, hcs, hpost⟩ | ⟨hpan, honp⟩ | ⟨code, hexit, honex⟩ | ⟨hoom, honoom⟩
  · refine Or.inl ⟨h1, hcs, ?_⟩
    dsimp only
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecVX,
      Spec.inImage] at honp ⊢
    refine Satisfies.mono ?_ honp
    rw [← sepConj_assoc, sepConj_assoc ⌜_⌝ anyHeap (TokenInit img)]
    refine sepConj_mono_left (sepConj_mono_right ?_)
    exact entails_anyHeap (anyHeap ∗ TokenInit img)
  · refine Or.inr (Or.inr (Or.inl ⟨code, hexit, ?_⟩))
    change sf.mem ⊨ ⌜False⌝ ∗ (TokenInit img ∗ R) at honex
    rw [satisfies_pure_sepConj] at honex
    exact False.elim honex.1
  · refine Or.inr (Or.inr (Or.inr ⟨hoom, ?_⟩))
    change sf.mem ⊨ ⌜False⌝ ∗ (TokenInit img ∗ R) at honoom
    rw [satisfies_pure_sepConj] at honoom
    exact False.elim honoom.1

private theorem decSegVTP_chain_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {next : State → Prop}
    (h1 : DecSegVXExt img C A ctl uuidTryParse S encRecord ext kit ikit st0 ist0 Scope
      (fun _ _ => False) x (TokenInit img ∗ R) s0 s next)
    (h2 : ∀ s', next s' → reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope) x R s0 s') :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope) x R s0 s := by
  refine Arm64.reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf hnext)
  · exact Arm64.reaches_outcome_steps hst (Arm64.reaches_outcome.of_outcome (subroutineOutcome_vx_to_framed hout))

private theorem decSegVTP_chainFs_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {next : State → Prop}
    (hfs : DecFsCtxExt kit ikit ext s0 s)
    (h1 : DecSegVXExt img C A ctl uuidTryParse S encRecord ext kit ikit st0 ist0 Scope
      (fun _ _ => False) x (TokenInit img ∗ R) s0 s next)
    (h2 : ∀ s', DecFsCtxExt kit ikit ext s0 s' → next s' →
      reaches_outcome (tripleRatchetProgAtExt img.base ext)
        (withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope) x R s0 s') :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope) x R s0 s := by
  refine Arm64.reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf (hfs.of_steps hst) hnext)
  · exact Arm64.reaches_outcome_steps hst (Arm64.reaches_outcome.of_outcome (subroutineOutcome_vx_to_framed hout))

private theorem decSegVT_chain_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {next : State → Prop}
    (h1 : DecSegVXExt img C A ctl uuidTryParse S encRecord ext kit ikit st0 ist0 Scope
      (fun x answers => x.recvPanics S answers) x (TokenInit img ∗ R) s0 s next)
    (h2 : ∀ s', next s' → reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (withStoresDecSpecVT C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope) x R s0 s') :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (withStoresDecSpecVT C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope) x R s0 s := by
  refine Arm64.reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf hnext)
  · exact Arm64.reaches_outcome_steps hst (Arm64.reaches_outcome.of_outcome (subroutineOutcome_vx_to_framed hout))

private theorem decSegVT_chainFs_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {next : State → Prop}
    (hfs : DecFsCtxExt kit ikit ext s0 s)
    (h1 : DecSegVXExt img C A ctl uuidTryParse S encRecord ext kit ikit st0 ist0 Scope
      (fun x answers => x.recvPanics S answers) x (TokenInit img ∗ R) s0 s next)
    (h2 : ∀ s', DecFsCtxExt kit ikit ext s0 s' → next s' →
      reaches_outcome (tripleRatchetProgAtExt img.base ext)
        (withStoresDecSpecVT C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope) x R s0 s') :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (withStoresDecSpecVT C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope) x R s0 s := by
  refine Arm64.reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf (hfs.of_steps hst) hnext)
  · exact Arm64.reaches_outcome_steps hst (Arm64.reaches_outcome.of_outcome (subroutineOutcome_vx_to_framed hout))

/-- Crosses the record-decrypt region at `recordDecryptSpecTPTight` restricted by `Q`, unframing
and restoring `TokenInit img` and mapping `recordDecryptOnPanicTight` to `Extra := fun _ _ => False`. -/
theorem segRegionSomeVTP_ok_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (Q : List (BitVec 8) → Prop)
    (hreg : region_ok (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      ((CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight
        C A ctl uuidTryParse S img).withVRegs.restrictPre (Q ·.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State)
    (hRS : RegionSomeStatePV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope
      x ans (TokenInit img ∗ R) s0 s) :
    (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.PostSomeStateV
          C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope
          x ans (TokenInit img ∗ R) s0 s' ∨
        SubroutineOutcome
          (withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
          x R s0 s') := by
  intro hL
  obtain ⟨hpc, ⟨hrun, hsp, hal0, hal, hx29, _hx27, hfrozen, hsym, hvregs⟩,
    rec, ses, G, prevCap, prevPtr, hload, hscope, hcur, hw0, htrace, hmem⟩ := hRS
  let x_rg := recGhostOf x prevPtr G ses.state
  let R_rg := wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗
    decStoreExtra kit ikit st0 ist0 s0 ∗ R
  obtain ⟨hpq_lt, hpq_Q⟩ := hQ x.rem.val rec ses hscope hcur
  have hmem_rg : s.mem ⊨
      (TokenInit img ∗
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpecP C A ctl uuidTryParse S img).pre
          x_rg s) ∗ R_rg := by
    dsimp only [x_rg, R_rg]
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hmem
  have hmemT : s.mem ⊨
      ((CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight
        C A ctl uuidTryParse S img).withVRegs.restrictPre (Q ·.st.pqRatchetState)).pre x_rg s ∗ R_rg := by
    dsimp only [Spec.restrictPre, Spec.withVRegs,
      CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpq_Q, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpq_lt, by simpa only [sepConj_assoc] using hmem_rg⟩
  obtain ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, hmf⟩ | ⟨hpan_sf, hmf⟩⟩ :=
    hreg x_rg R_rg s hpc hrun hmemT hL
  · refine ⟨sf, hsteps, Or.inl ?_⟩
    dsimp only [Spec.restrictPre, Spec.withVRegs] at hmf
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf
    obtain ⟨hvregs_sf, hmf⟩ := hmf
    have hmf' : sf.mem ⊨
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img).post
          x_rg s sf ∗
          (wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗
            decStoreExtra kit ikit st0 ist0 s0 ∗ (TokenInit img ∗ R)) := by
      dsimp only [CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight,
        CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecT, x_rg, R_rg] at hmf ⊢
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hmf
    obtain ⟨hsp_sf, hx29_sf, hx27_sf⟩ :=
      post_meta_extract_ext hmf'
    have hfrozen_sf : img.FrozenLoaded sf := hfrozen.of_keepsFrozen hsteps.keepsFrozen
    have hsym_sf : sf.symtab = img.symtab := hsteps.symtab_eq.trans hsym
    have hal_sf : sf.spAligned = true := by
      rw [State.spAligned, hsp_sf]
      exact hal
    have hmeta_sf : wsMeta img x s0 sf :=
      ⟨hrun_sf, hsp_sf.trans hsp, hal0, hal_sf, hx29_sf.trans hx29,
        hx27_sf, hfrozen_sf, hsym_sf, hvregs_sf.trans hvregs⟩
    refine ⟨hpc_sf, hmeta_sf, s, rec, ses, G, prevCap, prevPtr, hsp, htrace,
      hload, hscope, hcur, hw0, ?_⟩
    simpa only [sepConj_assoc] using hmf'
  · refine ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan_sf, ?_⟩))⟩
    dsimp only [Spec.restrictPre, Spec.withVRegs,
      CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight,
      CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptOnPanicTight,
      withStoresDecSpecVTP, CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecVX,
      Spec.inImage, R_rg] at hmf ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf
    rcases hmf with ⟨⟨hdisj, hpref⟩, hmf⟩
    have hload_pref : s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession <+: sf.trace := by
      rwa [← htrace]
    have hs0_pref : s0.trace <+: sf.trace :=
      (List.prefix_append s0.trace (kit.loadEvs encRecord x.rem.val ans.loadSession)).trans hload_pref
    have hpan_pure :
        s0.trace <+: sf.trace ∧
          (allocFailedIn s0 sf ∨
            ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
              kit.loadRel st0 x.rem.val answers.loadSession ∧
              s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
              ((x.model C S uuidTryParse answers).1 = .error .panic ∨ False)) := by
      refine ⟨hs0_pref, ?_⟩
      rcases hdisj with hmod_pan | halloc
      · exact Or.inr ⟨ans, hload ▸ hscope.2, hload_pref, Or.inl
          (Pf.SegRegionSome.model_panic_of_region_panic C S x ans rec ses G prevPtr hload hcur hmod_pan)⟩
      · exact Or.inl (Pf.SegRegionSome.allocFailedIn_of_load_prefix htrace hpref halloc)
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpan_pure, ?_⟩
    have h_any : anyHeap ∗ (wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗
        decStoreExtra kit ikit st0 ist0 s0) ⊢ anyHeap :=
      entails_anyHeap _
    rw [← sepConj_assoc, ← sepConj_assoc] at hmf
    rw [sepConj_assoc anyHeap] at hmf
    exact Satisfies.mono (sepConj_mono_left h_any) hmf

/-- Crosses the record-decrypt region at `recordDecryptSpecT` restricted by `Q` for `withStoresDecSpecVT`. -/
theorem segRegionSomeVT_ok_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (Q : List (BitVec 8) → Prop)
    (hreg : region_ok (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      ((CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecT
        C A ctl uuidTryParse S img).withVRegs.restrictPre (Q ·.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State)
    (hRS : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.RegionSomeStateV
      C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope
      x ans (TokenInit img ∗ R) s0 s) :
    (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.PostSomeStateV
          C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope
          x ans (TokenInit img ∗ R) s0 s' ∨
        SubroutineOutcome
          (withStoresDecSpecVT C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
          x R s0 s') := by
  intro hL
  obtain ⟨hpc, ⟨hrun, hsp, hal0, hal, hx29, _hx27, hfrozen, hsym, hvregs⟩,
    rec, ses, G, prevCap, prevPtr, hload, hscope, hcur, hw0, htrace, hmem⟩ := hRS
  let x_rg := recGhostOf x prevPtr G ses.state
  let R_rg := wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗
    decStoreExtra kit ikit st0 ist0 s0 ∗ R
  obtain ⟨hpq_lt, hpq_Q⟩ := hQ x.rem.val rec ses hscope hcur
  have hmem_rg : s.mem ⊨
      (TokenInit img ∗
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img).pre
          x_rg s) ∗ R_rg := by
    dsimp only [x_rg, R_rg]
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hmem
  have hmemT : s.mem ⊨
      ((CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecT
        C A ctl uuidTryParse S img).withVRegs.restrictPre (Q ·.st.pqRatchetState)).pre x_rg s ∗ R_rg := by
    dsimp only [Spec.restrictPre, Spec.withVRegs,
      CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecT]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpq_Q, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpq_lt, by simpa only [sepConj_assoc] using hmem_rg⟩
  obtain ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, hmf⟩ | ⟨hpan_sf, hmf⟩⟩ :=
    hreg x_rg R_rg s hpc hrun hmemT hL
  · refine ⟨sf, hsteps, Or.inl ?_⟩
    dsimp only [Spec.restrictPre, Spec.withVRegs] at hmf
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf
    obtain ⟨hvregs_sf, hmf⟩ := hmf
    have hmf' : sf.mem ⊨
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img).post
          x_rg s sf ∗
          (wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗
            decStoreExtra kit ikit st0 ist0 s0 ∗ (TokenInit img ∗ R)) := by
      dsimp only [CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecT, x_rg, R_rg] at hmf ⊢
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hmf
    obtain ⟨hsp_sf, hx29_sf, hx27_sf⟩ :=
      post_meta_extract_ext hmf'
    have hfrozen_sf : img.FrozenLoaded sf := hfrozen.of_keepsFrozen hsteps.keepsFrozen
    have hsym_sf : sf.symtab = img.symtab := hsteps.symtab_eq.trans hsym
    have hal_sf : sf.spAligned = true := by
      rw [State.spAligned, hsp_sf]
      exact hal
    have hmeta_sf : wsMeta img x s0 sf :=
      ⟨hrun_sf, hsp_sf.trans hsp, hal0, hal_sf, hx29_sf.trans hx29,
        hx27_sf, hfrozen_sf, hsym_sf, hvregs_sf.trans hvregs⟩
    refine ⟨hpc_sf, hmeta_sf, s, rec, ses, G, prevCap, prevPtr, hsp, htrace,
      hload, hscope, hcur, hw0, ?_⟩
    simpa only [sepConj_assoc] using hmf'
  · refine ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan_sf, ?_⟩))⟩
    dsimp only [Spec.restrictPre, Spec.withVRegs,
      CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecT,
      CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec,
      withStoresDecSpecVT, CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecV,
      Spec.inImage, R_rg] at hmf ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf
    rcases hmf with ⟨⟨hdisj, hpref⟩, hmf⟩
    have hload_pref : s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession <+: sf.trace := by
      rwa [← htrace]
    have hs0_pref : s0.trace <+: sf.trace :=
      (List.prefix_append s0.trace (kit.loadEvs encRecord x.rem.val ans.loadSession)).trans hload_pref
    have hpan_pure :
        s0.trace <+: sf.trace ∧
          (allocFailedIn s0 sf ∨
            ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
              kit.loadRel st0 x.rem.val answers.loadSession ∧
              s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
              ((x.model C S uuidTryParse answers).1 = .error .panic ∨ x.recvPanics S answers)) := by
      refine ⟨hs0_pref, ?_⟩
      rcases hdisj with hmod_pan | hrecv_pan | halloc
      · exact Or.inr ⟨ans, hload ▸ hscope.2, hload_pref, Or.inl
          (Pf.SegRegionSome.model_panic_of_region_panic C S x ans rec ses G prevPtr hload hcur hmod_pan)⟩
      · exact Or.inr ⟨ans, hload ▸ hscope.2, hload_pref, Or.inr
          (Pf.SegRegionSome.recvPanics_of_region_recvPanics S x ans rec ses G prevPtr hload hcur hrecv_pan)⟩
      · exact Or.inl (Pf.SegRegionSome.allocFailedIn_of_load_prefix htrace hpref halloc)
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpan_pure, ?_⟩
    have h_any : anyHeap ∗ (wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗
        decStoreExtra kit ikit st0 ist0 s0) ⊢ anyHeap :=
      entails_anyHeap _
    rw [← sepConj_assoc, ← sepConj_assoc] at hmf
    rw [sepConj_assoc anyHeap] at hmf
    exact Satisfies.mono (sepConj_mono_left h_any) hmf

/-! ## Callee bundles and `TrapsOnly` transfer -/

/-- Callee contracts at `tripleRatchetProgAtExt img.base ext` for `withStoresDecSpecVTP`. -/
structure DecCalleesTPExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) (Q : List (BitVec 8) → Prop) :
    Prop where
  region : region_ok (tripleRatchetProgAtExt img.base ext)
    (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
    (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
    ((CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight
      C A ctl uuidTryParse S img).withVRegs.restrictPre (Q ·.st.pqRatchetState))
  remoteIk : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr Getters.remoteIdentityKeyName)
    (Getters.remoteIdentityKeySpec A img)
  dropSs : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt
    img.base A ext

/-- Callee contracts at `tripleRatchetProgAtExt img.base ext` for `withStoresDecSpecVT`. -/
structure DecCalleesTExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) (Q : List (BitVec 8) → Prop) :
    Prop where
  region : region_ok (tripleRatchetProgAtExt img.base ext)
    (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
    (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
    ((CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecT
      C A ctl uuidTryParse S img).withVRegs.restrictPre (Q ·.st.pqRatchetState))
  remoteIk : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr Getters.remoteIdentityKeyName)
    (Getters.remoteIdentityKeySpec A img)
  dropSs : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt
    img.base A ext

/-- Transfers `DecCalleesTPExt` from `trTrapProgAt` to `tripleRatchetProgAtExt img.base (cliExterns W)`. -/
theorem DecCalleesTPExt.of_trTrap_cli {img : Obj.Image} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {Q : List (BitVec 8) → Prop}
    (W : CryptoVerification.SignalSession.CliHooks)
    (h : DecCalleesTPExt img W.C A ctl S (trTrapExterns W.C (CryptoVerification.SignalSession.cliExterns W)) Q) :
    DecCalleesTPExt img W.C A ctl S (CryptoVerification.SignalSession.cliExterns W) Q where
  region := region_ok_of_trapsOnly
    (CryptoVerification.SignalSession.Cli.Slots.trapsOnly_trTrap_cli img.base W) h.region
  remoteIk := CryptoVerification.SignalSession.Cli.Slots.subroutine_ok_cli_of_trTrap h.remoteIk
  dropSs := CryptoVerification.SignalSession.Cli.Slots.subroutine_ok_cli_of_trTrap h.dropSs

/-- Transfers `DecCalleesTExt` from `trTrapProgAt` to `tripleRatchetProgAtExt img.base (cliExterns W)`. -/
theorem DecCalleesTExt.of_trTrap_cli {img : Obj.Image} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {Q : List (BitVec 8) → Prop}
    (W : CryptoVerification.SignalSession.CliHooks)
    (h : DecCalleesTExt img W.C A ctl S (trTrapExterns W.C (CryptoVerification.SignalSession.cliExterns W)) Q) :
    DecCalleesTExt img W.C A ctl S (CryptoVerification.SignalSession.cliExterns W) Q where
  region := region_ok_of_trapsOnly
    (CryptoVerification.SignalSession.Cli.Slots.trapsOnly_trTrap_cli img.base W) h.region
  remoteIk := CryptoVerification.SignalSession.Cli.Slots.subroutine_ok_cli_of_trTrap h.remoteIk
  dropSs := CryptoVerification.SignalSession.Cli.Slots.subroutine_ok_cli_of_trTrap h.dropSs

/-! ## Twelve-segment assembly -/

section ChainVTP

variable {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {ext : String → Option (State → State)}
  {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
  {st0 : kit.StoreState} {ist0 : ikit.IdState}
  {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
  (hH : DecHypsExt4K img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
  (hC : DecCalleesTPExt img C A ctl S ext Q)
  (x : DecryptGhost) (R : SepProp) (s0 : State)
  (hAddr : kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val)

include hH in
private theorem reachVTP_resultFinal_ext (s : State)
    (h : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ResultFinalStateV
      C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x (TokenInit img ∗ R) s0 s) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegVTP_chain_ext (segWriteVX_ok_ext hH.loads x (TokenInit img ∗ R) s0 s h) (fun _ hf => hf.elim)

include hH hC in
private theorem reachVTP_errJoin_ext (pt : Bool) (s : State)
    (h : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV
      C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x pt (TokenInit img ∗ R) s0 s) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegVTP_chain_ext (segErrTeardownVX_ok_ext4K hH hC.dropSs x pt (TokenInit img ∗ R) s0 s h)
    (reachVTP_resultFinal_ext hH x R s0)

include hH hC hAddr in
private theorem reachVTP_storeCall_ext (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxExt kit ikit ext s0 s)
    (h : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.StoreCallStateV
      C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans (TokenInit img ∗ R) s0 s) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegVTP_chain_ext (segStoreVX_ok_ext4K hH hC.dropSs x ans (TokenInit img ∗ R) s0 s hAddr.1 hfs h)
    (fun s' h' => h'.elim
      (reachVTP_resultFinal_ext hH x R s0 s')
      (reachVTP_errJoin_ext hH hC x R s0 true s'))

include hH hC hAddr in
private theorem reachVTP_trusted_ext (ans : StoreAnswers (List (BitVec 8)) Unit) (t : Bool)
    (s : State) (hfs : DecFsCtxExt kit ikit ext s0 s)
    (h : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.TrustedStateV
      C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans t (TokenInit img ∗ R) s0 s) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
      x R s0 s := by
  cases t with
  | true =>
    exact decSegVTP_chainFs_ext hfs (segSaveVX_ok_ext4K hH x ans (TokenInit img ∗ R) s0 s hAddr.2 hfs h)
      (fun s' hfs' h' => h'.elim
        (fun ⟨ans', hsc⟩ => reachVTP_storeCall_ext hH hC x R s0 hAddr ans' s' hfs' hsc)
        (reachVTP_errJoin_ext hH hC x R s0 true s'))
  | false =>
    exact decSegVTP_chain_ext (segUntrustedVX_ok_of_loads_ext hH.loads hH.alloc x ans (TokenInit img ∗ R) s0 s h)
      (reachVTP_errJoin_ext hH hC x R s0 true)

include hH hC hAddr in
private theorem reachVTP_keyReady_ext (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxExt kit ikit ext s0 s)
    (h : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.KeyReadyStateV
      C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans (TokenInit img ∗ R) s0 s) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegVTP_chainFs_ext hfs (segTrustVX_ok_ext4K hH x ans (TokenInit img ∗ R) s0 s hAddr.2 hfs h)
    (fun s' hfs' h' => h'.elim
      (fun ⟨ans', t, ht⟩ => reachVTP_trusted_ext hH hC x R s0 hAddr ans' t s' hfs' ht)
      (reachVTP_errJoin_ext hH hC x R s0 true s'))

include hH hC hAddr in
private theorem reachVTP_loadPolled_ext
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hid : IdOrDistinctSid uuidTryParse kit st0 Scope x)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxExt kit ikit ext s0 s)
    (h : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.LoadPolledStateV
      ctl encRecord img kit ikit st0 ist0 Scope x ans (TokenInit img ∗ R) s0 s) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
      x R s0 s := by
  refine decSegVTP_chainFs_ext hfs (segDispatchVP_ok_ext4K hH x ans (TokenInit img ∗ R) s0 s hid h) ?_
  rintro s' hfs' (hSome | hNone | hFin)
  · refine Arm64.reaches_outcome.of_codeLoaded fun hL => ?_
    obtain ⟨s'', hst, hPost | hout⟩ :=
      segRegionSomeVTP_ok_ext Q hC.region hQ x ans R s0 s' hSome hL
    · refine Arm64.reaches_outcome_steps hst ?_
      exact decSegVTP_chainFs_ext (hfs'.of_steps hst)
        (segPostSomeVX_ok_of_loads_ext hH.loads hC.remoteIk x ans (TokenInit img ∗ R) s0 s'' hPost)
        (fun s3 hfs3 h3 => h3.elim
          (reachVTP_keyReady_ext hH hC x R s0 hAddr ans s3 hfs3)
          (reachVTP_errJoin_ext hH hC x R s0 false s3))
    · exact Arm64.reaches_outcome_steps hst (Arm64.reaches_outcome.of_outcome hout)
  · refine decSegVTP_chain_ext (segRegionNoneVX_ok_ext4K hH.loads hH.alloc x ans (TokenInit img ∗ R) s0 s' hNone) ?_
    intro s'' hPost
    exact decSegVTP_chain_ext (segPostNoneVX_ok_ext hH.loads x ans (TokenInit img ∗ R) s0 s'' hPost)
      (reachVTP_errJoin_ext hH hC x R s0 false)
  · exact reachVTP_resultFinal_ext hH x R s0 s' hFin

end ChainVTP

/-- Per-ghost reachability (`4K` stack hooks) for `withStoresDecSpecVTP` with entry-file `envOk`. -/
theorem withStoresDec_reachVTP_fs_ext4K {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExt4K img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (hC : DecCalleesTPExt img C A ctl S ext Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (x : DecryptGhost) (R : SepProp) (s0 : State)
    (hid : IdOrDistinctSid uuidTryParse kit st0 Scope x)
    (hpc : s0.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.wsEntryPC img)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨
      (withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).pre
        x s0 ∗ R)
    (hal : s0.spAligned = true)
    (hfs : DecFsCtxExt kit ikit ext s0 s0) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
      x R s0 s0 := by
  have hpreV : s0.mem ⊨
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecVX
        C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope (fun _ _ => False)).pre x s0 ∗
        (TokenInit img ∗ R) := by
    dsimp only [withStoresDecSpecVTP] at hpre
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
  have hAddr := CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecV_pre_addrOk
    (C := C) (ctl := ctl) (S := S) (encRecord := encRecord) (Scope := Scope) hpreV
  exact decSegVTP_chainFs_ext hfs
    (segLoadVX_ok_of_kit_ext hH.loads hH.kit x (TokenInit img ∗ R) s0 hfs hpc hrun hal hpreV)
    (fun s hfs' ⟨ans, h⟩ => reachVTP_loadPolled_ext hH hC x R s0 hAddr hQ hid ans s hfs' h)

/-- Per-ghost reachability for `withStoresDecSpecVTP` with entry-file `envOk`. -/
theorem withStoresDec_reachVTP_fs_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExt img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (hC : DecCalleesTPExt img C A ctl S ext Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (x : DecryptGhost) (R : SepProp) (s0 : State)
    (hid : IdOrDistinctSid uuidTryParse kit st0 Scope x)
    (hpc : s0.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.wsEntryPC img)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨
      (withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).pre
        x s0 ∗ R)
    (hal : s0.spAligned = true)
    (hfs : DecFsCtxExt kit ikit ext s0 s0) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
      x R s0 s0 :=
  withStoresDec_reachVTP_fs_ext4K hH.toDecHypsExt4K hC hQ x R s0 hid hpc hrun hpre hal hfs

/-- `subroutine_ok` (`4K` stack hooks) for `withStoresDecSpecVTP` under `IdOrDistinctSid`. -/
theorem withStoresDec_okVTP_fs_ext4K {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExt4K img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (hC : DecCalleesTPExt img C A ctl S ext Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base ext)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.wsEntryPC img)
      (withEnvPre
        ((withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).restrictPre
          (IdOrDistinctSid uuidTryParse kit st0 Scope))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  refine Arm64.subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre0 hal => ?_
  obtain ⟨h0, hpreR⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  dsimp only [Spec.restrictPre] at hpreR
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpreR
  exact (withStoresDec_reachVTP_fs_ext4K hH hC hQ x R s0 hpreR.1 hpc hrun hpreR.2 hal
    (FsCtx.of_entry hKitFs h0)).mono_outcome fun _ hout => hout

/-- `subroutine_ok` for `withStoresDecSpecVTP` under `IdOrDistinctSid` and entry-file `envOk`. -/
theorem withStoresDec_okVTP_fs_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExt img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (hC : DecCalleesTPExt img C A ctl S ext Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base ext)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.wsEntryPC img)
      (withEnvPre
        ((withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).restrictPre
          (IdOrDistinctSid uuidTryParse kit st0 Scope))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTP_fs_ext4K hH.toDecHypsExt4K hC hQ hKitFs

/-- Specialization of `withStoresDec_okVTP_fs_ext4K` to `DistinctSid`. -/
theorem withStoresDec_okVTP_distinct_fs_ext4K
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExt4K img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (hC : DecCalleesTPExt img C A ctl S ext Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base ext)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.wsEntryPC img)
      (withEnvPre
        ((withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).restrictPre
          (fun x => CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid
            uuidTryParse x.loc.name.bytes x.rem.name.bytes))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  refine Arm64.subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre0 hal => ?_
  obtain ⟨h0, hpreR⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  dsimp only [Spec.restrictPre] at hpreR
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpreR
  exact (withStoresDec_reachVTP_fs_ext4K hH hC hQ x R s0
    (idOrDistinctSid_of_distinctSid hpreR.1) hpc hrun hpreR.2 hal
    (FsCtx.of_entry hKitFs h0)).mono_outcome fun _ hout => hout

/-- Specialization of `withStoresDec_okVTP_fs_ext` to `DistinctSid`. -/
theorem withStoresDec_okVTP_distinct_fs_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExt img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (hC : DecCalleesTPExt img C A ctl S ext Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base ext)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.wsEntryPC img)
      (withEnvPre
        ((withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).restrictPre
          (fun x => CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid
            uuidTryParse x.loc.name.bytes x.rem.name.bytes))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTP_distinct_fs_ext4K hH.toDecHypsExt4K hC hQ hKitFs

theorem withStoresDec_okVTP_ext4K {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExt4K img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (hC : DecCalleesTPExt img C A ctl S ext Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.wsEntryPC img)
      ((withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).restrictPre
        (IdOrDistinctSid uuidTryParse kit st0 Scope)) :=
  subroutine_ok_of_withEnvPre (withStoresDec_okVTP_fs_ext4K hH hC hQ (.inl htriv))
    fun s => htriv s.fs.files

theorem withStoresDec_okVTP_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExt img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (hC : DecCalleesTPExt img C A ctl S ext Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.wsEntryPC img)
      ((withStoresDecSpecVTP C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).restrictPre
        (IdOrDistinctSid uuidTryParse kit st0 Scope)) :=
  withStoresDec_okVTP_ext4K hH.toDecHypsExt4K hC hQ htriv

section ChainVT

variable {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {ext : String → Option (State → State)}
  {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
  {st0 : kit.StoreState} {ist0 : ikit.IdState}
  {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
  (hH : DecHypsExt4K img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
  (hscopeIn : ∀ r, Scope r → RecordInScope r)
  (hC : DecCalleesTExt img C A ctl S ext Q)
  (x : DecryptGhost) (R : SepProp) (s0 : State)
  (hAddr : kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val)

include hH in
private theorem reachVT_resultFinal_ext (s : State)
    (h : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ResultFinalStateV
      C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x (TokenInit img ∗ R) s0 s) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (withStoresDecSpecVT C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegVT_chain_ext (segWriteVX_ok_ext hH.loads x (TokenInit img ∗ R) s0 s h) (fun _ hf => hf.elim)

include hH hC in
private theorem reachVT_errJoin_ext (pt : Bool) (s : State)
    (h : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV
      C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x pt (TokenInit img ∗ R) s0 s) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (withStoresDecSpecVT C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegVT_chain_ext (segErrTeardownVX_ok_ext4K hH hC.dropSs x pt (TokenInit img ∗ R) s0 s h)
    (reachVT_resultFinal_ext hH x R s0)

include hH hC hAddr in
private theorem reachVT_storeCall_ext (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxExt kit ikit ext s0 s)
    (h : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.StoreCallStateV
      C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans (TokenInit img ∗ R) s0 s) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (withStoresDecSpecVT C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegVT_chain_ext (segStoreVX_ok_ext4K hH hC.dropSs x ans (TokenInit img ∗ R) s0 s hAddr.1 hfs h)
    (fun s' h' => h'.elim
      (reachVT_resultFinal_ext hH x R s0 s')
      (reachVT_errJoin_ext hH hC x R s0 true s'))

include hH hC hAddr in
private theorem reachVT_trusted_ext (ans : StoreAnswers (List (BitVec 8)) Unit) (t : Bool)
    (s : State) (hfs : DecFsCtxExt kit ikit ext s0 s)
    (h : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.TrustedStateV
      C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans t (TokenInit img ∗ R) s0 s) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (withStoresDecSpecVT C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
      x R s0 s := by
  cases t with
  | true =>
    exact decSegVT_chainFs_ext hfs (segSaveVX_ok_ext4K hH x ans (TokenInit img ∗ R) s0 s hAddr.2 hfs h)
      (fun s' hfs' h' => h'.elim
        (fun ⟨ans', hsc⟩ => reachVT_storeCall_ext hH hC x R s0 hAddr ans' s' hfs' hsc)
        (reachVT_errJoin_ext hH hC x R s0 true s'))
  | false =>
    exact decSegVT_chain_ext (segUntrustedVX_ok_of_loads_ext hH.loads hH.alloc x ans (TokenInit img ∗ R) s0 s h)
      (reachVT_errJoin_ext hH hC x R s0 true)

include hH hC hAddr in
private theorem reachVT_keyReady_ext (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxExt kit ikit ext s0 s)
    (h : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.KeyReadyStateV
      C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans (TokenInit img ∗ R) s0 s) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (withStoresDecSpecVT C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegVT_chainFs_ext hfs (segTrustVX_ok_ext4K hH x ans (TokenInit img ∗ R) s0 s hAddr.2 hfs h)
    (fun s' hfs' h' => h'.elim
      (fun ⟨ans', t, ht⟩ => reachVT_trusted_ext hH hC x R s0 hAddr ans' t s' hfs' ht)
      (reachVT_errJoin_ext hH hC x R s0 true s'))

include hH hscopeIn hC hAddr in
private theorem reachVT_loadPolled_ext
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxExt kit ikit ext s0 s)
    (h : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.LoadPolledStateV
      ctl encRecord img kit ikit st0 ist0 Scope x ans (TokenInit img ∗ R) s0 s) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (withStoresDecSpecVT C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
      x R s0 s := by
  refine decSegVT_chainFs_ext hfs (segDispatchVX_ok_ext4K hH hscopeIn x ans (TokenInit img ∗ R) s0 s h) ?_
  rintro s' hfs' (hSome | hNone | hFin)
  · refine Arm64.reaches_outcome.of_codeLoaded fun hL => ?_
    obtain ⟨s'', hst, hPost | hout⟩ :=
      segRegionSomeVT_ok_ext Q hC.region hQ x ans R s0 s' hSome hL
    · refine Arm64.reaches_outcome_steps hst ?_
      exact decSegVT_chainFs_ext (hfs'.of_steps hst)
        (segPostSomeVX_ok_of_loads_ext hH.loads hC.remoteIk x ans (TokenInit img ∗ R) s0 s'' hPost)
        (fun s3 hfs3 h3 => h3.elim
          (reachVT_keyReady_ext hH hC x R s0 hAddr ans s3 hfs3)
          (reachVT_errJoin_ext hH hC x R s0 false s3))
    · exact Arm64.reaches_outcome_steps hst (Arm64.reaches_outcome.of_outcome hout)
  · refine decSegVT_chain_ext (segRegionNoneVX_ok_ext4K hH.loads hH.alloc x ans (TokenInit img ∗ R) s0 s' hNone) ?_
    intro s'' hPost
    exact decSegVT_chain_ext (segPostNoneVX_ok_ext hH.loads x ans (TokenInit img ∗ R) s0 s'' hPost)
      (reachVT_errJoin_ext hH hC x R s0 false)
  · exact reachVT_resultFinal_ext hH x R s0 s' hFin

end ChainVT

/-- `subroutine_ok` (`4K` stack hooks) for `withStoresDecSpecVT` under `Scope ⊆ RecordInScope`. -/
theorem withStoresDec_okVT_fs_ext4K {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExt4K img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (hscopeIn : ∀ r, Scope r → RecordInScope r)
    (hC : DecCalleesTExt img C A ctl S ext Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base ext)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.wsEntryPC img)
      (withEnvPre (withStoresDecSpecVT C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  refine Arm64.subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre0 hal => ?_
  obtain ⟨h0, hpre⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  have hpreV : s0.mem ⊨
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecV
        C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).pre x s0 ∗
        (TokenInit img ∗ R) := by
    dsimp only [withStoresDecSpecVT] at hpre
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
  have hAddr := CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecV_pre_addrOk hpreV
  have hfs0 : DecFsCtxExt kit ikit ext s0 s0 := FsCtx.of_entry hKitFs h0
  exact decSegVT_chainFs_ext hfs0
    (segLoadVX_ok_of_kit_ext hH.loads hH.kit x (TokenInit img ∗ R) s0 hfs0 hpc hrun hal hpreV)
    (fun s hfs ⟨ans, h⟩ => reachVT_loadPolled_ext hH hscopeIn hC x R s0 hAddr hQ ans s hfs h)

/-- `subroutine_ok` for `withStoresDecSpecVT` under `Scope ⊆ RecordInScope`. -/
theorem withStoresDec_okVT_fs_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExt img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (hscopeIn : ∀ r, Scope r → RecordInScope r)
    (hC : DecCalleesTExt img C A ctl S ext Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base ext)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.wsEntryPC img)
      (withEnvPre (withStoresDecSpecVT C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVT_fs_ext4K hH.toDecHypsExt4K hscopeIn hC hQ hKitFs

theorem withStoresDec_okVT_ext4K {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExt4K img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (hscopeIn : ∀ r, Scope r → RecordInScope r)
    (hC : DecCalleesTExt img C A ctl S ext Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.wsEntryPC img)
      (withStoresDecSpecVT C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope) :=
  subroutine_ok_of_withEnvPre (withStoresDec_okVT_fs_ext4K hH hscopeIn hC hQ (.inl htriv))
    fun s => htriv s.fs.files

theorem withStoresDec_okVT_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExt img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (hscopeIn : ∀ r, Scope r → RecordInScope r)
    (hC : DecCalleesTExt img C A ctl S ext Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.wsEntryPC img)
      (withStoresDecSpecVT C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope) :=
  withStoresDec_okVT_ext4K hH.toDecHypsExt4K hscopeIn hC hQ htriv

end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT
