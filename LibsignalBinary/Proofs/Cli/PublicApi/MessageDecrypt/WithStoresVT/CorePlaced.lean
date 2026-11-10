/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.AssemblyPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.Core
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegBatch1Placed
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegDispatchExtPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegRegionNoneExtPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegPostSomeExtPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegTrustExtPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegUntrustedExtPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegSaveExtPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegStoreExtPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegErrTeardownExtPlaced
public import LibsignalBinary.Proofs.SpqrV1.GF.Mul2U16
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegBatch1
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegErrTeardownExt
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegPostSomeExt
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegRegionNoneExt
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegSaveExt
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegStoreExt
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegTrustExt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridge

/-!
# Relocatable Token-Framed `MessageDecrypt` Assembly (`WithStoresVT.CorePlaced`)

Assembles the twelve relocatable (`[LibsignalPlacement]`) `MessageDecrypt` segments on `lsProg_463 H`
for token-framed `withStoresDecPlacedSpecVTPF` / `withStoresDecPlacedSpecVTP` (tight `onPanic`,
weak `RecordInScopeP` and `IdOrDistinctSid`) and `withStoresDecPlacedSpecVTF` / `withStoresDecPlacedSpecVT`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT

open Arm64 ProofLib ProofLib.Variant CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification (LibsignalFrozen libsignalFrozen_of_keepsFrozen)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Record hiding
  recordDecryptPlacedSpec recEntryPlaced recExitPlaced LibsignalCodeRoLoaded
open CryptoVerification.Cli.LibsignalTripleRatchet.Record hiding lsProg_463 LibsignalCodeRoLoaded
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.CliRatchet.DecPlaced

/-! ## Token-framed `withStoresDecPlacedSpecVT` and `withStoresDecPlacedSpecVTP` -/

/-- `withStoresDecPlacedSpecV` with token invariant `F0` framed in `pre` and `post`. -/
def withStoresDecPlacedSpecVTF [LibsignalPlacement] (F0 : SepProp)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Spec DecryptGhost :=
  { CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecV
      C A ctl parse S encRecord kit ikit st0 ist0 Scope with
    pre := fun x s =>
      F0 ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecV
          C A ctl parse S encRecord kit ikit st0 ist0 Scope).pre x s
    post := fun x s0 sf =>
      F0 ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecV
          C A ctl parse S encRecord kit ikit st0 ist0 Scope).post x s0 sf }

/-- `withStoresDecPlacedSpecVTF` specialized to `SpqrV1.GF.Mul2U16.tokenInitPlacedAt`. -/
abbrev withStoresDecPlacedSpecVT [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Spec DecryptGhost :=
  withStoresDecPlacedSpecVTF SpqrV1.GF.Mul2U16.tokenInitPlacedAt
    C A ctl parse S encRecord kit ikit st0 ist0 Scope

/-- Tight-panic `withStoresDecPlacedSpecVX` (`Extra := fun _ _ => False`) with `F0` framed. -/
def withStoresDecPlacedSpecVTPF [LibsignalPlacement] (F0 : SepProp)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Spec DecryptGhost :=
  { CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecVX
      C A ctl parse S encRecord kit ikit st0 ist0 Scope (fun _ _ => False) with
    pre := fun x s =>
      F0 ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecVX
          C A ctl parse S encRecord kit ikit st0 ist0 Scope (fun _ _ => False)).pre x s
    post := fun x s0 sf =>
      F0 ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecVX
          C A ctl parse S encRecord kit ikit st0 ist0 Scope (fun _ _ => False)).post x s0 sf }

/-- `withStoresDecPlacedSpecVTPF` specialized to `SpqrV1.GF.Mul2U16.tokenInitPlacedAt`. -/
abbrev withStoresDecPlacedSpecVTP [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Spec DecryptGhost :=
  withStoresDecPlacedSpecVTPF SpqrV1.GF.Mul2U16.tokenInitPlacedAt
    C A ctl parse S encRecord kit ikit st0 ist0 Scope

/-! ## Record-level relocatable specifications (`P`, `T`, `TPTight`) -/

/-- `recordDecryptPlacedSpec` weakened to `remoteIdentity ≠ some localIdentity ∨ DistinctSid uuidParse loc rem`. -/
def recordDecryptPlacedSpecP [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) : Spec RecordDecryptGhost :=
  { recordDecryptPlacedSpec C A ctl uuidParse S with
    pre := fun x s =>
      ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s.mem⌝ ∗
      ⌜s.spAligned = true ∧ s.readReg64 .x27 = x.sret ∧ s.readReg64 .x19 = x.remA ∧
        s.readReg64 .x23 = s.sp + 0x5f0#64 ∧ s.readReg64 .x24 = s.sp + 0xca0#64 ∧
        (x.st.remoteIdentity ≠ some x.st.localIdentity ∨
          CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid uuidParse x.loc.name.bytes x.rem.name.bytes) ∧
        SeedsLen32 x.st ∧ x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s.sp.toNat⌝ ∗
      memRegion s.sp 0xa0 ∗ ((s.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s.sp + 0xf0#64) ↦₆₄ x.locA) ∗
      ((s.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
      sessionStateAt A (s.sp + 0x138#64) x.G x.st ∗ memRegion (s.sp + 0x4b0#64) 0x950 ∗
      protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      CryptoVerification.Cli.CoinsTape.cliTapeAt ctl x.cur x.rest ∗
      FromRecordCallees.lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool }

/-- `recordDecryptPlacedSpec` with `pqRatchetState.length < 2 ^ 32` and `F0` framed. -/
def recordDecryptPlacedSpecTF [LibsignalPlacement] (F0 : SepProp)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser) (S : SpqrModel) :
    Spec RecordDecryptGhost :=
  { recordDecryptPlacedSpec C A ctl uuidParse S with
    pre := fun x s =>
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗ F0 ∗
        (recordDecryptPlacedSpec C A ctl uuidParse S).pre x s
    post := fun x s0 sf =>
      F0 ∗ (recordDecryptPlacedSpec C A ctl uuidParse S).post x s0 sf }

/-- `recordDecryptPlacedSpecTF` specialized to `SpqrV1.GF.Mul2U16.tokenInitPlacedAt`. -/
abbrev recordDecryptPlacedSpecT [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser) (S : SpqrModel) :
    Spec RecordDecryptGhost :=
  recordDecryptPlacedSpecTF SpqrV1.GF.Mul2U16.tokenInitPlacedAt C A ctl uuidParse S

/-- `recordDecryptPlacedSpecTF` with weak `recordDecryptPlacedSpecP` precondition and tight `recordDecryptOnPanicTight`. -/
def recordDecryptPlacedSpecTPTightF [LibsignalPlacement] (F0 : SepProp)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser) (S : SpqrModel) :
    Spec RecordDecryptGhost :=
  { recordDecryptPlacedSpecTF F0 C A ctl uuidParse S with
    pre := fun x s =>
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗ F0 ∗
        (recordDecryptPlacedSpecP C A ctl uuidParse S).pre x s
    onPanic := CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptOnPanicTight C S uuidParse }

/-- `recordDecryptPlacedSpecTPTightF` specialized to `SpqrV1.GF.Mul2U16.tokenInitPlacedAt`. -/
abbrev recordDecryptPlacedSpecTPTight [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser) (S : SpqrModel) :
    Spec RecordDecryptGhost :=
  recordDecryptPlacedSpecTPTightF SpqrV1.GF.Mul2U16.tokenInitPlacedAt C A ctl uuidParse S

/-! ## Weak-precondition `RegionSomeStatePVPlaced` and `segDispatchVP_placed_ok` -/

/-- `RegionSomeStateVPlaced` weakened to `recordDecryptPlacedSpecP`. -/
def RegionSomeStatePVPlaced [LibsignalPlacement] (C : Crypto) {A : RustAlloc} (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (R : SepProp) (s0 s : State) : Prop :=
  s.pc = recEntryPlaced ∧
  wsMetaPlaced x s0 s ∧
  ∃ (rec : SessionRecord (List (BitVec 8))) (ses : Session (List (BitVec 8))) (G : SessionGhost)
    (prevCap prevPtr : BitVec 64),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    rec.currentSession = some ses ∧ sessionModelRel G ses ∧
    s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
    (s.mem ⊨ (recordDecryptPlacedSpecP C A ctl parse S).pre
      (recGhostOf x prevPtr G ses.state) s ∗
      wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗
      decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ R)

section DispatchAndBridge

open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch (recordSome_split)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionSome

theorem regionSomePV_of_common_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (S : SpqrModel)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (x : DecryptGhost) (s0 sf : State) (sp : BitVec 64) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8))) (ses : Session (List (BitVec 8)))
    (hsp0 : s0.sp - 0xee0#64 = sp) (hsp : sf.sp = sp)
    (hscopeP : CryptoVerification.E2E.RecordX.RecordInScopeP rec)
    (hcur : rec.currentSession = some ses)
    (hid : ses.state.remoteIdentity ≠ some ses.state.localIdentity ∨
      CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid uuidTryParse x.loc.name.bytes x.rem.name.bytes)
    (hpure : StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ sf.spAligned = true ∧
      sf.readReg64 .x27 = x.ret ∧ sf.readReg64 .x19 = x.remA ∧
      sf.readReg64 .x23 = sp + 0x5f0#64 ∧ sf.readReg64 .x24 = sp + 0xca0#64 ∧
      rootStack ≤ sp.toNat) :
    sessionRecordAt A (sp + 0x120#64) g rec ∗
      regionCommonBodyPlaced A ctl x sp ∗
      wsRegionFrameRestPlaced kit ikit st0 ist0 x s0 sp ⊢
    ∃∗ G : SessionGhost,
      ⌜sessionModelRel G ses⌝ ∗
      (recordDecryptPlacedSpecP C A ctl uuidTryParse S).pre
        (recGhostOf x g.prevPtr G ses.state) sf ∗
      wsRegionFrameVPlaced kit ikit x s0 g.prevCap g.prevPtr ∗
      decStoreExtraPlaced kit ikit st0 ist0 s0 := by
  have hsplit := recordSome_split A (sp + 0x120#64) g rec ses hcur
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsplit
  refine Entails.trans (sepConj_mono_left hsplit) ?_
  simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro G
  refine Entails.sepExists_right G ?_
  rw [sepConj_assoc (⌜_⌝)]
  apply Entails.pure_left; intro hw0
  apply Entails.pure_right hw0
  have hsc := hscopeP ses hcur
  dsimp only [recordDecryptPlacedSpecP, recGhostOf]
  unfold regionCommonBodyPlaced wsRegionFrameVPlaced wsRegionFrameRestPlaced wsFixedVPlaced
  rw [hsp0, hsp]
  simp only [sepConj_assoc]
  apply Entails.pure_right hpure.1
  apply Entails.pure_right ⟨hpure.2.1, hpure.2.2.1, hpure.2.2.2.1,
    hpure.2.2.2.2.1, hpure.2.2.2.2.2.1, hid, hsc.1, hsc.2.1, hpure.2.2.2.2.2.2⟩
  exact Entails.of_eq (by ac_rfl)

theorem segDispatchVP_placed_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hH : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State)
    (hid : IdOrDistinctSid uuidTryParse kit st0 Scope x)
    (hLP : LoadPolledStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans R s0 s) :
    DecSegVXPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope Extra x R s0 s
      (fun s' =>
        RegionSomeStatePVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x ans R s0 s' ∨
        RegionNoneStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans R s0 s' ∨
        ResultFinalStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x R s0 s') := by
  refine segDispatchGen_placed_ok hH x ans R s0 s hLP ?_
  intro sf_3 g rec ses hpc3 hmeta3 hload hscope hscopeAt hcur htr3 hsp' hsp3 hpure3 hmf3'
  have hmf3'' := Satisfies.mono
    (sepConj_mono_left (regionSomePV_of_common_placed C A ctl S kit ikit st0 ist0 x s0 sf_3
      s.sp g rec ses hsp' hsp3
      (hH.scopeInP rec hscope) hcur (hid rec ses hscopeAt hcur) hpure3)) hmf3'
  rw [sepExists_sepConj_left, satisfies_sepExists] at hmf3''
  obtain ⟨G, hmf3''⟩ := hmf3''
  rw [sepConj_assoc (⌜_⌝), satisfies_pure_sepConj] at hmf3''
  obtain ⟨hw0, hmf3''⟩ := hmf3''
  simp only [sepConj_assoc] at hmf3''
  exact ⟨hpc3, hmeta3, rec, ses, G, g.prevCap, g.prevPtr, hload, hscopeAt, hcur, hw0, htr3, hmf3''⟩

/-! ## Outcome lifting and region crossing -/

private theorem subroutineOutcome_vx_to_framed_placed [LibsignalPlacement] {F0 : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome
      (withStoresDecPlacedSpecVX C A ctl parse S encRecord kit ikit st0 ist0 Scope Extra)
      x (F0 ∗ R) s0 sf) :
    SubroutineOutcome
      { withStoresDecPlacedSpecVX C A ctl parse S encRecord kit ikit st0 ist0 Scope Extra with
        pre := fun x s =>
          F0 ∗ (withStoresDecPlacedSpecVX C A ctl parse S encRecord kit ikit st0 ist0 Scope Extra).pre x s
        post := fun x s0 sf =>
          F0 ∗ (withStoresDecPlacedSpecVX C A ctl parse S encRecord kit ikit st0 ist0 Scope Extra).post x s0 sf }
      x R s0 sf := by
  rcases h with ⟨h1, hcs, hpost⟩ | ⟨hpan, honp⟩ | ⟨code, hexit, honex⟩ | ⟨hoom, honoom⟩
  · refine Or.inl ⟨h1, hcs, ?_⟩
    dsimp only
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withStoresDecPlacedSpecVX, StoreKit.withLsCodeRoLoaded] at honp ⊢
    refine Satisfies.mono ?_ honp
    rw [← sepConj_assoc, sepConj_assoc ⌜_⌝ anyHeap F0]
    refine sepConj_mono_left (sepConj_mono_right ?_)
    exact entails_anyHeap (anyHeap ∗ F0)
  · refine Or.inr (Or.inr (Or.inl ⟨code, hexit, ?_⟩))
    change sf.mem ⊨ ⌜False⌝ ∗ (F0 ∗ R) at honex
    rw [satisfies_pure_sepConj] at honex
    exact False.elim honex.1
  · refine Or.inr (Or.inr (Or.inr ⟨hoom, ?_⟩))
    change sf.mem ⊨ ⌜False⌝ ∗ (F0 ∗ R) at honoom
    rw [satisfies_pure_sepConj] at honoom
    exact False.elim honoom.1

private theorem decSegVTPF_chain_placed [LibsignalPlacement] {F0 : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {next : State → Prop}
    (h1 : DecSegVXPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope
      (fun _ _ => False) x (F0 ∗ R) s0 s next)
    (h2 : ∀ s', next s' → reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTPF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) x R s0 s') :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTPF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) x R s0 s := by
  intro hL
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf hnext) hL
  · exact ⟨sf, hst, subroutineOutcome_vx_to_framed_placed hout⟩

private theorem decSegVTPF_chainFs_placed [LibsignalPlacement] {F0 : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {next : State → Prop}
    (hfs : DecFsCtxExtPlaced kit ikit H s0 s)
    (h1 : DecSegVXPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope
      (fun _ _ => False) x (F0 ∗ R) s0 s next)
    (h2 : ∀ s', DecFsCtxExtPlaced kit ikit H s0 s' → next s' →
      reaches_outcome (lsProg_463 H)
        (withStoresDecPlacedSpecVTPF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) x R s0 s') :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTPF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) x R s0 s := by
  intro hL
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf (hfs.of_steps hst) hnext) hL
  · exact ⟨sf, hst, subroutineOutcome_vx_to_framed_placed hout⟩

private theorem decSegVTF_chain_placed [LibsignalPlacement] {F0 : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {next : State → Prop}
    (h1 : DecSegVXPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope
      (fun x answers => x.recvPanics S answers) x (F0 ∗ R) s0 s next)
    (h2 : ∀ s', next s' → reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) x R s0 s') :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) x R s0 s := by
  intro hL
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf hnext) hL
  · exact ⟨sf, hst, subroutineOutcome_vx_to_framed_placed hout⟩

private theorem decSegVTF_chainFs_placed [LibsignalPlacement] {F0 : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {next : State → Prop}
    (hfs : DecFsCtxExtPlaced kit ikit H s0 s)
    (h1 : DecSegVXPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope
      (fun x answers => x.recvPanics S answers) x (F0 ∗ R) s0 s next)
    (h2 : ∀ s', DecFsCtxExtPlaced kit ikit H s0 s' → next s' →
      reaches_outcome (lsProg_463 H)
        (withStoresDecPlacedSpecVTF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) x R s0 s') :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) x R s0 s := by
  intro hL
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf (hfs.of_steps hst) hnext) hL
  · exact ⟨sf, hst, subroutineOutcome_vx_to_framed_placed hout⟩

end DispatchAndBridge

/-- Crosses the record-decrypt region at `recordDecryptPlacedSpecTPTightF` restricted by `Q` for `withStoresDecPlacedSpecVTPF`. -/
theorem segRegionSomeVTP_placed_ok [LibsignalPlacement] {F0 : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (Q : List (BitVec 8) → Prop)
    (hreg : region_ok (lsProg_463 H) recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpecTPTightF F0 C A ctl uuidTryParse S).withVRegs.restrictPre
        (Q ·.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State)
    (hRS : RegionSomeStatePVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope
      x ans (F0 ∗ R) s0 s) :
    (lsProg_463 H).CodeLoaded s.mem →
    ∃ s', Steps (lsProg_463 H) s s' ∧
      (PostSomeStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope
          x ans (F0 ∗ R) s0 s' ∨
        SubroutineOutcome
          (withStoresDecPlacedSpecVTPF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
          x R s0 s') := by
  intro hL
  obtain ⟨hpc, ⟨hrun, hsp, hal0, hal, hx29, _hx27, hcrl, hvregs⟩,
    rec, ses, G, prevCap, prevPtr, hload, hscope, hcur, hw0, htrace, hmem⟩ := hRS
  let x_rg := recGhostOf x prevPtr G ses.state
  let R_rg := wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗
    decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ R
  obtain ⟨hpq_lt, hpq_Q⟩ := hQ x.rem.val rec ses hscope hcur
  have hmem_rg : s.mem ⊨
      (F0 ∗ (recordDecryptPlacedSpecP C A ctl uuidTryParse S).pre x_rg s) ∗ R_rg := by
    dsimp only [x_rg, R_rg]
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hmem
  have hmemT : s.mem ⊨
      ((recordDecryptPlacedSpecTPTightF F0 C A ctl uuidTryParse S).withVRegs.restrictPre
        (Q ·.st.pqRatchetState)).pre x_rg s ∗ R_rg := by
    dsimp only [Spec.restrictPre, Spec.withVRegs, recordDecryptPlacedSpecTPTightF]
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
        (recordDecryptPlacedSpec C A ctl uuidTryParse S).post x_rg s sf ∗
          (wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗
            decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ (F0 ∗ R)) := by
      dsimp only [recordDecryptPlacedSpecTPTightF, recordDecryptPlacedSpecTF,
        recordDecryptPlacedSpecP, x_rg, R_rg] at hmf ⊢
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hmf
    obtain ⟨hsp_sf, hx29_sf, hx27_sf⟩ :=
      CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionSome.post_meta_extract_placed hmf'
    have hcrl_sf : StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem := hcrl.of_keepsFrozen hsteps.keepsFrozen
    have hal_sf : sf.spAligned = true := by
      rw [State.spAligned, hsp_sf]
      exact hal
    have hmeta_sf : wsMetaPlaced x s0 sf :=
      ⟨hrun_sf, hsp_sf.trans hsp, hal0, hal_sf, hx29_sf.trans hx29,
        hx27_sf, hcrl_sf, hvregs_sf.trans hvregs⟩
    refine ⟨hpc_sf, hmeta_sf, s, rec, ses, G, prevCap, prevPtr, hsp, htrace,
      hload, hscope, hcur, hw0, ?_⟩
    simpa only [sepConj_assoc] using hmf'
  · refine ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan_sf, ?_⟩))⟩
    dsimp only [Spec.restrictPre, Spec.withVRegs,
      recordDecryptPlacedSpecTPTightF,
      CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptOnPanicTight,
      withStoresDecPlacedSpecVTPF, withStoresDecPlacedSpecVX,
      StoreKit.withLsCodeRoLoaded, R_rg] at hmf ⊢
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
          (CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionSome.model_panic_of_region_panic
            C S x ans rec ses G prevPtr hload hcur hmod_pan)⟩
      · exact Or.inl
          (CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionSome.allocFailedIn_of_load_prefix
            htrace hpref halloc)
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpan_pure, ?_⟩
    have h_any : anyHeap ∗ (wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗
        decStoreExtraPlaced kit ikit st0 ist0 s0) ⊢ anyHeap :=
      entails_anyHeap _
    rw [← sepConj_assoc, ← sepConj_assoc] at hmf
    rw [sepConj_assoc anyHeap] at hmf
    exact Satisfies.mono (sepConj_mono_left h_any) hmf

/-- `withLsFrozen`-guarded variant of `segRegionSomeVTP_placed_ok`. -/
theorem segRegionSomeVTP_frozen_placed_ok [LibsignalPlacement] {F0 : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (Q : List (BitVec 8) → Prop)
    (hreg : region_ok (lsProg_463 H) recEntryPlaced recExitPlaced
      ((withLsFrozen lsmpl (recordDecryptPlacedSpecTPTightF F0 C A ctl uuidTryParse S)).withVRegs.restrictPre
        (Q ·.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State)
    (hRS : RegionSomeStatePVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope
      x ans (F0 ∗ R) s0 s)
    (hFroz : LibsignalFrozen lsmpl s.mem) :
    (lsProg_463 H).CodeLoaded s.mem →
    ∃ s', Steps (lsProg_463 H) s s' ∧
      (PostSomeStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope
          x ans (F0 ∗ R) s0 s' ∨
        SubroutineOutcome
          (withStoresDecPlacedSpecVTPF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
          x R s0 s') := by
  intro hL
  obtain ⟨hpc, ⟨hrun, hsp, hal0, hal, hx29, _hx27, hcrl, hvregs⟩,
    rec, ses, G, prevCap, prevPtr, hload, hscope, hcur, hw0, htrace, hmem⟩ := hRS
  let x_rg := recGhostOf x prevPtr G ses.state
  let R_rg := wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗
    decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ R
  obtain ⟨hpq_lt, hpq_Q⟩ := hQ x.rem.val rec ses hscope hcur
  have hmem_rg : s.mem ⊨
      (F0 ∗ (recordDecryptPlacedSpecP C A ctl uuidTryParse S).pre x_rg s) ∗ R_rg := by
    dsimp only [x_rg, R_rg]
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hmem
  have hmemT : s.mem ⊨
      ((withLsFrozen lsmpl (recordDecryptPlacedSpecTPTightF F0 C A ctl uuidTryParse S)).withVRegs.restrictPre
        (Q ·.st.pqRatchetState)).pre x_rg s ∗ R_rg := by
    dsimp only [Spec.restrictPre, Spec.withVRegs, withLsFrozen, recordDecryptPlacedSpecTPTightF]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpq_Q, ?_⟩
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hFroz, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpq_lt, by simpa only [sepConj_assoc] using hmem_rg⟩
  obtain ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, hmf⟩ | ⟨hpan_sf, hmf⟩⟩ :=
    hreg x_rg R_rg s hpc hrun hmemT hL
  · refine ⟨sf, hsteps, Or.inl ?_⟩
    dsimp only [Spec.restrictPre, Spec.withVRegs, withLsFrozen] at hmf
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf
    obtain ⟨hvregs_sf, hmf⟩ := hmf
    have hmf' : sf.mem ⊨
        (recordDecryptPlacedSpec C A ctl uuidTryParse S).post x_rg s sf ∗
          (wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗
            decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ (F0 ∗ R)) := by
      dsimp only [recordDecryptPlacedSpecTPTightF, recordDecryptPlacedSpecTF,
        recordDecryptPlacedSpecP, x_rg, R_rg] at hmf ⊢
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hmf
    obtain ⟨hsp_sf, hx29_sf, hx27_sf⟩ :=
      CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionSome.post_meta_extract_placed hmf'
    have hcrl_sf : StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem := hcrl.of_keepsFrozen hsteps.keepsFrozen
    have hal_sf : sf.spAligned = true := by
      rw [State.spAligned, hsp_sf]
      exact hal
    have hmeta_sf : wsMetaPlaced x s0 sf :=
      ⟨hrun_sf, hsp_sf.trans hsp, hal0, hal_sf, hx29_sf.trans hx29,
        hx27_sf, hcrl_sf, hvregs_sf.trans hvregs⟩
    refine ⟨hpc_sf, hmeta_sf, s, rec, ses, G, prevCap, prevPtr, hsp, htrace,
      hload, hscope, hcur, hw0, ?_⟩
    simpa only [sepConj_assoc] using hmf'
  · refine ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan_sf, ?_⟩))⟩
    dsimp only [Spec.restrictPre, Spec.withVRegs, withLsFrozen,
      recordDecryptPlacedSpecTPTightF,
      CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptOnPanicTight,
      withStoresDecPlacedSpecVTPF, withStoresDecPlacedSpecVX,
      StoreKit.withLsCodeRoLoaded, R_rg] at hmf ⊢
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
          (CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionSome.model_panic_of_region_panic
            C S x ans rec ses G prevPtr hload hcur hmod_pan)⟩
      · exact Or.inl
          (CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionSome.allocFailedIn_of_load_prefix
            htrace hpref halloc)
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpan_pure, ?_⟩
    have h_any : anyHeap ∗ (wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗
        decStoreExtraPlaced kit ikit st0 ist0 s0) ⊢ anyHeap :=
      entails_anyHeap _
    rw [← sepConj_assoc, ← sepConj_assoc] at hmf
    rw [sepConj_assoc anyHeap] at hmf
    exact Satisfies.mono (sepConj_mono_left h_any) hmf

/-- Crosses the record-decrypt region at `recordDecryptPlacedSpecTF` restricted by `Q` for `withStoresDecPlacedSpecVTF`. -/
theorem segRegionSomeVT_placed_ok [LibsignalPlacement] {F0 : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (Q : List (BitVec 8) → Prop)
    (hreg : region_ok (lsProg_463 H) recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpecTF F0 C A ctl uuidTryParse S).withVRegs.restrictPre
        (Q ·.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State)
    (hRS : RegionSomeStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope
      x ans (F0 ∗ R) s0 s) :
    (lsProg_463 H).CodeLoaded s.mem →
    ∃ s', Steps (lsProg_463 H) s s' ∧
      (PostSomeStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope
          x ans (F0 ∗ R) s0 s' ∨
        SubroutineOutcome
          (withStoresDecPlacedSpecVTF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
          x R s0 s') := by
  intro hL
  obtain ⟨hpc, ⟨hrun, hsp, hal0, hal, hx29, _hx27, hcrl, hvregs⟩,
    rec, ses, G, prevCap, prevPtr, hload, hscope, hcur, hw0, htrace, hmem⟩ := hRS
  let x_rg := recGhostOf x prevPtr G ses.state
  let R_rg := wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗
    decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ R
  obtain ⟨hpq_lt, hpq_Q⟩ := hQ x.rem.val rec ses hscope hcur
  have hmem_rg : s.mem ⊨
      (F0 ∗ (recordDecryptPlacedSpec C A ctl uuidTryParse S).pre x_rg s) ∗ R_rg := by
    dsimp only [x_rg, R_rg]
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hmem
  have hmemT : s.mem ⊨
      ((recordDecryptPlacedSpecTF F0 C A ctl uuidTryParse S).withVRegs.restrictPre
        (Q ·.st.pqRatchetState)).pre x_rg s ∗ R_rg := by
    dsimp only [Spec.restrictPre, Spec.withVRegs, recordDecryptPlacedSpecTF]
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
        (recordDecryptPlacedSpec C A ctl uuidTryParse S).post x_rg s sf ∗
          (wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗
            decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ (F0 ∗ R)) := by
      dsimp only [recordDecryptPlacedSpecTF, x_rg, R_rg] at hmf ⊢
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hmf
    obtain ⟨hsp_sf, hx29_sf, hx27_sf⟩ :=
      CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionSome.post_meta_extract_placed hmf'
    have hcrl_sf : StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem := hcrl.of_keepsFrozen hsteps.keepsFrozen
    have hal_sf : sf.spAligned = true := by
      rw [State.spAligned, hsp_sf]
      exact hal
    have hmeta_sf : wsMetaPlaced x s0 sf :=
      ⟨hrun_sf, hsp_sf.trans hsp, hal0, hal_sf, hx29_sf.trans hx29,
        hx27_sf, hcrl_sf, hvregs_sf.trans hvregs⟩
    refine ⟨hpc_sf, hmeta_sf, s, rec, ses, G, prevCap, prevPtr, hsp, htrace,
      hload, hscope, hcur, hw0, ?_⟩
    simpa only [sepConj_assoc] using hmf'
  · refine ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan_sf, ?_⟩))⟩
    dsimp only [Spec.restrictPre, Spec.withVRegs,
      recordDecryptPlacedSpecTF, recordDecryptPlacedSpec,
      withStoresDecPlacedSpecVTF, withStoresDecPlacedSpecV,
      StoreKit.withLsCodeRoLoaded, R_rg] at hmf ⊢
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
          (CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionSome.model_panic_of_region_panic
            C S x ans rec ses G prevPtr hload hcur hmod_pan)⟩
      · exact Or.inr ⟨ans, hload ▸ hscope.2, hload_pref, Or.inr
          (CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionSome.recvPanics_of_region_recvPanics
            S x ans rec ses G prevPtr hload hcur hrecv_pan)⟩
      · exact Or.inl
          (CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionSome.allocFailedIn_of_load_prefix
            htrace hpref halloc)
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpan_pure, ?_⟩
    have h_any : anyHeap ∗ (wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗
        decStoreExtraPlaced kit ikit st0 ist0 s0) ⊢ anyHeap :=
      entails_anyHeap _
    rw [← sepConj_assoc, ← sepConj_assoc] at hmf
    rw [sepConj_assoc anyHeap] at hmf
    exact Satisfies.mono (sepConj_mono_left h_any) hmf

/-! ## Relocatable callee bundles -/

/-- Callee contracts on `lsProg_463 H` for `withStoresDecPlacedSpecVTPF`. -/
structure DecCalleesTPFPlaced [LibsignalPlacement] (F0 : SepProp)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : LibsignalHooks) (Q : List (BitVec 8) → Prop) : Prop where
  region : region_ok (lsProg_463 H) recEntryPlaced recExitPlaced
    ((recordDecryptPlacedSpecTPTightF F0 C A ctl uuidTryParse S).withVRegs.restrictPre
      (Q ·.st.pqRatchetState))
  remoteIk : RemoteIdentityKeyPlacedOk A H
  dropSs : DropSessionStructureLocal2PlacedOk A H

/-- `DecCalleesTPFPlaced` specialized to `SpqrV1.GF.Mul2U16.tokenInitPlacedAt`. -/
abbrev DecCalleesTPPlaced [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : LibsignalHooks) (Q : List (BitVec 8) → Prop) : Prop :=
  DecCalleesTPFPlaced SpqrV1.GF.Mul2U16.tokenInitPlacedAt C A ctl S H Q

/-- Callee contracts on `lsProg_463 H` for `withStoresDecPlacedSpecVTF`. -/
structure DecCalleesTFPlaced [LibsignalPlacement] (F0 : SepProp)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : LibsignalHooks) (Q : List (BitVec 8) → Prop) : Prop where
  region : region_ok (lsProg_463 H) recEntryPlaced recExitPlaced
    ((recordDecryptPlacedSpecTF F0 C A ctl uuidTryParse S).withVRegs.restrictPre
      (Q ·.st.pqRatchetState))
  remoteIk : RemoteIdentityKeyPlacedOk A H
  dropSs : DropSessionStructureLocal2PlacedOk A H

/-- `DecCalleesTFPlaced` specialized to `SpqrV1.GF.Mul2U16.tokenInitPlacedAt`. -/
abbrev DecCalleesTPlaced [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : LibsignalHooks) (Q : List (BitVec 8) → Prop) : Prop :=
  DecCalleesTFPlaced SpqrV1.GF.Mul2U16.tokenInitPlacedAt C A ctl S H Q

/-- Constructs `DecCalleesTPFPlaced` from the record-decrypt region contract and `rustDeallocSpec`. -/
theorem DecCalleesTPFPlaced.of_region [LibsignalPlacement] {F0 : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {H : LibsignalHooks} {Q : List (BitVec 8) → Prop}
    (hDealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hRegion : region_ok (lsProg_463 H) recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpecTPTightF F0 C A ctl uuidTryParse S).withVRegs.restrictPre
        (Q ·.st.pqRatchetState))) :
    DecCalleesTPFPlaced F0 C A ctl S H Q :=
  ⟨hRegion, remoteIdentityKeyPlacedOk A H, dropSessionStructureLocal2PlacedOk hDealloc⟩

/-- Constructs `DecCalleesTFPlaced` from the record-decrypt region contract and `rustDeallocSpec`. -/
theorem DecCalleesTFPlaced.of_region [LibsignalPlacement] {F0 : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {H : LibsignalHooks} {Q : List (BitVec 8) → Prop}
    (hDealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hRegion : region_ok (lsProg_463 H) recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpecTF F0 C A ctl uuidTryParse S).withVRegs.restrictPre
        (Q ·.st.pqRatchetState))) :
    DecCalleesTFPlaced F0 C A ctl S H Q :=
  ⟨hRegion, remoteIdentityKeyPlacedOk A H, dropSessionStructureLocal2PlacedOk hDealloc⟩

/-- `withLsFrozen`-guarded variant of `DecCalleesTPFPlaced`. -/
structure DecCalleesTPFFrozenPlaced [LibsignalPlacement] (F0 : SepProp)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : LibsignalHooks) (Q : List (BitVec 8) → Prop) : Prop where
  region : region_ok (lsProg_463 H) recEntryPlaced recExitPlaced
    ((withLsFrozen lsmpl (recordDecryptPlacedSpecTPTightF F0 C A ctl uuidTryParse S)).withVRegs.restrictPre
      (Q ·.st.pqRatchetState))
  remoteIk : RemoteIdentityKeyPlacedOk A H
  dropSs : DropSessionStructureLocal2PlacedOk A H

/-- `DecCalleesTPFFrozenPlaced` specialized to `SpqrV1.GF.Mul2U16.tokenInitPlacedAt`. -/
abbrev DecCalleesTPFrozenPlaced [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : LibsignalHooks) (Q : List (BitVec 8) → Prop) : Prop :=
  DecCalleesTPFFrozenPlaced SpqrV1.GF.Mul2U16.tokenInitPlacedAt C A ctl S H Q

/-- Constructs `DecCalleesTPFFrozenPlaced` from the `withLsFrozen` record-decrypt region contract. -/
theorem DecCalleesTPFFrozenPlaced.of_region [LibsignalPlacement] {F0 : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {H : LibsignalHooks} {Q : List (BitVec 8) → Prop}
    (hDealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hRegion : region_ok (lsProg_463 H) recEntryPlaced recExitPlaced
      ((withLsFrozen lsmpl (recordDecryptPlacedSpecTPTightF F0 C A ctl uuidTryParse S)).withVRegs.restrictPre
        (Q ·.st.pqRatchetState))) :
    DecCalleesTPFFrozenPlaced F0 C A ctl S H Q :=
  ⟨hRegion, remoteIdentityKeyPlacedOk A H, dropSessionStructureLocal2PlacedOk hDealloc⟩

/-! ## Twelve-segment assembly -/

section ChainVTPPlaced

variable [LibsignalPlacement] {F0 : SepProp} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {H : LibsignalHooks}
  {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
  {st0 : kit.StoreState} {ist0 : ikit.IdState}
  {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
  (hH : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
  (hDropSs : DropSessionStructureLocal2PlacedOk A H)
  (x : DecryptGhost) (R : SepProp) (s0 : State)
  (hAddr : kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val)

private theorem reachVTPF_resultFinal_placed (s : State)
    (h : ResultFinalStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTPF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegVTPF_chain_placed (segWriteVX_placed_ok x (F0 ∗ R) s0 s h) (fun _ hf => hf.elim)

include hH hDropSs in
private theorem reachVTPF_errJoin_placed (pt : Bool) (s : State)
    (h : ErrJoinStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x pt (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTPF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegVTPF_chain_placed (segErrTeardownVX_placed_ok hH hDropSs x pt (F0 ∗ R) s0 s h)
    (reachVTPF_resultFinal_placed x R s0)

include hH hDropSs hAddr in
private theorem reachVTPF_storeCall_placed (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxExtPlaced kit ikit H s0 s)
    (h : StoreCallStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x ans (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTPF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegVTPF_chain_placed (segStoreVX_placed_ok hH hDropSs x ans (F0 ∗ R) s0 s hAddr.1 hfs h)
    (fun s' h' => h'.elim
      (reachVTPF_resultFinal_placed x R s0 s')
      (reachVTPF_errJoin_placed hH hDropSs x R s0 true s'))

include hH hDropSs hAddr in
private theorem reachVTPF_trusted_placed (ans : StoreAnswers (List (BitVec 8)) Unit) (t : Bool)
    (s : State) (hfs : DecFsCtxExtPlaced kit ikit H s0 s)
    (h : TrustedStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x ans t (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTPF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s := by
  cases t with
  | true =>
    exact decSegVTPF_chainFs_placed hfs (segSaveVX_placed_ok hH x ans (F0 ∗ R) s0 s hAddr.2 hfs h)
      (fun s' hfs' h' => h'.elim
        (fun ⟨ans', hsc⟩ => reachVTPF_storeCall_placed hH hDropSs x R s0 hAddr ans' s' hfs' hsc)
        (reachVTPF_errJoin_placed hH hDropSs x R s0 true s'))
  | false =>
    exact decSegVTPF_chain_placed (segUntrustedVX_placed_ok hH x ans (F0 ∗ R) s0 s h)
      (reachVTPF_errJoin_placed hH hDropSs x R s0 true)

include hH hDropSs hAddr in
private theorem reachVTPF_keyReady_placed (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxExtPlaced kit ikit H s0 s)
    (h : KeyReadyStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x ans (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTPF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegVTPF_chainFs_placed hfs (segTrustVX_placed_ok hH x ans (F0 ∗ R) s0 s hAddr.2 hfs h)
    (fun s' hfs' h' => h'.elim
      (fun ⟨ans', t, ht⟩ => reachVTPF_trusted_placed hH hDropSs x R s0 hAddr ans' t s' hfs' ht)
      (reachVTPF_errJoin_placed hH hDropSs x R s0 true s'))

include hH hAddr in
private theorem reachVTPF_loadPolled_placed
    (hC : DecCalleesTPFPlaced F0 C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hid : IdOrDistinctSid uuidTryParse kit st0 Scope x)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxExtPlaced kit ikit H s0 s)
    (h : LoadPolledStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTPF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s := by
  refine decSegVTPF_chainFs_placed hfs (segDispatchVP_placed_ok hH x ans (F0 ∗ R) s0 s hid h) ?_
  rintro s' hfs' (hSome | hNone | hFin)
  · intro hL
    obtain ⟨s'', hst, hPost | hout⟩ :=
      segRegionSomeVTP_placed_ok Q hC.region hQ x ans R s0 s' hSome hL
    · refine Arm64.reaches_outcome_steps hst ?_ hL
      exact decSegVTPF_chainFs_placed (hfs'.of_steps hst)
        (segPostSomeVX_placed_ok hH hC.remoteIk x ans (F0 ∗ R) s0 s'' hPost)
        (fun s3 hfs3 h3 => h3.elim
          (reachVTPF_keyReady_placed hH hC.dropSs x R s0 hAddr ans s3 hfs3)
          (reachVTPF_errJoin_placed hH hC.dropSs x R s0 false s3))
    · exact ⟨s'', hst, hout⟩
  · refine decSegVTPF_chain_placed (segRegionNoneVX_placed_ok hH.hooks x ans (F0 ∗ R) s0 s' hNone) ?_
    intro s'' hPost
    exact decSegVTPF_chain_placed (segPostNoneVX_placed_ok x ans (F0 ∗ R) s0 s'' hPost)
      (reachVTPF_errJoin_placed hH hC.dropSs x R s0 false)
  · exact reachVTPF_resultFinal_placed x R s0 s' hFin

include hH hAddr in
private theorem reachVTPF_loadPolled_frozen_placed
    (hC : DecCalleesTPFFrozenPlaced F0 C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hid : IdOrDistinctSid uuidTryParse kit st0 Scope x)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxExtPlaced kit ikit H s0 s)
    (hFroz : LibsignalFrozen lsmpl s.mem)
    (h : LoadPolledStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTPF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s := by
  intro hL
  obtain ⟨s', hst0, hNext | hout0⟩ := segDispatchVP_placed_ok hH x ans (F0 ∗ R) s0 s hid h hL
  · have hfs' := hfs.of_steps hst0
    have hFroz' := libsignalFrozen_of_keepsFrozen hFroz hst0.keepsFrozen
    refine Arm64.reaches_outcome_steps hst0 ?_ hL
    rcases hNext with hSome | hNone | hFin
    · intro hL'
      obtain ⟨s'', hst, hPost | hout⟩ :=
        segRegionSomeVTP_frozen_placed_ok Q hC.region hQ x ans R s0 s' hSome hFroz' hL'
      · refine Arm64.reaches_outcome_steps hst ?_ hL'
        exact decSegVTPF_chainFs_placed (hfs'.of_steps hst)
          (segPostSomeVX_placed_ok hH hC.remoteIk x ans (F0 ∗ R) s0 s'' hPost)
          (fun s3 hfs3 h3 => h3.elim
            (reachVTPF_keyReady_placed hH hC.dropSs x R s0 hAddr ans s3 hfs3)
            (reachVTPF_errJoin_placed hH hC.dropSs x R s0 false s3))
      · exact ⟨s'', hst, hout⟩
    · refine decSegVTPF_chain_placed (segRegionNoneVX_placed_ok hH.hooks x ans (F0 ∗ R) s0 s' hNone) ?_
      intro s'' hPost
      exact decSegVTPF_chain_placed (segPostNoneVX_placed_ok x ans (F0 ∗ R) s0 s'' hPost)
        (reachVTPF_errJoin_placed hH hC.dropSs x R s0 false)
    · exact reachVTPF_resultFinal_placed x R s0 s' hFin
  · exact ⟨s', hst0, subroutineOutcome_vx_to_framed_placed hout0⟩

end ChainVTPPlaced

/-- Per-ghost relocatable reachability for `withStoresDecPlacedSpecVTPF` with entry-file `envOk`. -/
theorem withStoresDec_reachVTPF_fs_placed [LibsignalPlacement] {F0 : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hC : DecCalleesTPFPlaced F0 C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (x : DecryptGhost) (R : SepProp) (s0 : State)
    (hid : IdOrDistinctSid uuidTryParse kit st0 Scope x)
    (hpc : s0.pc = wsEntryPCPlaced)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨
      (withStoresDecPlacedSpecVTPF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).pre
        x s0 ∗ R)
    (hal : s0.spAligned = true)
    (hfs : DecFsCtxExtPlaced kit ikit H s0 s0) :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTPF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s0 := by
  have hpreV : s0.mem ⊨
      (withStoresDecPlacedSpecVX C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope
        (fun _ _ => False)).pre x s0 ∗ (F0 ∗ R) := by
    dsimp only [withStoresDecPlacedSpecVTPF] at hpre
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
  have hAddr := withStoresDecPlacedSpecV_pre_addrOk
    (C := C) (ctl := ctl) (S := S) (encRecord := encRecord) (Scope := Scope) hpreV
  exact decSegVTPF_chainFs_placed hfs
    (segLoadVX_placed_ok hH x (F0 ∗ R) s0 hfs hpc hrun hal hpreV)
    (fun s hfs' ⟨ans, h⟩ => reachVTPF_loadPolled_placed hH x R s0 hAddr hC hQ hid ans s hfs' h)

/-- `withStoresDec_reachVTPF_fs_placed` specialized to `SpqrV1.GF.Mul2U16.tokenInitPlacedAt`. -/
theorem withStoresDec_reachVTP_fs_placed [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hC : DecCalleesTPPlaced C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (x : DecryptGhost) (R : SepProp) (s0 : State)
    (hid : IdOrDistinctSid uuidTryParse kit st0 Scope x)
    (hpc : s0.pc = wsEntryPCPlaced)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨
      (withStoresDecPlacedSpecVTP C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).pre
        x s0 ∗ R)
    (hal : s0.spAligned = true)
    (hfs : DecFsCtxExtPlaced kit ikit H s0 s0) :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTP C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s0 :=
  withStoresDec_reachVTPF_fs_placed hH hC hQ x R s0 hid hpc hrun hpre hal hfs

/-- Relocatable `subroutine_ok` for `withStoresDecPlacedSpecVTPF` under `IdOrDistinctSid` and entry-file `envOk`. -/
theorem withStoresDec_okVTPF_fs_placed [LibsignalPlacement] {F0 : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hC : DecCalleesTPFPlaced F0 C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 H)) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      (withEnvPre
        ((withStoresDecPlacedSpecVTPF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).restrictPre
          (IdOrDistinctSid uuidTryParse kit st0 Scope))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  intro x R s0 hpc hrun hpre0 hal
  obtain ⟨h0, hpreR⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  dsimp only [Spec.restrictPre] at hpreR
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpreR
  exact withStoresDec_reachVTPF_fs_placed hH hC hQ x R s0 hpreR.1 hpc hrun hpreR.2 hal
    (FsCtx.of_entry hKitFs h0)

/-- `withStoresDec_okVTPF_fs_placed` specialized to `SpqrV1.GF.Mul2U16.tokenInitPlacedAt`. -/
theorem withStoresDec_okVTP_fs_placed [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hC : DecCalleesTPPlaced C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 H)) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      (withEnvPre
        ((withStoresDecPlacedSpecVTP C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).restrictPre
          (IdOrDistinctSid uuidTryParse kit st0 Scope))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTPF_fs_placed hH hC hQ hKitFs

/-- Specialization of `withStoresDec_okVTPF_fs_placed` to `DistinctSid`. -/
theorem withStoresDec_okVTPF_distinct_fs_placed [LibsignalPlacement] {F0 : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hC : DecCalleesTPFPlaced F0 C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 H)) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      (withEnvPre
        ((withStoresDecPlacedSpecVTPF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).restrictPre
          (fun x => CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid
            uuidTryParse x.loc.name.bytes x.rem.name.bytes))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  intro x R s0 hpc hrun hpre0 hal
  obtain ⟨h0, hpreR⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  dsimp only [Spec.restrictPre] at hpreR
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpreR
  exact withStoresDec_reachVTPF_fs_placed hH hC hQ x R s0
    (idOrDistinctSid_of_distinctSid hpreR.1) hpc hrun hpreR.2 hal (FsCtx.of_entry hKitFs h0)

/-- `withStoresDec_okVTPF_distinct_fs_placed` specialized to `SpqrV1.GF.Mul2U16.tokenInitPlacedAt`. -/
theorem withStoresDec_okVTP_distinct_fs_placed [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hC : DecCalleesTPPlaced C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 H)) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      (withEnvPre
        ((withStoresDecPlacedSpecVTP C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).restrictPre
          (fun x => CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid
            uuidTryParse x.loc.name.bytes x.rem.name.bytes))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTPF_distinct_fs_placed hH hC hQ hKitFs

theorem withStoresDec_okVTPF_placed [LibsignalPlacement] {F0 : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hC : DecCalleesTPFPlaced F0 C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      ((withStoresDecPlacedSpecVTPF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).restrictPre
        (IdOrDistinctSid uuidTryParse kit st0 Scope)) :=
  subroutine_ok_of_withEnvPre (withStoresDec_okVTPF_fs_placed hH hC hQ (.inl htriv))
    fun s => htriv s.fs.files

theorem withStoresDec_okVTP_placed [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hC : DecCalleesTPPlaced C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      ((withStoresDecPlacedSpecVTP C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).restrictPre
        (IdOrDistinctSid uuidTryParse kit st0 Scope)) :=
  withStoresDec_okVTPF_placed hH hC hQ htriv

/-- `withLsFrozen`-guarded per-ghost reachability for `withStoresDecPlacedSpecVTPF`. -/
theorem withStoresDec_reachVTPF_frozen_fs_placed [LibsignalPlacement] {F0 : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hC : DecCalleesTPFFrozenPlaced F0 C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (x : DecryptGhost) (R : SepProp) (s0 : State)
    (hid : IdOrDistinctSid uuidTryParse kit st0 Scope x)
    (hpc : s0.pc = wsEntryPCPlaced)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨
      (withStoresDecPlacedSpecVTPF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).pre
        x s0 ∗ R)
    (hFroz : LibsignalFrozen lsmpl s0.mem)
    (hal : s0.spAligned = true)
    (hfs : DecFsCtxExtPlaced kit ikit H s0 s0) :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTPF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s0 := by
  have hpreV : s0.mem ⊨
      (withStoresDecPlacedSpecVX C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope
        (fun _ _ => False)).pre x s0 ∗ (F0 ∗ R) := by
    dsimp only [withStoresDecPlacedSpecVTPF] at hpre
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
  have hAddr := withStoresDecPlacedSpecV_pre_addrOk
    (C := C) (ctl := ctl) (S := S) (encRecord := encRecord) (Scope := Scope) hpreV
  intro hL
  obtain ⟨s, hst, ⟨ans, h⟩ | hout⟩ :=
    segLoadVX_placed_ok hH x (F0 ∗ R) s0 hfs hpc hrun hal hpreV hL
  · exact Arm64.reaches_outcome_steps hst
      (reachVTPF_loadPolled_frozen_placed hH x R s0 hAddr hC hQ hid ans s
        (hfs.of_steps hst) (libsignalFrozen_of_keepsFrozen hFroz hst.keepsFrozen) h)
      hL
  · exact ⟨s, hst, subroutineOutcome_vx_to_framed_placed hout⟩

/-- `withStoresDec_reachVTPF_frozen_fs_placed` specialized to `SpqrV1.GF.Mul2U16.tokenInitPlacedAt`. -/
theorem withStoresDec_reachVTP_frozen_fs_placed [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hC : DecCalleesTPFrozenPlaced C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (x : DecryptGhost) (R : SepProp) (s0 : State)
    (hid : IdOrDistinctSid uuidTryParse kit st0 Scope x)
    (hpc : s0.pc = wsEntryPCPlaced)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨
      (withStoresDecPlacedSpecVTP C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).pre
        x s0 ∗ R)
    (hFroz : LibsignalFrozen lsmpl s0.mem)
    (hal : s0.spAligned = true)
    (hfs : DecFsCtxExtPlaced kit ikit H s0 s0) :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTP C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s0 :=
  withStoresDec_reachVTPF_frozen_fs_placed hH hC hQ x R s0 hid hpc hrun hpre hFroz hal hfs

/-- `withLsFrozen`-guarded `subroutine_ok` for `withStoresDecPlacedSpecVTPF` under `IdOrDistinctSid`. -/
theorem withStoresDec_okVTPF_frozen_fs_placed [LibsignalPlacement] {F0 : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hC : DecCalleesTPFFrozenPlaced F0 C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 H)) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      (withEnvPre
        ((withLsFrozen lsmpl
          (withStoresDecPlacedSpecVTPF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)).restrictPre
          (IdOrDistinctSid uuidTryParse kit st0 Scope))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  intro x R s0 hpc hrun hpre0 hal
  obtain ⟨h0, hpreR⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  dsimp only [Spec.restrictPre] at hpreR
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpreR
  obtain ⟨hFroz, hpre'⟩ := extract_withLsFrozen hpreR.2
  exact withStoresDec_reachVTPF_frozen_fs_placed hH hC hQ x R s0 hpreR.1 hpc hrun hpre' hFroz hal
    (FsCtx.of_entry hKitFs h0)

/-- `withStoresDec_okVTPF_frozen_fs_placed` specialized to `SpqrV1.GF.Mul2U16.tokenInitPlacedAt`. -/
theorem withStoresDec_okVTP_frozen_fs_placed [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hC : DecCalleesTPFrozenPlaced C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 H)) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      (withEnvPre
        ((withLsFrozen lsmpl
          (withStoresDecPlacedSpecVTP C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)).restrictPre
          (IdOrDistinctSid uuidTryParse kit st0 Scope))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTPF_frozen_fs_placed hH hC hQ hKitFs

/-- Specialization of `withStoresDec_okVTPF_frozen_fs_placed` to `DistinctSid`. -/
theorem withStoresDec_okVTPF_distinct_frozen_fs_placed [LibsignalPlacement] {F0 : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hC : DecCalleesTPFFrozenPlaced F0 C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 H)) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      (withEnvPre
        ((withLsFrozen lsmpl
          (withStoresDecPlacedSpecVTPF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)).restrictPre
          (fun x => CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid
            uuidTryParse x.loc.name.bytes x.rem.name.bytes))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  intro x R s0 hpc hrun hpre0 hal
  obtain ⟨h0, hpreR⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  dsimp only [Spec.restrictPre] at hpreR
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpreR
  obtain ⟨hFroz, hpre'⟩ := extract_withLsFrozen hpreR.2
  exact withStoresDec_reachVTPF_frozen_fs_placed hH hC hQ x R s0
    (idOrDistinctSid_of_distinctSid hpreR.1) hpc hrun hpre' hFroz hal (FsCtx.of_entry hKitFs h0)

/-- `withStoresDec_okVTPF_distinct_frozen_fs_placed` specialized to `SpqrV1.GF.Mul2U16.tokenInitPlacedAt`. -/
theorem withStoresDec_okVTP_distinct_frozen_fs_placed [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hC : DecCalleesTPFrozenPlaced C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 H)) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      (withEnvPre
        ((withLsFrozen lsmpl
          (withStoresDecPlacedSpecVTP C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)).restrictPre
          (fun x => CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid
            uuidTryParse x.loc.name.bytes x.rem.name.bytes))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTPF_distinct_frozen_fs_placed hH hC hQ hKitFs

section ChainVTPlaced

variable [LibsignalPlacement] {F0 : SepProp} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {H : LibsignalHooks}
  {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
  {st0 : kit.StoreState} {ist0 : ikit.IdState}
  {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
  (hH : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
  (hscopeIn : ∀ r, Scope r → RecordInScope r)
  (hC : DecCalleesTFPlaced F0 C A ctl S H Q)
  (x : DecryptGhost) (R : SepProp) (s0 : State)
  (hAddr : kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val)

private theorem reachVTF_resultFinal_placed (s : State)
    (h : ResultFinalStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegVTF_chain_placed (segWriteVX_placed_ok x (F0 ∗ R) s0 s h) (fun _ hf => hf.elim)

include hH hC in
private theorem reachVTF_errJoin_placed (pt : Bool) (s : State)
    (h : ErrJoinStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x pt (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegVTF_chain_placed (segErrTeardownVX_placed_ok hH hC.dropSs x pt (F0 ∗ R) s0 s h)
    (reachVTF_resultFinal_placed x R s0)

include hH hC hAddr in
private theorem reachVTF_storeCall_placed (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxExtPlaced kit ikit H s0 s)
    (h : StoreCallStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x ans (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegVTF_chain_placed (segStoreVX_placed_ok hH hC.dropSs x ans (F0 ∗ R) s0 s hAddr.1 hfs h)
    (fun s' h' => h'.elim
      (reachVTF_resultFinal_placed x R s0 s')
      (reachVTF_errJoin_placed hH hC x R s0 true s'))

include hH hC hAddr in
private theorem reachVTF_trusted_placed (ans : StoreAnswers (List (BitVec 8)) Unit) (t : Bool)
    (s : State) (hfs : DecFsCtxExtPlaced kit ikit H s0 s)
    (h : TrustedStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x ans t (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s := by
  cases t with
  | true =>
    exact decSegVTF_chainFs_placed hfs (segSaveVX_placed_ok hH x ans (F0 ∗ R) s0 s hAddr.2 hfs h)
      (fun s' hfs' h' => h'.elim
        (fun ⟨ans', hsc⟩ => reachVTF_storeCall_placed hH hC x R s0 hAddr ans' s' hfs' hsc)
        (reachVTF_errJoin_placed hH hC x R s0 true s'))
  | false =>
    exact decSegVTF_chain_placed (segUntrustedVX_placed_ok hH x ans (F0 ∗ R) s0 s h)
      (reachVTF_errJoin_placed hH hC x R s0 true)

include hH hC hAddr in
private theorem reachVTF_keyReady_placed (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxExtPlaced kit ikit H s0 s)
    (h : KeyReadyStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x ans (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegVTF_chainFs_placed hfs (segTrustVX_placed_ok hH x ans (F0 ∗ R) s0 s hAddr.2 hfs h)
    (fun s' hfs' h' => h'.elim
      (fun ⟨ans', t, ht⟩ => reachVTF_trusted_placed hH hC x R s0 hAddr ans' t s' hfs' ht)
      (reachVTF_errJoin_placed hH hC x R s0 true s'))

include hH hscopeIn hC hAddr in
private theorem reachVTF_loadPolled_placed
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxExtPlaced kit ikit H s0 s)
    (h : LoadPolledStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s := by
  refine decSegVTF_chainFs_placed hfs (segDispatchVX_placed_ok hH hscopeIn x ans (F0 ∗ R) s0 s h) ?_
  rintro s' hfs' (hSome | hNone | hFin)
  · intro hL
    obtain ⟨s'', hst, hPost | hout⟩ :=
      segRegionSomeVT_placed_ok Q hC.region hQ x ans R s0 s' hSome hL
    · refine Arm64.reaches_outcome_steps hst ?_ hL
      exact decSegVTF_chainFs_placed (hfs'.of_steps hst)
        (segPostSomeVX_placed_ok hH hC.remoteIk x ans (F0 ∗ R) s0 s'' hPost)
        (fun s3 hfs3 h3 => h3.elim
          (reachVTF_keyReady_placed hH hC x R s0 hAddr ans s3 hfs3)
          (reachVTF_errJoin_placed hH hC x R s0 false s3))
    · exact ⟨s'', hst, hout⟩
  · refine decSegVTF_chain_placed (segRegionNoneVX_placed_ok hH.hooks x ans (F0 ∗ R) s0 s' hNone) ?_
    intro s'' hPost
    exact decSegVTF_chain_placed (segPostNoneVX_placed_ok x ans (F0 ∗ R) s0 s'' hPost)
      (reachVTF_errJoin_placed hH hC x R s0 false)
  · exact reachVTF_resultFinal_placed x R s0 s' hFin

end ChainVTPlaced

/-- Relocatable `subroutine_ok` for `withStoresDecPlacedSpecVTF` under `Scope ⊆ RecordInScope`. -/
theorem withStoresDec_okVTF_fs_placed [LibsignalPlacement] {F0 : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hscopeIn : ∀ r, Scope r → RecordInScope r)
    (hC : DecCalleesTFPlaced F0 C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 H)) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      (withEnvPre (withStoresDecPlacedSpecVTF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  intro x R s0 hpc hrun hpre0 hal
  obtain ⟨h0, hpre⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  have hpreV : s0.mem ⊨
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).pre x s0 ∗
        (F0 ∗ R) := by
    dsimp only [withStoresDecPlacedSpecVTF] at hpre
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
  have hAddr := withStoresDecPlacedSpecV_pre_addrOk hpreV
  have hfs0 : DecFsCtxExtPlaced kit ikit H s0 s0 := FsCtx.of_entry hKitFs h0
  exact decSegVTF_chainFs_placed hfs0
    (segLoadVX_placed_ok hH x (F0 ∗ R) s0 hfs0 hpc hrun hal hpreV)
    (fun s hfs ⟨ans, h⟩ => reachVTF_loadPolled_placed hH hscopeIn hC x R s0 hAddr hQ ans s hfs h)

theorem withStoresDec_okVT_fs_placed [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hscopeIn : ∀ r, Scope r → RecordInScope r)
    (hC : DecCalleesTPlaced C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 H)) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      (withEnvPre (withStoresDecPlacedSpecVT C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTF_fs_placed hH hscopeIn hC hQ hKitFs

theorem withStoresDec_okVTF_placed [LibsignalPlacement] {F0 : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hscopeIn : ∀ r, Scope r → RecordInScope r)
    (hC : DecCalleesTFPlaced F0 C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      (withStoresDecPlacedSpecVTF F0 C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) :=
  subroutine_ok_of_withEnvPre (withStoresDec_okVTF_fs_placed hH hscopeIn hC hQ (.inl htriv))
    fun s => htriv s.fs.files

theorem withStoresDec_okVT_placed [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hscopeIn : ∀ r, Scope r → RecordInScope r)
    (hC : DecCalleesTPlaced C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      (withStoresDecPlacedSpecVT C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) :=
  withStoresDec_okVTF_placed hH hscopeIn hC hQ htriv

end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT
