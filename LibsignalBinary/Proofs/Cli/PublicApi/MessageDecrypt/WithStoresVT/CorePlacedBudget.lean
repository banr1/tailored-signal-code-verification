/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.AssemblyPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegBatch1PlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegDispatchExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegErrTeardownExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegPostSomeExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegRegionNoneExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegSaveExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegStoreExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegTrustExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegUntrustedExtPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.GF.Mul2U16
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Relocatable Token-Framed `MessageDecrypt` Assembly

Assembles the twelve budget-threaded relocatable (`[LibsignalPlacement]`) `MessageDecrypt` segments
on `lsProg_463 H` under `RustCliAllocBudget M` for `withStoresDecPlacedSpecVTPF` /
`withStoresDecPlacedSpecVTP` and `withStoresDecPlacedSpecVTF` / `withStoresDecPlacedSpecVT`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.LibsignalSessionApi (Session SessionRecord StoreAnswers)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsRustDeallocSym lsmpl)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.CliRatchet.DecPlaced (lsProg_463)
open CryptoVerification.RustHeap (RustAlloc vecBuf)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost UuidParser uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (RecordDecryptGhost SpqrModel region_ok)
open CryptoVerification.Cli.LibsignalTripleRatchet.Record (recEntryPlaced recExitPlaced)
open CryptoVerification.LibsignalPublicApi (DecryptGhost RecordInScope)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsCtx KitFsOk LibsignalCodeRoLoaded SessionStoreSpec reaches_outcome_withEnvPre
   subroutine_ok_of_withEnvPre withEnvPre withEnvPre_pre_elim)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (ScopePq prevBufAt recGhostOf sessionModelRel)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
  (decStoreExtraPlaced wsEntryPCPlaced wsMetaPlaced wsRegionFrameVPlaced)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT
  (IdOrDistinctSid idOrDistinctSid_of_distinctSid regionSomePV_of_common_placed)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionSome
  (model_panic_of_region_panic recvPanics_of_region_recvPanics)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionSome (post_meta_extract_placed)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv retagSessionStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv retagIdentityStore)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SeamBudget TryDecryptEnvArgs)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (FromRegionSomeEnv SessionGhostValid WithStoresDecEnv fromPostSomeEnv_nonempty)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlacedBudget
  (DropSessionStructureLocal2PlacedOk ErrJoinStateVPlaced KeyReadyStateVPlaced LoadPolledStateVPlaced
   PostNoneStateVPlaced PostSomeStateVPlaced RegionNoneStateVPlaced RegionSomeStateVPlaced
   RemoteIdentityKeyPlacedOk ResultFinalStateVPlaced StoreCallStateVPlaced TrustedStateVPlaced
   sessionGhostValid_of_recordPlacedPre withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudget (DecSegVXPlaced withStoresDecPlacedSpecVX)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.AssemblyPlacedBudget (dropSessionStructureLocal2PlacedOk remoteIdentityKeyPlacedOk)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlacedBudget (DecFsCtxExtPlaced DecHypsExtPlaced)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegBatch1PlacedBudget (segLoadVX_placed_ok segPostNoneVX_placed_ok segWriteVX_placed_ok)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegDispatchExtPlacedBudget (segDispatchGen_placed_ok segDispatchVX_placed_ok)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegErrTeardownExtPlacedBudget (segErrTeardownVX_placed_ok)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegPostSomeExtPlacedBudget (segPostSomeVX_placed_ok)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegRegionNoneExtPlacedBudget (segRegionNoneVX_placed_ok)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegSaveExtPlacedBudget (segSaveVX_placed_ok)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegStoreExtPlacedBudget (segStoreVX_placed_ok)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegTrustExtPlacedBudget (segTrustVX_placed_ok)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegUntrustedExtPlacedBudget (segUntrustedVX_placed_ok)

/-! ## Token-framed budget `withStoresDecPlacedSpecVT` and `withStoresDecPlacedSpecVTP` -/

/-- Budget-threaded `withStoresDecPlacedSpecV` with token invariant `F0` framed in `pre` and `post`. -/
def withStoresDecPlacedSpecVTF [LibsignalPlacement] {M : AllocCostModel} (F0 : SepProp) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Spec (DecryptGhost × M.σ) :=
  { withStoresDecPlacedSpecV C A lim ctl parse S tdEnv encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope with
    pre := fun p s => F0 ∗ (withStoresDecPlacedSpecV C A lim ctl parse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope).pre p s
    post := fun p s0 sf => F0 ∗ (withStoresDecPlacedSpecV C A lim ctl parse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope).post p s0 sf }

/-- `withStoresDecPlacedSpecVTF` specialized to `tokenInitPlacedAt`. -/
abbrev withStoresDecPlacedSpecVT [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Spec (DecryptGhost × M.σ) :=
  withStoresDecPlacedSpecVTF tokenInitPlacedAt
    C A lim ctl parse S tdEnv encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope

/-- Tight-panic budget-threaded `withStoresDecPlacedSpecVX` (`Extra := fun _ _ => False`) with `F0` framed. -/
def withStoresDecPlacedSpecVTPF [LibsignalPlacement] {M : AllocCostModel} (F0 : SepProp) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Spec (DecryptGhost × M.σ) :=
  { withStoresDecPlacedSpecVX C A lim ctl parse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope (fun _ _ => False) with
    pre := fun p s => F0 ∗ (withStoresDecPlacedSpecVX C A lim ctl parse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope (fun _ _ => False)).pre p s
    post := fun p s0 sf => F0 ∗ (withStoresDecPlacedSpecVX C A lim ctl parse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope (fun _ _ => False)).post p s0 sf }

/-- `withStoresDecPlacedSpecVTPF` specialized to `tokenInitPlacedAt`. -/
abbrev withStoresDecPlacedSpecVTP [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Spec (DecryptGhost × M.σ) :=
  withStoresDecPlacedSpecVTPF tokenInitPlacedAt
    C A lim ctl parse S tdEnv encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope

/-! ## Record-level budget specifications (`P`, `T`, `TPTight`) -/

/-- Budget-threaded `recordDecryptPlacedSpec` weakened to `remoteIdentity ≠ some localIdentity ∨ DistinctSid uuidParse loc rem`. -/
abbrev recordDecryptPlacedSpecP :=
  @LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegUntrustedExtBudget.recordDecryptPlacedSpecP

/-- Budget-threaded `recordDecryptPlacedSpec` with `pqRatchetState.length < 2 ^ 32` and `F0` framed. -/
def recordDecryptPlacedSpecTF [LibsignalPlacement] {M : AllocCostModel} (F0 : SepProp) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (RecordDecryptGhost × M.σ) :=
  { LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.recordDecryptPlacedSpec
      C A lim ctl uuidParse S tdEnv with
    pre := fun (x, st) s => ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗ F0 ∗
      (LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.recordDecryptPlacedSpec
        C A lim ctl uuidParse S tdEnv).pre (x, st) s
    post := fun (x, st) s0 sf => F0 ∗
      (LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.recordDecryptPlacedSpec
        C A lim ctl uuidParse S tdEnv).post (x, st) s0 sf }

/-- `recordDecryptPlacedSpecTF` specialized to `tokenInitPlacedAt`. -/
abbrev recordDecryptPlacedSpecT [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (RecordDecryptGhost × M.σ) :=
  recordDecryptPlacedSpecTF tokenInitPlacedAt C A lim ctl uuidParse S tdEnv

/-- `recordDecryptPlacedSpecTF` with weak `recordDecryptPlacedSpecP` precondition and model-panic-only `onPanic`. -/
def recordDecryptPlacedSpecTPTightF [LibsignalPlacement] {M : AllocCostModel} (F0 : SepProp)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) : Spec (RecordDecryptGhost × M.σ) :=
  { recordDecryptPlacedSpecTF F0 C A lim ctl uuidParse S tdEnv with
    pre := fun (x, st) s => ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗ F0 ∗
      (recordDecryptPlacedSpecP C A lim ctl uuidParse S tdEnv).pre (x, st) s
    onPanic := fun (x, _) s0 sf =>
      ⌜(x.model C S uuidParse).1 = .error .panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

/-- `recordDecryptPlacedSpecTPTightF` specialized to `tokenInitPlacedAt`. -/
abbrev recordDecryptPlacedSpecTPTight [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (RecordDecryptGhost × M.σ) :=
  recordDecryptPlacedSpecTPTightF tokenInitPlacedAt C A lim ctl uuidParse S tdEnv

/-! ## Weak-precondition `RegionSomeStatePVPlaced` and `segDispatchVP_placed_ok` -/

private theorem ex_frame_drop_left {m : Memory} {P Q : SepProp}
    (h : ∃ R, m ⊨ (P ∗ Q) ∗ R) : ∃ R, m ⊨ Q ∗ R :=
  let ⟨R, hR⟩ := h; ⟨P ∗ R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hR⟩

/-- Extracts `SessionGhostValid G ses` from `(WithStoresVT.recordDecryptPlacedSpecP ...).pre`. -/
theorem sessionGhostValid_of_recordPlacedPreP [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {x : DecryptGhost} {prevPtr : BitVec 64}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} {s : State} {R : SepProp}
    (hw0 : sessionModelRel G ses)
    (hm : s.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT.recordDecryptPlacedSpecP
      C A ctl parse S).pre (recGhostOf x prevPtr G ses.state) s ∗ R) :
    SessionGhostValid G ses := by
  refine ⟨hw0, A, s.sp + 0x138#64, s.mem, ?_⟩
  have h0 : ∃ R', s.mem ⊨
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT.recordDecryptPlacedSpecP
        C A ctl parse S).pre (recGhostOf x prevPtr G ses.state) s ∗ R' := ⟨R, hm⟩
  dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT.recordDecryptPlacedSpecP,
    recGhostOf] at h0
  have ⟨_, h7⟩ := ex_frame_drop_left (ex_frame_drop_left (ex_frame_drop_left (ex_frame_drop_left
    (ex_frame_drop_left (ex_frame_drop_left (ex_frame_drop_left h0))))))
  rw [sepConj_assoc] at h7
  exact ⟨_, h7⟩

/-- Budget-threaded `RegionSomeStateVPlaced` weakened to `WithStoresVT.recordDecryptPlacedSpecP`. -/
def RegionSomeStatePVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (R : SepProp) (s0 s : State) : Prop :=
  ∃ st : M.σ,
    (∀ rec ses G, ans.loadSession = .ok (some rec) → kit.ScopeAt Scope st0 x.rem.val rec →
      rec.currentSession = some ses → SessionGhostValid G ses →
      SeamBudget M lim (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse tdEnv Scope x)
        st_init st (FromRegionSomeEnv C S parse tdEnv kit kitEnv st0 ikit ikitEnv ist0 x rec G ses.state)) ∧
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT.RegionSomeStatePVPlaced
      C ctl parse S encRecord (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit) st0 ist0 Scope x ans R s0 s

/-- Budget-threaded `SegDispatch` into `RegionSomeStatePVPlaced` under `IdOrDistinctSid`. -/
theorem segDispatchVP_placed_ok [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hH : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (R : SepProp) (s0 s : State) (hid : IdOrDistinctSid uuidTryParse kit st0 Scope x)
    (hLP : LoadPolledStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s) :
    DecSegVXPlaced C A lim ctl uuidTryParse S tdEnv encRecord H kit kitEnv ikit ikitEnv
      st0 ist0 Scope Extra x st_init R s0 s (fun s' =>
        RegionSomeStatePVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s' ∨
        RegionNoneStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s' ∨
        ResultFinalStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s') := by
  refine segDispatchGen_placed_ok hH x st_init ans R s0 s hLP ?_
  intro sf_3 st1 g rec ses hsb_rs hpc3 hmeta3 hload hscope hscopeAt hcur htr3 hsp' hsp3 hpure3 hmf3'
  have hmf3'' := Satisfies.mono
    (sepConj_mono_left (regionSomePV_of_common_placed C (A.atState lim st1 sf_3) ctl S
      (retagSessionStore (A' := A.atState lim st1 sf_3) kit)
      (retagIdentityStore (A' := A.atState lim st1 sf_3) ikit)
      st0 ist0 x s0 sf_3 s.sp g rec ses hsp' hsp3
      (hH.scopeInP rec hscope) hcur (hid rec ses hscopeAt hcur) hpure3)) hmf3'
  rw [sepExists_sepConj_left, satisfies_sepExists] at hmf3''
  obtain ⟨G, hmf3''⟩ := hmf3''
  rw [sepConj_assoc (⌜_⌝), satisfies_pure_sepConj] at hmf3''
  obtain ⟨hw0, hmf3''⟩ := hmf3''
  simp only [sepConj_assoc] at hmf3''
  exact ⟨st1, hsb_rs, hpc3, hmeta3, rec, ses, G, g.prevCap, g.prevPtr,
    hload, hscopeAt, hcur, hw0, htr3, hmf3''⟩

/-! ## Outcome lifting and region crossing -/

private theorem subroutineOutcome_vx_to_framed_placed [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    {x : DecryptGhost} {st_init : M.σ} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome
      (withStoresDecPlacedSpecVX C A lim ctl parse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope Extra) (x, st_init) (F0 ∗ R) s0 sf) :
    SubroutineOutcome
      { withStoresDecPlacedSpecVX C A lim ctl parse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope Extra with
        pre := fun p s =>
          F0 ∗ (withStoresDecPlacedSpecVX C A lim ctl parse S tdEnv encRecord
            kit kitEnv ikit ikitEnv st0 ist0 Scope Extra).pre p s
        post := fun p s0 sf =>
          F0 ∗ (withStoresDecPlacedSpecVX C A lim ctl parse S tdEnv encRecord
            kit kitEnv ikit ikitEnv st0 ist0 Scope Extra).post p s0 sf }
      (x, st_init) R s0 sf := by
  rcases h with ⟨h1, hcs, hpost⟩ | ⟨hpan, honp⟩ | ⟨code, hexit, honex⟩ | ⟨hoom, honoom⟩
  · refine Or.inl ⟨h1, hcs, ?_⟩
    dsimp only
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withStoresDecPlacedSpecVX] at honp ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at honp ⊢
    refine ⟨honp.1, ?_⟩
    have h2 := honp.2
    rw [← sepConj_assoc] at h2
    exact Satisfies.mono (sepConj_mono_left (entails_anyHeap (anyHeap ∗ F0))) h2
  · refine Or.inr (Or.inr (Or.inl ⟨code, hexit, ?_⟩))
    change sf.mem ⊨ ⌜False⌝ ∗ (F0 ∗ R) at honex
    rw [satisfies_pure_sepConj] at honex
    exact False.elim honex.1
  · refine Or.inr (Or.inr (Or.inr ⟨hoom, ?_⟩))
    change sf.mem ⊨ ⌜False⌝ ∗ (F0 ∗ R) at honoom
    rw [satisfies_pure_sepConj] at honoom
    exact False.elim honoom.1

section ChainHelpers

variable [LibsignalPlacement] {M : AllocCostModel} {F0 : SepProp}
  {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
  {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
  {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
  {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
  {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
  {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
  {x : DecryptGhost} {st_init : M.σ} {R : SepProp} {s0 s : State} {next : State → Prop}

private theorem decSegVTPF_chain_placed
    (h1 : DecSegVXPlaced C A lim ctl uuidTryParse S tdEnv encRecord H kit kitEnv ikit ikitEnv
      st0 ist0 Scope (fun _ _ => False) x st_init (F0 ∗ R) s0 s next)
    (h2 : ∀ s', next s' → reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTPF F0 C A lim ctl
      uuidTryParse S tdEnv encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s') :
    reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv
      encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s := by
  refine Arm64.reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf hnext)
  · exact Arm64.reaches_outcome_steps hst
      (Arm64.reaches_outcome.of_outcome (subroutineOutcome_vx_to_framed_placed hout))

private theorem decSegVTPF_chainFs_placed (hfs : DecFsCtxExtPlaced kit ikit H s0 s)
    (h1 : DecSegVXPlaced C A lim ctl uuidTryParse S tdEnv encRecord H kit kitEnv ikit ikitEnv
      st0 ist0 Scope (fun _ _ => False) x st_init (F0 ∗ R) s0 s next)
    (h2 : ∀ s', DecFsCtxExtPlaced kit ikit H s0 s' → next s' → reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv encRecord kit kitEnv
        ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s') :
    reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv
      encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s := by
  refine Arm64.reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf (hfs.of_steps hst) hnext)
  · exact Arm64.reaches_outcome_steps hst
      (Arm64.reaches_outcome.of_outcome (subroutineOutcome_vx_to_framed_placed hout))

private theorem decSegVTF_chain_placed
    (h1 : DecSegVXPlaced C A lim ctl uuidTryParse S tdEnv encRecord H kit kitEnv ikit ikitEnv
      st0 ist0 Scope (fun x answers => x.recvPanics S answers) x st_init (F0 ∗ R) s0 s next)
    (h2 : ∀ s', next s' → reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTF F0 C A lim ctl
      uuidTryParse S tdEnv encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s') :
    reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTF F0 C A lim ctl uuidTryParse S tdEnv
      encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s := by
  refine Arm64.reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf hnext)
  · exact Arm64.reaches_outcome_steps hst
      (Arm64.reaches_outcome.of_outcome (subroutineOutcome_vx_to_framed_placed hout))

private theorem decSegVTF_chainFs_placed (hfs : DecFsCtxExtPlaced kit ikit H s0 s)
    (h1 : DecSegVXPlaced C A lim ctl uuidTryParse S tdEnv encRecord H kit kitEnv ikit ikitEnv
      st0 ist0 Scope (fun x answers => x.recvPanics S answers) x st_init (F0 ∗ R) s0 s next)
    (h2 : ∀ s', DecFsCtxExtPlaced kit ikit H s0 s' → next s' → reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVTF F0 C A lim ctl uuidTryParse S tdEnv encRecord kit kitEnv
        ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s') :
    reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTF F0 C A lim ctl uuidTryParse S tdEnv
      encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s := by
  refine Arm64.reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf (hfs.of_steps hst) hnext)
  · exact Arm64.reaches_outcome_steps hst
      (Arm64.reaches_outcome.of_outcome (subroutineOutcome_vx_to_framed_placed hout))

end ChainHelpers

private theorem rep_wsRegionFrameV_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (P₁ P₂ : SepProp)
    (kit : SessionStoreSpec A.repAlloc 0#64) (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (x : DecryptGhost) (s0 : State) (prevCap prevPtr : BitVec 64) :
    wsRegionFrameVPlaced
      (retagSessionStore (A' := { pool := P₁, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P₁, live := A.live }) ikit) x s0 prevCap prevPtr =
    wsRegionFrameVPlaced
      (retagSessionStore (A' := { pool := P₂, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P₂, live := A.live }) ikit) x s0 prevCap prevPtr := by
  dsimp only [wsRegionFrameVPlaced, prevBufAt, vecBuf]
  split <;> rfl

private theorem rep_decStoreExtra_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (P₁ P₂ : SepProp)
    (kit : SessionStoreSpec A.repAlloc 0#64) (ikit : IdentityStoreSpec A.repAlloc 0#64) :
    decStoreExtraPlaced
      (retagSessionStore (A' := { pool := P₁, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P₁, live := A.live }) ikit) =
    decStoreExtraPlaced
      (retagSessionStore (A' := { pool := P₂, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P₂, live := A.live }) ikit) := rfl

/-- Crosses the record-decrypt region at budget `recordDecryptPlacedSpecTPTightF` restricted by `Q`. -/
theorem segRegionSomeVTP_placed_ok [LibsignalPlacement] {M : AllocCostModel} {F0 : SepProp}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (Q : List (BitVec 8) → Prop)
    (hreg : region_ok (lsProg_463 H) recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpecTPTightF F0 C A lim ctl uuidTryParse S tdEnv).withVRegs.restrictPre
        (fun p => Q p.1.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (R : SepProp) (s0 s : State)
    (hRS : RegionSomeStatePVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans (F0 ∗ R) s0 s) :
    (lsProg_463 H).CodeLoaded s.mem →
    ∃ s', Steps (lsProg_463 H) s s' ∧
      (PostSomeStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans (F0 ∗ R) s0 s' ∨
        SubroutineOutcome
          (withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv encRecord
            kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s') := by
  intro hL
  obtain ⟨st, hsb_all, hpc, ⟨hrun, hsp, hal0, hal, hx29, _hx27, hcrl, hvregs⟩,
    rec, ses, G, prevCap, prevPtr, hload, hscope, hcur, hw0, htrace, hmem⟩ := hRS
  let x_rg := recGhostOf x prevPtr G ses.state
  let R_rg : SepProp :=
    wsRegionFrameVPlaced (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit) x s0 prevCap prevPtr ∗
    decStoreExtraPlaced (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit) st0 ist0 s0 ∗ R
  have hgv := sessionGhostValid_of_recordPlacedPreP hw0 (by simpa only [sepConj_assoc] using hmem)
  have hsb := hsb_all rec ses G hload hscope hcur hgv
  have hfits := hsb.fitsSeg (fun _ _ h1 h2 => SeqEnv.append h1 h2) fromPostSomeEnv_nonempty
  obtain ⟨hpq_lt, hpq_Q⟩ := hQ x.rem.val rec ses hscope hcur
  have hmemP : s.mem ⊨
      (recordDecryptPlacedSpecP C A lim ctl uuidTryParse S tdEnv).pre (x_rg, st) s ∗ (F0 ∗ R_rg) := by
    dsimp only [recordDecryptPlacedSpecP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegUntrustedExtBudget.recordDecryptPlacedSpecP,
      x_rg, R_rg]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hfits, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem⟩
  have hmemTF : s.mem ⊨
      (recordDecryptPlacedSpecTPTightF F0 C A lim ctl uuidTryParse S tdEnv).withVRegs.pre (x_rg, st) s ∗ R_rg := by
    dsimp only [Spec.withVRegs, recordDecryptPlacedSpecTPTightF]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpq_lt, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmemP⟩
  have hmemQ : s.mem ⊨
      ((recordDecryptPlacedSpecTPTightF F0 C A lim ctl uuidTryParse S tdEnv).withVRegs.restrictPre
        (fun p => Q p.1.st.pqRatchetState)).pre (x_rg, st) s ∗ R_rg :=
    Spec.satisfies_restrictPre.mpr ⟨hpq_Q, hmemTF⟩
  obtain ⟨sf, hsteps, hout⟩ := hreg (x_rg, st) R_rg s hpc hrun hmemQ hL
  try dsimp only [Spec.restrictPre] at hout
  rcases hout with ⟨hpc_sf, hrun_sf, hmf⟩ | ⟨hpan_sf, hmf⟩
  · refine ⟨sf, hsteps, Or.inl ?_⟩
    dsimp only [Spec.withVRegs, recordDecryptPlacedSpecTPTightF, recordDecryptPlacedSpecTF] at hmf
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf
    obtain ⟨hvregs_sf, hmf⟩ := hmf
    let R_rgF : SepProp :=
      wsRegionFrameVPlaced (retagSessionStore (A' := A.atState lim st s) kit)
        (retagIdentityStore (A' := A.atState lim st s) ikit) x s0 prevCap prevPtr ∗
      decStoreExtraPlaced (retagSessionStore (A' := A.atState lim st s) kit)
        (retagIdentityStore (A' := A.atState lim st s) ikit) st0 ist0 s0 ∗ (F0 ∗ R)
    have hmf1 : sf.mem ⊨
        (LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.recordDecryptPlacedSpec
          C A lim ctl uuidTryParse S tdEnv).post (x_rg, st) s sf ∗ R_rgF := by
      dsimp only [R_rg, R_rgF] at hmf ⊢
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmf
    dsimp only [LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.recordDecryptPlacedSpec] at hmf1
    rw [sepExists_sepConj_left, satisfies_sepExists] at hmf1
    obtain ⟨evs, hmf1⟩ := hmf1
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf1
    obtain ⟨hevs, hmf1⟩ := hmf1
    obtain ⟨hsp_sf, hx29_sf, hx27_sf⟩ := post_meta_extract_placed hmf1
    have hcrl_sf : LibsignalCodeRoLoaded lsmpl sf.mem := hcrl.of_keepsFrozen hsteps.keepsFrozen
    have hal_sf : sf.spAligned = true := by rw [State.spAligned, hsp_sf]; exact hal
    have hmeta_sf : wsMetaPlaced x s0 sf :=
      ⟨hrun_sf, hsp_sf.trans hsp, hal0, hal_sf, hx29_sf.trans hx29, hx27_sf, hcrl_sf, hvregs_sf.trans hvregs⟩
    have hsb' := hsb.step (fun _ _ h1 h2 => SeqEnv.append h1 h2) hevs
    refine ⟨M.stepEvents evs st, ?_, hpc_sf, hmeta_sf, s, rec, ses, G, prevCap, prevPtr,
      hsp, htrace, hload, hscope, hcur, hw0, ?_⟩
    · intro rec₁ hload₁
      cases Option.some.inj (Except.ok.inj (hload.symm.trans hload₁))
      exact hsb'
    · dsimp only [x_rg, R_rgF, RustCliAllocBudget.atState] at hmf1 ⊢
      rw [rep_wsRegionFrameV_eq A (A.pool lim st s) (A.pool lim (M.stepEvents evs st) sf),
        rep_decStoreExtra_eq A (A.pool lim st s) (A.pool lim (M.stepEvents evs st) sf)] at hmf1
      simpa only [sepConj_assoc] using hmf1
  · refine ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan_sf, ?_⟩))⟩
    dsimp only [Spec.withVRegs, recordDecryptPlacedSpecTPTightF,
      withStoresDecPlacedSpecVTPF, withStoresDecPlacedSpecVX, R_rg] at hmf ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf
    rcases hmf with ⟨⟨hmod_pan, hpref⟩, hmf⟩
    have hload_pref : s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession <+: sf.trace := by
      rwa [← htrace]
    have hs0_pref : s0.trace <+: sf.trace :=
      (List.prefix_append s0.trace (kit.loadEvs encRecord x.rem.val ans.loadSession)).trans hload_pref
    have hpan_pure : s0.trace <+: sf.trace ∧
        (∃ answers : StoreAnswers (List (BitVec 8)) Unit,
          kit.loadRel st0 x.rem.val answers.loadSession ∧
          s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
          ((x.model C S uuidTryParse answers).1 = .error .panic ∨ False)) :=
      ⟨hs0_pref, ⟨ans, hload ▸ hscope.2, hload_pref, Or.inl
        (model_panic_of_region_panic C S x ans rec ses G prevPtr hload hcur hmod_pan)⟩⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpan_pure, ?_⟩
    have h_any : anyHeap ∗
        (wsRegionFrameVPlaced (retagSessionStore (A' := A.atState lim st s) kit)
          (retagIdentityStore (A' := A.atState lim st s) ikit) x s0 prevCap prevPtr ∗
        decStoreExtraPlaced (retagSessionStore (A' := A.atState lim st s) kit)
          (retagIdentityStore (A' := A.atState lim st s) ikit) st0 ist0 s0) ⊢ anyHeap :=
      entails_anyHeap _
    rw [← sepConj_assoc, ← sepConj_assoc] at hmf
    rw [sepConj_assoc anyHeap] at hmf
    exact Satisfies.mono (sepConj_mono_left h_any) hmf

/-- Crosses the record-decrypt region at budget `recordDecryptPlacedSpecTF` restricted by `Q`. -/
theorem segRegionSomeVT_placed_ok [LibsignalPlacement] {M : AllocCostModel} {F0 : SepProp}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (Q : List (BitVec 8) → Prop)
    (hreg : region_ok (lsProg_463 H) recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpecTF F0 C A lim ctl uuidTryParse S tdEnv).withVRegs.restrictPre
        (fun p => Q p.1.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (R : SepProp) (s0 s : State)
    (hRS : RegionSomeStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans (F0 ∗ R) s0 s) :
    (lsProg_463 H).CodeLoaded s.mem →
    ∃ s', Steps (lsProg_463 H) s s' ∧
      (PostSomeStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans (F0 ∗ R) s0 s' ∨
        SubroutineOutcome (withStoresDecPlacedSpecVTF F0 C A lim ctl uuidTryParse S tdEnv
          encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s') := by
  intro hL
  obtain ⟨st, hsb_all, hpc, ⟨hrun, hsp, hal0, hal, hx29, _hx27, hcrl, hvregs⟩,
    rec, ses, G, prevCap, prevPtr, hload, hscope, hcur, hw0, htrace, hmem⟩ := hRS
  let x_rg := recGhostOf x prevPtr G ses.state
  let R_rg : SepProp :=
    wsRegionFrameVPlaced (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit) x s0 prevCap prevPtr ∗
    decStoreExtraPlaced (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit) st0 ist0 s0 ∗ R
  have hgv := sessionGhostValid_of_recordPlacedPre hw0 (by simpa only [sepConj_assoc] using hmem)
  have hsb := hsb_all rec ses G hload hscope hcur hgv
  have hfits := hsb.fitsSeg (fun _ _ h1 h2 => SeqEnv.append h1 h2) fromPostSomeEnv_nonempty
  obtain ⟨hpq_lt, hpq_Q⟩ := hQ x.rem.val rec ses hscope hcur
  have hmem0 : s.mem ⊨
      (LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.recordDecryptPlacedSpec
        C A lim ctl uuidTryParse S tdEnv).pre (x_rg, st) s ∗ (F0 ∗ R_rg) := by
    dsimp only [LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.recordDecryptPlacedSpec,
      x_rg, R_rg]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hfits, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem⟩
  have hmemTF : s.mem ⊨
      (recordDecryptPlacedSpecTF F0 C A lim ctl uuidTryParse S tdEnv).withVRegs.pre (x_rg, st) s ∗ R_rg := by
    dsimp only [Spec.withVRegs, recordDecryptPlacedSpecTF]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpq_lt, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem0⟩
  have hmemQ : s.mem ⊨
      ((recordDecryptPlacedSpecTF F0 C A lim ctl uuidTryParse S tdEnv).withVRegs.restrictPre
        (fun p => Q p.1.st.pqRatchetState)).pre (x_rg, st) s ∗ R_rg :=
    Spec.satisfies_restrictPre.mpr ⟨hpq_Q, hmemTF⟩
  obtain ⟨sf, hsteps, hout⟩ := hreg (x_rg, st) R_rg s hpc hrun hmemQ hL
  try dsimp only [Spec.restrictPre] at hout
  rcases hout with ⟨hpc_sf, hrun_sf, hmf⟩ | ⟨hpan_sf, hmf⟩
  · refine ⟨sf, hsteps, Or.inl ?_⟩
    dsimp only [Spec.withVRegs, recordDecryptPlacedSpecTF] at hmf
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf
    obtain ⟨hvregs_sf, hmf⟩ := hmf
    let R_rgF : SepProp :=
      wsRegionFrameVPlaced (retagSessionStore (A' := A.atState lim st s) kit)
        (retagIdentityStore (A' := A.atState lim st s) ikit) x s0 prevCap prevPtr ∗
      decStoreExtraPlaced (retagSessionStore (A' := A.atState lim st s) kit)
        (retagIdentityStore (A' := A.atState lim st s) ikit) st0 ist0 s0 ∗ (F0 ∗ R)
    have hmf1 : sf.mem ⊨
        (LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.recordDecryptPlacedSpec
          C A lim ctl uuidTryParse S tdEnv).post (x_rg, st) s sf ∗ R_rgF := by
      dsimp only [R_rg, R_rgF] at hmf ⊢
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmf
    dsimp only [LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.recordDecryptPlacedSpec] at hmf1
    rw [sepExists_sepConj_left, satisfies_sepExists] at hmf1
    obtain ⟨evs, hmf1⟩ := hmf1
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf1
    obtain ⟨hevs, hmf1⟩ := hmf1
    obtain ⟨hsp_sf, hx29_sf, hx27_sf⟩ := post_meta_extract_placed hmf1
    have hcrl_sf : LibsignalCodeRoLoaded lsmpl sf.mem := hcrl.of_keepsFrozen hsteps.keepsFrozen
    have hal_sf : sf.spAligned = true := by rw [State.spAligned, hsp_sf]; exact hal
    have hmeta_sf : wsMetaPlaced x s0 sf :=
      ⟨hrun_sf, hsp_sf.trans hsp, hal0, hal_sf, hx29_sf.trans hx29, hx27_sf, hcrl_sf, hvregs_sf.trans hvregs⟩
    have hsb' := hsb.step (fun _ _ h1 h2 => SeqEnv.append h1 h2) hevs
    refine ⟨M.stepEvents evs st, ?_, hpc_sf, hmeta_sf, s, rec, ses, G, prevCap, prevPtr,
      hsp, htrace, hload, hscope, hcur, hw0, ?_⟩
    · intro rec₁ hload₁
      cases Option.some.inj (Except.ok.inj (hload.symm.trans hload₁))
      exact hsb'
    · dsimp only [x_rg, R_rgF, RustCliAllocBudget.atState] at hmf1 ⊢
      rw [rep_wsRegionFrameV_eq A (A.pool lim st s) (A.pool lim (M.stepEvents evs st) sf),
        rep_decStoreExtra_eq A (A.pool lim st s) (A.pool lim (M.stepEvents evs st) sf)] at hmf1
      simpa only [sepConj_assoc] using hmf1
  · refine ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan_sf, ?_⟩))⟩
    dsimp only [Spec.withVRegs, recordDecryptPlacedSpecTF,
      LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.recordDecryptPlacedSpec,
      withStoresDecPlacedSpecVTF, withStoresDecPlacedSpecV, R_rg] at hmf ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf
    rcases hmf with ⟨⟨hdisj, hpref⟩, hmf⟩
    have hload_pref : s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession <+: sf.trace := by
      rwa [← htrace]
    have hs0_pref : s0.trace <+: sf.trace :=
      (List.prefix_append s0.trace (kit.loadEvs encRecord x.rem.val ans.loadSession)).trans hload_pref
    have hpan_pure : s0.trace <+: sf.trace ∧
        (∃ answers : StoreAnswers (List (BitVec 8)) Unit,
          kit.loadRel st0 x.rem.val answers.loadSession ∧
          s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
          ((x.model C S uuidTryParse answers).1 = .error .panic ∨ x.recvPanics S answers)) := by
      refine ⟨hs0_pref, ?_⟩
      rcases hdisj with hmod_pan | hrecv_pan
      · exact ⟨ans, hload ▸ hscope.2, hload_pref, Or.inl
          (model_panic_of_region_panic C S x ans rec ses G prevPtr hload hcur hmod_pan)⟩
      · exact ⟨ans, hload ▸ hscope.2, hload_pref, Or.inr
          (recvPanics_of_region_recvPanics S x ans rec ses G prevPtr hload hcur hrecv_pan)⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpan_pure, ?_⟩
    have h_any : anyHeap ∗
        (wsRegionFrameVPlaced (retagSessionStore (A' := A.atState lim st s) kit)
          (retagIdentityStore (A' := A.atState lim st s) ikit) x s0 prevCap prevPtr ∗
        decStoreExtraPlaced (retagSessionStore (A' := A.atState lim st s) kit)
          (retagIdentityStore (A' := A.atState lim st s) ikit) st0 ist0 s0) ⊢ anyHeap :=
      entails_anyHeap _
    rw [← sepConj_assoc, ← sepConj_assoc] at hmf
    rw [sepConj_assoc anyHeap] at hmf
    exact Satisfies.mono (sepConj_mono_left h_any) hmf

/-! ## Budget callee bundles -/

/-- Budget callee contracts on `lsProg_463 H` for `withStoresDecPlacedSpecVTPF`. -/
structure DecCalleesTPFPlaced [LibsignalPlacement] {M : AllocCostModel} (F0 : SepProp) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) (H : LibsignalHooks)
    (Q : List (BitVec 8) → Prop) : Prop where
  region : region_ok (lsProg_463 H) recEntryPlaced recExitPlaced
    ((recordDecryptPlacedSpecTPTightF F0 C A lim ctl uuidTryParse S tdEnv).withVRegs.restrictPre
      (fun p => Q p.1.st.pqRatchetState))
  remoteIk : RemoteIdentityKeyPlacedOk A.repAlloc H
  dropSs : DropSessionStructureLocal2PlacedOk A lim H

/-- `DecCalleesTPFPlaced` specialized to `tokenInitPlacedAt`. -/
abbrev DecCalleesTPPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) (H : LibsignalHooks)
    (Q : List (BitVec 8) → Prop) : Prop :=
  DecCalleesTPFPlaced tokenInitPlacedAt C A lim ctl S tdEnv H Q

/-- Budget callee contracts on `lsProg_463 H` for `withStoresDecPlacedSpecVTF`. -/
structure DecCalleesTFPlaced [LibsignalPlacement] {M : AllocCostModel} (F0 : SepProp) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) (H : LibsignalHooks)
    (Q : List (BitVec 8) → Prop) : Prop where
  region : region_ok (lsProg_463 H) recEntryPlaced recExitPlaced
    ((recordDecryptPlacedSpecTF F0 C A lim ctl uuidTryParse S tdEnv).withVRegs.restrictPre
      (fun p => Q p.1.st.pqRatchetState))
  remoteIk : RemoteIdentityKeyPlacedOk A.repAlloc H
  dropSs : DropSessionStructureLocal2PlacedOk A lim H

/-- `DecCalleesTFPlaced` specialized to `tokenInitPlacedAt`. -/
abbrev DecCalleesTPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) (H : LibsignalHooks)
    (Q : List (BitVec 8) → Prop) : Prop :=
  DecCalleesTFPlaced tokenInitPlacedAt C A lim ctl S tdEnv H Q

/-- Constructs `DecCalleesTPFPlaced` from the record-decrypt region contract and `rustCliDeallocBudgetSpec`. -/
theorem DecCalleesTPFPlaced.of_region [LibsignalPlacement] {M : AllocCostModel} {F0 : SepProp}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop} {H : LibsignalHooks} {Q : List (BitVec 8) → Prop}
    (hDealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hRegion : region_ok (lsProg_463 H) recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpecTPTightF F0 C A lim ctl uuidTryParse S tdEnv).withVRegs.restrictPre
        (fun p => Q p.1.st.pqRatchetState))) :
    DecCalleesTPFPlaced F0 C A lim ctl S tdEnv H Q :=
  ⟨hRegion, remoteIdentityKeyPlacedOk A.repAlloc H, dropSessionStructureLocal2PlacedOk hDealloc⟩

/-- Constructs `DecCalleesTFPlaced` from the record-decrypt region contract and `rustCliDeallocBudgetSpec`. -/
theorem DecCalleesTFPlaced.of_region [LibsignalPlacement] {M : AllocCostModel} {F0 : SepProp}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop} {H : LibsignalHooks} {Q : List (BitVec 8) → Prop}
    (hDealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hRegion : region_ok (lsProg_463 H) recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpecTF F0 C A lim ctl uuidTryParse S tdEnv).withVRegs.restrictPre
        (fun p => Q p.1.st.pqRatchetState))) :
    DecCalleesTFPlaced F0 C A lim ctl S tdEnv H Q :=
  ⟨hRegion, remoteIdentityKeyPlacedOk A.repAlloc H, dropSessionStructureLocal2PlacedOk hDealloc⟩

/-! ## Twelve-segment assembly -/

section ChainVTPPlaced

variable [LibsignalPlacement] {M : AllocCostModel} {F0 : SepProp}
  {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
  {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
  {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
  {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
  {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
  {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
  {Q : List (BitVec 8) → Prop}
  (hH : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
  (hC : DecCalleesTPFPlaced F0 C A lim ctl S tdEnv H Q)
  (x : DecryptGhost) (st_init : M.σ) (R : SepProp) (s0 : State)
  (hAddr : kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val)

private theorem reachVTPF_resultFinal_placed (s : State)
    (h : ResultFinalStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv
      encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s :=
  decSegVTPF_chain_placed (segWriteVX_placed_ok x st_init (F0 ∗ R) s0 s h) (fun _ hf => hf.elim)

include hH hC in
private theorem reachVTPF_errJoin_placed (pt : Bool) (s : State)
    (h : ErrJoinStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init pt (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv
      encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s :=
  decSegVTPF_chain_placed (segErrTeardownVX_placed_ok hH hC.dropSs x st_init pt (F0 ∗ R) s0 s h)
    (reachVTPF_resultFinal_placed x st_init R s0)

include hH hC hAddr in
private theorem reachVTPF_storeCall_placed (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxExtPlaced kit ikit H s0 s)
    (h : StoreCallStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv
      encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s :=
  decSegVTPF_chain_placed (segStoreVX_placed_ok hH hC.dropSs x st_init ans (F0 ∗ R) s0 s hAddr.1 hfs h)
    (fun s' h' => h'.elim (reachVTPF_resultFinal_placed x st_init R s0 s')
      (reachVTPF_errJoin_placed hH hC x st_init R s0 true s'))

include hH hC hAddr in
private theorem reachVTPF_trusted_placed (ans : StoreAnswers (List (BitVec 8)) Unit) (t : Bool)
    (s : State) (hfs : DecFsCtxExtPlaced kit ikit H s0 s)
    (h : TrustedStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans t (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv
      encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s := by
  cases t with
  | true =>
    exact decSegVTPF_chainFs_placed hfs
      (segSaveVX_placed_ok hH x st_init ans (F0 ∗ R) s0 s hAddr.2 hfs h)
      (fun s' hfs' h' => h'.elim
        (fun ⟨ans', hsc⟩ => reachVTPF_storeCall_placed hH hC x st_init R s0 hAddr ans' s' hfs' hsc)
        (reachVTPF_errJoin_placed hH hC x st_init R s0 true s'))
  | false =>
    exact decSegVTPF_chain_placed (segUntrustedVX_placed_ok hH x st_init ans (F0 ∗ R) s0 s h)
      (reachVTPF_errJoin_placed hH hC x st_init R s0 true)

include hH hC hAddr in
private theorem reachVTPF_keyReady_placed (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxExtPlaced kit ikit H s0 s)
    (h : KeyReadyStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv
      encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s :=
  decSegVTPF_chainFs_placed hfs
    (segTrustVX_placed_ok hH x st_init ans (F0 ∗ R) s0 s hAddr.2 hfs h)
    (fun s' hfs' h' => h'.elim
      (fun ⟨ans', t, ht⟩ => reachVTPF_trusted_placed hH hC x st_init R s0 hAddr ans' t s' hfs' ht)
      (reachVTPF_errJoin_placed hH hC x st_init R s0 true s'))

include hH hC hAddr in
private theorem reachVTPF_loadPolled_placed
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hid : IdOrDistinctSid uuidTryParse kit st0 Scope x)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State) (hfs : DecFsCtxExtPlaced kit ikit H s0 s)
    (h : LoadPolledStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv
      encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s := by
  refine decSegVTPF_chainFs_placed hfs
    (segDispatchVP_placed_ok hH x st_init ans (F0 ∗ R) s0 s hid h) ?_
  rintro s' hfs' (hSome | hNone | hFin)
  · refine Arm64.reaches_outcome.of_codeLoaded fun hL => ?_
    obtain ⟨s'', hst, hPost | hout⟩ :=
      segRegionSomeVTP_placed_ok Q hC.region hQ x st_init ans R s0 s' hSome hL
    · refine Arm64.reaches_outcome_steps hst ?_
      exact decSegVTPF_chainFs_placed (hfs'.of_steps hst)
        (segPostSomeVX_placed_ok hH hC.remoteIk x st_init ans (F0 ∗ R) s0 s'' hPost)
        (fun s3 hfs3 h3 => h3.elim
          (reachVTPF_keyReady_placed hH hC x st_init R s0 hAddr ans s3 hfs3)
          (reachVTPF_errJoin_placed hH hC x st_init R s0 false s3))
    · exact Arm64.reaches_outcome_steps hst (Arm64.reaches_outcome.of_outcome hout)
  · refine decSegVTPF_chain_placed
      (segRegionNoneVX_placed_ok hH.hooks x st_init ans (F0 ∗ R) s0 s' hNone) ?_
    intro s'' hPost
    exact decSegVTPF_chain_placed (segPostNoneVX_placed_ok x st_init ans (F0 ∗ R) s0 s'' hPost)
      (reachVTPF_errJoin_placed hH hC x st_init R s0 false)
  · exact reachVTPF_resultFinal_placed x st_init R s0 s' hFin

end ChainVTPPlaced

/-- Per-ghost reachability for budget-threaded `withStoresDecPlacedSpecVTPF` with entry-file `envOk`. -/
theorem withStoresDec_reachVTPF_fs_placed [LibsignalPlacement] {M : AllocCostModel} {F0 : SepProp}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hC : DecCalleesTPFPlaced F0 C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (x : DecryptGhost) (st_init : M.σ) (R : SepProp) (s0 : State)
    (hid : IdOrDistinctSid uuidTryParse kit st0 Scope x) (hpc : s0.pc = wsEntryPCPlaced)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope).pre (x, st_init) s0 ∗ R)
    (hal : s0.spAligned = true) (hfs : DecFsCtxExtPlaced kit ikit H s0 s0) :
    reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv
      encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s0 := by
  have hpreV : s0.mem ⊨ (withStoresDecPlacedSpecVX C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope (fun _ _ => False)).pre (x, st_init) s0 ∗ (F0 ∗ R) := by
    dsimp only [withStoresDecPlacedSpecVTPF] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  have hAddr := withStoresDecPlacedSpecV_pre_addrOk
    (C := C) (ctl := ctl) (S := S) (tdEnv := tdEnv) (encRecord := encRecord) (Scope := Scope) hpreV
  exact decSegVTPF_chainFs_placed hfs
    (segLoadVX_placed_ok hH x st_init (F0 ∗ R) s0 hfs hpc hrun hal hpreV)
    (fun s hfs' ⟨ans, h⟩ =>
      reachVTPF_loadPolled_placed hH hC x st_init R s0 hAddr hQ hid ans s hfs' h)

/-- `withStoresDec_reachVTPF_fs_placed` specialized to `tokenInitPlacedAt`. -/
theorem withStoresDec_reachVTP_fs_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hC : DecCalleesTPPlaced C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (x : DecryptGhost) (st_init : M.σ) (R : SepProp) (s0 : State)
    (hid : IdOrDistinctSid uuidTryParse kit st0 Scope x) (hpc : s0.pc = wsEntryPCPlaced)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (withStoresDecPlacedSpecVTP C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope).pre (x, st_init) s0 ∗ R)
    (hal : s0.spAligned = true) (hfs : DecFsCtxExtPlaced kit ikit H s0 s0) :
    reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTP C A lim ctl uuidTryParse S tdEnv
      encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s0 :=
  withStoresDec_reachVTPF_fs_placed hH hC hQ x st_init R s0 hid hpc hrun hpre hal hfs

/-- Relocatable `subroutine_ok` for budget-threaded `withStoresDecPlacedSpecVTPF` under `IdOrDistinctSid`. -/
theorem withStoresDec_okVTPF_fs_placed [LibsignalPlacement] {M : AllocCostModel} {F0 : SepProp}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hC : DecCalleesTPFPlaced F0 C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet) (lsProg_463 H)) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced (withEnvPre
      ((withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope).restrictPre
        (fun p => IdOrDistinctSid uuidTryParse kit st0 Scope p.1))
      fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  refine Arm64.subroutine_ok_outcome_intro ?_
  rintro ⟨x, st_init⟩ R s0 hpc hrun hpre0 hal
  obtain ⟨h0, hpreR⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  obtain ⟨hid, hpre⟩ := Spec.satisfies_restrictPre.mp hpreR
  exact (withStoresDec_reachVTPF_fs_placed hH hC hQ x st_init R s0 hid hpc hrun hpre hal
    (FsCtx.of_entry hKitFs h0)).mono_outcome fun _ hout => hout

/-- `withStoresDec_okVTPF_fs_placed` specialized to `tokenInitPlacedAt`. -/
theorem withStoresDec_okVTP_fs_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hC : DecCalleesTPPlaced C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet) (lsProg_463 H)) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced (withEnvPre
      ((withStoresDecPlacedSpecVTP C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope).restrictPre
        (fun p => IdOrDistinctSid uuidTryParse kit st0 Scope p.1))
      fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTPF_fs_placed hH hC hQ hKitFs

/-- Specialization of `withStoresDec_okVTPF_fs_placed` to `DistinctSid`. -/
theorem withStoresDec_okVTPF_distinct_fs_placed [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hC : DecCalleesTPFPlaced F0 C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet) (lsProg_463 H)) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced (withEnvPre
      ((withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope).restrictPre
        (fun p => CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid
          uuidTryParse p.1.loc.name.bytes p.1.rem.name.bytes))
      fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  refine Arm64.subroutine_ok_outcome_intro ?_
  rintro ⟨x, st_init⟩ R s0 hpc hrun hpre0 hal
  obtain ⟨h0, hpreR⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  obtain ⟨hdist, hpre⟩ := Spec.satisfies_restrictPre.mp hpreR
  exact (withStoresDec_reachVTPF_fs_placed hH hC hQ x st_init R s0
    (idOrDistinctSid_of_distinctSid hdist) hpc hrun hpre hal
    (FsCtx.of_entry hKitFs h0)).mono_outcome fun _ hout => hout

/-- `withStoresDec_okVTPF_distinct_fs_placed` specialized to `tokenInitPlacedAt`. -/
theorem withStoresDec_okVTP_distinct_fs_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hC : DecCalleesTPPlaced C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet) (lsProg_463 H)) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced (withEnvPre
      ((withStoresDecPlacedSpecVTP C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope).restrictPre
        (fun p => CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid
          uuidTryParse p.1.loc.name.bytes p.1.rem.name.bytes))
      fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTPF_distinct_fs_placed hH hC hQ hKitFs

theorem withStoresDec_okVTPF_placed [LibsignalPlacement] {M : AllocCostModel} {F0 : SepProp}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hC : DecCalleesTPFPlaced F0 C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      ((withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope).restrictPre
        (fun p => IdOrDistinctSid uuidTryParse kit st0 Scope p.1)) :=
  subroutine_ok_of_withEnvPre (withStoresDec_okVTPF_fs_placed hH hC hQ (.inl htriv))
    fun s => htriv s.fs.files

theorem withStoresDec_okVTP_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hC : DecCalleesTPPlaced C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      ((withStoresDecPlacedSpecVTP C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope).restrictPre
        (fun p => IdOrDistinctSid uuidTryParse kit st0 Scope p.1)) :=
  withStoresDec_okVTPF_placed hH hC hQ htriv

section ChainVTPlaced

variable [LibsignalPlacement] {M : AllocCostModel} {F0 : SepProp}
  {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
  {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
  {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
  {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
  {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
  {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
  {Q : List (BitVec 8) → Prop}
  (hH : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
  (hscopeIn : ∀ r, Scope r → RecordInScope r) (hC : DecCalleesTFPlaced F0 C A lim ctl S tdEnv H Q)
  (x : DecryptGhost) (st_init : M.σ) (R : SepProp) (s0 : State)
  (hAddr : kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val)

private theorem reachVTF_resultFinal_placed (s : State)
    (h : ResultFinalStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTF F0 C A lim ctl uuidTryParse S tdEnv
      encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s :=
  decSegVTF_chain_placed (segWriteVX_placed_ok x st_init (F0 ∗ R) s0 s h) (fun _ hf => hf.elim)

include hH hC in
private theorem reachVTF_errJoin_placed (pt : Bool) (s : State)
    (h : ErrJoinStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init pt (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTF F0 C A lim ctl uuidTryParse S tdEnv
      encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s :=
  decSegVTF_chain_placed (segErrTeardownVX_placed_ok hH hC.dropSs x st_init pt (F0 ∗ R) s0 s h)
    (reachVTF_resultFinal_placed x st_init R s0)

include hH hC hAddr in
private theorem reachVTF_storeCall_placed (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxExtPlaced kit ikit H s0 s)
    (h : StoreCallStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTF F0 C A lim ctl uuidTryParse S tdEnv
      encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s :=
  decSegVTF_chain_placed (segStoreVX_placed_ok hH hC.dropSs x st_init ans (F0 ∗ R) s0 s hAddr.1 hfs h)
    (fun s' h' => h'.elim (reachVTF_resultFinal_placed x st_init R s0 s')
      (reachVTF_errJoin_placed hH hC x st_init R s0 true s'))

include hH hC hAddr in
private theorem reachVTF_trusted_placed (ans : StoreAnswers (List (BitVec 8)) Unit) (t : Bool)
    (s : State) (hfs : DecFsCtxExtPlaced kit ikit H s0 s)
    (h : TrustedStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans t (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTF F0 C A lim ctl uuidTryParse S tdEnv
      encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s := by
  cases t with
  | true =>
    exact decSegVTF_chainFs_placed hfs
      (segSaveVX_placed_ok hH x st_init ans (F0 ∗ R) s0 s hAddr.2 hfs h)
      (fun s' hfs' h' => h'.elim
        (fun ⟨ans', hsc⟩ => reachVTF_storeCall_placed hH hC x st_init R s0 hAddr ans' s' hfs' hsc)
        (reachVTF_errJoin_placed hH hC x st_init R s0 true s'))
  | false =>
    exact decSegVTF_chain_placed (segUntrustedVX_placed_ok hH x st_init ans (F0 ∗ R) s0 s h)
      (reachVTF_errJoin_placed hH hC x st_init R s0 true)

include hH hC hAddr in
private theorem reachVTF_keyReady_placed (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxExtPlaced kit ikit H s0 s)
    (h : KeyReadyStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTF F0 C A lim ctl uuidTryParse S tdEnv
      encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s :=
  decSegVTF_chainFs_placed hfs
    (segTrustVX_placed_ok hH x st_init ans (F0 ∗ R) s0 s hAddr.2 hfs h)
    (fun s' hfs' h' => h'.elim
      (fun ⟨ans', t, ht⟩ => reachVTF_trusted_placed hH hC x st_init R s0 hAddr ans' t s' hfs' ht)
      (reachVTF_errJoin_placed hH hC x st_init R s0 true s'))

include hH hscopeIn hC hAddr in
private theorem reachVTF_loadPolled_placed
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State) (hfs : DecFsCtxExtPlaced kit ikit H s0 s)
    (h : LoadPolledStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans (F0 ∗ R) s0 s) :
    reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTF F0 C A lim ctl uuidTryParse S tdEnv
      encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s := by
  refine decSegVTF_chainFs_placed hfs
    (segDispatchVX_placed_ok hH hscopeIn x st_init ans (F0 ∗ R) s0 s h) ?_
  rintro s' hfs' (hSome | hNone | hFin)
  · refine Arm64.reaches_outcome.of_codeLoaded fun hL => ?_
    obtain ⟨s'', hst, hPost | hout⟩ :=
      segRegionSomeVT_placed_ok Q hC.region hQ x st_init ans R s0 s' hSome hL
    · refine Arm64.reaches_outcome_steps hst ?_
      exact decSegVTF_chainFs_placed (hfs'.of_steps hst)
        (segPostSomeVX_placed_ok hH hC.remoteIk x st_init ans (F0 ∗ R) s0 s'' hPost)
        (fun s3 hfs3 h3 => h3.elim
          (reachVTF_keyReady_placed hH hC x st_init R s0 hAddr ans s3 hfs3)
          (reachVTF_errJoin_placed hH hC x st_init R s0 false s3))
    · exact Arm64.reaches_outcome_steps hst (Arm64.reaches_outcome.of_outcome hout)
  · refine decSegVTF_chain_placed
      (segRegionNoneVX_placed_ok hH.hooks x st_init ans (F0 ∗ R) s0 s' hNone) ?_
    intro s'' hPost
    exact decSegVTF_chain_placed (segPostNoneVX_placed_ok x st_init ans (F0 ∗ R) s0 s'' hPost)
      (reachVTF_errJoin_placed hH hC x st_init R s0 false)
  · exact reachVTF_resultFinal_placed x st_init R s0 s' hFin

end ChainVTPlaced

/-- Relocatable `subroutine_ok` for budget-threaded `withStoresDecPlacedSpecVTF` under `Scope ⊆ RecordInScope`. -/
theorem withStoresDec_okVTF_fs_placed [LibsignalPlacement] {M : AllocCostModel} {F0 : SepProp}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hscopeIn : ∀ r, Scope r → RecordInScope r) (hC : DecCalleesTFPlaced F0 C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet) (lsProg_463 H)) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced (withEnvPre
      (withStoresDecPlacedSpecVTF F0 C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope)
      fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  refine Arm64.subroutine_ok_outcome_intro ?_
  rintro ⟨x, st_init⟩ R s0 hpc hrun hpre0 hal
  obtain ⟨h0, hpre⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  have hpreV : s0.mem ⊨ (withStoresDecPlacedSpecV C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope).pre (x, st_init) s0 ∗ (F0 ∗ R) := by
    dsimp only [withStoresDecPlacedSpecVTF] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  have hAddr := withStoresDecPlacedSpecV_pre_addrOk hpreV
  have hfs0 : DecFsCtxExtPlaced kit ikit H s0 s0 := FsCtx.of_entry hKitFs h0
  exact decSegVTF_chainFs_placed hfs0
    (segLoadVX_placed_ok hH x st_init (F0 ∗ R) s0 hfs0 hpc hrun hal hpreV)
    (fun s hfs ⟨ans, h⟩ =>
      reachVTF_loadPolled_placed hH hscopeIn hC x st_init R s0 hAddr hQ ans s hfs h)

theorem withStoresDec_okVT_fs_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hscopeIn : ∀ r, Scope r → RecordInScope r) (hC : DecCalleesTPlaced C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet) (lsProg_463 H)) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced (withEnvPre
      (withStoresDecPlacedSpecVT C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope)
      fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTF_fs_placed hH hscopeIn hC hQ hKitFs

theorem withStoresDec_okVTF_placed [LibsignalPlacement] {M : AllocCostModel} {F0 : SepProp}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hscopeIn : ∀ r, Scope r → RecordInScope r) (hC : DecCalleesTFPlaced F0 C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      (withStoresDecPlacedSpecVTF F0 C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope) :=
  subroutine_ok_of_withEnvPre (withStoresDec_okVTF_fs_placed hH hscopeIn hC hQ (.inl htriv))
    fun s => htriv s.fs.files

theorem withStoresDec_okVT_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hscopeIn : ∀ r, Scope r → RecordInScope r) (hC : DecCalleesTPlaced C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      (withStoresDecPlacedSpecVT C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope) :=
  withStoresDec_okVTF_placed hH hscopeIn hC hQ htriv

/-- `withLsFrozen`-guarded variant of budget-threaded `DecCalleesTPFPlaced`. -/
structure DecCalleesTPFFrozenPlaced [LibsignalPlacement] {M : AllocCostModel} (F0 : SepProp)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (H : LibsignalHooks) (Q : List (BitVec 8) → Prop) : Prop where
  region : region_ok (lsProg_463 H) recEntryPlaced recExitPlaced
    ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
      (recordDecryptPlacedSpecTPTightF F0 C A lim ctl uuidTryParse S tdEnv)).withVRegs.restrictPre
      (fun p => Q p.1.st.pqRatchetState))
  remoteIk : RemoteIdentityKeyPlacedOk A.repAlloc H
  dropSs : DropSessionStructureLocal2PlacedOk A lim H

/-- `DecCalleesTPFFrozenPlaced` specialized to `tokenInitPlacedAt`. -/
abbrev DecCalleesTPFrozenPlaced [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (H : LibsignalHooks) (Q : List (BitVec 8) → Prop) : Prop :=
  DecCalleesTPFFrozenPlaced tokenInitPlacedAt C A lim ctl S tdEnv H Q

/-- Constructs `DecCalleesTPFFrozenPlaced` from the `withLsFrozen` record-decrypt region contract. -/
theorem DecCalleesTPFFrozenPlaced.of_region [LibsignalPlacement] {M : AllocCostModel} {F0 : SepProp}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop} {H : LibsignalHooks}
    {Q : List (BitVec 8) → Prop}
    (hDealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hRegion : region_ok (lsProg_463 H) recEntryPlaced recExitPlaced
      ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTightF F0 C A lim ctl uuidTryParse S tdEnv)).withVRegs.restrictPre
        (fun p => Q p.1.st.pqRatchetState))) :
    DecCalleesTPFFrozenPlaced F0 C A lim ctl S tdEnv H Q :=
  ⟨hRegion, remoteIdentityKeyPlacedOk A.repAlloc H, dropSessionStructureLocal2PlacedOk hDealloc⟩

/-- `withLsFrozen`-guarded budget-threaded `SegRegionSome` for `withStoresDecPlacedSpecVTPF`. -/
theorem segRegionSomeVTP_frozen_placed_ok [LibsignalPlacement] {M : AllocCostModel} {F0 : SepProp}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (Q : List (BitVec 8) → Prop)
    (hreg : region_ok (lsProg_463 H) recEntryPlaced recExitPlaced
      ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTightF F0 C A lim ctl uuidTryParse S tdEnv)).withVRegs.restrictPre
        (fun p => Q p.1.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (R : SepProp) (s0 s : State)
    (hRS : RegionSomeStatePVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans (F0 ∗ R) s0 s)
    (hFroz : CryptoVerification.LibsignalFrozen lsmpl s.mem) :
    (lsProg_463 H).CodeLoaded s.mem →
    ∃ s', Steps (lsProg_463 H) s s' ∧
      (PostSomeStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans (F0 ∗ R) s0 s' ∨
        SubroutineOutcome
          (withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv encRecord
            kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s') := by
  intro hL
  obtain ⟨st, hsb_all, hpc, ⟨hrun, hsp, hal0, hal, hx29, _hx27, hcrl, hvregs⟩,
    rec, ses, G, prevCap, prevPtr, hload, hscope, hcur, hw0, htrace, hmem⟩ := hRS
  let x_rg := recGhostOf x prevPtr G ses.state
  let R_rg : SepProp :=
    wsRegionFrameVPlaced (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit) x s0 prevCap prevPtr ∗
    decStoreExtraPlaced (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit) st0 ist0 s0 ∗ R
  have hgv := sessionGhostValid_of_recordPlacedPreP hw0 (by simpa only [sepConj_assoc] using hmem)
  have hsb := hsb_all rec ses G hload hscope hcur hgv
  have hfits := hsb.fitsSeg (fun _ _ h1 h2 => SeqEnv.append h1 h2) fromPostSomeEnv_nonempty
  obtain ⟨hpq_lt, hpq_Q⟩ := hQ x.rem.val rec ses hscope hcur
  have hmemP : s.mem ⊨
      (recordDecryptPlacedSpecP C A lim ctl uuidTryParse S tdEnv).pre (x_rg, st) s ∗ (F0 ∗ R_rg) := by
    dsimp only [recordDecryptPlacedSpecP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegUntrustedExtBudget.recordDecryptPlacedSpecP,
      x_rg, R_rg]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hfits, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem⟩
  have hmemTF : s.mem ⊨
      (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTightF F0 C A lim ctl uuidTryParse S tdEnv)).withVRegs.pre (x_rg, st) s ∗ R_rg := by
    dsimp only [Spec.withVRegs, CryptoVerification.LibsignalTripleRatchet.withLsFrozen, recordDecryptPlacedSpecTPTightF]
    have hgoal : s.mem ⊨ ⌜x_rg.st.pqRatchetState.length < 2 ^ 32⌝ ∗
        (⌜CryptoVerification.LibsignalFrozen lsmpl s.mem⌝ ∗
          ((recordDecryptPlacedSpecP C A lim ctl uuidTryParse S tdEnv).pre (x_rg, st) s ∗ (F0 ∗ R_rg))) := by
      rw [satisfies_pure_sepConj]; refine ⟨hpq_lt, ?_⟩
      rw [satisfies_pure_sepConj]; exact ⟨hFroz, hmemP⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hgoal
  have hmemQ : s.mem ⊨
      ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTightF F0 C A lim ctl uuidTryParse S tdEnv)).withVRegs.restrictPre
        (fun p => Q p.1.st.pqRatchetState)).pre (x_rg, st) s ∗ R_rg :=
    Spec.satisfies_restrictPre.mpr ⟨hpq_Q, hmemTF⟩
  obtain ⟨sf, hsteps, hout⟩ := hreg (x_rg, st) R_rg s hpc hrun hmemQ hL
  try dsimp only [Spec.restrictPre] at hout
  rcases hout with ⟨hpc_sf, hrun_sf, hmf⟩ | ⟨hpan_sf, hmf⟩
  · refine ⟨sf, hsteps, Or.inl ?_⟩
    dsimp only [Spec.withVRegs, CryptoVerification.LibsignalTripleRatchet.withLsFrozen,
      recordDecryptPlacedSpecTPTightF, recordDecryptPlacedSpecTF] at hmf
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf
    obtain ⟨hvregs_sf, hmf⟩ := hmf
    let R_rgF : SepProp :=
      wsRegionFrameVPlaced (retagSessionStore (A' := A.atState lim st s) kit)
        (retagIdentityStore (A' := A.atState lim st s) ikit) x s0 prevCap prevPtr ∗
      decStoreExtraPlaced (retagSessionStore (A' := A.atState lim st s) kit)
        (retagIdentityStore (A' := A.atState lim st s) ikit) st0 ist0 s0 ∗ (F0 ∗ R)
    have hmf1 : sf.mem ⊨
        (LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.recordDecryptPlacedSpec
          C A lim ctl uuidTryParse S tdEnv).post (x_rg, st) s sf ∗ R_rgF := by
      dsimp only [R_rg, R_rgF] at hmf ⊢
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmf
    dsimp only [LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.recordDecryptPlacedSpec] at hmf1
    rw [sepExists_sepConj_left, satisfies_sepExists] at hmf1
    obtain ⟨evs, hmf1⟩ := hmf1
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf1
    obtain ⟨hevs, hmf1⟩ := hmf1
    obtain ⟨hsp_sf, hx29_sf, hx27_sf⟩ := post_meta_extract_placed hmf1
    have hcrl_sf : LibsignalCodeRoLoaded lsmpl sf.mem := hcrl.of_keepsFrozen hsteps.keepsFrozen
    have hal_sf : sf.spAligned = true := by rw [State.spAligned, hsp_sf]; exact hal
    have hmeta_sf : wsMetaPlaced x s0 sf :=
      ⟨hrun_sf, hsp_sf.trans hsp, hal0, hal_sf, hx29_sf.trans hx29, hx27_sf, hcrl_sf, hvregs_sf.trans hvregs⟩
    have hsb' := hsb.step (fun _ _ h1 h2 => SeqEnv.append h1 h2) hevs
    refine ⟨M.stepEvents evs st, ?_, hpc_sf, hmeta_sf, s, rec, ses, G, prevCap, prevPtr,
      hsp, htrace, hload, hscope, hcur, hw0, ?_⟩
    · intro rec₁ hload₁
      cases Option.some.inj (Except.ok.inj (hload.symm.trans hload₁))
      exact hsb'
    · dsimp only [x_rg, R_rgF, RustCliAllocBudget.atState] at hmf1 ⊢
      rw [rep_wsRegionFrameV_eq A (A.pool lim st s) (A.pool lim (M.stepEvents evs st) sf),
        rep_decStoreExtra_eq A (A.pool lim st s) (A.pool lim (M.stepEvents evs st) sf)] at hmf1
      simpa only [sepConj_assoc] using hmf1
  · refine ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan_sf, ?_⟩))⟩
    dsimp only [Spec.withVRegs, CryptoVerification.LibsignalTripleRatchet.withLsFrozen,
      recordDecryptPlacedSpecTPTightF,
      withStoresDecPlacedSpecVTPF, withStoresDecPlacedSpecVX, R_rg] at hmf ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf
    rcases hmf with ⟨⟨hmod_pan, hpref⟩, hmf⟩
    have hload_pref : s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession <+: sf.trace := by
      rwa [← htrace]
    have hs0_pref : s0.trace <+: sf.trace :=
      (List.prefix_append s0.trace (kit.loadEvs encRecord x.rem.val ans.loadSession)).trans hload_pref
    have hpan_pure : s0.trace <+: sf.trace ∧
        (∃ answers : StoreAnswers (List (BitVec 8)) Unit,
          kit.loadRel st0 x.rem.val answers.loadSession ∧
          s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
          ((x.model C S uuidTryParse answers).1 = .error .panic ∨ False)) :=
      ⟨hs0_pref, ⟨ans, hload ▸ hscope.2, hload_pref, Or.inl
        (model_panic_of_region_panic C S x ans rec ses G prevPtr hload hcur hmod_pan)⟩⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpan_pure, ?_⟩
    have h_any : anyHeap ∗
        (wsRegionFrameVPlaced (retagSessionStore (A' := A.atState lim st s) kit)
          (retagIdentityStore (A' := A.atState lim st s) ikit) x s0 prevCap prevPtr ∗
        decStoreExtraPlaced (retagSessionStore (A' := A.atState lim st s) kit)
          (retagIdentityStore (A' := A.atState lim st s) ikit) st0 ist0 s0) ⊢ anyHeap :=
      entails_anyHeap _
    rw [← sepConj_assoc, ← sepConj_assoc] at hmf
    rw [sepConj_assoc anyHeap] at hmf
    exact Satisfies.mono (sepConj_mono_left h_any) hmf

/-- `withLsFrozen`-guarded per-ghost reachability for budget-threaded `withStoresDecPlacedSpecVTPF`. -/
theorem withStoresDec_reachVTPF_frozen_fs_placed [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hC : DecCalleesTPFFrozenPlaced F0 C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (x : DecryptGhost) (st_init : M.σ) (R : SepProp) (s0 : State)
    (hid : IdOrDistinctSid uuidTryParse kit st0 Scope x) (hpc : s0.pc = wsEntryPCPlaced)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope).pre (x, st_init) s0 ∗ R)
    (hFroz : CryptoVerification.LibsignalFrozen lsmpl s0.mem)
    (hal : s0.spAligned = true) (hfs : DecFsCtxExtPlaced kit ikit H s0 s0) :
    reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv
      encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s0 := by
  have hpreV : s0.mem ⊨ (withStoresDecPlacedSpecVX C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope (fun _ _ => False)).pre (x, st_init) s0 ∗ (F0 ∗ R) := by
    dsimp only [withStoresDecPlacedSpecVTPF] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  have hAddr := withStoresDecPlacedSpecV_pre_addrOk
    (C := C) (ctl := ctl) (S := S) (tdEnv := tdEnv) (encRecord := encRecord) (Scope := Scope) hpreV
  have hErrJoin : ∀ (pt : Bool) (s : State),
      ErrJoinStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init pt (F0 ∗ R) s0 s →
      reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv
        encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s :=
    fun pt s h =>
      decSegVTPF_chain_placed (segErrTeardownVX_placed_ok hH hC.dropSs x st_init pt (F0 ∗ R) s0 s h)
        (reachVTPF_resultFinal_placed x st_init R s0)
  have hStoreCall : ∀ (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State),
      DecFsCtxExtPlaced kit ikit H s0 s →
      StoreCallStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans (F0 ∗ R) s0 s →
      reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv
        encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s :=
    fun ans s hfs_sc h =>
      decSegVTPF_chain_placed (segStoreVX_placed_ok hH hC.dropSs x st_init ans (F0 ∗ R) s0 s hAddr.1 hfs_sc h)
        (fun s' h' => h'.elim (reachVTPF_resultFinal_placed x st_init R s0 s')
          (hErrJoin true s'))
  have hTrusted : ∀ (ans : StoreAnswers (List (BitVec 8)) Unit) (t : Bool) (s : State),
      DecFsCtxExtPlaced kit ikit H s0 s →
      TrustedStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans t (F0 ∗ R) s0 s →
      reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv
        encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s := by
    intro ans t s hfs_t h
    cases t with
    | true =>
      exact decSegVTPF_chainFs_placed hfs_t
        (segSaveVX_placed_ok hH x st_init ans (F0 ∗ R) s0 s hAddr.2 hfs_t h)
        (fun s' hfs' h' => h'.elim
          (fun ⟨ans', hsc⟩ => hStoreCall ans' s' hfs' hsc)
          (hErrJoin true s'))
    | false =>
      exact decSegVTPF_chain_placed (segUntrustedVX_placed_ok hH x st_init ans (F0 ∗ R) s0 s h)
        (hErrJoin true)
  have hKeyReady : ∀ (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State),
      DecFsCtxExtPlaced kit ikit H s0 s →
      KeyReadyStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans (F0 ∗ R) s0 s →
      reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv
        encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s :=
    fun ans s hfs_kr h =>
      decSegVTPF_chainFs_placed hfs_kr
        (segTrustVX_placed_ok hH x st_init ans (F0 ∗ R) s0 s hAddr.2 hfs_kr h)
        (fun s' hfs' h' => h'.elim
          (fun ⟨ans', t, ht⟩ => hTrusted ans' t s' hfs' ht)
          (hErrJoin true s'))
  refine Arm64.reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨s, hst, ⟨ans, h⟩ | hout⟩ :=
    segLoadVX_placed_ok hH x st_init (F0 ∗ R) s0 hfs hpc hrun hal hpreV hL
  · have hfs1 := hfs.of_steps hst
    have hFroz1 := CryptoVerification.libsignalFrozen_of_keepsFrozen hFroz hst.keepsFrozen
    refine Arm64.reaches_outcome_steps hst ?_
    refine Arm64.reaches_outcome.of_codeLoaded fun hL1 => ?_
    obtain ⟨s', hst0, hNext | hout0⟩ :=
      segDispatchVP_placed_ok hH x st_init ans (F0 ∗ R) s0 s hid h hL1
    · have hfs' := hfs1.of_steps hst0
      have hFroz' := CryptoVerification.libsignalFrozen_of_keepsFrozen hFroz1 hst0.keepsFrozen
      refine Arm64.reaches_outcome_steps hst0 ?_
      rcases hNext with hSome | hNone | hFin
      · refine Arm64.reaches_outcome.of_codeLoaded fun hL' => ?_
        obtain ⟨s'', hst', hPost | hout'⟩ :=
          segRegionSomeVTP_frozen_placed_ok Q hC.region hQ x st_init ans R s0 s' hSome hFroz' hL'
        · refine Arm64.reaches_outcome_steps hst' ?_
          exact decSegVTPF_chainFs_placed (hfs'.of_steps hst')
            (segPostSomeVX_placed_ok hH hC.remoteIk x st_init ans (F0 ∗ R) s0 s'' hPost)
            (fun s3 hfs3 h3 => h3.elim
              (hKeyReady ans s3 hfs3)
              (hErrJoin false s3))
        · exact Arm64.reaches_outcome_steps hst' (Arm64.reaches_outcome.of_outcome hout')
      · refine decSegVTPF_chain_placed
          (segRegionNoneVX_placed_ok hH.hooks x st_init ans (F0 ∗ R) s0 s' hNone) ?_
        intro s'' hPost
        exact decSegVTPF_chain_placed (segPostNoneVX_placed_ok x st_init ans (F0 ∗ R) s0 s'' hPost)
          (hErrJoin false)
      · exact reachVTPF_resultFinal_placed x st_init R s0 s' hFin
    · exact Arm64.reaches_outcome_steps hst0
        (Arm64.reaches_outcome.of_outcome (subroutineOutcome_vx_to_framed_placed hout0))
  · exact Arm64.reaches_outcome_steps hst
      (Arm64.reaches_outcome.of_outcome (subroutineOutcome_vx_to_framed_placed hout))

/-- `withStoresDec_reachVTPF_frozen_fs_placed` specialized to `tokenInitPlacedAt`. -/
theorem withStoresDec_reachVTP_frozen_fs_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hC : DecCalleesTPFrozenPlaced C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (x : DecryptGhost) (st_init : M.σ) (R : SepProp) (s0 : State)
    (hid : IdOrDistinctSid uuidTryParse kit st0 Scope x) (hpc : s0.pc = wsEntryPCPlaced)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (withStoresDecPlacedSpecVTP C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope).pre (x, st_init) s0 ∗ R)
    (hFroz : CryptoVerification.LibsignalFrozen lsmpl s0.mem)
    (hal : s0.spAligned = true) (hfs : DecFsCtxExtPlaced kit ikit H s0 s0) :
    reaches_outcome (lsProg_463 H) (withStoresDecPlacedSpecVTP C A lim ctl uuidTryParse S tdEnv
      encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s0 :=
  withStoresDec_reachVTPF_frozen_fs_placed hH hC hQ x st_init R s0 hid hpc hrun hpre hFroz hal hfs

/-- `withLsFrozen`-guarded `subroutine_ok` for budget-threaded `withStoresDecPlacedSpecVTPF`. -/
theorem withStoresDec_okVTPF_frozen_fs_placed [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hC : DecCalleesTPFFrozenPlaced F0 C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet) (lsProg_463 H)) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced (withEnvPre
      ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope)).restrictPre
        (fun p => IdOrDistinctSid uuidTryParse kit st0 Scope p.1))
      fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  refine Arm64.subroutine_ok_outcome_intro ?_
  rintro ⟨x, st_init⟩ R s0 hpc hrun hpre0 hal
  obtain ⟨h0, hpreR⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  obtain ⟨hid, hpreF⟩ := Spec.satisfies_restrictPre.mp hpreR
  obtain ⟨hFroz, hpre⟩ := CryptoVerification.LibsignalTripleRatchet.extract_withLsFrozen hpreF
  exact (withStoresDec_reachVTPF_frozen_fs_placed hH hC hQ x st_init R s0 hid hpc hrun hpre hFroz hal
    (FsCtx.of_entry hKitFs h0)).mono_outcome fun _ hout => hout

/-- `withStoresDec_okVTPF_frozen_fs_placed` specialized to `tokenInitPlacedAt`. -/
theorem withStoresDec_okVTP_frozen_fs_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hC : DecCalleesTPFrozenPlaced C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet) (lsProg_463 H)) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced (withEnvPre
      ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (withStoresDecPlacedSpecVTP C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope)).restrictPre
        (fun p => IdOrDistinctSid uuidTryParse kit st0 Scope p.1))
      fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTPF_frozen_fs_placed hH hC hQ hKitFs

/-- Specialization of `withStoresDec_okVTPF_frozen_fs_placed` to `DistinctSid`. -/
theorem withStoresDec_okVTPF_distinct_frozen_fs_placed [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hC : DecCalleesTPFFrozenPlaced F0 C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet) (lsProg_463 H)) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced (withEnvPre
      ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope)).restrictPre
        (fun p => CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid
          uuidTryParse p.1.loc.name.bytes p.1.rem.name.bytes))
      fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  refine Arm64.subroutine_ok_outcome_intro ?_
  rintro ⟨x, st_init⟩ R s0 hpc hrun hpre0 hal
  obtain ⟨h0, hpreR⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  obtain ⟨hdist, hpreF⟩ := Spec.satisfies_restrictPre.mp hpreR
  obtain ⟨hFroz, hpre⟩ := CryptoVerification.LibsignalTripleRatchet.extract_withLsFrozen hpreF
  exact (withStoresDec_reachVTPF_frozen_fs_placed hH hC hQ x st_init R s0
    (idOrDistinctSid_of_distinctSid hdist) hpc hrun hpre hFroz hal
    (FsCtx.of_entry hKitFs h0)).mono_outcome fun _ hout => hout

/-- `withStoresDec_okVTPF_distinct_frozen_fs_placed` specialized to `tokenInitPlacedAt`. -/
theorem withStoresDec_okVTP_distinct_frozen_fs_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hC : DecCalleesTPFrozenPlaced C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet) (lsProg_463 H)) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced (withEnvPre
      ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (withStoresDecPlacedSpecVTP C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope)).restrictPre
        (fun p => CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid
          uuidTryParse p.1.loc.name.bytes p.1.rem.name.bytes))
      fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTPF_distinct_frozen_fs_placed hH hC hQ hKitFs

theorem withStoresDec_okVTPF_frozen_placed [LibsignalPlacement] {M : AllocCostModel} {F0 : SepProp}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hC : DecCalleesTPFFrozenPlaced F0 C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (withStoresDecPlacedSpecVTPF F0 C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope)).restrictPre
        (fun p => IdOrDistinctSid uuidTryParse kit st0 Scope p.1)) :=
  subroutine_ok_of_withEnvPre (withStoresDec_okVTPF_frozen_fs_placed hH hC hQ (.inl htriv))
    fun s => htriv s.fs.files

theorem withStoresDec_okVTP_frozen_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hC : DecCalleesTPFrozenPlaced C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (withStoresDecPlacedSpecVTP C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope)).restrictPre
        (fun p => IdOrDistinctSid uuidTryParse kit st0 Scope p.1)) :=
  withStoresDec_okVTPF_frozen_placed hH hC hQ htriv

end LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget
