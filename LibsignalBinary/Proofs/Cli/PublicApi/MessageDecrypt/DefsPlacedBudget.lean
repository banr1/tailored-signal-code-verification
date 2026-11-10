/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# Budget-Threaded Relocatable CLI `MessageDecrypt` Seam States and Specifications

Wraps the relocatable (`[LibsignalPlacement]`) CLI `MessageDecrypt` seam states and segment
specifications on `lsProg_463` with `RustCliAllocBudget M` and `SeamBudget`, eliminating
`allocFailedIn` from `onPanic`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto IdentityKey SessionState)
open CryptoGames.LibsignalSessionApi (Session SessionRecord StoreAnswers)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.CliRatchet.DecPlaced (lsProg_463)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
  (ScopePq decryptRecord recGhostOf sessionModelRel)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt (DecFsCtxPlaced wsEntryPCPlaced)
open CryptoVerification.LibsignalPublicApi.StoreKit (SessionStoreSpec withLsRoCl)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel region_ok)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost UuidParser uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (SessionStoreBudgetEnv retagSessionStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv retagIdentityStore)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (SeamBudget TryDecryptEnvArgs)

/-! ## Envelopes, hook bundles, and `SessionGhostValid` -/

open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (SessionGhostValid
   FromStoreCallEnv FromTrustedEnv FromKeyReadyEnv FromPostSomeEnv FromRegionSomeEnv
   FromRegionNoneEnv FromLoadPolledEnv WithStoresDecEnv)

export LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (PublicApiDecHooksPlaced DecHypsVPlaced)

private theorem ex_frame_drop_left {m : Memory} {P Q : SepProp}
    (h : ∃ R, m ⊨ (P ∗ Q) ∗ R) : ∃ R, m ⊨ Q ∗ R :=
  let ⟨R, hR⟩ := h
  ⟨P ∗ R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hR⟩

/-- Extracts `SessionGhostValid G ses` from `(Record.recordDecryptPlacedSpec ...).pre`. -/
theorem sessionGhostValid_of_recordPlacedPre [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {x : DecryptGhost} {prevPtr : BitVec 64} {G : SessionGhost}
    {ses : Session (List (BitVec 8))} {s : State} {R : SepProp}
    (hw0 : sessionModelRel G ses)
    (hm : s.mem ⊨
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec
        C A ctl parse S).pre (recGhostOf x prevPtr G ses.state) s ∗ R) :
    SessionGhostValid G ses := by
  refine ⟨hw0, A, s.sp + 0x138#64, s.mem, ?_⟩
  have h0 : ∃ R', s.mem ⊨
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec
        C A ctl parse S).pre (recGhostOf x prevPtr G ses.state) s ∗ R' := ⟨R, hm⟩
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec,
    recGhostOf] at h0
  have h1 := ex_frame_drop_left h0
  have h2 := ex_frame_drop_left h1
  have h3 := ex_frame_drop_left h2
  have h4 := ex_frame_drop_left h3
  have h5 := ex_frame_drop_left h4
  have h6 := ex_frame_drop_left h5
  have ⟨_, h7⟩ := ex_frame_drop_left h6
  rw [sepConj_assoc] at h7
  exact ⟨_, h7⟩

/-! ## Budget-threaded seam states -/

/-- Budget-threaded seam state at `+0x8c` after `load_session`. -/
def LoadPolledStateVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (R : SepProp) (s0 s : State) : Prop :=
  ∃ st : M.σ,
    SeamBudget M lim
      (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse tdEnv Scope x)
      st_init st
      (FromLoadPolledEnv C S parse tdEnv kit kitEnv st0 ikit ikitEnv ist0 Scope x) ∧
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.LoadPolledStateVPlaced ctl encRecord
      (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit)
      st0 ist0 Scope x ans R s0 s

/-- Budget-threaded seam state at `recEntryPlaced` (`+0x1a8`) with `currentSession = some _`. -/
def RegionSomeStateVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (R : SepProp) (s0 s : State) : Prop :=
  ∃ st : M.σ,
    (∀ rec ses G,
      ans.loadSession = .ok (some rec) →
      kit.ScopeAt Scope st0 x.rem.val rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      SeamBudget M lim
        (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse tdEnv Scope x)
        st_init st
        (FromRegionSomeEnv C S parse tdEnv kit kitEnv st0 ikit ikitEnv ist0 x rec G ses.state)) ∧
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.RegionSomeStateVPlaced C ctl parse S encRecord
      (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit)
      st0 ist0 Scope x ans R s0 s

/-- Budget-threaded seam state at `recEntryPlaced` (`+0x1a8`) with `currentSession = none`. -/
def RegionNoneStateVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (R : SepProp) (s0 s : State) : Prop :=
  ∃ st : M.σ,
    SeamBudget M lim
      (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse tdEnv Scope x)
      st_init st FromRegionNoneEnv ∧
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.RegionNoneStateVPlaced ctl encRecord
      (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit)
      st0 ist0 Scope x ans R s0 s

/-- Budget-threaded seam state at `recExitPlaced` (`+0x1f50`) exiting `RegionSomeStateVPlaced`. -/
def PostSomeStateVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (R : SepProp) (s0 s : State) : Prop :=
  ∃ st : M.σ,
    (∀ rec, ans.loadSession = .ok (some rec) →
      SeamBudget M lim
        (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse tdEnv Scope x)
        st_init st
        (FromPostSomeEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 x rec)) ∧
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.PostSomeStateVPlaced C ctl parse S encRecord
      (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit)
      st0 ist0 Scope x ans R s0 s

/-- Budget-threaded seam state at `recExitPlaced` (`+0x1f50`) exiting `RegionNoneStateVPlaced`. -/
def PostNoneStateVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (R : SepProp) (s0 s : State) : Prop :=
  ∃ st : M.σ,
    SeamBudget M lim
      (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse tdEnv Scope x)
      st_init st FreeOnlyEvs ∧
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.PostNoneStateVPlaced ctl encRecord
      (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit)
      st0 ist0 Scope x ans R s0 s

/-- Budget-threaded seam state at `+0x1fcc` before `is_trusted_identity`. -/
def KeyReadyStateVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (R : SepProp) (s0 s : State) : Prop :=
  ∃ st : M.σ,
    (∀ rec rec' pt ses k,
      ans.loadSession = .ok (some rec) →
      decryptRecord C S parse x rec = .ok (pt, rec') →
      rec'.currentSession = some ses →
      ses.state.remoteIdentity = some k →
      SeamBudget M lim
        (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse tdEnv Scope x)
        st_init st
        (FromKeyReadyEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k)) ∧
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.KeyReadyStateVPlaced C ctl parse S encRecord
      (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit)
      st0 ist0 Scope x ans R s0 s

/-- Budget-threaded seam state at `trustedPCPlaced t` after `is_trusted_identity`. -/
def TrustedStateVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (t : Bool)
    (R : SepProp) (s0 s : State) : Prop :=
  ∃ st : M.σ,
    (∀ rec rec' pt ses k,
      ans.loadSession = .ok (some rec) →
      decryptRecord C S parse x rec = .ok (pt, rec') →
      rec'.currentSession = some ses →
      ses.state.remoteIdentity = some k →
      SeamBudget M lim
        (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse tdEnv Scope x)
        st_init st
        (FromTrustedEnv kit kitEnv st0 ikit ikitEnv ist0 x t rec' k)) ∧
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.TrustedStateVPlaced C ctl parse S encRecord
      (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit)
      st0 ist0 Scope x ans t R s0 s

/-- Budget-threaded seam state at `+0x2388` before `store_session`. -/
def StoreCallStateVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (R : SepProp) (s0 s : State) : Prop :=
  ∃ st : M.σ,
    (∀ rec pt rec',
      ans.loadSession = .ok (some rec) →
      decryptRecord C S parse x rec = .ok (pt, rec') →
      SeamBudget M lim
        (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse tdEnv Scope x)
        st_init st
        (FromStoreCallEnv kit kitEnv st0 x.rem.val rec')) ∧
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.StoreCallStateVPlaced C ctl parse S encRecord
      (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit)
      st0 ist0 Scope x ans R s0 s

/-- Budget-threaded seam state at `errJoinPCPlaced pt` on error paths. -/
def ErrJoinStateVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (pt : Bool)
    (R : SepProp) (s0 s : State) : Prop :=
  ∃ st : M.σ,
    SeamBudget M lim
      (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse tdEnv Scope x)
      st_init st FreeOnlyEvs ∧
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateVPlaced C ctl parse S encRecord
      (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit)
      st0 ist0 Scope x pt R s0 s

/-- Budget-threaded seam state at `+0x24d4` before writing the final `Result`. -/
def ResultFinalStateVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ)
    (R : SepProp) (s0 s : State) : Prop :=
  ∃ st : M.σ,
    SeamBudget M lim
      (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse tdEnv Scope x)
      st_init st FreeOnlyEvs ∧
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ResultFinalStateVPlaced C ctl parse S encRecord
      (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit)
      st0 ist0 Scope x R s0 s

/-! ## Top-level specification, callees, and segment specifications -/

/-- Budget-threaded relocatable specification of `session_message_decrypt_signal_with_stores`
(Block `463`), wrapping `DefsPlaced.withStoresDecPlacedSpecV` via `A.atState` without
`allocFailedIn` in `onPanic`. -/
def withStoresDecPlacedSpecV [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Spec (DecryptGhost × M.σ) where
  pre := fun (x, st_init) s =>
    ⌜FitsEnv M lim st_init
      (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse tdEnv Scope x)⌝ ∗
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecV
        C (A.atState lim st_init s) ctl parse S encRecord
        (retagSessionStore kit) (retagIdentityStore ikit) st0 ist0 Scope).pre x s
  post := fun (x, st_init) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse tdEnv Scope x evs⌝ ∗
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecV
        C (A.atState lim (M.stepEvents evs st_init) sf) ctl parse S encRecord
        (retagSessionStore kit) (retagIdentityStore ikit) st0 ist0 Scope).post x s0 sf
  onPanic := fun (x, _) s0 sf =>
    ⌜s0.trace <+: sf.trace ∧
      (∃ answers : StoreAnswers (List (BitVec 8)) Unit,
        kit.loadRel st0 x.rem.val answers.loadSession ∧
        s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
        ((x.model C S parse answers).1 = .error .panic ∨ x.recvPanics S answers))⌝ ∗
      anyHeap

theorem withStoresDecPlacedSpecV_pre_addrOk [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {st_init : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (withStoresDecPlacedSpecV C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope).pre (x, st_init) s0 ∗ R) :
    kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val := by
  dsimp only [withStoresDecPlacedSpecV] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecV_pre_addrOk
    (A := A.atState lim st_init s0) (kit := retagSessionStore kit) (ikit := retagIdentityStore ikit) hpre.2

/-- Step relation for a budget-threaded relocatable segment on `lsProg_463 H`. -/
def DecSegVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (R : SepProp) (s0 s : State)
    (Out : State → Prop) : Prop :=
  (lsProg_463 H).CodeLoaded s.mem →
  ∃ s', Steps (lsProg_463 H) s s' ∧
    (Out s' ∨
      SubroutineOutcome
        (withStoresDecPlacedSpecV C A lim ctl parse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope)
        (x, st_init) R s0 s')

/-- Relocatable `<SessionState>::remote_identity_key` (Block `29`) lifted to `lsProg_463 H`. -/
abbrev RemoteIdentityKeyPlacedOk [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_463 H) (lsmpl.base 29)
    (withLsRoCl lsmpl
      (LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget.remoteIdentityKeyPlacedSpec A))

/-- Budget-threaded `drop_glue::<SessionStructure> [local#2]` (Block `442`) lifted to `lsProg_463 H`. -/
abbrev DropSessionStructureLocal2PlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_463 H) (lsmpl.base 442)
    (withLsRoCl lsmpl
      (LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec
        M A lim))

/-- Budget-threaded `SegLoad` specification (`+0x0 → +0x8c`). -/
def SegLoadSpecVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A lim parse S encRecord H kit kitEnv ikit ikitEnv Scope →
  ∀ (x : DecryptGhost) (st_init : M.σ) (R : SepProp) (s0 : State),
    DecFsCtxPlaced kit ikit H s0 s0 →
    s0.pc = wsEntryPCPlaced → s0.status = .Running → s0.spAligned = true →
    (s0.mem ⊨ (withStoresDecPlacedSpecV C A lim ctl parse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope).pre (x, st_init) s0 ∗ R) →
    DecSegVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
      x st_init R s0 s0
      (fun s' => ∃ ans, LoadPolledStateVPlaced C A lim ctl parse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s')

/-- Budget-threaded `SegDispatch` specification (`+0x8c → +0x1a8 / +0x24d4`). -/
def SegDispatchSpecVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A lim parse S encRecord H kit kitEnv ikit ikitEnv Scope →
  ∀ (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    LoadPolledStateVPlaced C A lim ctl parse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s →
    DecSegVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
      x st_init R s0 s
      (fun s' =>
        RegionSomeStateVPlaced C A lim ctl parse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s' ∨
        RegionNoneStateVPlaced C A lim ctl parse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s' ∨
        ResultFinalStateVPlaced C A lim ctl parse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s')

/-- Budget-threaded `SegRegionSome` specification (`+0x1a8 → +0x1f50`). -/
def SegRegionSomeSpecVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A lim parse S encRecord H kit kitEnv ikit ikitEnv Scope →
  ∀ (Q : List (BitVec 8) → Prop),
  region_ok (lsProg_463 H)
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.recEntryPlaced
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.recExitPlaced
    ((LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.recordDecryptPlacedSpec
        C A lim ctl uuidTryParse S tdEnv).withVRegs.restrictPre
      (fun p => Q p.1.st.pqRatchetState)) →
  ScopePq kit st0 Scope Q →
  ∀ (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    RegionSomeStateVPlaced C A lim ctl parse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s →
    DecSegVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
      x st_init R s0 s
      (fun s' => PostSomeStateVPlaced C A lim ctl parse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s')

/-- Budget-threaded `SegRegionNone` specification (`+0x1a8 → +0x1f50`). -/
def SegRegionNoneSpecVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A lim parse S encRecord H kit kitEnv ikit ikitEnv Scope →
  ∀ (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    RegionNoneStateVPlaced C A lim ctl parse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s →
    DecSegVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
      x st_init R s0 s
      (fun s' => PostNoneStateVPlaced C A lim ctl parse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s')

/-- Budget-threaded `SegPostSome` specification (`+0x1f50 → +0x1fcc / +0x22a8`). -/
def SegPostSomeSpecVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A lim parse S encRecord H kit kitEnv ikit ikitEnv Scope →
  RemoteIdentityKeyPlacedOk A.repAlloc H →
  ∀ (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    PostSomeStateVPlaced C A lim ctl parse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s →
    DecSegVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
      x st_init R s0 s
      (fun s' =>
        KeyReadyStateVPlaced C A lim ctl parse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s' ∨
        ErrJoinStateVPlaced C A lim ctl parse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init false R s0 s')

/-- Budget-threaded `SegPostNone` specification (`+0x1f50 → +0x22a8`). -/
def SegPostNoneSpecVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A lim parse S encRecord H kit kitEnv ikit ikitEnv Scope →
  ∀ (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    PostNoneStateVPlaced C A lim ctl parse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s →
    DecSegVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
      x st_init R s0 s
      (fun s' => ErrJoinStateVPlaced C A lim ctl parse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init false R s0 s')

/-- Budget-threaded `SegTrust` specification (`+0x1fcc → +0x2150 / +0x21b0 / +0x2294`). -/
def SegTrustSpecVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A lim parse S encRecord H kit kitEnv ikit ikitEnv Scope →
  ∀ (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    ikit.addrOk x.rem.val →
    DecFsCtxPlaced kit ikit H s0 s →
    KeyReadyStateVPlaced C A lim ctl parse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s →
    DecSegVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
      x st_init R s0 s
      (fun s' =>
        (∃ ans' t, TrustedStateVPlaced C A lim ctl parse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans' t R s0 s') ∨
        ErrJoinStateVPlaced C A lim ctl parse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init true R s0 s')

/-- Budget-threaded `SegUntrusted` specification (`+0x21b0 → +0x2294`). -/
def SegUntrustedSpecVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A lim parse S encRecord H kit kitEnv ikit ikitEnv Scope →
  ∀ (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    TrustedStateVPlaced C A lim ctl parse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans false R s0 s →
    DecSegVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
      x st_init R s0 s
      (fun s' => ErrJoinStateVPlaced C A lim ctl parse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init true R s0 s')

/-- Budget-threaded `SegSave` specification (`+0x2150 → +0x2388 / +0x2294`). -/
def SegSaveSpecVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A lim parse S encRecord H kit kitEnv ikit ikitEnv Scope →
  ∀ (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    ikit.addrOk x.rem.val →
    DecFsCtxPlaced kit ikit H s0 s →
    TrustedStateVPlaced C A lim ctl parse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans true R s0 s →
    DecSegVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
      x st_init R s0 s
      (fun s' =>
        (∃ ans', StoreCallStateVPlaced C A lim ctl parse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans' R s0 s') ∨
        ErrJoinStateVPlaced C A lim ctl parse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init true R s0 s')

/-- Budget-threaded `SegStore` specification (`+0x2388 → +0x24d4 / +0x2294`). -/
def SegStoreSpecVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A lim parse S encRecord H kit kitEnv ikit ikitEnv Scope →
  DropSessionStructureLocal2PlacedOk A lim H →
  ∀ (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    kit.addrOk x.rem.val →
    DecFsCtxPlaced kit ikit H s0 s →
    StoreCallStateVPlaced C A lim ctl parse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s →
    DecSegVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
      x st_init R s0 s
      (fun s' =>
        ResultFinalStateVPlaced C A lim ctl parse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s' ∨
        ErrJoinStateVPlaced C A lim ctl parse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init true R s0 s')

/-- Budget-threaded `SegErrTeardown` specification (`+0x2294 / +0x22a8 → +0x24d4`). -/
def SegErrTeardownSpecVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A lim parse S encRecord H kit kitEnv ikit ikitEnv Scope →
  DropSessionStructureLocal2PlacedOk A lim H →
  ∀ (x : DecryptGhost) (st_init : M.σ) (pt : Bool) (R : SepProp) (s0 s : State),
    ErrJoinStateVPlaced C A lim ctl parse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init pt R s0 s →
    DecSegVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
      x st_init R s0 s
      (fun s' => ResultFinalStateVPlaced C A lim ctl parse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s')

/-- Budget-threaded `SegWrite` specification (`+0x24d4 → +0x2510`). -/
def SegWriteSpecVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A lim parse S encRecord H kit kitEnv ikit ikitEnv Scope →
  ∀ (x : DecryptGhost) (st_init : M.σ) (R : SepProp) (s0 s : State),
    ResultFinalStateVPlaced C A lim ctl parse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s →
    DecSegVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
      x st_init R s0 s (fun _ => False)

end LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlacedBudget
