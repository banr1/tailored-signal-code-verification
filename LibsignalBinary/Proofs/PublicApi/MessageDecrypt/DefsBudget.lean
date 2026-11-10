/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.Placed.PublicApiCodeSym
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# Budget-Threaded Relocatable `MessageDecrypt` Seam States and Segment Specifications

Budget-threaded (`RustCliAllocBudget M`) allocation envelopes, seam states, and segment
specifications for `session_message_decrypt_signal_with_stores` on block `197` (`lsProg_197 H`),
wrapping the `[LibsignalPlacement]` definitions from `Defs` with `A.atState lim st s` and
`SeamBudget` (`onOom = ⌜False⌝`, `allocFailedIn` dropped from `onPanic`).
-/

@[expose] public section

set_option autoImplicit false

open CryptoGames.LibsignalSession (Crypto IdentityKey SessionState)
open CryptoGames.LibsignalSessionApi (Session SessionRecord StoreAnswers)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsHandleErrorSym lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsmpl)
open CryptoVerification.LibsignalPublicApi (DecryptGhost RecordInScope)
open CryptoVerification.LibsignalPublicApi.Placed (lsProg_197)
open CryptoVerification.LibsignalPublicApi.StoreKit (SessionStoreSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel region_ok)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost UuidParser sessionStateAt uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)

namespace LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget

open Arm64 ProofLib
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
  (DecFsCtxPlaced DecModelRecOk ScopePq decryptRecord
   lsExpectFailedSym lsStringCloneSym recGhostOf sessionModelRel wsEntryPCPlaced)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
   rustAllocEvents rustDeallocEvents rustCliAllocBudgetSpec rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (StringCloneEnv stringCloneBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (SessionStoreBudgetEnv StoreStepEnv retagSessionStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv SaveStepEnv TrustStepEnv retagIdentityStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (RecordDecryptEnv SeamBudget TryDecryptEnvArgs)

/-! ## 1. Pure `SessionGhostValid` & Per-Seam Event Envelopes -/

/-- Pure ghost-to-model shape validity implied by `sessionModelRel` together with `sessionStateAt`
    satisfiability (constraining every ghost `Vec` length in `SegCloneEnv` and `RecordDecryptEnv`
    in terms of `ses`). -/
def SessionGhostValid (G : SessionGhost) (ses : Session (List (BitVec 8))) : Prop :=
  sessionModelRel G ses ∧
  ∃ (A : RustAlloc) (ss : BitVec 64) (m : Memory) (R : SepProp),
    m ⊨ sessionStateAt A ss G ses.state ∗ R

private theorem ex_frame_drop_left {m : Memory} {P Q : SepProp}
    (h : ∃ R, m ⊨ (P ∗ Q) ∗ R) : ∃ R, m ⊨ Q ∗ R :=
  let ⟨R, hR⟩ := h
  ⟨P ∗ R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hR⟩

/-- Extract `SessionGhostValid G ses` from `(Record.recordDecryptPlacedSpec ...).pre`. -/
theorem sessionGhostValid_of_recordPlacedPre [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {x : DecryptGhost} {prevPtr : BitVec 64} {G : SessionGhost}
    {ses : Session (List (BitVec 8))} {s : State} {R : SepProp}
    (hw0 : sessionModelRel G ses)
    (hm : s.mem ⊨
      (CryptoVerification.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec
        C A ctl parse S).pre (recGhostOf x prevPtr G ses.state) s ∗ R) :
    SessionGhostValid G ses := by
  refine ⟨hw0, A, s.sp + 0x138#64, s.mem, ?_⟩
  have h0 : ∃ R', s.mem ⊨
      (CryptoVerification.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec
        C A ctl parse S).pre (recGhostOf x prevPtr G ses.state) s ∗ R' := ⟨R, hm⟩
  dsimp only [CryptoVerification.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec,
    recGhostOf] at h0
  have h1 := ex_frame_drop_left h0
  have h2 := ex_frame_drop_left h1
  have h3 := ex_frame_drop_left h2
  have h4 := ex_frame_drop_left h3
  have h5 := ex_frame_drop_left h4
  have h6 := ex_frame_drop_left h5
  have ⟨R', h7⟩ := ex_frame_drop_left h6
  rw [sepConj_assoc] at h7
  exact ⟨_, h7⟩

/-- `RecordDecryptEnv` on `recGhostOf` is definitionally independent of `prevPtr`. -/
theorem recordDecryptEnv_recGhostOf_eq (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (x : DecryptGhost) (prevPtr₁ prevPtr₂ : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    RecordDecryptEnv tdEnv (recGhostOf x prevPtr₁ G st) =
      RecordDecryptEnv tdEnv (recGhostOf x prevPtr₂ G st) := rfl

/-- `load_session` shim + poll step envelope (`+0x0 → +0x8c`, before the `Box` dealloc at `+0x8c`). -/
def LoadPollStepEnv {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b)
    (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (rem : AddrVal) : List AllocEvent → Prop :=
  SeqEnv (BoxAllocEnv kit.loadBoxSize) (kitEnv.loadPollEnv st0 rem)

/-- Remaining-events envelope from `StoreCall` (`+0x2388`) to function return. -/
def FromStoreCallEnv {A : RustAlloc} (kit : SessionStoreSpec A 0#64)
    (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (rem : AddrVal) (rec' : SessionRecord (List (BitVec 8))) : List AllocEvent → Prop :=
  SeqEnv (StoreStepEnv kit kitEnv st0 rem rec') FreeOnlyEvs

/-- Remaining-events envelope from `Trusted false` (`+0x21b0`) to function return. -/
def FromTrustedFalseEnv (x : DecryptGhost) : List AllocEvent → Prop :=
  SeqEnv (StringCloneEnv x.rem.name) FreeOnlyEvs

/-- Remaining-events envelope from `Trusted true` (`+0x2150`) to function return. -/
def FromTrustedTrueEnv {A : RustAlloc} (kit : SessionStoreSpec A 0#64)
    (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (x : DecryptGhost)
    (rec' : SessionRecord (List (BitVec 8))) (k : IdentityKey) : List AllocEvent → Prop :=
  SeqEnv
    (SaveStepEnv ikit ikitEnv (ikit.trustUpdate ist0 x.rem.val k .receiving (.ok true)) x.rem.val k)
    (fun evs => FreeOnlyEvs evs ∨ FromStoreCallEnv kit kitEnv st0 x.rem.val rec' evs)

/-- Remaining-events envelope from `Trusted t` (`trustedPCPlaced t`) to function return. -/
def FromTrustedEnv {A : RustAlloc} (kit : SessionStoreSpec A 0#64)
    (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (x : DecryptGhost) (t : Bool)
    (rec' : SessionRecord (List (BitVec 8))) (k : IdentityKey) : List AllocEvent → Prop :=
  if t then FromTrustedTrueEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k
  else FromTrustedFalseEnv x

/-- Remaining-events envelope from `KeyReady` (`+0x1fcc`) to function return. -/
def FromKeyReadyEnv {A : RustAlloc} (kit : SessionStoreSpec A 0#64)
    (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (x : DecryptGhost)
    (rec' : SessionRecord (List (BitVec 8))) (k : IdentityKey) : List AllocEvent → Prop :=
  SeqEnv (TrustStepEnv ikit ikitEnv ist0 x.rem.val k .receiving)
    (fun evs => FreeOnlyEvs evs ∨ FromTrustedFalseEnv x evs ∨
      FromTrustedTrueEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k evs)

/-- Remaining-events envelope from `PostSome` (`+0x1f50`) to function return. -/
def FromPostSomeEnv {A : RustAlloc} (C : Crypto) (S : SpqrModel) (parse : UuidParser)
    (kit : SessionStoreSpec A 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8))) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    ∃ pt rec' ses k,
      decryptRecord C S parse x rec = .ok (pt, rec') ∧
      rec'.currentSession = some ses ∧
      ses.state.remoteIdentity = some k ∧
      FromKeyReadyEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k evs

/-- Remaining-events envelope from `RegionSome` (`+0x1a8`) to function return. -/
def FromRegionSomeEnv {A : RustAlloc} (C : Crypto) (S : SpqrModel) (parse : UuidParser)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kit : SessionStoreSpec A 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
    (G : SessionGhost) (ses_st : SessionState (List (BitVec 8))) : List AllocEvent → Prop :=
  SeqEnv (RecordDecryptEnv tdEnv (recGhostOf x 0#64 G ses_st))
    (FromPostSomeEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 x rec)

/-- Remaining-events envelope from `RegionNone` (`+0x1a8`) to function return:
    17-byte `"decryption failed"` allocation followed by teardown frees. -/
def FromRegionNoneEnv : List AllocEvent → Prop :=
  SeqEnv (· = rustAllocEvents 17 1) FreeOnlyEvs

/-- Remaining-events envelope from `LoadPolled` (`+0x8c`) to function return. -/
def FromLoadPolledEnv {A : RustAlloc} (C : Crypto) (S : SpqrModel) (parse : UuidParser)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kit : SessionStoreSpec A 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) : List AllocEvent → Prop :=
  SeqEnv (· = rustDeallocEvents kit.loadBoxSize 8)
    (fun evs =>
      FreeOnlyEvs evs ∨
      SeqEnv (StringCloneEnv x.rem.name) FreeOnlyEvs evs ∨
      FromRegionNoneEnv evs ∨
      ∃ rec ses G,
        kit.ScopeAt Scope st0 x.rem.val rec ∧
        rec.currentSession = some ses ∧
        SessionGhostValid G ses ∧
        FromRegionSomeEnv C S parse tdEnv kit kitEnv st0 ikit ikitEnv ist0 x rec G ses.state evs)

/-- Full end-to-end allocation envelope of `session_message_decrypt_signal_with_stores`. -/
def WithStoresDecEnv {A : RustAlloc} (kit : SessionStoreSpec A 0#64)
    (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (C : Crypto) (S : SpqrModel) (parse : UuidParser)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) : List AllocEvent → Prop :=
  SeqEnv (LoadPollStepEnv kit kitEnv st0 x.rem.val)
    (FromLoadPolledEnv C S parse tdEnv kit kitEnv st0 ikit ikitEnv ist0 Scope x)

theorem fromPostSomeEnv_nonempty {A : RustAlloc} {C : Crypto} {S : SpqrModel} {parse : UuidParser}
    {kit : SessionStoreSpec A 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {x : DecryptGhost} {rec : SessionRecord (List (BitVec 8))} :
    ∃ evs, FromPostSomeEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 x rec evs :=
  ⟨[], Or.inl LibsignalBinary.Heap.FreeOnlyEvs.nil⟩

theorem fromLoadPolledEnv_nonempty {A : RustAlloc} {C : Crypto} {S : SpqrModel} {parse : UuidParser}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {kit : SessionStoreSpec A 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {x : DecryptGhost} :
    ∃ evs, FromLoadPolledEnv C S parse tdEnv kit kitEnv st0 ikit ikitEnv ist0 Scope x evs :=
  ⟨rustDeallocEvents kit.loadBoxSize 8, Or.inl rfl⟩

/-! ## 2. Budget-Threaded Seam States (`lsProg_197`, Block `197`) -/

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
    CryptoVerification.LibsignalPublicApi.MessageDecrypt.LoadPolledStateVPlaced ctl encRecord
      (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit)
      st0 ist0 Scope x ans R s0 s

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
    CryptoVerification.LibsignalPublicApi.MessageDecrypt.RegionSomeStateVPlaced C ctl parse S encRecord
      (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit)
      st0 ist0 Scope x ans R s0 s

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
    CryptoVerification.LibsignalPublicApi.MessageDecrypt.RegionNoneStateVPlaced ctl encRecord
      (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit)
      st0 ist0 Scope x ans R s0 s

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
    CryptoVerification.LibsignalPublicApi.MessageDecrypt.PostSomeStateVPlaced C ctl parse S encRecord
      (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit)
      st0 ist0 Scope x ans R s0 s

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
    CryptoVerification.LibsignalPublicApi.MessageDecrypt.PostNoneStateVPlaced ctl encRecord
      (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit)
      st0 ist0 Scope x ans R s0 s

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
    CryptoVerification.LibsignalPublicApi.MessageDecrypt.KeyReadyStateVPlaced C ctl parse S encRecord
      (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit)
      st0 ist0 Scope x ans R s0 s

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
    CryptoVerification.LibsignalPublicApi.MessageDecrypt.TrustedStateVPlaced C ctl parse S encRecord
      (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit)
      st0 ist0 Scope x ans t R s0 s

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
    CryptoVerification.LibsignalPublicApi.MessageDecrypt.StoreCallStateVPlaced C ctl parse S encRecord
      (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit)
      st0 ist0 Scope x ans R s0 s

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
    CryptoVerification.LibsignalPublicApi.MessageDecrypt.ErrJoinStateVPlaced C ctl parse S encRecord
      (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit)
      st0 ist0 Scope x pt R s0 s

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
    CryptoVerification.LibsignalPublicApi.MessageDecrypt.ResultFinalStateVPlaced C ctl parse S encRecord
      (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit)
      st0 ist0 Scope x R s0 s

/-! ## 3. Budget-Threaded `withStoresDecPlacedSpecV`, Hooks, and Segment Specs -/

/-- Budget-threaded `[LibsignalPlacement]` specification of
    `session_message_decrypt_signal_with_stores` (Block `197`), reusing
    `Defs.withStoresDecPlacedSpecV` via `A.atState` and dropping `allocFailedIn` from `onPanic`. -/
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
      (CryptoVerification.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecV
        C (A.atState lim st_init s) ctl parse S encRecord
        (retagSessionStore kit) (retagIdentityStore ikit) st0 ist0 Scope).pre x s
  post := fun (x, st_init) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse tdEnv Scope x evs⌝ ∗
      (CryptoVerification.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecV
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
  exact CryptoVerification.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecV_pre_addrOk
    (A := A.atState lim st_init s0) (kit := retagSessionStore kit) (ikit := retagIdentityStore ikit) hpre.2

/-- Common budget-threaded segment step shape on `lsProg_197 H` under `[LibsignalPlacement]`. -/
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
  (lsProg_197 H).CodeLoaded s.mem →
  ∃ s', Steps (lsProg_197 H) s s' ∧
    (Out s' ∨
      SubroutineOutcome
        (withStoresDecPlacedSpecV C A lim ctl parse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope)
        (x, st_init) R s0 s')

/-- Budget-threaded external hook contracts on `H : LibsignalHooks` used by Block `197`
    and its `FromRecordCallees` / `FromRecordChainClone` callees. -/
structure PublicApiDecHooksPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  shim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec
  alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)
  dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)
  memcpy : HookSat H "memcpy" sessionMemcpyRegionBudgetSpec
  stringClone : HookSat H lsStringCloneSym (stringCloneBudgetSpec M A lim)
  handleError : H lsHandleErrorSym = some Rust.panicked
  expectFailed : H lsExpectFailedSym = some Rust.panicked

/-- Budget-threaded hypotheses available to every `[LibsignalPlacement]` `MessageDecrypt` segment. -/
structure DecHypsVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (ss : SessionStoreSpec A.repAlloc 0#64) (ssEnv : SessionStoreBudgetEnv ss)
    (id : IdentityStoreSpec A.repAlloc 0#64) (idEnv : IdentityStoreBudgetEnv id)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop where
  hooks : PublicApiDecHooksPlaced A lim H
  kit : SessionOnlyKitPlacedOkSE A lim ss ssEnv Scope encRecord H
  ikit : IdentityStoreKitPlacedOkI A lim id idEnv H
  scopeIn : ∀ r, Scope r → RecordInScope r
  recOk : DecModelRecOk ss C S parse Scope

/-- Placed `<SessionState>::remote_identity_key` (Block `29`, `VmPreserved`) lifted to `lsProg_197 H`. -/
abbrev RemoteIdentityKeyPlacedOk [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_197 H) (lsmpl.base 29)
    (CryptoVerification.LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
      (LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget.remoteIdentityKeyPlacedSpec A))

/-- Placed budget-threaded `drop_glue::<SessionStructure> [local#2]` (Block `139`) lifted to
    `lsProg_197 H`. -/
abbrev DropSessionStructureLocal2PlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_197 H) (lsmpl.base 139)
    (CryptoVerification.LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
      (LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec
        M A lim))

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
  region_ok (lsProg_197 H)
    CryptoVerification.LibsignalTripleRatchet.Record.recEntryPlaced
    CryptoVerification.LibsignalTripleRatchet.Record.recExitPlaced
    ((LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.recordDecryptPlacedSpec
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

end LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
