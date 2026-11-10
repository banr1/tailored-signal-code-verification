/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4None
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsKyberRefusedPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberProofPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsNonePlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsRemovePreKeyProofPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsSaveIdProofPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsStoreSessionProofPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4DefsPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsSaveIdProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsStoreSessionProof
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Stage P4 Outcome Branches, `+0x3cc` Tail, and `none` OPK Arm

Defines the Stage P4 budget envelopes (`StageP4NoneStepEnv`, `StageP4StepEnv`, `StageP4StoreBranchEnv`,
`StageP4RemoveBranchErrEnv`, `StageP4NoneExitEnv`), placed outcome classification
`StageP4RawBranchPlaced` / `StageP4BranchPlaced`, shared `+0x3cc → exit` wrapper, and
`opkId? = none` Stage P4 theorems on Block `518` (`lsProg_518 ext`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsNonePlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees hiding dropSessionStructureLocal2Spec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit hiding
  IdentityStoreKitPlacedOkI KyberPreKeyStoreKitPlacedOk
  PreKeyStoreKitPlacedOk SessionOnlyKitPlacedOkSE
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0 stackAt_sub_eq
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits hiding
  stageP4SaveIdSharedPlaced stageP4SaveIdPrePlaced
  stageP4SaveIdOkPostPlaced stageP4SaveIdErrPostPlaced
  stageP4_saveIdentity_dispatch_vregs_kits_placed
  stageP4MarkKyberSharedPlaced stageP4MarkKyberPrePlaced
  stageP4MarkKyberOkPostPlaced stageP4MarkKyberErrPostPlaced
  KyberPreKeyMarkKitPlacedOk kyberPreKeyMarkKitPlacedOk_of_store
  stageP4_markKyber_none_dispatch_vregs_mark_placed
  stageP4_markKyber_none_dispatch_vregs_kits_placed
  stageP4StoreSessionSharedPlaced stageP4StoreSessionPrePlaced
  stageP4StoreSessionOkPostPlaced stageP4StoreSessionErrPostPlaced
  stageP4_storeSession_dispatch_vregs_kits_placed
  stageP4SharedPlaced stageP4RawPrePlaced stageP4PrePlaced stageP4ExitAtPlaced
  StageP4RawBranchPlaced StageP4BranchPlaced
  stageP4At3ccPrePlaced stageP4_at_3cc_vregs_kits_placed
  stageP4_none_v1_vregs_mark_placed_ok stageP4_none_v1_vregs_kits_placed_ok
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (storeSessionVtablesPlacedAt)
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SignalSession
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
  rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (
  IdentityStoreBudgetEnv SaveStepEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (
  KyberPreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (
  PreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (
  SessionStoreBudgetEnv StoreStepEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentityStoreKitPlacedOkI KyberPreKeyStoreKitPlacedOk SessionOnlyKitPlacedOkSE
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsKyberRefusedPlacedBudget (
  StageP4KyberRefusedMarkErrEnv
  stageP4SharedPlaced stageP4RawPrePlaced stageP4PrePlaced stageP4ExitAtPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberProofPlacedBudget (
  MarkStepEnv StageP4MarkErrEnv
  stageP4MarkKyberSharedPlaced stageP4MarkKyberPrePlaced
  stageP4MarkKyberOkPostPlaced stageP4MarkKyberErrPostPlaced
  KyberPreKeyMarkKitPlacedOk kyberPreKeyMarkKitPlacedOk_of_store
  stageP4_markKyber_none_dispatch_vregs_mark_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsRemovePreKeyProofPlacedBudget (
  RemoveStepEnv StageP4RemoveErrEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsSaveIdProofPlacedBudget (
  stageP4SaveIdSharedPlaced stageP4SaveIdPrePlaced
  stageP4SaveIdOkPostPlaced stageP4SaveIdErrPostPlaced
  stageP4_saveIdentity_dispatch_vregs_kits_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsStoreSessionProofPlacedBudget (
  SessionStoreOnlyKitPlacedOk StageP4StoreExitEnv sessionStoreOnlyKitPlacedOk_of_se
  stageP4StoreSessionSharedPlaced stageP4StoreSessionPrePlaced
  stageP4StoreSessionOkPostPlaced stageP4StoreSessionErrPostPlaced
  stageP4_storeSession_dispatch_vregs_store_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4DefsPlacedBudget (
  StageP4MatchedSaveErrEnv
)

/-! ## Allocation envelopes and five-way outcome classification -/

/-- Entry budget envelope for Stage P4 when `opkId? = none`:
`SaveStepEnv` (`P4.1` `save_identity`) followed by `MarkStepEnv` (`P4.2` `mark_kyber_pre_key_used`)
followed by `StoreStepEnv` (`P4.4` `store_session`; `P4.3` `remove_pre_key` is skipped, and all
error/exit teardown tails are `FreeOnlyEvs`). -/
abbrev StageP4NoneStepEnv {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (kpkKit : KyberPreKeyStoreSpec A b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState) (kst0 : kpkKit.KpkState)
    (rem : AddrVal) (remoteIk : IdentityKey)
    (kyberPreKeyId signedPreKeyId : BitVec 32) (baseKey : PublicKey)
    (rec : SessionRecord (List (BitVec 8))) : List AllocEvent → Prop :=
  SeqEnv (SaveStepEnv ikit ikitEnv ist0 rem remoteIk)
    (SeqEnv (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey)
      (StoreStepEnv kit kitEnv sst0 rem rec))

/-- Entry budget envelope for Stage P4 parameterized by `opkId? : Option (BitVec 32)`:
reduces definitionally (`rfl`) to `StageP4NoneStepEnv` when `opkId? = none`, and inserts
`RemoveStepEnv` (`P4.3` `remove_pre_key`) between `MarkStepEnv` and `StoreStepEnv` when
`opkId? = some opkId`. -/
def StageP4StepEnv {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A b) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (opkId? : Option (BitVec 32))
    (rem : AddrVal) (remoteIk : IdentityKey)
    (kyberPreKeyId signedPreKeyId : BitVec 32) (baseKey : PublicKey)
    (rec : SessionRecord (List (BitVec 8))) : List AllocEvent → Prop :=
  match opkId? with
  | none =>
      StageP4NoneStepEnv kit kitEnv ikit ikitEnv kpkKit kpkKitEnv
        sst0 ist0 kst0 rem remoteIk kyberPreKeyId signedPreKeyId baseKey rec
  | some opkId =>
      SeqEnv (SaveStepEnv ikit ikitEnv ist0 rem remoteIk)
        (SeqEnv (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey)
          (SeqEnv (RemoveStepEnv pkKit pkKitEnv pst0 opkId)
            (StoreStepEnv kit kitEnv sst0 rem rec)))

/-- Allocation envelope on the `ok` and `storeErr` exits of Stage P4 (`P4.1` `save_identity` →
`P4.2` `mark_kyber_pre_key_used` → optional `P4.3` `remove_pre_key` → `P4.4`
`StageP4StoreExitEnv`). -/
def StageP4StoreBranchEnv {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A b) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (opkId? : Option (BitVec 32))
    (rem : AddrVal) (remoteIk : IdentityKey)
    (kyberPreKeyId signedPreKeyId : BitVec 32) (baseKey : PublicKey)
    (rec : SessionRecord (List (BitVec 8))) : List AllocEvent → Prop :=
  match opkId? with
  | none =>
      SeqEnv (SaveStepEnv ikit ikitEnv ist0 rem remoteIk)
        (SeqEnv (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey)
          (StageP4StoreExitEnv kit kitEnv sst0 rem rec))
  | some opkId =>
      SeqEnv (SaveStepEnv ikit ikitEnv ist0 rem remoteIk)
        (SeqEnv (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey)
          (SeqEnv (RemoveStepEnv pkKit pkKitEnv pst0 opkId)
            (StageP4StoreExitEnv kit kitEnv sst0 rem rec)))

/-- Allocation envelope on the `remove_pre_key = Err(e)` exit of Stage P4 (`opkId? = some opkId`):
`SaveStepEnv` → `MarkStepEnv` → `StageP4RemoveErrEnv`. -/
def StageP4RemoveBranchErrEnv {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A b) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (ist0 : ikit.IdState) (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (rem : AddrVal) (remoteIk : IdentityKey)
    (opkId kyberPreKeyId signedPreKeyId : BitVec 32) (baseKey : PublicKey) :
    List AllocEvent → Prop :=
  SeqEnv (SaveStepEnv ikit ikitEnv ist0 rem remoteIk)
    (SeqEnv (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey)
      (StageP4RemoveErrEnv pkKit pkKitEnv pst0 opkId))

/-- Combined exit allocation envelope of Stage P4 when `opkId? = none`, covering `ok`/`storeErr`,
`markErr`, and `saveErr`. -/
def StageP4NoneExitEnv {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (kpkKit : KyberPreKeyStoreSpec A b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState) (kst0 : kpkKit.KpkState)
    (rem : AddrVal) (remoteIk : IdentityKey)
    (kyberPreKeyId signedPreKeyId : BitVec 32) (baseKey : PublicKey)
    (rec : SessionRecord (List (BitVec 8))) (evs : List AllocEvent) : Prop :=
  SeqEnv (SaveStepEnv ikit ikitEnv ist0 rem remoteIk)
    (SeqEnv (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey)
      (StageP4StoreExitEnv kit kitEnv sst0 rem rec)) evs ∨
  StageP4KyberRefusedMarkErrEnv ikit ikitEnv kpkKit kpkKitEnv ist0 kst0
    rem remoteIk kyberPreKeyId signedPreKeyId baseKey evs ∨
  StageP4MatchedSaveErrEnv ikit ikitEnv ist0 rem remoteIk evs

theorem fitsEnv_noneStep_of_noneExit {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {A : RustAlloc} {b : BitVec 64}
    {kit : SessionStoreSpec A b} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A b} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {kpkKit : KyberPreKeyStoreSpec A b} {kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit}
    {sst0 : kit.StoreState} {ist0 : ikit.IdState} {kst0 : kpkKit.KpkState}
    {rem : AddrVal} {remoteIk : IdentityKey}
    {kyberPreKeyId signedPreKeyId : BitVec 32} {baseKey : PublicKey}
    {rec : SessionRecord (List (BitVec 8))}
    (h : FitsEnv M lim st
      (StageP4NoneExitEnv kit kitEnv ikit ikitEnv kpkKit kpkKitEnv
        sst0 ist0 kst0 rem remoteIk kyberPreKeyId signedPreKeyId baseKey rec)) :
    FitsEnv M lim st
      (StageP4NoneStepEnv kit kitEnv ikit ikitEnv kpkKit kpkKitEnv
        sst0 ist0 kst0 rem remoteIk kyberPreKeyId signedPreKeyId baseKey rec) :=
  h.mono fun
    | _, Or.inl hsave => Or.inl (Or.inl hsave)
    | _, Or.inr ⟨_, _, rfl, hsave, Or.inl hmark⟩ =>
        Or.inl (SeqEnv.append hsave (Or.inl hmark))
    | _, Or.inr ⟨_, _, rfl, hsave, Or.inr ⟨_, _, rfl, hmark, hstore⟩⟩ =>
        Or.inl (SeqEnv.append hsave (SeqEnv.append hmark (Or.inl hstore)))

/-- Budget-threaded placed five-way outcome classification of Stage P4
(`(blkPl_518).base + 0x34dc → s0.readReg64 .x30`) parameterized by an `opkSlot` assertion at
`coroPtr + 0x298..0x2a0`. -/
inductive StageP4RawBranchPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot : SepProp) (opkId? : Option (BitVec 32))
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (ss : Session (List (BitVec 8))) (sf : State) (Pf : SepProp) : Prop where
  | ok (c : IdentityChange) (evs : List AllocEvent)
      (hevs : StageP4StoreBranchEnv kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
        sst0 ist0 pst0 kst0 opkId? peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey
        ⟨some ss⟩ evs)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hmark : kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
      (hrem : match opkId? with
              | none => True
              | some opkId => pkKit.removeRel pst0 opkId (.ok ()))
      (hstore : kit.storeRel sst0 peer.val ⟨some ss⟩ (.ok ()))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) ++
        (match opkId? with | none => [] | some opkId => pkKit.removeEvs opkId (.ok ())) ++
        kit.storeEvs encRecord peer.val ⟨some ss⟩ (.ok ()))
      (hpost : Pf ⊢ stageP4ExitAtPlaced A lim (M.stepEvents evs st0) kit ikit pkKit kpkKit
        s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
        preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkSlot
        (vecResultAt A.repAlloc outPtr (.ok pt))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.ok ()))
        (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
        (match opkId? with | none => pst0 | some opkId => pkKit.removeUpdate pst0 opkId (.ok ()))
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())))
  | saveErr (evs : List AllocEvent)
      (hevs : StageP4MatchedSaveErrEnv ikit ikitEnv ist0 peer.val remoteIk evs)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.error ()))
      (htr : sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()))
      (hpost : Pf ⊢ stageP4ExitAtPlaced A lim (M.stepEvents evs st0) kit ikit pkKit kpkKit
        s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
        preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkSlot
        (savePollPlacedOutAt outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.error ())) pst0 kst0)
  | markErr (c : IdentityChange) (e : kpkKit.MarkErr) (evs : List AllocEvent)
      (hevs : StageP4KyberRefusedMarkErrEnv ikit ikitEnv kpkKit kpkKitEnv ist0 kst0
        peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey evs)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hmark : kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e))
      (hpost : Pf ⊢ stageP4ExitAtPlaced A lim (M.stepEvents evs st0) kit ikit pkKit kpkKit
        s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
        preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkSlot
        (speErrAt kpkKit.markErr outPtr e)
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.error e)))
  | removeErr (opkId : BitVec 32) (c : IdentityChange) (e : pkKit.RemoveErr)
      (evs : List AllocEvent)
      (hopk : opkId? = some opkId)
      (hevs : StageP4RemoveBranchErrEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
        ist0 pst0 kst0 peer.val remoteIk opkId kyberPreKeyId signedPreKeyId baseKey evs)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hmark : kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
      (hrem : pkKit.removeRel pst0 opkId (.error e))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) ++
        pkKit.removeEvs opkId (.error e))
      (hpost : Pf ⊢ stageP4ExitAtPlaced A lim (M.stepEvents evs st0) kit ikit pkKit kpkKit
        s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
        preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkSlot
        (speErrAt pkKit.removeErr outPtr e)
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
        (pkKit.removeUpdate pst0 opkId (.error e))
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())))
  | storeErr (c : IdentityChange) (evs : List AllocEvent)
      (hevs : StageP4StoreBranchEnv kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
        sst0 ist0 pst0 kst0 opkId? peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey
        ⟨some ss⟩ evs)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hmark : kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
      (hrem : match opkId? with
              | none => True
              | some opkId => pkKit.removeRel pst0 opkId (.ok ()))
      (hstore : kit.storeRel sst0 peer.val ⟨some ss⟩ (.error ()))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) ++
        (match opkId? with | none => [] | some opkId => pkKit.removeEvs opkId (.ok ())) ++
        kit.storeEvs encRecord peer.val ⟨some ss⟩ (.error ()))
      (hpost : Pf ⊢ stageP4ExitAtPlaced A lim (M.stepEvents evs st0) kit ikit pkKit kpkKit
        s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
        preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkSlot
        (storePollPlacedOutAt outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.error ()))
        (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
        (match opkId? with | none => pst0 | some opkId => pkKit.removeUpdate pst0 opkId (.ok ()))
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())))

abbrev StageP4BranchPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (ss : Session (List (BitVec 8))) (sf : State) (Pf : SepProp) : Prop :=
  StageP4RawBranchPlaced A lim st0 kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
    encRecord s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
    (coroOpkIdAtP4 coroPtr opkId?) opkId? kyberPreKeyId signedPreKeyId pt peer remoteIk
    baseKey sst0 ist0 pst0 kst0 ss sf Pf

theorem StageP4RawBranchPlaced.mono_opkSlot [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ} {b : BitVec 64}
    {kit : SessionStoreSpec A.repAlloc b} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc b} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {pkKit : PreKeyStoreSpec A.repAlloc b} {pkKitEnv : PreKeyStoreBudgetEnv pkKit}
    {kpkKit : KyberPreKeyStoreSpec A.repAlloc b} {kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {s0 s : State}
    {coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64}
    {opkSlot1 opkSlot2 : SepProp} {opkId? : Option (BitVec 32)}
    {kyberPreKeyId signedPreKeyId : BitVec 32}
    {pt : List (BitVec 8)} {peer : AddrGhost} {remoteIk : IdentityKey} {baseKey : PublicKey}
    {sst0 : kit.StoreState} {ist0 : ikit.IdState}
    {pst0 : pkKit.PkState} {kst0 : kpkKit.KpkState}
    {ss : Session (List (BitVec 8))} {sf : State} {Pf : SepProp}
    (hopk : opkSlot1 ⊢ opkSlot2)
    (h : StageP4RawBranchPlaced A lim st0 kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
      encRecord s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
      preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkSlot1 opkId?
      kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sst0 ist0 pst0 kst0 ss sf Pf) :
    StageP4RawBranchPlaced A lim st0 kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
      encRecord s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
      preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkSlot2 opkId?
      kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sst0 ist0 pst0 kst0 ss sf Pf := by
  have hexit : ∀ stf outSlot sstf istf pstf kstf,
      stageP4ExitAtPlaced A lim stf kit ikit pkKit kpkKit s0 s sf coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
        ptCap ptPtr v_3d0 opkSlot1 outSlot kyberPreKeyId signedPreKeyId pt peer remoteIk
        baseKey sstf istf pstf kstf ⊢
      stageP4ExitAtPlaced A lim stf kit ikit pkKit kpkKit s0 s sf coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
        ptCap ptPtr v_3d0 opkSlot2 outSlot kyberPreKeyId signedPreKeyId pt peer remoteIk
        baseKey sstf istf pstf kstf :=
    fun _ _ _ _ _ _ => by
      unfold stageP4ExitAtPlaced
      exact sepConj_mono_right (sepConj_mono_left hopk)
  rcases h with ⟨c, evs, hevs, hs, hm, hr, hst, htr, hp⟩
    | ⟨evs, hevs, hs, htr, hp⟩
    | ⟨c, e, evs, hevs, hs, hm, htr, hp⟩
    | ⟨opkId, c, e, evs, hopk_eq, hevs, hs, hm, hr, htr, hp⟩
    | ⟨c, evs, hevs, hs, hm, hr, hst, htr, hp⟩
  · exact .ok c evs hevs hs hm hr hst htr (Entails.trans hp (hexit _ _ _ _ _ _))
  · exact .saveErr evs hevs hs htr (Entails.trans hp (hexit _ _ _ _ _ _))
  · exact .markErr c e evs hevs hs hm htr (Entails.trans hp (hexit _ _ _ _ _ _))
  · exact .removeErr opkId c e evs hopk_eq hevs hs hm hr htr (Entails.trans hp (hexit _ _ _ _ _ _))
  · exact .storeErr c evs hevs hs hm hr hst htr (Entails.trans hp (hexit _ _ _ _ _ _))

/-! ## Budget-threaded `+0x3cc → exit` wrapper -/

/-- Spatial assertion on the full 4-kit Stage P4 frame at `(blkPl_518).base + 0x3cc`
(entering Substage P4.4 `SessionStore::store_session`), separating the stack-frame anchor `s`
from the current pool state `s3`. -/
def stageP4At3ccPrePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st3 : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (s0 s s3 : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot : SepProp)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist1 : ikit.IdState)
    (pst1 : pkKit.PkState) (kst1 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8))) : SepProp :=
  stageP4SharedPlaced A lim st3 kit ikit pkKit kpkKit s0 s s3 coroPtr msgPtr remoteAddrPtr
    remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
    ptCap ptPtr v_3d0 kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ∗
  opkSlot ∗
  memRegion (coroPtr + 0x2ac#64) 20 ∗
  sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G ss.state ∗
  ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
  ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
  ((coroPtr + 0x290#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  memRegion outPtr 48 ∗
  ikit.identityAt idStorePtr ist1 ∗
  kpkKit.storeAt kyberStorePtr kst1 ∗
  pkKit.storeAt preKeyStorePtr pst1 ∗
  kit.storeAt sessionStorePtr sst0

set_option maxHeartbeats 800000 in
/-- Budget-threaded `[LibsignalPlacement]` `+0x3cc → exit` `store_session` wrapper on the 4-kit
`stageP4At3ccPrePlaced` frame under `SessionStoreOnlyKitPlacedOk` and `StoreStepEnv`. -/
theorem stageP4_at_3cc_vregs_store_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hkit : SessionStoreOnlyKitPlacedOk A lim kit kitEnv encRecord ext)
    (hsVt : SessionOnlyVtablesPlacedOk kit)
    {Qfs : Prop} {Qp : State → SepProp → Prop}
    (st3 : M.σ) (s0 s s3 : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot : SepProp)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist1 : ikit.IdState)
    (pst1 : pkKit.PkState) (kst1 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (Q : State → SepProp → Prop)
    (hprev_nz : prevStatesPtr ≠ 0#64)
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : kit.RecOk ⟨some ss⟩)
    (haddr_ss : kit.addrOk peer.val)
    (hfits : FitsEnv M lim st3 (StoreStepEnv kit kitEnv sst0 peer.val ⟨some ss⟩))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs3 : FsAt kit.envOk Qfs (lsProg_518 ext) s3)
    (hcro3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem)
    (hpc3 : s3.pc = (blkPl_518).base + 0x3cc#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19_3 : s3.readReg64 .x19 = coroPtr)
    (hx24_3 : s3.readReg64 .x24 = s.sp + 0x370#64)
    (hx25_3 : s3.readReg64 .x25 = s.sp + 0x210#64)
    (hx26_3 : s3.readReg64 .x26 = outPtr)
    (hx27_3 : s3.readReg64 .x27 = ctxPtr)
    (hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0)
    (hOk : ∀ (evs : List AllocEvent) (sf : State) (Pf : SepProp),
      StageP4StoreExitEnv kit kitEnv sst0 peer.val ⟨some ss⟩ evs →
      Steps (lsProg_518 ext) s3 sf →
      kit.storeRel sst0 peer.val ⟨some ss⟩ (.ok ()) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s3.trace ++ kit.storeEvs encRecord peer.val ⟨some ss⟩ (.ok ()) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢ stageP4ExitAtPlaced A lim (M.stepEvents evs st3) kit ikit pkKit kpkKit s0 s sf
        coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr
        kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkSlot
        (vecResultAt A.repAlloc outPtr (.ok pt))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.ok ())) ist1 pst1 kst1) →
      Q sf Pf)
    (hErr : ∀ (evs : List AllocEvent) (sf : State) (Pf : SepProp),
      StageP4StoreExitEnv kit kitEnv sst0 peer.val ⟨some ss⟩ evs →
      Steps (lsProg_518 ext) s3 sf →
      kit.storeRel sst0 peer.val ⟨some ss⟩ (.error ()) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s3.trace ++ kit.storeEvs encRecord peer.val ⟨some ss⟩ (.error ()) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢ stageP4ExitAtPlaced A lim (M.stepEvents evs st3) kit ikit pkKit kpkKit s0 s sf
        coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr
        kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkSlot
        (storePollPlacedOutAt outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.error ())) ist1 pst1 kst1) →
      Q sf Pf) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s3
      (stageP4At3ccPrePlaced A lim st3 kit ikit pkKit kpkKit s0 s s3 coroPtr msgPtr outPtr
        remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
        prevStatesPtr ptCap ptPtr v_3d0 opkSlot kyberPreKeyId signedPreKeyId b_2c0 pt peer
        remoteIk baseKey sst0 ist1 pst1 kst1 G ss)
      Q Qp := by
  have hsp_ss : storeSessionCallStack kit ≤ 2 ^ 64 :=
    Nat.le_trans (storeSessionStack_le_stageP4 kit ikit pkKit kpkKit) hsp_ub
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3]; exact hsp_align
  refine SepWPp.congr_post_drop_left ?_
  refine SepWPp.focus_pre
    (T := stageP4StoreSessionPrePlaced A lim st3 kit s0 s3 coroPtr outPtr remoteAddrPtr
      sessionStorePtr prevStatesPtr ptCap ptPtr b_2c0 pt peer sst0 G ss)
    (by
      unfold stageP4At3ccPrePlaced stageP4SharedPlaced stageP4StoreSessionPrePlaced
        stageP4StoreSessionSharedPlaced
      rw [hsp3, stack_stageP4_to_storeSession kit ikit pkKit kpkKit s.sp hsp_ub]
      sep_focus)
    ?_
  refine stageP4_storeSession_dispatch_vregs_store_placed ext encRecord kit kitEnv
    hdealloc hDropSS3 hkit hsVt st3 s0 s3 coroPtr ctxPtr outPtr remoteAddrPtr sessionStorePtr
    prevStatesPtr ptCap ptPtr b_2c0 pt peer sst0 G ss _ _
    hprev_nz hExtra hrec_ok haddr_ss hfits hpt_le hcap_lt hptr_nz hsp_ss
    hfs3 hcro3 hpc3 hrun3 hsp3_align
    hx19_3 (hsp3.symm ▸ hx24_3) (hsp3.symm ▸ hx25_3) hx26_3 hx27_3 hvregs3
    (fun evs sf Pf hevs4 hst4 hrel4 _ _ hspf htr4 hcsf hvregsf hcrof hPf => ?_)
    (fun evs sf Pf hevs4 hst4 hrel4 _ _ hspf htr4 hcsf hvregsf hcrof hPf => ?_)
  · refine ⟨storeSessionVtablesPlacedAt kit,
      stageP4ExitAtPlaced A lim (M.stepEvents evs st3) kit ikit pkKit kpkKit s0 s sf
        coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr
        kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkSlot
        (vecResultAt A.repAlloc outPtr (.ok pt))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.ok ())) ist1 pst1 kst1,
      ?_, hOk evs sf _ hevs4 hst4 hrel4 (by rw [hspf, hsp3]) htr4 hcsf hvregsf hcrof
        (Entails.refl _)⟩
    refine Entails.trans hPf (Entails.of_eq ?_)
    unfold stageP4StoreSessionOkPostPlaced stageP4StoreSessionSharedPlaced
      stageP4ExitAtPlaced stageP4SharedPlaced
    rw [hsp3, stack_stageP4_to_storeSession kit ikit pkKit kpkKit s.sp hsp_ub]
    sep_ac_rfl
  · refine ⟨storeSessionVtablesPlacedAt kit,
      stageP4ExitAtPlaced A lim (M.stepEvents evs st3) kit ikit pkKit kpkKit s0 s sf
        coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr
        kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkSlot
        (storePollPlacedOutAt outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.error ())) ist1 pst1 kst1,
      ?_, hErr evs sf _ hevs4 hst4 hrel4 (by rw [hspf, hsp3]) htr4 hcsf hvregsf hcrof
        (Entails.refl _)⟩
    refine Entails.trans hPf (Entails.of_eq ?_)
    unfold stageP4StoreSessionErrPostPlaced stageP4StoreSessionSharedPlaced
      stageP4ExitAtPlaced stageP4SharedPlaced
    rw [hsp3, stack_stageP4_to_storeSession kit ikit pkKit kpkKit s.sp hsp_ub]
    sep_ac_rfl

theorem stageP4_at_3cc_vregs_kits_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hkit : SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encRecord ext)
    (hsVt : SessionOnlyVtablesPlacedOk kit)
    {Qfs : Prop} {Qp : State → SepProp → Prop}
    (st3 : M.σ) (s0 s s3 : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot : SepProp)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist1 : ikit.IdState)
    (pst1 : pkKit.PkState) (kst1 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (Q : State → SepProp → Prop)
    (hprev_nz : prevStatesPtr ≠ 0#64)
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : kit.RecOk ⟨some ss⟩)
    (haddr_ss : kit.addrOk peer.val)
    (hfits : FitsEnv M lim st3 (StoreStepEnv kit kitEnv sst0 peer.val ⟨some ss⟩))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs3 : FsAt kit.envOk Qfs (lsProg_518 ext) s3)
    (hcro3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem)
    (hpc3 : s3.pc = (blkPl_518).base + 0x3cc#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19_3 : s3.readReg64 .x19 = coroPtr)
    (hx24_3 : s3.readReg64 .x24 = s.sp + 0x370#64)
    (hx25_3 : s3.readReg64 .x25 = s.sp + 0x210#64)
    (hx26_3 : s3.readReg64 .x26 = outPtr)
    (hx27_3 : s3.readReg64 .x27 = ctxPtr)
    (hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0)
    (hOk : ∀ (evs : List AllocEvent) (sf : State) (Pf : SepProp),
      StageP4StoreExitEnv kit kitEnv sst0 peer.val ⟨some ss⟩ evs →
      Steps (lsProg_518 ext) s3 sf →
      kit.storeRel sst0 peer.val ⟨some ss⟩ (.ok ()) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s3.trace ++ kit.storeEvs encRecord peer.val ⟨some ss⟩ (.ok ()) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢ stageP4ExitAtPlaced A lim (M.stepEvents evs st3) kit ikit pkKit kpkKit s0 s sf
        coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr
        kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkSlot
        (vecResultAt A.repAlloc outPtr (.ok pt))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.ok ())) ist1 pst1 kst1) →
      Q sf Pf)
    (hErr : ∀ (evs : List AllocEvent) (sf : State) (Pf : SepProp),
      StageP4StoreExitEnv kit kitEnv sst0 peer.val ⟨some ss⟩ evs →
      Steps (lsProg_518 ext) s3 sf →
      kit.storeRel sst0 peer.val ⟨some ss⟩ (.error ()) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s3.trace ++ kit.storeEvs encRecord peer.val ⟨some ss⟩ (.error ()) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢ stageP4ExitAtPlaced A lim (M.stepEvents evs st3) kit ikit pkKit kpkKit s0 s sf
        coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr
        kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkSlot
        (storePollPlacedOutAt outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.error ())) ist1 pst1 kst1) →
      Q sf Pf) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s3
      (stageP4At3ccPrePlaced A lim st3 kit ikit pkKit kpkKit s0 s s3 coroPtr msgPtr outPtr
        remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
        prevStatesPtr ptCap ptPtr v_3d0 opkSlot kyberPreKeyId signedPreKeyId b_2c0 pt peer
        remoteIk baseKey sst0 ist1 pst1 kst1 G ss)
      Q Qp :=
  stageP4_at_3cc_vregs_store_placed ext encRecord kit kitEnv ikit pkKit kpkKit
    hdealloc hDropSS3 (sessionStoreOnlyKitPlacedOk_of_se hkit) hsVt st3 s0 s s3
    coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkSlot
    kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
    sst0 ist1 pst1 kst1 G ss Q
    hprev_nz hExtra hrec_ok haddr_ss hfits hpt_le hcap_lt hptr_nz hsp_ub
    hfs3 hcro3 hpc3 hrun3 hsp3 hsp_align
    hx19_3 hx24_3 hx25_3 hx26_3 hx27_3 hvregs3 hOk hErr

/-! ## Budget-threaded Stage P4 for `opkId? = none` -/

set_option maxHeartbeats 1200000 in
/-- Budget-threaded `[LibsignalPlacement]` Stage P4 (`opkId? = none`,
`(blkPl_518).base + 0x34dc → s0.readReg64 .x30`) under `SessionStoreOnlyKitPlacedOk` and
`KyberPreKeyMarkKitPlacedOk`. -/
theorem stageP4_none_v1_vregs_store_mark_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hkit : SessionStoreOnlyKitPlacedOk A lim kit kitEnv encRecord ext)
    (hsVt : SessionOnlyVtablesPlacedOk kit)
    (hikit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv ext)
    (hiVt : IdentityVtablesPlacedOk ikit)
    (hkpkKit : KyberPreKeyMarkKitPlacedOk A lim kpkKit kpkKitEnv ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qp : State → SepProp → Prop}
    (st0 : M.σ) (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdDummy kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hprev_nz : prevStatesPtr ≠ 0#64)
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : kit.RecOk ⟨some ss⟩)
    (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val)
    (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hfits : FitsEnv M lim st0
      (StageP4NoneStepEnv kit kitEnv ikit ikitEnv kpkKit kpkKitEnv
        sst0 ist0 kst0 peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey ⟨some ss⟩))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4RawPrePlaced A lim st0 kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
        remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
        prevStatesPtr ptCap ptPtr v_3d0
        (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
        kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (lsProg_518 ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        StageP4RawBranchPlaced A lim st0 kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
          encRecord s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr
          idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
          none kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sst0 ist0 pst0 kst0 ss sf Pf)
      Qp := by
  have hsp_save : saveIdCallStack ikit ≤ 2 ^ 64 :=
    Nat.le_trans (saveIdStack_le_stageP4 kit ikit pkKit kpkKit) hsp_ub
  have hsp_mark : markKyberCallStack kpkKit ≤ 2 ^ 64 :=
    Nat.le_trans (markKyberStack_le_stageP4 kit ikit pkKit kpkKit) hsp_ub
  refine SepWPp.congr_post_drop_left ?_
  refine SepWPp.focus_pre
    (T := stageP4SaveIdPrePlaced A lim st0 ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr
      remoteIkPtr idStorePtr kyberStorePtr kpkKit.kpk_vt prevStatesPtr ptCap ptPtr v_3d0
      0#32 opkIdDummy kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk ist0 G ss.state)
    (by
      unfold stageP4RawPrePlaced stageP4SharedPlaced stageP4SaveIdPrePlaced
        stageP4SaveIdSharedPlaced
      rw [stack_stageP4_to_saveId kit ikit pkKit kpkKit s.sp hsp_ub]
      sep_focus)
    ?_
  refine stageP4_saveIdentity_dispatch_vregs_kits_placed ext ikit ikitEnv hdealloc hDropSS3
    hikit hiVt st0 s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
    kyberStorePtr kpkKit.kpk_vt (0#64 + kpkKit.markShimOff) prevStatesPtr ptCap ptPtr v_3d0
    0#32 opkIdDummy kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk ist0 G ss.state _ _
    haddr_id hfits.seq_left (by decide) hpt_le hsp_save
    (fun hro' hP' => hkVt.markSlot hro' hP')
    (hfs.mono (fun _ h => h.2.1) id)
    hcro hpc hrun hsp_align hx19 hx24 hx25 hx26 hx27 hx28 hvregs
    (fun c evs1 s1 P1 hevs1 hst1 hrel1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx2_1 hx3_1
      hx19_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hlr1 hcro1 hvregs1 hP1 => ?_)
    (fun evs1 sf Pf hevs1 hstf hrelf _ _ hspf htrf hcsf hvregsf hcrof hPf => ?_)
  · -- P4.1 Ok(c) → P4.2 mark_kyber_pre_key_used (none)
    let st1 := M.stepEvents evs1 st0
    have hfits_after1 := hfits.seq_right hevs1
    refine SepWPp.drop_swap_focus_pre
      (Drop := saveIdVtablesAt ikit ∗
        ((kpkKit.kpk_vt + 0x28#64) ↦₆₄ᵣ (0#64 + kpkKit.markShimOff)))
      (T := stageP4MarkKyberPrePlaced A lim st1 kpkKit s0 s1 coroPtr msgPtr outPtr kyberStorePtr
        prevStatesPtr ptCap ptPtr b_2c0 pt baseKey kst0 G ss.state ∗
        ((coroPtr + 0x2ac#64) ↦₃₂ 0#32))
      hP1
      ((stack_stageP4_to_saveId kit ikit pkKit kpkKit s.sp hsp_ub).symm.trans
        (stack_stageP4_to_markKyber kit ikit pkKit kpkKit s.sp hsp_ub))
      (by unfold stageP4SaveIdOkPostPlaced stageP4SaveIdSharedPlaced; sep_focus)
      (by unfold stageP4MarkKyberPrePlaced stageP4MarkKyberSharedPlaced; rw [hsp1]; sep_focus)
      ?_
    rw [sepConj_assoc]
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    have hfs1 := hfs.of_steps hst1 htr1 (fun hQ => hQ.2.1.2 peer.val remoteIk (.ok c))
    refine stageP4_markKyber_none_dispatch_vregs_mark_placed ext kpkKit kpkKitEnv
      hdealloc hDropSS3 hkpkKit hkVt
      st1 s0 s1 coroPtr ctxPtr msgPtr outPtr kyberStorePtr prevStatesPtr ptCap ptPtr
      kyberPreKeyId signedPreKeyId b_2c0 pt baseKey kst0 G ss.state _ _
      hmark_ok hfits_after1.seq_left hpt_le hsp_mark
      (hfs1.mono (fun _ h => h.2.2.2) id)
      hcro1 hpc1 hrun1 hsp1_align
      hx0_1 hx1_1 hx2_1 hx3_1 hx19_1 (hsp1.symm ▸ hx24_1) (hsp1.symm ▸ hx25_1)
      hx26_1 hx27_1 hx28_1 hlr1 hvregs1
      (fun evs2 s2 P2 hevs2 hst2 hrel2 hpc2 hrun2 hsp2_1 htr2 hx19_2 hx24_2 hx25_2 hx26_2 hx27_2 _
        hcro2 hvregs2 hP2 => ?_)
      (fun e evs2 sf Pf hevs2 hst2 hrel2 _ _ hspf htr2 hcsf hvregsf hcrof hPf => ?_)
    · -- P4.2 Ok(()) → P4.4 store_session at +0x3cc
      let st2 := M.stepEvents evs2 st1
      have hfits_store := hfits_after1.seq_right hevs2
      have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
      have hfs2 := hfs1.of_steps hst2 htr2
        (fun hQ => hQ.2.2.2.2 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
      have hto3cc :
          P2 ⊢ markKyberVtablesAt kpkKit ∗
            stageP4At3ccPrePlaced A lim st2 kit ikit pkKit kpkKit s0 s s2 coroPtr msgPtr outPtr
              remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
              prevStatesPtr ptCap ptPtr v_3d0
              (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
              kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
              sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
              (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())) G ss := by
        refine Entails.trans hP2
          (Entails.replace_factor
            (coro2ac_words_entails_memRegion20 coroPtr 0#32 opkIdDummy 1#32
              kyberPreKeyId signedPreKeyId)
            (by
              unfold stageP4MarkKyberOkPostPlaced stageP4MarkKyberSharedPlaced
              rw [hsp1, coro298_split_eq coroPtr 0#32 opkIdDummy]
              sep_focus)
            (by
              unfold stageP4At3ccPrePlaced stageP4SharedPlaced
              rw [stack_stageP4_to_markKyber kit ikit pkKit kpkKit s.sp hsp_ub]
              sep_ac_rfl))
      refine SepWPp.drop_pre_of_entails hto3cc ?_
      refine stageP4_at_3cc_vregs_store_placed ext encRecord kit kitEnv ikit pkKit kpkKit
        hdealloc hDropSS3 hkit hsVt st2 s0 s s2
        coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
        preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
        (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
        kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())) G ss _
        hprev_nz hExtra hrec_ok haddr_ss hfits_store hpt_le hcap_lt hptr_nz hsp_ub
        (hfs2.mono (fun _ h => h.1) id)
        hcro2 hpc2 hrun2 hsp2 hsp_align
        hx19_2 (hsp1 ▸ hx24_2) (hsp1 ▸ hx25_2) hx26_2 hx27_2 hvregs2
        (fun evs4 sf Pf hevs4 hst4 hrel4 hspf htr4 hcsf hvregsf hcrof hPf => ?_)
        (fun evs4 sf Pf hevs4 hst4 hrel4 hspf htr4 hcsf hvregsf hcrof hPf => ?_)
      · have hst_eq : M.stepEvents evs4 st2 = M.stepEvents (evs1 ++ (evs2 ++ evs4)) st0 := by
          dsimp only [st2, st1]
          simp only [AllocCostModel.stepEvents_append]
        exact ⟨emp, Pf, by rw [emp_sepConj]; exact Entails.refl _,
          hst1.trans (hst2.trans hst4), hspf, hcsf, hvregsf, hcrof,
          .ok c (evs1 ++ (evs2 ++ evs4))
            (SeqEnv.append hevs1 (SeqEnv.append hevs2 hevs4))
            hrel1 hrel2 trivial hrel4
            (by simp only [List.append_nil]; rw [htr4, htr2, htr1])
            (hst_eq ▸ hPf)⟩
      · have hst_eq : M.stepEvents evs4 st2 = M.stepEvents (evs1 ++ (evs2 ++ evs4)) st0 := by
          dsimp only [st2, st1]
          simp only [AllocCostModel.stepEvents_append]
        exact ⟨emp, Pf, by rw [emp_sepConj]; exact Entails.refl _,
          hst1.trans (hst2.trans hst4), hspf, hcsf, hvregsf, hcrof,
          .storeErr c (evs1 ++ (evs2 ++ evs4))
            (SeqEnv.append hevs1 (SeqEnv.append hevs2 hevs4))
            hrel1 hrel2 trivial hrel4
            (by simp only [List.append_nil]; rw [htr4, htr2, htr1])
            (hst_eq ▸ hPf)⟩
    · -- P4.2 Err(e)
      have hst_eq : M.stepEvents evs2 st1 = M.stepEvents (evs1 ++ evs2) st0 :=
        (M.stepEvents_append evs1 evs2 st0).symm
      refine ⟨markKyberVtablesAt kpkKit,
        stageP4ExitAtPlaced A lim (M.stepEvents (evs1 ++ evs2) st0) kit ikit pkKit kpkKit s0 s sf
          coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr
          kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
          (speErrAt kpkKit.markErr outPtr e)
          kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
          sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
          (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.error e)),
        ?_, hst1.trans hst2, by rw [hspf, hsp1], hcsf, hvregsf, hcrof,
        .markErr c e (evs1 ++ evs2) (SeqEnv.append hevs1 hevs2) hrel1 hrel2
          (by rw [htr2, htr1, List.append_assoc]) (Entails.refl _)⟩
      refine Entails.trans hPf
        (Entails.replace_factor
          (coro2ac_words_entails_memRegion20 coroPtr 0#32 opkIdDummy 1#32
            kyberPreKeyId signedPreKeyId)
          (by
            unfold stageP4MarkKyberErrPostPlaced stageP4MarkKyberSharedPlaced
            rw [hsp1, coro298_split_eq coroPtr 0#32 opkIdDummy]
            sep_focus)
          (by
            unfold stageP4ExitAtPlaced stageP4SharedPlaced
            rw [hst_eq, stack_stageP4_to_markKyber kit ikit pkKit kpkKit s.sp hsp_ub]
            sep_ac_rfl))
  · -- P4.1 Err()
    refine ⟨saveIdVtablesAt ikit ∗
        ((kpkKit.kpk_vt + 0x28#64) ↦₆₄ᵣ (0#64 + kpkKit.markShimOff)),
      stageP4ExitAtPlaced A lim (M.stepEvents evs1 st0) kit ikit pkKit kpkKit s0 s sf
        coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr
        kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
        (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
        (savePollPlacedOutAt outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.error ())) pst0 kst0,
      ?_, hstf, hspf, hcsf, hvregsf, hcrof,
      .saveErr evs1 hevs1 hrelf htrf (Entails.refl _)⟩
    refine Entails.trans hPf (Entails.of_eq ?_)
    unfold stageP4SaveIdErrPostPlaced stageP4SaveIdSharedPlaced stageP4ExitAtPlaced
      stageP4SharedPlaced
    rw [stack_stageP4_to_saveId kit ikit pkKit kpkKit s.sp hsp_ub]
    sep_ac_rfl

theorem stageP4_none_v1_vregs_mark_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hkit : SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encRecord ext)
    (hsVt : SessionOnlyVtablesPlacedOk kit)
    (hikit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv ext)
    (hiVt : IdentityVtablesPlacedOk ikit)
    (hkpkKit : KyberPreKeyMarkKitPlacedOk A lim kpkKit kpkKitEnv ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qp : State → SepProp → Prop}
    (st0 : M.σ) (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdDummy kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hprev_nz : prevStatesPtr ≠ 0#64)
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : kit.RecOk ⟨some ss⟩)
    (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val)
    (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hfits : FitsEnv M lim st0
      (StageP4NoneStepEnv kit kitEnv ikit ikitEnv kpkKit kpkKitEnv
        sst0 ist0 kst0 peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey ⟨some ss⟩))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4RawPrePlaced A lim st0 kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
        remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
        prevStatesPtr ptCap ptPtr v_3d0
        (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
        kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (lsProg_518 ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        StageP4RawBranchPlaced A lim st0 kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
          encRecord s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr
          idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
          none kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sst0 ist0 pst0 kst0 ss sf Pf)
      Qp :=
  stageP4_none_v1_vregs_store_mark_placed_ok ext encRecord kit kitEnv ikit ikitEnv pkKit pkKitEnv
    kpkKit kpkKitEnv hdealloc hDropSS3 (sessionStoreOnlyKitPlacedOk_of_se hkit) hsVt hikit hiVt
    hkpkKit hkVt st0 s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr
    idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkIdDummy
    kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss
    hprev_nz hExtra hrec_ok haddr_ss haddr_id hmark_ok hfits hpt_le hcap_lt hptr_nz
    hsp_ub hfs hcro hpc hrun hsp_align hx19 hx24 hx25 hx26 hx27 hx28 hvregs

/-- Budget-threaded `[LibsignalPlacement]` Stage P4 (`opkId? = none`) under
`SessionOnlyKitPlacedOkSE` and `KyberPreKeyStoreKitPlacedOk`. -/
theorem stageP4_none_v1_vregs_kits_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hkit : SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encRecord ext)
    (hsVt : SessionOnlyVtablesPlacedOk kit)
    (hikit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv ext)
    (hiVt : IdentityVtablesPlacedOk ikit)
    (hkpkKit : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkKitEnv ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qp : State → SepProp → Prop}
    (st0 : M.σ) (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdDummy kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hprev_nz : prevStatesPtr ≠ 0#64)
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : kit.RecOk ⟨some ss⟩)
    (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val)
    (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hfits : FitsEnv M lim st0
      (StageP4NoneStepEnv kit kitEnv ikit ikitEnv kpkKit kpkKitEnv
        sst0 ist0 kst0 peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey ⟨some ss⟩))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4RawPrePlaced A lim st0 kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
        remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
        prevStatesPtr ptCap ptPtr v_3d0
        (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
        kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (lsProg_518 ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        StageP4RawBranchPlaced A lim st0 kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
          encRecord s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr
          idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
          none kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sst0 ist0 pst0 kst0 ss sf Pf)
      Qp :=
  stageP4_none_v1_vregs_mark_placed_ok ext Scope encRecord kit kitEnv ikit ikitEnv pkKit pkKitEnv
    kpkKit kpkKitEnv hdealloc hDropSS3 hkit hsVt hikit hiVt
    (kyberPreKeyMarkKitPlacedOk_of_store hkpkKit) hkVt st0 s0 s coroPtr ctxPtr msgPtr outPtr
    remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
    prevStatesPtr ptCap ptPtr v_3d0 opkIdDummy kyberPreKeyId signedPreKeyId b_2c0 pt
    peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss
    hprev_nz hExtra hrec_ok haddr_ss haddr_id hmark_ok hfits hpt_le hcap_lt hptr_nz
    hsp_ub hfs hcro hpc hrun hsp_align hx19 hx24 hx25 hx26 hx27 hx28 hvregs

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsNonePlacedBudget
