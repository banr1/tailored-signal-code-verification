/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustFramePlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs

/-!
# Budget-Threaded Relocatable Poll Buffer and Seam Frame Bundles for `segTrust`

Adapts the `SegTrustFramePlaced` seam frame bundles to `RustCliAllocBudget M` via `A.atState` for
use in `segTrust_placed_okV`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustFramePlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (SessionState OutgoingTripleRatchet IdentityKey)
open CryptoGames.LibsignalSessionApi (Session CiphertextMessage)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (protocolAddressAt)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalPublicApi.StoreKit (SessionStoreSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (
  WithStoresEncGhost takenRecord cmSlots cmScratch encSpillsAtV encSubStack encSubStackV
  withStoresEncStackV
)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails (dropRecordSlots)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust (trustPollRest)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt (encCommonPlaced encStoreExtraPlaced)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust (
  cliEncCommonRest cliTrustPassive encCommonPlaced_eq trustBaseActivePlaced
  seam_mem_split_placed seam_mem_to_tail_placed trustActivePlaced
  trustBaseActive_join_extra_placed trustActive_split_extra_placed trustPollPlacedOut_words
)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins (
  retagSessionStore retagIdentityStore
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

export CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust (
  cliEncCommonRest cliTrustPassive encCommonPlaced_eq trustBaseActivePlaced seam_mem_split_placed
)
export CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust (
  seam_mem_to_tail_placed trustActivePlaced trustBaseActive_join_extra_placed
  trustActive_split_extra_placed trustPollPlacedOut_words
)

theorem cliEncCommonRest_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (ctl : BitVec 64) (x : WithStoresEncGhost) (draws : Nat) (s0 : State) :
    cliEncCommonRest (A.atState lim st s) ctl x draws s0 =
      cliEncCommonRest A.repAlloc ctl x draws s0 := rfl

theorem cliTrustPassive_atState [LibsignalPlacement] {M : AllocCostModel}
    (ss_vt id_vt : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (ctl : BitVec 64) (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (m : CiphertextMessage) (draws : Nat) (s0 : State) :
    cliTrustPassive ss_vt id_vt (A.atState lim st s) ctl x sess taken otr' pqCap' pqPtr' m draws s0 =
      cliTrustPassive ss_vt id_vt A.repAlloc ctl x sess taken otr' pqCap' pqPtr' m draws s0 := rfl

theorem encCommonPlaced_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (ctl : BitVec 64) (x : WithStoresEncGhost) (draws : Nat) (s0 : State) :
    encCommonPlaced (A.atState lim st s) ctl x draws s0 =
      protocolAddressAt A.repAlloc x.rem x.remA ∗ lsLogOff ∗
      stackAt (s0.sp - 0xbe0#64) encSubStack ∗ A.pool lim st s ∗
      cliEncCommonRest A.repAlloc ctl x draws s0 :=
  encCommonPlaced_eq (A.atState lim st s) ctl x draws s0

theorem trustBaseActivePlaced_atState [LibsignalPlacement] {M : AllocCostModel}
    (id_vt : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (sp : BitVec 64) (x : WithStoresEncGhost) (k : IdentityKey) :
    trustBaseActivePlaced id_vt (A.atState lim st s) sp x k =
      ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
      ((sp + 0xc0#64) ↦₆₄ x.remA) ∗
      ((sp + 0xe0#64) ↦₆₄ x.idA) ∗
      ((sp + 0xe8#64) ↦₆₄ id_vt) ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      lsLogOff ∗
      stackAt sp encSubStack ∗
      A.pool lim st s := rfl

theorem seam_mem_split_placed_budget [LibsignalPlacement] {M : AllocCostModel}
    (ss_vt id_vt : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (ctl : BitVec 64) (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (k : IdentityKey) (m : CiphertextMessage)
    (draws : Nat) (s0 : State) (sp : BitVec 64) (hsp : sp = s0.sp - 0xbe0#64) :
    cmSlots A.repAlloc sp sess taken otr' pqCap' pqPtr' k m ∗ cmScratch sp ∗
      encSpillsAtV ss_vt id_vt sp x ∗ memRegion (sp + 0x46a#64) 0x716 ∗
      memRegion x.ret 248 ∗ encCommonPlaced (A.atState lim st s) ctl x draws s0 =
    (trustBaseActivePlaced id_vt (A.atState lim st s) sp x k ∗
      memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      memRegion (sp + 0x970#64) 24 ∗
      memRegion (sp + 0x9d0#64) 24) ∗
    cliTrustPassive ss_vt id_vt A.repAlloc ctl x sess taken otr' pqCap' pqPtr' m draws s0 :=
  seam_mem_split_placed ss_vt id_vt (A.atState lim st s) ctl x sess taken otr' pqCap' pqPtr' k m
    draws s0 sp hsp

theorem seam_mem_to_tail_placed_budget [LibsignalPlacement] {M : AllocCostModel}
    (ss_vt id_vt : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (ctl : BitVec 64) (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (k : IdentityKey) (m : CiphertextMessage)
    (draws : Nat) (s0 : State) (sp : BitVec 64) (hsp : sp = s0.sp - 0xbe0#64)
    (P970 P9d0 poll H : SepProp)
    (hpoll :
      memRegion (sp + 0x470#64) 16 ∗ memRegion (sp + 0x480#64) 32 ∗
        memRegion (sp + 0x580#64) 48 ∗ P970 ∗ P9d0 ∗ trustPollRest sp ⊢ poll) :
    (trustBaseActivePlaced id_vt (A.atState lim st s) sp x k ∗
      memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      P970 ∗ P9d0 ∗ H) ∗
    cliTrustPassive ss_vt id_vt A.repAlloc ctl x sess taken otr' pqCap' pqPtr' m draws s0 ⊢
    ∃∗ g : RecordGhost,
      (dropRecordSlots A.repAlloc sp cmScratch g (takenRecord sess taken)
          (some (pqCap', pqPtr', otr')) (some m) poll ∗ H) ∗
        encSpillsAtV ss_vt id_vt sp x ∗ memRegion x.ret 248 ∗
        encCommonPlaced (A.atState lim st s) ctl x draws s0 :=
  seam_mem_to_tail_placed ss_vt id_vt (A.atState lim st s) ctl x sess taken otr' pqCap' pqPtr' k m
    draws s0 sp hsp P970 P9d0 poll H hpoll

theorem trustActivePlaced_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ist : ikit.IdState)
    (sp : BitVec 64) (subStack : Nat) (x : WithStoresEncGhost) (k : IdentityKey) :
    trustActivePlaced (retagIdentityStore (A' := A.atState lim st s) ikit) ist sp subStack x k =
      ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
      ((sp + 0xc0#64) ↦₆₄ x.remA) ∗
      ((sp + 0xe0#64) ↦₆₄ x.idA) ∗
      ((sp + 0xe8#64) ↦₆₄ ikit.id_vt) ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      lsLogOff ∗
      ikit.identityAt x.idA ist ∗
      stackAt sp subStack ∗
      A.pool lim st s := rfl

theorem trustBaseActive_join_extra_placed_budget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (kit : SessionStoreSpec A.repAlloc 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ist : ikit.IdState)
    (x : WithStoresEncGhost) (k : IdentityKey) (s0 : State)
    (sp : BitVec 64) (hsp : sp = s0.sp - 0xbe0#64) :
    trustBaseActivePlaced ikit.id_vt (A.atState lim st s) sp x k ∗
      encStoreExtraPlaced kit st0 ikit ist x s0 ⊢
    ⌜withStoresEncStackV kit ikit ≤ s0.sp.toNat⌝ ∗
      trustActivePlaced (retagIdentityStore (A' := A.atState lim st s) ikit) ist
        sp (encSubStackV kit ikit) x k ∗
      kit.storeAt x.ssA st0 :=
  trustBaseActive_join_extra_placed
    (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist x k s0 sp hsp

theorem trustActive_split_extra_placed_budget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (kit : SessionStoreSpec A.repAlloc 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ist : ikit.IdState)
    (x : WithStoresEncGhost) (k : IdentityKey) (s0 : State)
    (sp : BitVec 64) (hsp : sp = s0.sp - 0xbe0#64)
    (hbound : withStoresEncStackV kit ikit ≤ s0.sp.toNat) :
    trustActivePlaced (retagIdentityStore (A' := A.atState lim st s) ikit) ist
        sp (encSubStackV kit ikit) x k ∗
      kit.storeAt x.ssA st0 ⊢
    trustBaseActivePlaced ikit.id_vt (A.atState lim st s) sp x k ∗
      encStoreExtraPlaced kit st0 ikit ist x s0 :=
  trustActive_split_extra_placed
    (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist x k s0 sp hsp hbound

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustFramePlacedBudget
