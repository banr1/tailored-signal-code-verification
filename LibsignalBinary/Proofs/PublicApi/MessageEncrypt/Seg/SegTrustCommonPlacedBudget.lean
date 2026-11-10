/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public meta import ProofLib
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PlacedDefs
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.TailsPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommon
public import LibsignalBinary.Proofs.Common.StringClonePlacedBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPure

/-!
# Budget-Threaded Shared Infrastructure for Relocatable `MessageEncrypt` Segments

Defines `SeamBudget`, store-poll and callee allocation envelopes, budget-threaded seam states and
segment specifications on `lsProg_198 H`, concrete `FitsEnv` non-vacuity witnesses, and relocatable
call/stepping combinators under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Heap
open LibsignalBinary.Heap.Fine (fineCostModel FineStepBound)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineStepReserveOfCum fineMaxMetaAreasOfCum fineDynIvsOfCum fineMaxGroupsOfCum)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_modelHyps fitsEnv_fineCostModel_of_phaseCredit)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.DefsBudget (otrApplyEnv_phaseCreditSpec)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget
  (otrSignalMsgGhost otrEncryptCoreEnv_phaseCreditSpec_bounded witnessPublicKey witnessKeyPair
   witnessIdentityKey witnessCrypto witnessSpqrModel witnessSendEnv witnessUuidParse
   witnessAddrGhost witnessOtr)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget
  (kyberPayloadLen kyberOptEnv_phaseCreditSpec preKeyMsgNewRawEnv_phaseCreditSpec
   preKeySignalMessage_new_small_length_le)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.Placed
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust (spAligned_of_sp_eq)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace TempTwins

/-! ## `SeamBudget` Carrier and VM-Step Helpers -/

export LibsignalBinary.Proofs.Placed.BudgetVmSteps (
  vmPreserved_right_congr vmPreserved_refl_iff vmPreserved_setPC vmPreserved_advancePC
  vmPreserved_setPState vmPreserved_writeReg64 vmPreserved_writeReg32 vmPreserved_writeReg
  vmPreserved_writeVReg128 vmPreserved_writeVReg64 vmPreserved_writeVReg32
  vmPreserved_applyWriteback vmPreserved_setMem_writeBytes vmPreserved_setMem_write8
  vmPreserved_setMem_write16 vmPreserved_setMem_write32 vmPreserved_setMem_write64
  vmPreserved_setStatus vmPreserved_appendTrace vmPreserved_setFs vmPreserved_stepExclLoop
  tpidrEl0_applyWriteback trapHooks sepWP_rebase_vmPreserved)

theorem freeOnlyEvs_rustDeallocEvents (size align : Nat) :
    FreeOnlyEvs (rustDeallocEvents size align) :=
  FreeOnlyEvs.singleton align size

/-- Relates entry cost-model state `st_init` (`TopEnv`) to an intermediate seam state `st`
with remaining allocation envelope `RemEnv`. -/
def SeamBudget {M : AllocCostModel} (lim : BudgetLimits)
    (TopEnv : List AllocEvent → Prop) (st_init st : M.σ)
    (RemEnv : List AllocEvent → Prop) : Prop :=
  FitsEnv M lim st RemEnv ∧
  ∃ evs_pre : List AllocEvent,
    st = M.stepEvents evs_pre st_init ∧
    ∀ evs_rem, RemEnv evs_rem → TopEnv (evs_pre ++ evs_rem)

theorem SeamBudget.init {M : AllocCostModel} {lim : BudgetLimits}
    {TopEnv : List AllocEvent → Prop} {st_init : M.σ}
    (h : FitsEnv M lim st_init TopEnv) :
    SeamBudget lim TopEnv st_init st_init TopEnv :=
  ⟨h, [], rfl, fun _ hr => hr⟩

theorem SeamBudget.narrow {M : AllocCostModel} {lim : BudgetLimits}
    {TopEnv RemEnv RemEnv' : List AllocEvent → Prop} {st_init st : M.σ}
    (h : SeamBudget lim TopEnv st_init st RemEnv)
    (himp : ∀ evs, RemEnv' evs → RemEnv evs) :
    SeamBudget lim TopEnv st_init st RemEnv' := by
  rcases h with ⟨hfit, evs_pre, hst, htop⟩
  exact ⟨FitsEnv.mono himp hfit, evs_pre, hst, fun evs hr => htop evs (himp evs hr)⟩

theorem SeamBudget.advance {M : AllocCostModel} {lim : BudgetLimits}
    {TopEnv StepEnv NextEnv : List AllocEvent → Prop} {st_init st : M.σ}
    {evs_step : List AllocEvent}
    (h : SeamBudget lim TopEnv st_init st (SeqEnv StepEnv NextEnv))
    (hstep : StepEnv evs_step) :
    SeamBudget lim TopEnv st_init (M.stepEvents evs_step st) NextEnv := by
  rcases h with ⟨hfit, evs_pre, hst, htop⟩
  refine ⟨hfit.seq_right hstep, evs_pre ++ evs_step, ?_, ?_⟩
  · rw [M.stepEvents_append, ← hst]
  · intro evs_rem hrem
    rw [List.append_assoc]
    exact htop (evs_step ++ evs_rem) (Or.inr ⟨evs_step, evs_rem, rfl, hstep, hrem⟩)

theorem SeamBudget.finish {M : AllocCostModel} {lim : BudgetLimits}
    {TopEnv RemEnv : List AllocEvent → Prop} {st_init st : M.σ}
    {evs_end : List AllocEvent}
    (h : SeamBudget lim TopEnv st_init st RemEnv)
    (hend : RemEnv evs_end) :
    ∃ evs_tot : List AllocEvent,
      TopEnv evs_tot ∧ M.stepEvents evs_end st = M.stepEvents evs_tot st_init := by
  rcases h with ⟨_, evs_pre, hst, htop⟩
  refine ⟨evs_pre ++ evs_end, htop evs_end hend, ?_⟩
  rw [M.stepEvents_append, ← hst]

/-! ## Store Retags, Allocation Envelopes, and Callee Budget Contracts -/

def retagSessionStore {A A' : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) : SessionStoreSpec A' b :=
  { kit with }

def retagIdentityStore {A A' : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) : IdentityStoreSpec A' b :=
  { ikit with }

/-- Allocation envelope for boxed store-future shims (`size = 0` or `rustAllocEvents size 8`). -/
def BoxAllocEnv (boxSize : Nat) (evs : List AllocEvent) : Prop :=
  (boxSize = 0 ∧ evs = []) ∨
  (0 < boxSize ∧ evs = rustAllocEvents boxSize 8)

/-- Allocation envelope for `<String as Clone>::clone` (`len = 0` or `rustAllocEvents len 1`). -/
def StringCloneEnv (g : VecGhost) (evs : List AllocEvent) : Prop :=
  (g.bytes.length = 0 ∧ evs = []) ∨
  (0 < g.bytes.length ∧ evs = rustAllocEvents g.bytes.length 1)

abbrev ValidRustAllocEv := LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.ValidRustAllocEv
abbrev SpqrSendBudgetEnv := LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.SpqrSendBudgetEnv
abbrev OtrEncryptCoreEnv := LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.OtrEncryptCoreEnv
abbrev OtrEncryptEnv := LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.OtrEncryptEnv
abbrev OtrApplyEnv := LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.DefsBudget.OtrApplyEnv
abbrev KyberOptEnv := LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget.KyberOptEnv
abbrev PreKeyMsgNewRawEnv := LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget.PreKeyMsgNewRawEnv

/-- Poll allocation envelopes for `SessionStoreSpec`. -/
structure SessionStoreBudgetEnv {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) where
  loadPollEnv : kit.StoreState → AddrVal → List AllocEvent → Prop
  storePollEnv : kit.StoreState → AddrVal → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop

/-- Poll allocation envelopes for `IdentityStoreSpec`. -/
structure IdentityStoreBudgetEnv {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) where
  trustPollEnv : ikit.IdState → AddrVal → IdentityKey → Direction → List AllocEvent → Prop
  savePollEnv : ikit.IdState → AddrVal → IdentityKey → List AllocEvent → Prop

def stringCloneBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (BitVec 64 × BitVec 64 × VecGhost × M.σ) where
  pre := fun (p, ret, g, st) s =>
    ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret ∧ FitsEnv M lim st (StringCloneEnv g)⌝ ∗
      vecGhostAt A.repAlloc g p ∗ memRegion ret 24 ∗ A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (p, ret, g, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ StringCloneEnv g evs⌝ ∗
      vecGhostAt A.repAlloc g p ∗ vecU8 A.repAlloc ret g.bytes ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp extHookStack

def futDropBudgetSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝

def kitTrustShimBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (ikit : IdentityStoreSpec A.repAlloc b) :
    Spec (IdentityShimCall × BitVec 8 × M.σ) where
  pre := fun (x, d, st) s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.keyA ∧
      (s.readReg64 .x3).setWidth 8 = d ∧ FitsEnv M lim st (BoxAllocEnv ikit.trustBoxSize)⌝ ∗
      A.pool lim st s ∗ stackAt s.sp ikit.trustShimStack
  post := fun (x, d, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.readReg64 .x1 = b + ikit.trustFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
        (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
        BoxAllocEnv ikit.trustBoxSize evs⌝ ∗
      A.live (sf.readReg64 .x0) ikit.trustBoxSize 8 ∗
      ikit.trustBoxAt (sf.readReg64 .x0) x.self x.addrA x.keyA 0#8 d ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp ikit.trustShimStack

def kitSaveShimBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (ikit : IdentityStoreSpec A.repAlloc b) :
    Spec (IdentityShimCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.keyA ∧
      FitsEnv M lim st (BoxAllocEnv ikit.saveBoxSize)⌝ ∗
      A.pool lim st s ∗ stackAt s.sp ikit.saveShimStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.readReg64 .x1 = b + ikit.saveFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
        (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
        BoxAllocEnv ikit.saveBoxSize evs⌝ ∗
      A.live (sf.readReg64 .x0) ikit.saveBoxSize 8 ∗
      ikit.saveBoxAt (sf.readReg64 .x0) x.self x.addrA x.keyA 0#8 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp ikit.saveShimStack

def kitTrustPollBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) :
    Spec (IdentityPollCall × Direction × BitVec 64 × ikit.IdState × M.σ) where
  pre := fun (x, d, self, ist0, st) s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧ ikit.addrOk x.call.addr.val ∧
      FitsEnv M lim st (ikitEnv.trustPollEnv ist0 x.call.addr.val x.call.key d)⌝ ∗
      ikit.trustBoxAt x.fut self x.call.addrA x.call.keyA 0#8 (directionByte d) ∗
      ikit.identityAt self ist0 ∗ memRegion x.out 48 ∗
      protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
      (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ A.pool lim st s ∗
      stackAt s.sp ikit.trustPollStack
  post := fun (x, d, self, ist0, st) s0 sf =>
    ∃∗ ans : Except Unit Bool, ∃∗ evs : List AllocEvent,
      ⌜ikit.trustRel ist0 x.call.addr.val x.call.key d ans ∧
        sf.trace = s0.trace ++ ikit.trustEvs x.call.addr.val x.call.key d ans ∧
        ikitEnv.trustPollEnv ist0 x.call.addr.val x.call.key d evs⌝ ∗
      ikit.trustBoxAt x.fut self x.call.addrA x.call.keyA 1#8 (directionByte d) ∗
      ikit.identityAt self (ikit.trustUpdate ist0 x.call.addr.val x.call.key d ans) ∗
      trustPollPlacedOutAt x.out ans ∗
      protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
      (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp ikit.trustPollStack

abbrev kitTrustPollBudgetSpecE (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) :
    Spec (IdentityPollCall × Direction × BitVec 64 × ikit.IdState × M.σ) :=
  withEnvPre (kitTrustPollBudgetSpec M A lim ikit ikitEnv) fun s => ikit.envOk s.fs.files

abbrev kitTrustPollBudgetSpecI [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (ikitEnv : IdentityStoreBudgetEnv ikit) :
    Spec (IdentityPollCall × Direction × BitVec 64 × ikit.IdState × M.σ) :=
  withLsLogOff (kitTrustPollBudgetSpecE M A lim ikit ikitEnv)

def kitSavePollBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) :
    Spec (IdentityPollCall × BitVec 64 × ikit.IdState × M.σ) where
  pre := fun (x, self, ist0, st) s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧ ikit.addrOk x.call.addr.val ∧
      FitsEnv M lim st (ikitEnv.savePollEnv ist0 x.call.addr.val x.call.key)⌝ ∗
      ikit.saveBoxAt x.fut self x.call.addrA x.call.keyA 0#8 ∗
      ikit.identityAt self ist0 ∗ memRegion x.out 48 ∗
      protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
      (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ A.pool lim st s ∗
      stackAt s.sp ikit.savePollStack
  post := fun (x, self, ist0, st) s0 sf =>
    ∃∗ ans : Except Unit IdentityChange, ∃∗ evs : List AllocEvent,
      ⌜ikit.saveRel ist0 x.call.addr.val x.call.key ans ∧
        sf.trace = s0.trace ++ ikit.saveEvs x.call.addr.val x.call.key ans ∧
        ikitEnv.savePollEnv ist0 x.call.addr.val x.call.key evs⌝ ∗
      ikit.saveBoxAt x.fut self x.call.addrA x.call.keyA 1#8 ∗
      ikit.identityAt self (ikit.saveUpdate ist0 x.call.addr.val x.call.key ans) ∗
      savePollPlacedOutAt x.out ans ∗
      protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
      (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp ikit.savePollStack

abbrev kitSavePollBudgetSpecE (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) :
    Spec (IdentityPollCall × BitVec 64 × ikit.IdState × M.σ) :=
  withEnvPre (kitSavePollBudgetSpec M A lim ikit ikitEnv) fun s => ikit.envOk s.fs.files

abbrev kitSavePollBudgetSpecI [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (ikitEnv : IdentityStoreBudgetEnv ikit) :
    Spec (IdentityPollCall × BitVec 64 × ikit.IdState × M.σ) :=
  withLsLogOff (kitSavePollBudgetSpecE M A lim ikit ikitEnv)

structure IdentityStoreKitBudgetOkI [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (H : LibsignalHooks) : Prop where
  trustShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + ikit.trustShimOff)
      (withLsRoCl lsmpl (kitTrustShimBudgetSpec M A lim ikit))
  trustPoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + ikit.trustPollOff)
      (withLsRoCl lsmpl (kitTrustPollBudgetSpecI M A lim ikit ikitEnv))
  trustFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + ikit.trustFutDropOff) (withLsRoCl lsmpl futDropBudgetSpec)
  saveShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + ikit.saveShimOff)
      (withLsRoCl lsmpl (kitSaveShimBudgetSpec M A lim ikit))
  savePoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + ikit.savePollOff)
      (withLsRoCl lsmpl (kitSavePollBudgetSpecI M A lim ikit ikitEnv))
  saveFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + ikit.saveFutDropOff) (withLsRoCl lsmpl futDropBudgetSpec)

def remoteIdentityKeyBudgetSpec [LibsignalPlacement] (A : RustAlloc) :
    Spec CryptoVerification.LibsignalTripleRatchet.Getters.RemoteIdentityKeyGhost :=
  let base := CryptoVerification.LibsignalTripleRatchet.Getters.remoteIdentityKeyPlacedSpec A
  { base with
    post := fun x s0 sf => ⌜VmPreserved s0 sf⌝ ∗ base.post x s0 sf }

def unackItemsBudgetSpec [LibsignalPlacement] (A : RustAlloc) :
    Spec UnackCall :=
  let base := CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems.unackItemsPlacedSpec A
  { base with
    post := fun x s0 sf => ⌜VmPreserved s0 sf⌝ ∗ base.post x s0 sf }

/-- Budget-threaded relocatable `OTR::encrypt::<HookRng>` contract (`onOom = ⌜False⌝`). -/
def otrEncryptBudgetSpec [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv) :
    Spec (OtrEncryptGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (OtrEncryptEnv C S sendEnv uuidParse x)⌝ ∗
      (otrEncryptPlacedSpec C (A.atState lim st s) ctl uuidParse S).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜OtrEncryptEnv C S sendEnv uuidParse x evs⌝ ∗
      (otrEncryptPlacedSpec C (A.atState lim (M.stepEvents evs st) sf) ctl uuidParse S).post x s0 sf
  onPanic := fun (x, _) s0 sf =>
    ⌜((x.model C S uuidParse).1 = .error .panic ∨ S.sendPanics x.ot.pqrState x.rest) ∧
      s0.trace <+: sf.trace⌝ ∗
      anyHeap

def otrEncryptBudgetSpecQ [LibsignalPlacement] {M : AllocCostModel} (Q : List (BitVec 8) → Prop)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv) :
    Spec (OtrEncryptGhost × M.σ) :=
  { otrEncryptBudgetSpec C A lim ctl parse S sendEnv with
    pre := fun (x, st) s =>
      ⌜FitsEnv M lim st (OtrEncryptEnv C S sendEnv parse x)⌝ ∗
        (otrEncryptPlacedSpecQ Q C (A.atState lim st s) ctl parse S).pre x s }

/-- External hook contracts on `H : LibsignalHooks` for budget-threaded `MessageEncrypt`. -/
structure PublicApiEncHooksBudget [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  shim : HookSat H lsRustNoAllocShimSym sessionShimSpec
  shimVm : HookSat H lsRustNoAllocShimSym LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionShimBudgetSpec
  alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)
  dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)
  realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)
  memcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec
  memcpyVm : HookSat H lsMemcpySym LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec
  stringClone : HookSat H lsStringCloneSym
    (LibsignalBinary.Heap.RustStdAllocBudgetBridge.stringCloneBudgetSpec M A lim)
  timeAdd : HookSat H lsTimeAddSym timeAddSpec
  durationSince : HookSat H lsDurationSinceSym durationSinceSpec
  handleError : H lsHandleErrorSym = some Rust.panicked
  handleAllocError : H lsHandleAllocErrorSym = some Rust.panicked
  expectFailed : H lsExpectFailedSym = some Rust.panicked

/-- Callee `subroutine_ok` bundle for `SegIdentity`, `SegSignal`, `SegTrust`, and `SegSave`
on `lsProg_198 H`. -/
structure EncCalleesBudget [LibsignalPlacement] {M : AllocCostModel} (Q : List (BitVec 8) → Prop)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv) (H : LibsignalHooks) : Prop where
  remoteIk : subroutine_ok (lsProg_198 H) (lsmpl.base 29)
    (StoreKit.withLsRoCl lsmpl (remoteIdentityKeyBudgetSpec A.repAlloc))
  otrEnc : subroutine_ok (lsProg_198 H) (libsignalSessionLib.fnAddr lsmpl otrEncryptName)
    (StoreKit.withLsRoCl lsmpl (otrEncryptBudgetSpecQ Q C A lim ctl parse S sendEnv))
  unack : subroutine_ok (lsProg_198 H) (lsmpl.base 36)
    (StoreKit.withLsRoCl lsmpl (unackItemsBudgetSpec A.repAlloc))

/-! ## Seam Envelopes, Seam States, and Segment Contracts -/

def TrustStepEnv {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b)
    (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (rem : AddrVal) (k : IdentityKey) : List AllocEvent → Prop :=
  SeqEnv (BoxAllocEnv ikit.trustBoxSize)
    (SeqEnv (ikitEnv.trustPollEnv ist0 rem k .sending)
      (· = rustDeallocEvents ikit.trustBoxSize 8))

def SaveStepEnv {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b)
    (ikitEnv : IdentityStoreBudgetEnv ikit) (ist1 : ikit.IdState)
    (rem : AddrVal) (k : IdentityKey) : List AllocEvent → Prop :=
  SeqEnv (BoxAllocEnv ikit.saveBoxSize)
    (SeqEnv (ikitEnv.savePollEnv ist1 rem k)
      (· = rustDeallocEvents ikit.saveBoxSize 8))

def FromApplyEnv {A : RustAlloc} (kit : SessionStoreSpec A 0#64)
    (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) : List AllocEvent → Prop :=
  SeqEnv OtrApplyEnv
    (SeqEnv (BoxAllocEnv kit.storeBoxSize)
      (SeqEnv (kitEnv.storePollEnv st0 x.rem.val (storedRecord sess otr' taken))
        (SeqEnv (· = rustDeallocEvents kit.storeBoxSize 8) FreeOnlyEvs)))

def FromSaveEnv {A : RustAlloc} (kit : SessionStoreSpec A 0#64)
    (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist1 : ikit.IdState) (x : WithStoresEncGhost)
    (sess : Session (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) : List AllocEvent → Prop :=
  SeqEnv (SaveStepEnv ikit ikitEnv ist1 x.rem.val k)
    (fun evs => FreeOnlyEvs evs ∨ FromApplyEnv kit kitEnv st0 x sess otr' taken evs)

def FromCmEnv {A : RustAlloc} (kit : SessionStoreSpec A 0#64)
    (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (x : WithStoresEncGhost)
    (sess : Session (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) : List AllocEvent → Prop :=
  SeqEnv (TrustStepEnv ikit ikitEnv ist0 x.rem.val k)
    (fun evs =>
      FreeOnlyEvs evs ∨
      SeqEnv (StringCloneEnv x.rem.name) FreeOnlyEvs evs ∨
      FromSaveEnv kit kitEnv st0 ikit ikitEnv
        (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x sess otr' taken k evs)

def pendingKyberPayload (sess : Session (List (BitVec 8))) : Option KyberPayload :=
  sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)

def preKeyMsgFromItems (sess : Session (List (BitVec 8))) (items : PendingPreKey)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (sm : SignalMessage) : PreKeySignalMessage :=
  PreKeySignalMessage.new otr'.sessionVersion sess.localRegistrationId items.preKeyId
    items.signedPreKeyId (pendingKyberPayload sess) items.baseKey otr'.localIdentityKey sm

def PreKeyPostEncryptEnv {A : RustAlloc} (C : Crypto) (S : SpqrModel) (parse : UuidParser)
    (kit : SessionStoreSpec A 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (items : PendingPreKey) (evs' : List AllocEvent) : Prop :=
  let res := Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext
    (serializeAddresses (serviceIdParse parse) x.loc x.rem) x.rest) otr
  FreeOnlyEvs evs' ∨
  match res.1 with
  | .error _ => False
  | .ok sm =>
    SeqEnv
      (PreKeyMsgNewRawEnv (pendingKyberPayload sess) sm.serialized.length
        (preKeyMsgFromItems sess items res.2 sm).serialized.length)
      (fun evs'' =>
        FreeOnlyEvs evs'' ∨
        FromCmEnv kit kitEnv st0 ikit ikitEnv ist0 x sess res.2 taken k evs'') evs'

def FromKeyEnv {A : RustAlloc} (C : Crypto) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (parse : UuidParser)
    (kit : SessionStoreSpec A 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (x : WithStoresEncGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (evs : List AllocEvent) : Prop :=
  (sess.pendingPreKey = none ∧
    SeqEnv (OtrEncryptCoreEnv C S sendEnv parse otr x.ptext none x.rem x.rest)
      (fun evs' =>
        FreeOnlyEvs evs' ∨
        FromCmEnv kit kitEnv st0 ikit ikitEnv ist0 x sess
          (Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext none x.rest) otr).2
          taken k evs') evs) ∨
  (∃ items, sess.pendingPreKey = some items ∧
    (SeqEnv (StringCloneEnv x.rem.name) FreeOnlyEvs evs ∨
      SeqEnv (KyberOptEnv (sess.pendingKyberPreKey.map (·.ciphertext)))
        (SeqEnv (OtrEncryptCoreEnv C S sendEnv parse otr x.ptext (some x.loc) x.rem x.rest)
          (PreKeyPostEncryptEnv C S parse kit kitEnv st0 ikit ikitEnv ist0
            x sess otr taken k items)) evs))

def FromOtrEnv {A : RustAlloc} (C : Crypto) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (parse : UuidParser)
    (kit : SessionStoreSpec A 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (x : WithStoresEncGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  ∃ k, taken.remoteIdentity = some k ∧
    FromKeyEnv C S sendEnv parse kit kitEnv st0 ikit ikitEnv ist0 x sess otr taken k evs

/-- End-to-end allocation event envelope for `session_message_encrypt_with_stores`. -/
def WithStoresEncEnv {A : RustAlloc} (kit : SessionStoreSpec A 0#64)
    (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv) (parse : UuidParser)
    (x : WithStoresEncGhost) : List AllocEvent → Prop :=
  SeqEnv
    (SeqEnv (BoxAllocEnv kit.loadBoxSize)
      (SeqEnv (kitEnv.loadPollEnv st0 x.rem.val)
        (· = rustDeallocEvents kit.loadBoxSize 8)))
    (fun evs =>
      FreeOnlyEvs evs ∨
      SeqEnv (StringCloneEnv x.rem.name) FreeOnlyEvs evs ∨
      SeqEnv FreeOnlyEvs
        (fun evs' =>
          FreeOnlyEvs evs' ∨
          ∃ r sess otr taken,
            kit.ScopeAt Scope st0 x.rem.val r ∧
            r.currentSession = some sess ∧
            execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) ∧
            FromOtrEnv C S sendEnv parse kit kitEnv st0 ikit ikitEnv ist0 x sess otr taken evs') evs)

/-- Budget-threaded relocatable contract for `session_message_encrypt_with_stores`
(block `198`, `onOom = ⌜False⌝`). -/
def withStoresEncBudgetSpecV [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) :
    Spec (WithStoresEncGhost × M.σ) :=
  StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st_init) s =>
        ⌜FitsEnv M lim st_init
            (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidParse x) ∧
          s.readReg64 .x0 = x.ptA ∧ (s.readReg64 .x1).toNat = x.ptext.length ∧
          x.ptext.length < 2 ^ 32 ∧ s.readReg64 .x2 = x.remA ∧ s.readReg64 .x3 = x.locA ∧
          x.locA ≠ 0#64 ∧
          s.readReg64 .x4 = x.ssA ∧ s.readReg64 .x5 = kit.ss_vt ∧
          s.readReg64 .x6 = x.idA ∧ s.readReg64 .x7 = ikit.id_vt ∧
          x.now.tvNsec.toNat < 10 ^ 9 ∧ s.readReg64 .x8 = x.ret ∧
          withStoresEncStackV kit ikit ≤ s.sp.toNat ∧
          kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val⌝ ∗
        kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist0 ∗
        nowAt s.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        protocolAddressAt A.repAlloc x.loc x.locA ∗ memRegion x.ret 248 ∗ tapeAt ctl x.cur x.rest ∗
        FromRecordCallees.lsLogOff ∗ stackAt s.sp (withStoresEncStackV kit ikit) ∗
        A.pool lim st_init s
      post := fun (x, st_init) s0 sf =>
        ∃∗ answers : StoreAnswers (List (BitVec 8)) Unit, ∃∗ evs : List AllocEvent,
          ⌜(x.model C S uuidParse answers).1 ≠ .error .panic ∧
            kit.callsRel st0 answers (x.model C S uuidParse answers).2 ∧
            ikit.idCallsRel ist0 answers (x.model C S uuidParse answers).2 ∧
            sf.trace = s0.trace ++
              ikit.traceOfWith kit encRecord answers (x.model C S uuidParse answers).2 ∧
            WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidParse x evs⌝ ∗
          kit.storeAt x.ssA (kit.storeFinal st0 answers (x.model C S uuidParse answers).2) ∗
          ikit.identityAt x.idA (ikit.idFinal ist0 answers (x.model C S uuidParse answers).2) ∗
          apiEncResultAt A.repAlloc x.ret (x.model C S uuidParse answers).1 ∗
          nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
          protocolAddressAt A.repAlloc x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗
          FromRecordCallees.lsLogOff ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗
          A.pool lim (M.stepEvents evs st_init) sf
      onPanic := fun (x, _) s0 sf =>
        ⌜s0.trace <+: sf.trace ∧
          ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
            kit.loadRel st0 x.rem.val answers.loadSession ∧
            s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
            ((x.model C S uuidParse answers).1 = .error .panic ∨ x.sendPanics S answers)⌝ ∗
          anyHeap }

def OtrStateVBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x) st_init st
    (FromOtrEnv C S sendEnv parse kit kitEnv st0 ikit ikitEnv ist0 x sess otr taken) ∧
  OtrStateVPlaced (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 Scope ctl encRecord
    x r sess otr taken pqCap pqPtr R s0 s

def KeyStateVBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x) st_init st
    (FromKeyEnv C S sendEnv parse kit kitEnv st0 ikit ikitEnv ist0 x sess otr taken k) ∧
  KeyStateVPlaced (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 Scope ctl encRecord
    x r sess otr taken pqCap pqPtr k R s0 s

def CmStateVBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (m : CiphertextMessage) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x) st_init st
    (FromCmEnv kit kitEnv st0 ikit ikitEnv ist0 x sess otr' taken k) ∧
  CmStateVPlaced (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 Scope C ctl parse S encRecord
    x r sess otr taken k m otr' pqCap' pqPtr' R s0 s

def SaveStateVBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (m : CiphertextMessage) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x) st_init st
    (FromSaveEnv kit kitEnv st0 ikit ikitEnv
      (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x sess otr' taken k) ∧
  SaveStateVPlaced (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 Scope C ctl parse S encRecord
    x r sess otr taken k m otr' pqCap' pqPtr' R s0 s

def ApplyStateVBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (m : CiphertextMessage) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (c : IdentityChange) (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x) st_init st
    (FromApplyEnv kit kitEnv st0 x sess otr' taken) ∧
  ApplyStateVPlaced (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 Scope C ctl parse S encRecord
    x r sess otr taken k m otr' pqCap' pqPtr' c R s0 s

/-- Budget-threaded error-tail entry state (`FreeOnlyEvs` remaining to exit). -/
def EncTailVBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (answers : StoreAnswers (List (BitVec 8)) Unit)
    (pc : BitVec 64) (regs : BitVec 64 → State → Prop) (slots : BitVec 64 → SepProp) (R : SepProp)
    (s0 s : State) : Prop :=
  SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x) st_init st FreeOnlyEvs ∧
  EncTailVPlaced (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 C ctl parse S
    x answers pc regs slots R s0 s

/-- Budget-threaded segment-exit relation on `lsProg_198 H`. -/
def SegExitBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (x : WithStoresEncGhost) (st_init : M.σ) (R : SepProp) (s0 s : State)
    (next : State → Prop) : Prop :=
  (lsProg_198 H).CodeLoaded s.mem →
    ∃ sf, Steps (lsProg_198 H) s sf ∧
      (next sf ∨
        SubroutineOutcome
          (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord)
          (x, st_init) R s0 sf)

theorem SegExitBudget.next [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {st_init : M.σ} {R : SepProp}
    {s0 s : State} {next : State → Prop} (h : next s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R s0 s next :=
  fun _ => ⟨s, Steps.refl s, Or.inl h⟩

theorem SegExitBudget.of_false [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {st_init : M.σ} {R : SepProp}
    {s0 s : State} {next : State → Prop}
    (h : SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R s0 s (fun _ => False)) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R s0 s next := by
  intro hL
  obtain ⟨sf, hsteps, hfalse | hout⟩ := h hL
  · exact False.elim hfalse
  · exact ⟨sf, hsteps, Or.inr hout⟩

theorem SegExitBudget.of_sepWP [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {st_init : M.σ} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {mid : BitVec 64} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hm : s.mem ⊨ P ∗ (F ∗ R))
    (hwp : SepWP (lsProg_198 Hk) mid s P post)
    (hcont : ∀ sm Pm, (lsProg_198 Hk).CodeLoaded s.mem →
      Steps (lsProg_198 Hk) s sm →
      sm.pc = mid → sm.status = .Running → (sm.mem ⊨ Pm ∗ (F ∗ R)) →
      post sm Pm →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
        x st_init R0 s0 sm next) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s next := by
  intro hL
  obtain ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hpost⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left
  · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ := hcont sm Pm hL hsteps hpc hrun hmm hpost (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

theorem SegExitBudget.call {α : Type} [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {st_init : M.σ} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (lsProg_198 Hk) entry spec)
    (xc : α) {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hm : s.mem ⊨ spec.pre xc s ∗ (F ∗ R))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit xc code s sf ∗ R') → False)
    (hpanic : ∀ sf, Steps (lsProg_198 Hk) s sf → sf.status = .Panicked →
      (sf.mem ⊨ (spec.onPanic xc s sf ∗ F) ∗ R) →
      (sf.mem ⊨ (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
        C ctl uuidTryParse S sendEnv encRecord).onPanic (x, st_init) s0 sf ∗ R0))
    (hnext : ∀ sm : State, (lsProg_198 Hk).CodeLoaded s.mem →
      Steps (lsProg_198 Hk) s sm →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm →
      (sm.mem ⊨ (spec.post xc s sm ∗ F) ∗ R) →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
        x st_init R0 s0 sm next)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom xc s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s next := by
  intro hL
  have hwpp : SepWPp (lsProg_198 Hk) ret_pc s (spec.pre xc s ∗ F)
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ Pm = spec.post xc s sm ∗ F)
      (fun sf Pf => Pf = spec.onPanic xc s sf ∗ F) :=
    SepWPp.call (x := xc) (F := F) hcall hpc hrun hsp hlr
      (fun _ h => by rwa [sepConj_assoc] at h) hexit (fun _ _ => rfl)
      (fun _ hpcm hrunm hspm hcsm => SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sf R' hst hmem => False.elim (hoom sf (F ∗ R') hst hmem))
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, _, hpost, hspm, hcsm, rfl⟩ | ⟨hpan, _, hpost, rfl⟩ | ⟨_, hoom_f⟩⟩ :=
    hwpp R (by rwa [← sepConj_assoc] at hm) hL
  · obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hL hsteps hpcm hrunm hspm hcsm hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, hpanic sm hsteps hpan hpost⟩))⟩
  · exact (not_satisfies_false_sepConj hoom_f).elim

/-- Budget-threaded segment environment for `MessageEncrypt` on `lsProg_198 H`. -/
structure EncEnvBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop where
  hooks : PublicApiEncHooksBudget A lim H
  ikitOk : IdentityStoreKitBudgetOkI A lim ikit ikitEnv H
  callees : EncCalleesBudget Q C A lim ctl parse S sendEnv H
  vtables : SessionOnlyVtablesPlacedOk kit
  idVtables : IdentityVtablesPlacedOk ikit
  scopeIn : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))),
    kit.ScopeAt Scope st0 rem r → RecordInScopeEnc r
  scopeQ : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))) (s : Session (List (BitVec 8))),
    kit.ScopeAt Scope st0 rem r → r.currentSession = some s → Q s.state.pqRatchetState
  recOk : ∀ {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
    {otr' : OutgoingTripleRatchet (List (BitVec 8))},
    StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S parse x r sess otr taken k m otr' →
    kit.RecOk (storedRecord sess otr' taken)
  tailDropRecord :
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State)
      (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
      (w0 w1 w2 w3 w4 w5 : BitVec 64) (Hp : SepProp) (scratch : BitVec 64 → SepProp),
      (scratch = curScratch ∨ scratch = cmScratch) →
      ∀ (g : RecordGhost) (rec : SessionRecord (List (BitVec 8)))
        (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8)))),
        TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s →
        SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] Hp →
        EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv x st_init st answers
          (encEntryPlaced + 0x46c#64) (tailRegs w0 w1 w2)
          (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot none
            (pollWith sp 0x9d0 [w3, w4, w5]) ∗ Hp) R s0 s →
        SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
          x st_init R s0 s (fun _ => False)
  tailSignalEncryptErr :
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State)
      (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
      (w0 w1 w2 w3 w4 w5 : BitVec 64) (Hp : SepProp) (scratch : BitVec 64 → SepProp),
      (scratch = curScratch ∨ scratch = cmScratch) →
      ∀ (g : RecordGhost) (rec : SessionRecord (List (BitVec 8)))
        (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8)))),
        TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s →
        SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] Hp →
        EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv x st_init st answers
          (encEntryPlaced + 0xc14#64) (tailRegs w0 w1 w2)
          (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot none
            (pollWith sp 0xb00 [w3, w4, w5]) ∗ Hp) R s0 s →
        SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
          x st_init R s0 s (fun _ => False)
  tailCmDrop :
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State)
      (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
      (w0 w1 w2 w3 w4 w5 : BitVec 64) (Hp : SepProp) (scratch : BitVec 64 → SepProp),
      (scratch = curScratch ∨ scratch = cmScratch) →
      ∀ (g : RecordGhost) (rec : SessionRecord (List (BitVec 8)))
        (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
        (m : CiphertextMessage),
        TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s →
        SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] Hp →
        EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv x st_init st answers
          (encEntryPlaced + 0xd40#64) (tailRegs w0 w1 w2)
          (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot (some m)
            (pollWith sp 0x9d0 [w3, w4, w5]) ∗ Hp) R s0 s →
        SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
          x st_init R s0 s (fun _ => False)
  tailStoreHookErr :
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State)
      (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
      (w0 w1 w2 w3 w4 w5 : BitVec 64) (Hp : SepProp) (scratch : BitVec 64 → SepProp),
      (scratch = curScratch ∨ scratch = cmScratch) →
      ∀ (g : RecordGhost) (rec : SessionRecord (List (BitVec 8)))
        (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
        (m : CiphertextMessage) (pcOff src : Nat),
        ((pcOff, src) = (0xc20, 0x970) ∨ (pcOff, src) = (0xe28, 0x990) ∨
          (pcOff, src) = (0xf2c, 0x9b0)) →
        TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s →
        SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] Hp →
        EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv x st_init st answers
          (encEntryPlaced + BitVec.ofNat 64 pcOff) (tailRegs w0 w1 w2)
          (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot (some m)
            (pollWith sp src [w3, w4, w5]) ∗ Hp) R s0 s →
        SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
          x st_init R s0 s (fun _ => False)

theorem EncEnvBudget.q_otr [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    (env : EncEnvBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord H)
    {rem : AddrVal} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} (hcur : r.currentSession = some sess)
    (hsc : kit.ScopeAt Scope st0 rem r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken)) :
    Q otr.pqrState :=
  fromSessionState_pqrState hfrom ▸ env.scopeQ r sess hsc hcur

def SegIdentitySpecVBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (H : LibsignalHooks) : Prop :=
  EncEnvBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H →
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (R : SepProp) (s0 s : State),
      OtrStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
        x st_init st r sess otr taken pqCap pqPtr R s0 s →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
        x st_init R s0 s (fun s' => ∃ k,
          KeyStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
            x st_init st r sess otr taken pqCap pqPtr k R s0 s')

def SegSignalSpecVBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (H : LibsignalHooks) : Prop :=
  EncEnvBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H →
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
      (R : SepProp) (s0 s : State),
      sess.pendingPreKey = none →
      KeyStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
        x st_init st r sess otr taken pqCap pqPtr k R s0 s →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
        x st_init R s0 s (fun s' => ∃ st' m otr' pqCap' pqPtr',
          CmStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
            x st_init st' r sess otr taken k m otr' pqCap' pqPtr' R s0 s')

def SegTrustSpecVBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (H : LibsignalHooks) : Prop :=
  EncEnvBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H →
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64) (R : SepProp) (s0 s : State),
      ikit.addrOk x.rem.val → EncFsCtxPlaced kit ikit H s0 s →
      CmStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
        x st_init st r sess otr taken k m otr' pqCap' pqPtr' R s0 s →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
        x st_init R s0 s (fun s' => ∃ st',
          SaveStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
            x st_init st' r sess otr taken k m otr' pqCap' pqPtr' R s0 s')

def SegSaveSpecVBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (H : LibsignalHooks) : Prop :=
  EncEnvBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H →
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64) (R : SepProp) (s0 s : State),
      ikit.addrOk x.rem.val → EncFsCtxPlaced kit ikit H s0 s →
      SaveStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
        x st_init st r sess otr taken k m otr' pqCap' pqPtr' R s0 s →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
        x st_init R s0 s (fun s' => ∃ st' c,
          ApplyStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
            x st_init st' r sess otr taken k m otr' pqCap' pqPtr' c R s0 s')

/-! ## `FitsEnv` Non-Vacuity Witnesses -/

def witnessRustAlloc : RustAlloc := ⟨.emp, fun _ _ _ => .emp⟩
def witnessKit : SessionStoreSpec witnessRustAlloc 0#64 := hookSessionStoreSpec witnessRustAlloc 0#64
def witnessKitEnv : SessionStoreBudgetEnv witnessKit :=
  ⟨fun _ _ evs => evs = rustAllocEvents 16 1, fun _ _ _ evs => evs = rustAllocEvents 16 1⟩
def witnessIkit : IdentityStoreSpec witnessRustAlloc 0#64 := hookIdentityStoreSpec witnessRustAlloc 0#64
def witnessIkitEnv : IdentityStoreBudgetEnv witnessIkit :=
  ⟨fun _ _ _ _ evs => evs = rustAllocEvents 16 1, fun _ _ _ evs => evs = rustAllocEvents 16 1⟩
def witnessPendingPreKey : PendingPreKey := ⟨some 2#32, 3#32, witnessPublicKey, 0#64⟩
def witnessEncSession : Session (List (BitVec 8)) :=
  { state := ⟨4#32, witnessIdentityKey, some witnessIdentityKey, 0#256, 0#32,
      some ⟨witnessKeyPair, ⟨0#256, 0#32⟩⟩, [], true, [1#8]⟩
    pendingPreKey := some witnessPendingPreKey, pendingKyberPreKey := some ⟨4#32, [0x44#8]⟩
    localRegistrationId := 1#32, remoteRegistrationId := 2#32, aliceBaseKey := [0x45#8] }
def witnessEncRecord : SessionRecord (List (BitVec 8)) := ⟨some witnessEncSession⟩
def witnessWithStoresGhost : WithStoresEncGhost :=
  ⟨⟨0#64, 0#64, [0x41#8], 0#64, witnessAddrGhost, 0#64, witnessAddrGhost,
    SystemTime.unixEpoch, 0#64, [0x42#8]⟩, 0#64, 0#64⟩

theorem encode_protoMsg_small_length_le (parse : UuidParser) (x : SignalMessageNewGhost) :
    (encode (x.protoMsg parse)).length ≤ 117 + x.ciphertext.length + x.pqRatchet.length := by
  unfold encode
  have hf1 : encodeBytesField 1 (x.protoMsg parse).ratchetKey =
      [0x0a#8, 0x21#8] ++ x.senderRatchetKey.serialize := by
    simp [SignalMessageNewGhost.protoMsg, encodeBytesField, publicKey_serialize_length,
      encodeKey_1_ld, encodeVarint_33]
  have hf2 : encodeUint32Field 2 (x.protoMsg parse).counter =
      [0x10#8] ++ encodeVarint (x.counter.zeroExtend 64) := by
    simp [SignalMessageNewGhost.protoMsg, encodeUint32Field, encodeKey_2_varint]
  have hf3 : encodeUint32Field 3 (x.protoMsg parse).previousCounter =
      [0x18#8] ++ encodeVarint (x.previousCounter.zeroExtend 64) := by
    simp [SignalMessageNewGhost.protoMsg, encodeUint32Field, encodeKey_3_varint]
  have hf4 : encodeBytesField 4 (x.protoMsg parse).ciphertext =
      [0x22#8] ++ encodeVarint (BitVec.ofNat 64 x.ciphertext.length) ++ x.ciphertext := by
    simp [SignalMessageNewGhost.protoMsg, encodeBytesField, encodeKey_4_ld]
  rw [hf1, hf2, hf3, hf4]
  have hrk := publicKey_serialize_length x.senderRatchetKey
  have ⟨_, hv2⟩ := signalMessageNew_encodeVarint_length_bounds (x.counter.zeroExtend 64)
  have ⟨_, hv3⟩ := signalMessageNew_encodeVarint_length_bounds (x.previousCounter.zeroExtend 64)
  have ⟨_, hv4⟩ := signalMessageNew_encodeVarint_length_bounds (BitVec.ofNat 64 x.ciphertext.length)
  have hpq_len : (encodeBytesField 5 (x.protoMsg parse).pqRatchet).length ≤ 11 + x.pqRatchet.length := by
    by_cases hpq0 : x.pqRatchet = []
    · simp [SignalMessageNewGhost.protoMsg, hpq0, encodeBytesField]
    · have hemp : x.pqRatchet.isEmpty = false := List.isEmpty_eq_false_iff.mpr hpq0
      have ⟨_, hv5⟩ := signalMessageNew_encodeVarint_length_bounds (BitVec.ofNat 64 x.pqRatchet.length)
      have hf5 : encodeBytesField 5 (x.protoMsg parse).pqRatchet =
          [0x2a#8] ++ encodeVarint (BitVec.ofNat 64 x.pqRatchet.length) ++ x.pqRatchet := by
        simp [SignalMessageNewGhost.protoMsg, hemp, encodeBytesField, encodeKey_5_ld]
      rw [hf5]
      simp only [List.length_append, List.length_singleton]
      omega
  have had_len : (encodeBytesField 6 (x.protoMsg parse).addresses).length ≤ 38 := by
    cases had : x.addresses parse with
    | none => simp [SignalMessageNewGhost.protoMsg, had, encodeBytesField]
    | some ad =>
      have hlen : ad.length = 36 := by
        simp only [SignalMessageNewGhost.addresses] at had
        cases hx : x.loc with
        | none => simp [hx] at had
        | some l => simp only [hx, Option.bind_some] at had; exact serializeAddresses_length had
      simp [SignalMessageNewGhost.protoMsg, had, hlen, encodeBytesField, encodeKey_6_ld, encodeVarint_36]
  simp only [List.length_append, List.length_cons, List.length_nil, hrk]
  omega

theorem boxAllocEnv_phaseCreditSpec {sz : Nat} (hsz : sz ≤ 32) :
    PhaseCreditSpec fineCostModel (BoxAllocEnv sz) 9603 8227 8227 32 :=
  (PhaseCreditSpec.or_of_imp (fun _ h => h)
    ((PhaseCreditSpec.nil fineCostModel).of_imp fun _ h => h.2)
    ((PhaseCreditSpec.rustAlloc_aff fineCostModel_modelHyps (req := sz) (al := 8) (by decide)).of_imp
      fun _ h => h.2)).mono (by omega) (by omega) (by omega) (by omega)

theorem fromCurBody_phaseCreditSpec :
    PhaseCreditSpec fineCostModel
      (SeqEnv FreeOnlyEvs
        (fun evs' =>
          FreeOnlyEvs evs' ∨
          ∃ r sess otr taken,
            witnessKit.ScopeAt (· = witnessEncRecord) () witnessWithStoresGhost.rem.val r ∧
            r.currentSession = some sess ∧
            execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) ∧
            FromOtrEnv witnessCrypto witnessSpqrModel witnessSendEnv witnessUuidParse
              witnessKit witnessKitEnv () witnessIkit witnessIkitEnv ()
              witnessWithStoresGhost sess otr taken evs'))
      320000 270000 270000 512 := by
  have hfr := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hp16 := PhaseCreditSpec.rustAlloc_aff fineCostModel_modelHyps (req := 16) (al := 1) (by decide)
  have hd32 := PhaseCreditSpec.rustDealloc fineCostModel_modelHyps.freeNonInc 32 8
  have hb32 := boxAllocEnv_phaseCreditSpec (sz := 32) (by decide)
  have hsc : PhaseCreditSpec fineCostModel (StringCloneEnv witnessWithStoresGhost.rem.name)
      9541 8196 8196 1 :=
    (PhaseCreditSpec.or_of_imp (fun _ h => h)
      ((PhaseCreditSpec.nil fineCostModel).of_imp fun _ h => h.2)
      ((PhaseCreditSpec.rustAlloc_aff fineCostModel_modelHyps
        (req := witnessWithStoresGhost.rem.name.bytes.length) (al := 1) (by decide)).of_imp
        fun _ h => h.2)).mono (by decide) (by decide) (by decide) (by decide)
  have hscFr := hsc.seq hfr
  have hcm (otr' : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8))) :
      PhaseCreditSpec fineCostModel
        (FromCmEnv witnessKit witnessKitEnv () witnessIkit witnessIkitEnv ()
          witnessWithStoresGhost witnessEncSession otr' taken witnessIdentityKey)
        70000 60000 60000 32 := by
    have hap : PhaseCreditSpec fineCostModel
        (FromApplyEnv witnessKit witnessKitEnv () witnessWithStoresGhost witnessEncSession otr' taken)
        29000 25000 25000 32 :=
      ((otrApplyEnv_phaseCreditSpec fineCostModel_modelHyps).seq
        (hb32.seq (hp16.seq (hd32.seq hfr)))).mono (by decide) (by decide) (by decide) (by decide)
    have hsv : PhaseCreditSpec fineCostModel
        (FromSaveEnv witnessKit witnessKitEnv () witnessIkit witnessIkitEnv ()
          witnessWithStoresGhost witnessEncSession otr' taken witnessIdentityKey)
        49000 42000 42000 32 :=
      ((hb32.seq (hp16.seq hd32)).seq (hfr.or hap)).mono (by decide) (by decide) (by decide) (by decide)
    exact ((hb32.seq (hp16.seq hd32)).seq (hfr.or (hscFr.or hsv))).mono
      (by decide) (by decide) (by decide) (by decide)
  let g0 := otrSignalMsgGhost witnessCrypto witnessOtr none [2#8]
    witnessWithStoresGhost.ptext (some witnessWithStoresGhost.loc) witnessWithStoresGhost.rem
  have hg0_ct : g0.ciphertext.length ≤ 16 := by decide
  have hg0_pq : g0.pqRatchet.length ≤ 1 := by decide
  have hg0_enc : (encode (g0.protoMsg witnessUuidParse)).length + 9 ≤ 160 := by
    have h := encode_protoMsg_small_length_le witnessUuidParse g0
    omega
  have henc : PhaseCreditSpec fineCostModel
      (OtrEncryptCoreEnv witnessCrypto witnessSpqrModel witnessSendEnv witnessUuidParse
        witnessOtr witnessWithStoresGhost.ptext (some witnessWithStoresGhost.loc)
        witnessWithStoresGhost.rem witnessWithStoresGhost.rest)
      118000 101000 101000 256 := by
    refine (otrEncryptCoreEnv_phaseCreditSpec_bounded fineCostModel_modelHyps
      witnessCrypto witnessSpqrModel witnessSendEnv witnessUuidParse
      witnessOtr witnessWithStoresGhost.ptext (some witnessWithStoresGhost.loc)
      witnessWithStoresGhost.rem witnessWithStoresGhost.rest 256
      hp16 (by decide) (fun st' pqrKey pqrMsg hS => ?_)).mono
      (by decide) (by decide) (by decide) (by decide)
    change some ([1#8], none, [2#8]) = some (st', pqrKey, pqrMsg) at hS
    injection hS with ht; injection ht with h1 h23; injection h23 with h2 h3
    subst h1 h2 h3
    change g0.ciphertext.length ≤ 256 ∧ g0.pqRatchet.length ≤ 256 ∧
      (encode (g0.protoMsg witnessUuidParse)).length + 9 ≤ 256
    exact ⟨by omega, by omega, by omega⟩
  have hprePost (taken : SessionState (List (BitVec 8))) :
      PhaseCreditSpec fineCostModel
        (PreKeyPostEncryptEnv witnessCrypto witnessSpqrModel witnessUuidParse
          witnessKit witnessKitEnv () witnessIkit witnessIkitEnv ()
          witnessWithStoresGhost witnessEncSession witnessOtr taken witnessIdentityKey witnessPendingPreKey)
        130000 110000 110000 512 := by
    let res := Mut.exec (OutgoingTripleRatchet.encrypt witnessCrypto protoSignalCodec
      witnessSpqrModel.spqr witnessWithStoresGhost.ptext
      (serializeAddresses (serviceIdParse witnessUuidParse)
        witnessWithStoresGhost.loc witnessWithStoresGhost.rem)
      witnessWithStoresGhost.rest) witnessOtr
    have hpreBody : PhaseCreditSpec fineCostModel
        (fun evs' => match res.1 with
          | .error _ => False
          | .ok sm => SeqEnv (PreKeyMsgNewRawEnv (pendingKyberPayload witnessEncSession)
              sm.serialized.length (preKeyMsgFromItems witnessEncSession witnessPendingPreKey res.2 sm).serialized.length)
              (fun evs'' => FreeOnlyEvs evs'' ∨
                FromCmEnv witnessKit witnessKitEnv () witnessIkit witnessIkitEnv ()
                  witnessWithStoresGhost witnessEncSession res.2 taken witnessIdentityKey evs'') evs')
        130000 110000 110000 512 := by
      cases hres : res.1 with
      | error _ =>
        exact ((PhaseCreditSpec.nil fineCostModel).of_imp fun _ h => False.elim h).mono
          (by decide) (by decide) (by decide) (by decide)
      | ok sm =>
        have hsm : sm.serialized.length ≤ 160 := by
          have hresEq : res =
              (match witnessOtr.senderChainKey.nextChainKey witnessCrypto.F with
               | .error e => (.error e, witnessOtr)
               | .ok next =>
                 (.ok (SignalMessage.new witnessCrypto.F protoSignalCodec witnessOtr.sessionVersion
                   ((witnessOtr.senderChainKey.messageKeys witnessCrypto.F).generateKeys witnessCrypto.F none).macKey
                   (serializeAddresses (serviceIdParse witnessUuidParse)
                     witnessWithStoresGhost.loc witnessWithStoresGhost.rem)
                   witnessOtr.senderRatchetKey.publicKey witnessOtr.senderChainKey.index
                   witnessOtr.previousCounter g0.ciphertext
                   witnessOtr.localIdentityKey witnessOtr.remoteIdentityKey [2#8]),
                  { witnessOtr with senderChainKey := next, pqrState := [1#8] })) := rfl
          have hres1 := congrArg Prod.fst hresEq
          rw [hres] at hres1
          cases hnk : witnessOtr.senderChainKey.nextChainKey witnessCrypto.F with
          | error e => rw [hnk] at hres1; cases hres1
          | ok next =>
            rw [hnk] at hres1; injection hres1 with hsmEq; subst hsmEq
            dsimp only [SignalMessage.new]
            rw [List.length_append, signalMessageNew_computeMac_length]
            have hser : (serializeContent protoSignalCodec witnessOtr.sessionVersion
                witnessOtr.senderRatchetKey.publicKey witnessOtr.senderChainKey.index
                witnessOtr.previousCounter g0.ciphertext [2#8]
                (serializeAddresses (serviceIdParse witnessUuidParse)
                  witnessWithStoresGhost.loc witnessWithStoresGhost.rem)).length =
                1 + (encode (g0.protoMsg witnessUuidParse)).length := by
              simp [serializeContent, protoSignalCodec, SignalMessageNewGhost.protoMsg,
                SignalMessageNewGhost.addresses, otrSignalMsgGhost, g0]
              omega
            omega
        have hout : (preKeyMsgFromItems witnessEncSession witnessPendingPreKey res.2 sm).serialized.length ≤ 512 := by
          have h := preKeySignalMessage_new_small_length_le
            res.2.sessionVersion witnessEncSession.localRegistrationId
            witnessPendingPreKey.preKeyId witnessPendingPreKey.signedPreKeyId
            (pendingKyberPayload witnessEncSession) witnessPendingPreKey.baseKey
            res.2.localIdentityKey sm
            (by decide) (by rintro _ ⟨⟩; decide) (by decide) (by rintro _ ⟨⟩; decide)
          have hky1 : kyberPayloadLen (pendingKyberPayload witnessEncSession) = 1 := rfl
          change (PreKeySignalMessage.new res.2.sessionVersion witnessEncSession.localRegistrationId
            witnessPendingPreKey.preKeyId witnessPendingPreKey.signedPreKeyId
            (pendingKyberPayload witnessEncSession) witnessPendingPreKey.baseKey
            res.2.localIdentityKey sm).serialized.length ≤ 512
          omega
        have hmono : ∀ sL oL : Nat, sL ≤ 160 → oL ≤ 512 →
            (2 * 1 + 2 * sL + 2 * oL + 47827) + 70000 ≤ 130000 ∧
            (1 + sL + oL + 41041) + 60000 ≤ 110000 ∧
            max (1 + sL + oL + 41041) (1 + sL + oL + 41041 + 60000) ≤ 110000 ∧
            max (max (max 1 33) (max sL oL)) 32 ≤ 512 := by omega
        obtain ⟨hm1, hm2, hm3, hm4⟩ := hmono sm.serialized.length
          (preKeyMsgFromItems witnessEncSession witnessPendingPreKey res.2 sm).serialized.length hsm hout
        exact ((preKeyMsgNewRawEnv_phaseCreditSpec fineCostModel_modelHyps
          (pendingKyberPayload witnessEncSession) sm.serialized.length
          (preKeyMsgFromItems witnessEncSession witnessPendingPreKey res.2 sm).serialized.length).seq
          (hfr.or (hcm res.2 taken))).mono hm1 hm2 hm3 hm4
    unfold PreKeyPostEncryptEnv
    exact (hfr.or hpreBody).mono (by decide) (by decide) (by decide) (by decide)
  have hky := kyberOptEnv_phaseCreditSpec fineCostModel_modelHyps
    (witnessEncSession.pendingKyberPreKey.map (·.ciphertext))
  let htaken := { witnessEncSession.state with pqRatchetState := ([] : List (BitVec 8)) }
  have hex : PhaseCreditSpec fineCostModel
      (fun evs' => ∃ r sess otr taken,
        witnessKit.ScopeAt (· = witnessEncRecord) () witnessWithStoresGhost.rem.val r ∧
        r.currentSession = some sess ∧
        execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) ∧
        FromOtrEnv witnessCrypto witnessSpqrModel witnessSendEnv witnessUuidParse
          witnessKit witnessKitEnv () witnessIkit witnessIkitEnv ()
          witnessWithStoresGhost sess otr taken evs')
      320000 270000 270000 512 := by
    refine ((hfr.or (hscFr.or (hky.seq (henc.seq (hprePost htaken))))).of_imp ?_).mono
      (by decide) (by decide) (by decide) (by decide)
    rintro evs' ⟨r, sess, otr, taken, ⟨rfl, -⟩, hcur, hexec, hotr⟩
    injection hcur with hcur'; subst hcur'
    have hexec0 : execOk OutgoingTripleRatchet.fromSessionState witnessEncSession.state =
        .ok (witnessOtr, htaken) := rfl
    rw [hexec0] at hexec; injection hexec with hp; injection hp with ho ht; subst ho ht
    rcases hotr with hfree | ⟨k, hk, hkey⟩
    · exact Or.inl hfree
    · injection hk with hk'; subst hk'
      rcases hkey with ⟨hnone, _⟩ | ⟨items, hsome, hbody⟩
      · cases hnone
      · injection hsome with hi; subst hi; exact Or.inr hbody
  exact (hfr.seq (hfr.or hex)).mono (by decide) (by decide) (by decide) (by decide)

/-- Non-vacuity witness showing `WithStoresEncEnv` fits within concrete `BudgetLimits` under
`fineCostModel`. -/
theorem withStoresEncEnv_fitsEnv_witness :
    FitsEnv fineCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024,
        physCap := 2 ^ 30, enforced := true }
      fineCostModel.init
      (WithStoresEncEnv witnessKit witnessKitEnv () witnessIkit witnessIkitEnv ()
        (· = witnessEncRecord) witnessCrypto witnessSpqrModel witnessSendEnv witnessUuidParse
        witnessWithStoresGhost) := by
  have hfr := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hp16 := PhaseCreditSpec.rustAlloc_aff fineCostModel_modelHyps (req := 16) (al := 1) (by decide)
  have hd24 := PhaseCreditSpec.rustDealloc fineCostModel_modelHyps.freeNonInc 24 8
  have hload := (boxAllocEnv_phaseCreditSpec (sz := 24) (by decide)).seq (hp16.seq hd24)
  have hsc : PhaseCreditSpec fineCostModel (StringCloneEnv witnessWithStoresGhost.rem.name)
      9541 8196 8196 1 :=
    (PhaseCreditSpec.or_of_imp (fun _ h => h)
      ((PhaseCreditSpec.nil fineCostModel).of_imp fun _ h => h.2)
      ((PhaseCreditSpec.rustAlloc_aff fineCostModel_modelHyps
        (req := witnessWithStoresGhost.rem.name.bytes.length) (al := 1) (by decide)).of_imp
        fun _ h => h.2)).mono (by decide) (by decide) (by decide) (by decide)
  have hSpec : PhaseCreditSpec fineCostModel
      (WithStoresEncEnv witnessKit witnessKitEnv () witnessIkit witnessIkitEnv ()
        (· = witnessEncRecord) witnessCrypto witnessSpqrModel witnessSendEnv witnessUuidParse
        witnessWithStoresGhost)
      340000 287000 287000 512 :=
    (hload.seq (hfr.or ((hsc.seq hfr).or fromCurBody_phaseCreditSpec))).mono
      (by decide) (by decide) (by decide) (by decide)
  refine fitsEnv_fineCostModel_of_phaseCredit hSpec (by decide) rfl ?_ ?_
  · unfold fineStepReserveOfCum FineStepBound fineMaxMetaAreasOfCum pageAlignUp PAGE_SIZE
    decide
  · unfold fineStepReserveOfCum FineStepBound fineMaxMetaAreasOfCum fineDynIvsOfCum
      fineMaxGroupsOfCum pageAlignUp MMAP_MIN_ADDR PAGE_SIZE
    decide

end TempTwins

open TempTwins

/-! ## `SegExitBudget` Combinators and Panic Bridge -/

theorem SegExitBudget.step_left [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {ctl : BitVec 64} {S : SpqrModel}
    {sendEnv : SpqrSendBudgetEnv} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {st_init : M.σ} {R : SepProp} {s0 s sm : State}
    {next : State → Prop} (hsteps : Steps (lsProg_198 Hk) s sm)
    (h : SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk x st_init R s0 sm next) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk x st_init R s0 s next := by
  intro hL; obtain ⟨sf, hsteps', hout⟩ := h (hsteps.codeLoaded hL); exact ⟨sf, hsteps.trans hsteps', hout⟩

/-- Under `FitsEnv`, budget-threaded shims, polls, and `String::clone` have `onPanic = ⌜False⌝`,
vacuously entailing `withStoresEncBudgetSpecV.onPanic`. -/
theorem alloc_onPanic_entails_placed [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {ctl : BitVec 64} {S : SpqrModel}
    {sendEnv : SpqrSendBudgetEnv} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {st_init : M.σ} {s0 sf : State} {F R R0 : SepProp} :
    (⌜False⌝ ∗ F) ∗ R ⊢
      (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord).onPanic
        (x, st_init) s0 sf ∗ R0 := by
  rw [sepConj_assoc]; exact Entails.pure_left fun h => False.elim h

/-! ## External Hook Projections on `lsProg_198 Hk` -/

theorem dealloc_placed_ok_at_enc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop} {C : Crypto}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    (env : EncEnvBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk) :
    subroutine_ok (lsProg_198 Hk) (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem (by decide : lsRustDeallocSym ∈ libsignalSessionExterns)
  exact ls_hook_ok (k := k) (by simp [hk, hget]) env.hooks.dealloc

section StringCloneEncProof
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
open SepProp ProofLib.SepLogic
open ProofLib.StdStartup (hasInstrs)
open ProofLib.StdStartup.Stage1Internal (step_str64_perm)
open LibsignalBinary.Proofs.Common.StringCloneFlat (rustStringCloneInstrs)
open LibsignalBinary.Proofs.Common.StringClonePlaced
  (lsRustNoAllocShimPlacedSym lsRustAllocPlacedSym lsProg_623 lsProg_623_hasInstrs)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsRetAddr624_base_add)

private theorem bv_sub_add_cancel48 (sp : BitVec 64) : sp - 48#64 + 48#64 = sp := by bv_omega
private theorem bv_add_neg48 (sp : BitVec 64) : sp + (-48#64) = sp - 48#64 := by bv_omega
private theorem bv_add_neg16 (sp : BitVec 64) : sp + (-16#64) = sp - 16#64 := by bv_omega

@[local simp, local arm64_norm]
private theorem setMem_setMem_eq (s : State) (m1 m2 : Memory) :
    (s.setMem m1).setMem m2 = s.setMem m2 := by cases s; rfl
@[local simp, local arm64_norm]
private theorem setPC_setMem_eq (s : State) (m : Memory) (pc : BitVec 64) :
    (s.setMem m).setPC pc = (s.setPC pc).setMem m := by cases s; rfl
@[local simp, local arm64_norm]
private theorem mem_setMem_eq (s : State) (m : Memory) : (s.setMem m).mem = m := by cases s; rfl
@[local simp, local arm64_norm]
private theorem mem_setPC_eq (s : State) (pc : BitVec 64) : (s.setPC pc).mem = s.mem := by
  cases s; rfl
@[local simp, local arm64_norm]
private theorem mem_advancePC_eq (s : State) : s.advancePC.mem = s.mem := by
  cases s; rfl
@[local simp, local arm64_norm]
private theorem mem_setPState_eq (s : State) (ps : PState) : (s.setPState ps).mem = s.mem := by
  cases s; rfl
@[local simp, local arm64_norm]
private theorem mem_writeReg64_eq (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).mem = s.mem := by cases s; cases r <;> rfl
@[local simp, local arm64_norm]
private theorem mem_writeReg32_eq (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).mem = s.mem := mem_writeReg64_eq s r _
@[local simp, local arm64_norm]
private theorem mem_writeReg_eq (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).mem = s.mem := mem_writeReg64_eq s r _

@[local simp]
private theorem brkStart_setMem (s : State) (m : Memory) : (s.setMem m).brkStart = s.brkStart := by
  cases s; rfl
@[local simp]
private theorem brkStart_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).brkStart = s.brkStart := by
  cases s; rfl
@[local simp]
private theorem brkStart_advancePC (s : State) : s.advancePC.brkStart = s.brkStart := by
  cases s; rfl
@[local simp]
private theorem brkStart_setPState (s : State) (ps : PState) :
    (s.setPState ps).brkStart = s.brkStart := by cases s; rfl
@[local simp]
private theorem brkStart_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).brkStart = s.brkStart := by cases s; cases r <;> rfl
@[local simp]
private theorem brkStart_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).brkStart = s.brkStart := brkStart_writeReg64 s r _
@[local simp]
private theorem brkStart_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).brkStart = s.brkStart := brkStart_writeReg64 s r _

@[local simp]
private theorem brk_setMem (s : State) (m : Memory) : (s.setMem m).brk = s.brk := by
  cases s; rfl
@[local simp]
private theorem brk_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).brk = s.brk := by
  cases s; rfl
@[local simp]
private theorem brk_advancePC (s : State) : s.advancePC.brk = s.brk := by
  cases s; rfl
@[local simp]
private theorem brk_setPState (s : State) (ps : PState) :
    (s.setPState ps).brk = s.brk := by cases s; rfl
@[local simp]
private theorem brk_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).brk = s.brk := by cases s; cases r <;> rfl
@[local simp]
private theorem brk_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).brk = s.brk := brk_writeReg64 s r _
@[local simp]
private theorem brk_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).brk = s.brk := brk_writeReg64 s r _

@[local simp]
private theorem tpidrEl0_setMem (s : State) (m : Memory) : (s.setMem m).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl
@[local simp]
private theorem tpidrEl0_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[local simp]
private theorem tpidrEl0_advancePC (s : State) : s.advancePC.tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl
@[local simp]
private theorem tpidrEl0_setPState (s : State) (ps : PState) :
    (s.setPState ps).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[local simp]
private theorem tpidrEl0_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).tpidrEl0 = s.tpidrEl0 := by cases s; cases r <;> rfl
@[local simp]
private theorem tpidrEl0_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).tpidrEl0 = s.tpidrEl0 := tpidrEl0_writeReg64 s r _
@[local simp]
private theorem tpidrEl0_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).tpidrEl0 = s.tpidrEl0 := tpidrEl0_writeReg64 s r _

@[local simp]
private theorem physMemAvail_setMem (s : State) (m : Memory) :
    (s.setMem m).physMemAvail = s.physMemAvail := by cases s; rfl
@[local simp]
private theorem physMemAvail_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).physMemAvail = s.physMemAvail := by cases s; rfl
@[local simp]
private theorem physMemAvail_advancePC (s : State) :
    s.advancePC.physMemAvail = s.physMemAvail := by cases s; rfl
@[local simp]
private theorem physMemAvail_setPState (s : State) (ps : PState) :
    (s.setPState ps).physMemAvail = s.physMemAvail := by cases s; rfl
@[local simp]
private theorem physMemAvail_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).physMemAvail = s.physMemAvail := by cases s; cases r <;> rfl
@[local simp]
private theorem physMemAvail_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).physMemAvail = s.physMemAvail := physMemAvail_writeReg64 s r _
@[local simp]
private theorem physMemAvail_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).physMemAvail = s.physMemAvail := physMemAvail_writeReg64 s r _

@[local simp]
private theorem fs_setMem (s : State) (m : Memory) :
    (s.setMem m).fs = s.fs := by cases s; rfl
@[local simp]
private theorem fs_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).fs = s.fs := by cases s; rfl
@[local simp]
private theorem fs_advancePC (s : State) :
    s.advancePC.fs = s.fs := by cases s; rfl
@[local simp]
private theorem fs_setPState (s : State) (ps : PState) :
    (s.setPState ps).fs = s.fs := by cases s; rfl
@[local simp]
private theorem fs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).fs = s.fs := by cases s; cases r <;> rfl
@[local simp]
private theorem fs_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).fs = s.fs := fs_writeReg64 s r _
@[local simp]
private theorem fs_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := fs_writeReg64 s r _

private theorem vmPreserved_of_fields {s0 t : State}
    (h1 : t.brkStart = s0.brkStart)
    (h2 : t.brk = s0.brk)
    (h3 : t.tpidrEl0 = s0.tpidrEl0)
    (h4 : t.physMemAvail = s0.physMemAvail)
    (h5 : t.mem.perm = s0.mem.perm)
    (h6 : t.fs = s0.fs := by first | rfl | simp [*]) :
    VmPreserved s0 t :=
  ⟨⟨h1, h2, h3⟩, h4, fun a => congrFun h5 a, LibsignalBinary.Heap.FdsHiFrame.of_fs_eq h6⟩

private theorem step_stp64_perm {prog : Program} {target_pc pc ea ea2 v1 v2 : BitVec 64}
    {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr)) (hpc : s.pc = pc)
    (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hea2 : ea + 8#64 = ea2)
    (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2)
    (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.stp .W64 rt1 rt2 addr) := hpc.symm ▸ hfetch
  let m1 := s.mem.write64 ea v1; let m2 := m1.write64 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm; have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s = s'.setMem m2 := by
    rw [← hexec]; cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized,
      applyWriteback, State.advancePC, State.setMem, State.setPC, State.writeReg64, hsp, haddr,
      hea2, hv1, hv2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m2 (funext fun a => by rw [Memory.perm_write64, Memory.perm_write64])) hm2

local macro "wp_str64 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_str64_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_sep_access); (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

local macro "wp_stp64 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_stp64_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_sep_access); (· wp_focus_close wp_sep_access)
  (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

attribute [local arm64_norm] bv_sub_add_lit bv_sub_add_cancel48 bv_add_neg48 bv_add_neg16

private theorem spAligned_sub48 {sp : BitVec 64} (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp - 48#64) &&& 15#64 == 0#64) = true := by
  revert h; bv_robdd

private theorem extHookStack_split_48 (sp : BitVec 64) :
    stackAt sp extHookStack =
      stackFrameAt sp 48 ∗
        (stackAt (sp - 48#64) allocHookStack ∗
          stackFrameAt (sp - 48#64 - 4096#64) 12240) := by
  unfold stackAt extHookStack allocHookStack
  change memRegion (sp - 16384#64) 16384 = _
  rw [← stackFrameAt_eq_memRegion sp 16384 (by decide),
      ← stackFrameAt_eq_memRegion (sp - 48#64) 4096 (by decide),
      show (16384 : Nat) = 48 + 16336 from rfl,
      stackFrameAt_split sp 48 16336 (by decide),
      show (16336 : Nat) = 4096 + 12240 from rfl,
      stackFrameAt_split (sp - 48#64) 4096 12240 (by decide)]

private theorem stackFrameAt48_eq (sp : BitVec 64) :
    stackFrameAt sp 48 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
       ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗
        ((sp - 32#64) ↦₆₄ w2) ∗ ((sp - 24#64) ↦₆₄ w3) ∗
        ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) := by
  simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]

private theorem pack_stack48 (sp w0 w1 w2 w3 w4 w5 : BitVec 64) :
    (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗
     ((sp - 32#64) ↦₆₄ w2) ∗ ((sp - 24#64) ↦₆₄ w3) ∗
     ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ⊢ stackFrameAt sp 48 := by
  rw [stackFrameAt48_eq sp]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.refl _))))))

private theorem sepWP_done_let {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = mid) (hrun : s.status = .Running)
    (h : ∀ sm, sm = s → sm.pc = mid → sm.status = .Running → SepWPp prog ret sm P Q Qp oom) :
    SepWP prog mid s P (fun sm Pm => SepWPp prog ret sm Pm Q Qp oom) oom :=
  SepWP.done hpc hrun (h s rfl hpc hrun)

private theorem memRegion24_eq_exists_pts (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, ∃∗ r2 : BitVec 64,
        (a ↦₆₄ r0) ∗ ((a + 8#64) ↦₆₄ r1) ∗ ((a + 16#64) ↦₆₄ r2)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) from rfl,
      memRegion_split a 8 (8 + 8) (by decide),
      memRegion_split (a + 8#64) 8 8 (by decide),
      ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [sepExists_sepConj_left]
  refine congrArg SepProp.sepExists (funext fun _ => ?_)
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine congrArg SepProp.sepExists (funext fun _ => ?_)
  rw [sepExists_sepConj_right, sepExists_sepConj_right]

private abbrev FetchSeq (P : Program) (fnAddr : BitVec 64) (ls : List Instr) : Prop :=
  ∀ (i : Nat) (hi : i < ls.length),
    P.fetch (fnAddr + BitVec.ofNat 64 (4 * i)) = some ls[i]

private theorem fetch_seq_at {P : Program} {fnAddr off : BitVec 64} {ls : List Instr} {inst : Instr}
    (i : Nat) (hf : FetchSeq P fnAddr ls)
    (hi : ls[i]? = some inst := by rfl)
    (hoff : BitVec.ofNat 64 (4 * i) = off := by rfl) :
    P.fetch (fnAddr + off) = some inst := by
  have hlt : i < ls.length := (List.getElem?_eq_some_iff.mp hi).1
  have h := hf i hlt
  rw [List.getElem?_eq_getElem hlt] at hi
  cases hi
  rwa [hoff] at h

private theorem fetch_seq_at0 {P : Program} {fnAddr : BitVec 64} {ls : List Instr} {inst : Instr}
    (hf : FetchSeq P fnAddr ls) (hi : ls[0]? = some inst := by rfl) :
    P.fetch fnAddr = some inst := by
  simpa using fetch_seq_at 0 hf hi rfl

private theorem vecGhostAt_bytes_lt_2pow63 {A : RustAlloc}
    {m : Memory} {g : VecGhost} {p : BitVec 64} {R : SepProp}
    (hm : m ⊨ vecGhostAt A g p ∗ R) :
    g.bytes.length < 2 ^ 63 := by
  unfold vecGhostAt vecU8At at hm
  have hPull :
      (vecHeader p g.cap g.ptr (BitVec.ofNat 64 g.bytes.length) ∗
        ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
        (if g.cap = 0 then emp
         else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
           memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))) ∗ R =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
        (vecHeader p g.cap g.ptr (BitVec.ofNat 64 g.bytes.length) ∗
          (if g.cap = 0 then emp
           else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
             memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) ∗ R) := by
    sep_ac_rfl
  rw [hPull, satisfies_pure_sepConj] at hm
  omega

private def vecGhostPayload (A : RustAlloc) (g : VecGhost) : SepProp :=
  ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
  (if g.cap = 0 then emp
   else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
     memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))

private theorem vecGhostAt_eq_header_payload (A : RustAlloc) (g : VecGhost) (p : BitVec 64) :
    vecGhostAt A g p =
      (((p ↦₆₄ g.cap) ∗ ((p + 8#64) ↦₆₄ g.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length)) ∗
        vecGhostPayload A g) := by
  unfold vecGhostAt vecU8At vecHeader vecGhostPayload; sep_ac_rfl

private def vecGhostPayloadRest (A : RustAlloc) (g : VecGhost) : SepProp :=
  ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗ A.live g.ptr g.cap.toNat 1 ∗
  memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)

private theorem vecGhostPayload_nonempty_entails (A : RustAlloc) (g : VecGhost)
    (hpos : 0 < g.bytes.length) :
    vecGhostPayload A g ⊢ (g.ptr ↦ₛ g.bytes) ∗ vecGhostPayloadRest A g := by
  unfold vecGhostPayload vecGhostPayloadRest; refine Entails.pure_left fun ⟨hle, hlt, hne⟩ => ?_
  have hcapNe : g.cap ≠ 0 := by
    intro hc0; have : g.cap.toNat = 0 := by rw [hc0]; rfl
    omega
  simp only [hcapNe, ↓reduceIte]
  have hEq :
      A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
        memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length) =
      (g.ptr ↦ₛ g.bytes) ∗ (A.live g.ptr g.cap.toNat 1 ∗
        memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) := by
    sep_ac_rfl
  rw [hEq]; exact sepConj_mono_right (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.of_eq (by sep_ac_rfl)))

private theorem vecGhostPayload_nonempty_pack (A : RustAlloc) (g : VecGhost)
    (hpos : 0 < g.bytes.length) :
    ((g.ptr ↦ₛ g.bytes) ∗ vecGhostPayloadRest A g) ⊢ vecGhostPayload A g := by
  unfold vecGhostPayloadRest vecGhostPayload
  have hPull :
      (g.ptr ↦ₛ g.bytes) ∗ (⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
        A.live g.ptr g.cap.toNat 1 ∗
        memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
        ((g.ptr ↦ₛ g.bytes) ∗ A.live g.ptr g.cap.toNat 1 ∗
          memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) := by
    sep_ac_rfl
  rw [hPull]; refine Entails.pure_left fun ⟨hle, hlt, hne⟩ => ?_
  have hcapNe : g.cap ≠ 0 := by
    intro hc0; have : g.cap.toNat = 0 := by rw [hc0]; rfl
    omega
  simp only [hcapNe, ↓reduceIte]
  exact Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.of_eq (by sep_ac_rfl))

private theorem vecU8_empty_pack (A : RustAlloc) (ret : BitVec 64) :
    ((ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ 1#64) ∗ ((ret + 16#64) ↦₆₄ 0#64)) ⊢ vecU8 A ret [] := by
  unfold vecU8 vecU8At vecHeader
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 1#64 ?_)
  have hZero : (0#64 : BitVec 64) = 0 := rfl
  simp only [hZero, ↓reduceIte, sepConj_emp, List.length_nil]
  refine Entails.trans (Entails.pure_right
    (φ := 0 ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0)
    (by decide) (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl))

private theorem vecU8_nonempty_pack (A : RustAlloc)
    (ret newPtr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt63 : bs.length < 2 ^ 63) (hne0 : newPtr ≠ 0#64) :
    let lenBv := BitVec.ofNat 64 bs.length
    (((ret ↦₆₄ lenBv) ∗ ((ret + 8#64) ↦₆₄ newPtr) ∗ ((ret + 16#64) ↦₆₄ lenBv)) ∗
      A.live newPtr bs.length 1 ∗ (newPtr ↦ₛ bs)) ⊢ vecU8 A ret bs := by
  intro lenBv
  have hlenNat : lenBv.toNat = bs.length := by
    dsimp only [lenBv]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcapNe : lenBv ≠ 0 := by
    intro h0; have := congrArg BitVec.toNat h0; rw [hlenNat] at this; change bs.length = 0 at this; omega
  unfold vecU8 vecU8At vecHeader
  refine Entails.sepExists_right lenBv (Entails.sepExists_right newPtr ?_)
  simp only [hcapNe, ↓reduceIte, hlenNat, Nat.sub_self, memRegion_zero, sepConj_emp]
  refine Entails.trans (Entails.pure_right (φ := bs.length ≤ bs.length ∧ bs.length < 2 ^ 63 ∧ newPtr ≠ 0)
    ⟨Nat.le_refl _, hlt63, hne0⟩ (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl))

private abbrev savedStack48 (s0 : State) : SepProp :=
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

private abbrev vecHdrPts (p : BitVec 64) (g : VecGhost) : SepProp :=
  (p ↦₆₄ g.cap) ∗ ((p + 8#64) ↦₆₄ g.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length)

private abbrev retPts (ret r0 r1 r2 : BitVec 64) : SepProp :=
  (ret ↦₆₄ r0) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r2)

private abbrev csUpperPreserved (s0 sm : State) : Prop :=
  ∀ r ∈ ([.x23, .x24, .x25, .x26, .x27, .x28] : List Reg), sm.readReg64 r = s0.readReg64 r

private theorem csUpperPreserved_trans {s0 sm sf : State}
    (h1 : csUpperPreserved s0 sm) (h2 : CalleeSavedPreserved sm sf) :
    csUpperPreserved s0 sf := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h2.readReg64_x23.trans (h1 .x23 (by simp))
  · exact h2.readReg64_x24.trans (h1 .x24 (by simp))
  · exact h2.readReg64_x25.trans (h1 .x25 (by simp))
  · exact h2.readReg64_x26.trans (h1 .x26 (by simp))
  · exact h2.readReg64_x27.trans (h1 .x27 (by simp))
  · exact h2.readReg64_x28.trans (h1 .x28 (by simp))

private abbrev cloneFrame0 (s0 : State) : SepProp :=
  stackFrameAt (s0.sp - 48#64 - 4096#64) 12240

private abbrev cloneBudgetPost [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (p ret : BitVec 64) (g : VecGhost) (st : M.σ) (R : SepProp) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ (cloneFrame0 s0 ∗ R)) →
      sf.mem ⊨ (stringCloneBudgetSpec M A lim).post (p, ret, g, st) s0 sf ∗ R) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

private abbrev cloneBudgetPanic [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (p ret : BitVec 64) (g : VecGhost) (st : M.σ) (R : SepProp) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ (cloneFrame0 s0 ∗ R)) →
      sf.mem ⊨ (stringCloneBudgetSpec M A lim).onPanic (p, ret, g, st) s0 sf ∗ R

private abbrev cloneBudgetOom : State → SepProp :=
  fun _ => ⌜False⌝

private theorem cloneBudget_empty_epilogue [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program}
    {fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : FetchSeq P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr))
    (p ret : BitVec 64) (g : VecGhost) (st : M.σ)
    (r0 r1 r2 : BitVec 64) (R : SepProp) (s0 sm : State)
    (hg_empty : g.bytes = []) (hsp0 : s0.spAligned = true)
    (hpcm : sm.pc = fnAddr + 0x5c#64) (hrunm : sm.status = .Running)
    (hspm : sm.sp = s0.sp - 48#64) (hx19 : sm.readReg64 .x19 = 0#64)
    (hx20 : sm.readReg64 .x20 = ret) (hcsm : csUpperPreserved s0 sm)
    (hvm : calleeSavedVRegs sm = calleeSavedVRegs s0) (htrm : sm.trace = s0.trace)
    (hvm_sm : VmPreserved s0 sm) :
    SepWPp P (s0.readReg64 .lr) sm
      (retPts ret r0 r1 r2 ∗ savedStack48 s0 ∗
        (vecHdrPts p g ∗ vecGhostPayload A.repAlloc g) ∗
        A.pool lim st s0 ∗ stackAt (s0.sp - 48#64) allocHookStack)
      (cloneBudgetPost A lim p ret g st R s0)
      (cloneBudgetPanic A lim p ret g st R s0)
      cloneBudgetOom := by
  have hf23 := fetch_seq_at 23 hCode; have hf24 := fetch_seq_at 24 hCode
  have hf25 := fetch_seq_at 25 hCode; have hf26 := fetch_seq_at 26 hCode
  have hf27 := fetch_seq_at 27 hCode; have hf28 := fetch_seq_at 28 hCode
  have hf29 := fetch_seq_at 29 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
  have hspAl48 : decide (sm.sp &&& 15#64 = 0#64) = true := by
    rw [hspm]; exact decide_eq_true (beq_iff_eq.mp (spAligned_sub48 hspAl0))
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  dsimp only [retPts, savedStack48, vecHdrPts]
  wp_step; wp_stp64 hf24 m1 hm1; wp_str64 hf25 m2 hm2
  wp_step; wp_step; wp_step; wp_step
  refine sepWP_done_let (by simp [arm64_norm]) (by simp [arm64_norm, hrunm])
    fun sf hsf hpcf hrunf => ?_
  have hspf : sf.sp = s0.sp := by rw [hsf]; simp [arm64_norm]
  have htrf : sf.trace = s0.trace := by rw [hsf]; simp [arm64_norm, htrm]
  have hvm_sm_sf : VmPreserved sm sf := by
    simp only [mem_setMem_eq, mem_setPC_eq, mem_advancePC_eq, mem_setPState_eq,
      mem_writeReg64_eq, mem_writeReg32_eq, mem_writeReg_eq] at hm1 hm2
    exact vmPreserved_of_fields
      (by rw [hsf]; simp) (by rw [hsf]; simp) (by rw [hsf]; simp) (by rw [hsf]; simp)
      (by rw [hsf]; simp [hm2, hm1])
  have hvm_sf : VmPreserved s0 sf := hvm_sm.trans hvm_sm_sf
  have hcsf : CalleeSavedPreserved s0 sf := by
    rw [hsf]
    refine ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simpa [arm64_norm] using hcsm .x23 (by simp), by simpa [arm64_norm] using hcsm .x24 (by simp),
      by simpa [arm64_norm] using hcsm .x25 (by simp), by simpa [arm64_norm] using hcsm .x26 (by simp),
      by simpa [arm64_norm] using hcsm .x27 (by simp), by simpa [arm64_norm] using hcsm .x28 (by simp),
      by simp [arm64_norm], by simpa [calleeSavedVRegs, arm64_norm] using hvm⟩
  clear hsf
  refine SepWPp.done hpcf hrunf ⟨fun hmf => ?_, hspf, hcsf⟩
  dsimp only [cloneBudgetPost, cloneFrame0, stringCloneBudgetSpec] at hmf ⊢
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨[], ?_⟩
  rw [show M.stepEvents ([] : List AllocEvent) st = st from rfl,
      A.pool_transport lim st s0 sf hvm_sf, extHookStack_split_48 s0.sp]
  have hx19' : sm.readReg64 (Reg.gpr 19#5) = 0#64 := hx19
  have hx20' : sm.readReg64 (Reg.gpr 20#5) = ret := hx20
  try simp only [hx19', hx20', BitVec.add_zero] at hmf
  have hVecEq : (vecHdrPts p g ∗ vecGhostPayload A.repAlloc g) = vecGhostAt A.repAlloc g p :=
    (vecGhostAt_eq_header_payload A.repAlloc g p).symm
  have hmf1 : sf.mem ⊨
      (vecGhostAt A.repAlloc g p ∗
        (retPts ret 0#64 1#64 0#64 ∗ A.pool lim st s0 ∗
          (savedStack48 s0 ∗
            (stackAt (s0.sp - 48#64) allocHookStack ∗ cloneFrame0 s0)))) ∗ R := by
    rw [← hVecEq]; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmf
  have hEnv0 : StringCloneEnv g [] := Or.inl ⟨by simp [hg_empty], rfl⟩
  rw [hg_empty]
  refine Satisfies.mono (sepConj_mono_left ?_) hmf1
  refine Entails.trans
    (sepConj_mono_right
      (sepConj_mono (vecU8_empty_pack A.repAlloc ret)
        (sepConj_mono_right (sepConj_mono_left (pack_stack48 s0.sp _ _ _ _ _ _))))) ?_
  exact Entails.pure_right ⟨htrf, hEnv0⟩ (Entails.of_eq (by sep_ac_rfl))

private theorem cloneBudget_memcpy_epilogue [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program}
    {fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : FetchSeq P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr))
    (hMemcpy : subroutine_ok P memcpyAddr LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec)
    (p ret newPtr : BitVec 64) (g : VecGhost) (st : M.σ)
    (r0 r1 r2 : BitVec 64) (R : SepProp) (s0 sf2 : State)
    (hpos : 0 < g.bytes.length) (hlt63 : g.bytes.length < 2 ^ 63)
    (hsp0 : s0.spAligned = true) (hpNe0 : newPtr ≠ 0#64)
    (hpc2 : sf2.pc = fnAddr + 0x30#64) (hrun2 : sf2.status = .Running)
    (hsp2 : sf2.sp = s0.sp - 48#64) (hx0_2 : sf2.readReg64 .x0 = newPtr)
    (hx19_2 : sf2.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length)
    (hx20_2 : sf2.readReg64 .x20 = ret) (hx22_2 : sf2.readReg64 .x22 = g.ptr)
    (hcs2 : csUpperPreserved s0 sf2) (hv2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0)
    (htr2 : sf2.trace = s0.trace) :
    let st' := M.stepEvents (rustAllocEvents g.bytes.length 1) st
    SepWPp P (s0.readReg64 .lr) sf2
      (memRegion newPtr g.bytes.length ∗ vecGhostPayload A.repAlloc g ∗
        A.live newPtr g.bytes.length 1 ∗ A.pool lim st' sf2 ∗
        stackAt (s0.sp - 48#64) allocHookStack ∗ retPts ret r0 r1 r2 ∗
        vecHdrPts p g ∗ savedStack48 s0)
      (cloneBudgetPost A lim p ret g st R s0)
      (cloneBudgetPanic A lim p ret g st R s0)
      cloneBudgetOom := by
  intro st'
  have hf12 := fetch_seq_at 12 hCode; have hf13 := fetch_seq_at 13 hCode
  have hf14 := fetch_seq_at 14 hCode; have hf15 := fetch_seq_at 15 hCode
  have hf16 := fetch_seq_at 16 hCode; have hf17 := fetch_seq_at 17 hCode
  have hf18 := fetch_seq_at 18 hCode; have hf19 := fetch_seq_at 19 hCode
  have hf20 := fetch_seq_at 20 hCode; have hf21 := fetch_seq_at 21 hCode
  have hf22 := fetch_seq_at 22 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
  have hspAl48b : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub48 hspAl0
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (vecGhostPayload_nonempty_entails A.repAlloc g hpos))) ?_
  apply SepWPp.of_sepWP (mid := memcpyAddr)
  dsimp only [retPts, savedStack48, vecHdrPts]
  wp_step; wp_step; wp_step; wp_step; wp_step
  refine sepWP_done_let (by simp only [arm64_norm]; try bv_omega)
    (by simp [arm64_norm, hrun2]) fun sm3 hsm hpc3 hrun3 => ?_
  have hsp3 : sm3.sp = s0.sp - 48#64 := by rw [hsm]; simp [arm64_norm, hsp2]
  have hlr3 : sm3.readReg64 .lr = fnAddr + 0x44#64 := by
    rw [hsm]; simp only [arm64_norm]; try bv_omega
  have hx0_3 : sm3.readReg64 .x0 = newPtr := by rw [hsm]; simp [arm64_norm, hx0_2]
  have hx1_3 : sm3.readReg64 .x1 = g.ptr := by rw [hsm]; simp [arm64_norm]
  have hx2_3 : (sm3.readReg64 .x2).toNat = g.bytes.length := by
    rw [hsm]; simp only [arm64_norm]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx19_3 : sm3.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length := by
    rw [hsm]; simp [arm64_norm, hx19_2]
  have hx20_3 : sm3.readReg64 .x20 = ret := by rw [hsm]; simp [arm64_norm, hx20_2]
  have hx21_3 : sm3.readReg64 .x21 = newPtr := by rw [hsm]; simp [arm64_norm]
  have hcs3 : csUpperPreserved s0 sm3 := by
    rw [hsm]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [arm64_norm] using hcs2 _ (by simp)
  have hv3 : calleeSavedVRegs sm3 = calleeSavedVRegs s0 := by
    rw [hsm]; simpa [calleeSavedVRegs, arm64_norm] using hv2
  have htr3 : sm3.trace = s0.trace := by rw [hsm]; simp [arm64_norm, htr2]
  have hvm_sf2_sm3 : VmPreserved sf2 sm3 :=
    vmPreserved_of_fields
      (by rw [hsm]; simp) (by rw [hsm]; simp) (by rw [hsm]; simp) (by rw [hsm]; simp)
      (by rw [hsm]; simp)
  clear hsm
  let FrameMc :=
    vecGhostPayloadRest A.repAlloc g ∗ A.live newPtr g.bytes.length 1 ∗
    A.pool lim st' sf2 ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
    retPts ret r0 r1 r2 ∗ vecHdrPts p g ∗ savedStack48 s0
  refine SepWPp.call_wpp (x := (newPtr, g.ptr, g.bytes)) (ret_pc := fnAddr + 0x44#64)
    (F := FrameMc) hMemcpy hpc3 hrun3
    (by simpa [State.spAligned, hsp3] using hspAl48b) hlr3 ?_
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ ⟨_, hp⟩ => by
      dsimp only [LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec] at hp
      exact False.elim (not_satisfies_false_sepConj hp))
    ?_
    (fun _ _ _ ho => by
      dsimp only [LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec] at ho
      exact False.elim (not_satisfies_false_sepConj ho))
  · intro R' hm'
    dsimp only [LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec, FrameMc]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hx0_3, hx1_3, hx2_3⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'⟩
  · intro sf3 hpc_sf3 hrun_sf3 hsp_sf3 hcs_sf3
    dsimp only [LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec, FrameMc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hvm_mc => SepWPp.pure_elim fun ⟨_, htr_mc⟩ => ?_
    have hvm_sf2_sf3 : VmPreserved sf2 sf3 := hvm_sf2_sm3.trans hvm_mc
    have hsp3' : sf3.sp = s0.sp - 48#64 := hsp_sf3.trans hsp3
    have hspAl48 : decide (sf3.sp &&& 15#64 = 0#64) = true := by
      rw [hsp3']; exact decide_eq_true (beq_iff_eq.mp hspAl48b)
    have hx19_sf3 : sf3.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length :=
      hcs_sf3.readReg64_x19.trans hx19_3
    have hx20_sf3 : sf3.readReg64 .x20 = ret := hcs_sf3.readReg64_x20.trans hx20_3
    have hx21_sf3 : sf3.readReg64 .x21 = newPtr := hcs_sf3.readReg64_x21.trans hx21_3
    have hcs_sf3_s0 : csUpperPreserved s0 sf3 := csUpperPreserved_trans hcs3 hcs_sf3
    have htr_sf3 : sf3.trace = s0.trace := htr_mc.trans htr3
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    dsimp only [retPts, savedStack48, vecHdrPts]
    wp_stp64 hf17 m1 hm1; wp_str64 hf18 m2 hm2
    wp_step; wp_step; wp_step; wp_step
    refine sepWP_done_let (by simp [arm64_norm]) (by simp [arm64_norm, hrun_sf3])
      fun sf hsf hpcf hrunf => ?_
    have hspf : sf.sp = s0.sp := by rw [hsf]; simp [arm64_norm]
    have htrf : sf.trace = s0.trace := by rw [hsf]; simp [arm64_norm, htr_sf3]
    have hvm_sf3_sf : VmPreserved sf3 sf := by
      simp only [mem_setMem_eq, mem_setPC_eq, mem_advancePC_eq, mem_setPState_eq,
        mem_writeReg64_eq, mem_writeReg32_eq, mem_writeReg_eq] at hm1 hm2
      exact vmPreserved_of_fields
        (by rw [hsf]; simp) (by rw [hsf]; simp) (by rw [hsf]; simp) (by rw [hsf]; simp)
        (by rw [hsf]; simp [hm2, hm1])
    have hvm_sf2_sf : VmPreserved sf2 sf := hvm_sf2_sf3.trans hvm_sf3_sf
    have hcsf : CalleeSavedPreserved s0 sf := by
      rw [hsf]
      refine ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
        by simpa [arm64_norm] using hcs_sf3_s0 .x23 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x24 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x25 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x26 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x27 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x28 (by simp),
        by simp [arm64_norm],
        by simpa [calleeSavedVRegs, arm64_norm] using hcs_sf3.vregs.trans hv3⟩
    clear hsf
    refine SepWPp.done hpcf hrunf ⟨fun hmf => ?_, hspf, hcsf⟩
    dsimp only [cloneBudgetPost, cloneFrame0, stringCloneBudgetSpec] at hmf ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨rustAllocEvents g.bytes.length 1, ?_⟩
    change sf.mem ⊨
      (⌜sf.trace = s0.trace ∧ StringCloneEnv g (rustAllocEvents g.bytes.length 1)⌝ ∗
        vecGhostAt A.repAlloc g p ∗ vecU8 A.repAlloc ret g.bytes ∗
        A.pool lim st' sf ∗ stackAt s0.sp extHookStack) ∗ R
    rw [A.pool_transport lim st' sf2 sf hvm_sf2_sf, extHookStack_split_48 s0.sp]
    have hx19' : sf3.readReg64 (Reg.gpr 19#5) = BitVec.ofNat 64 g.bytes.length := hx19_sf3
    have hx20' : sf3.readReg64 (Reg.gpr 20#5) = ret := hx20_sf3
    have hx21' : sf3.readReg64 (Reg.gpr 21#5) = newPtr := hx21_sf3
    try simp only [hx19', hx20', hx21', BitVec.add_zero] at hmf
    let lenBv := BitVec.ofNat 64 g.bytes.length
    have hmf1 : sf.mem ⊨
        ((vecHdrPts p g ∗ ((g.ptr ↦ₛ g.bytes) ∗ vecGhostPayloadRest A.repAlloc g)) ∗
          ((retPts ret lenBv newPtr lenBv ∗
            A.repAlloc.live newPtr g.bytes.length 1 ∗ (newPtr ↦ₛ g.bytes)) ∗
           A.pool lim st' sf2 ∗
           (savedStack48 s0 ∗
            (stackAt (s0.sp - 48#64) allocHookStack ∗ cloneFrame0 s0)))) ∗ R :=
      Satisfies.mono (Entails.of_eq (by dsimp only [lenBv, RustCliAllocBudget.repAlloc]; sep_ac_rfl)) hmf
    refine Satisfies.mono (sepConj_mono_left ?_) hmf1
    have hGhostEnt :
        (vecHdrPts p g ∗ ((g.ptr ↦ₛ g.bytes) ∗ vecGhostPayloadRest A.repAlloc g)) ⊢
        vecGhostAt A.repAlloc g p := by
      rw [vecGhostAt_eq_header_payload A.repAlloc g p]
      exact sepConj_mono_right (vecGhostPayload_nonempty_pack A.repAlloc g hpos)
    refine Entails.trans
      (sepConj_mono hGhostEnt
        (sepConj_mono (vecU8_nonempty_pack A.repAlloc ret newPtr g.bytes hpos hlt63 hpNe0)
          (sepConj_mono_right (sepConj_mono_left (pack_stack48 s0.sp _ _ _ _ _ _))))) ?_
    exact Entails.pure_right ⟨htrf, Or.inr ⟨hpos, rfl⟩⟩ (Entails.of_eq (by sep_ac_rfl))

private theorem cloneBudget_nonempty_branch [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program}
    {fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : FetchSeq P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr))
    (hShim : subroutine_ok P shimAddr LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionShimBudgetSpec)
    (hAlloc : subroutine_ok P allocAddr (rustCliAllocBudgetSpec M A lim false))
    (hMemcpy : subroutine_ok P memcpyAddr LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec)
    (hlr_al : LsRetAddr624 (fnAddr + 0x30#64))
    (p ret : BitVec 64) (g : VecGhost) (st : M.σ)
    (r0 r1 r2 : BitVec 64) (R : SepProp) (s0 sm0 : State)
    (hpos : 0 < g.bytes.length) (hlt63 : g.bytes.length < 2 ^ 63)
    (hFit : FitsEvents M lim st (rustAllocEvents g.bytes.length 1))
    (hsp0 : s0.spAligned = true)
    (hpcm0 : sm0.pc = fnAddr + 0x1c#64) (hrunm0 : sm0.status = .Running)
    (hspm0 : sm0.sp = s0.sp - 48#64) (hx0_m0 : sm0.readReg64 .x0 = p)
    (hx19_m0 : sm0.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length)
    (hx20_m0 : sm0.readReg64 .x20 = ret) (hcsm0 : csUpperPreserved s0 sm0)
    (hvm0 : calleeSavedVRegs sm0 = calleeSavedVRegs s0) (htrm0 : sm0.trace = s0.trace)
    (hvm_sm0 : VmPreserved s0 sm0) :
    SepWPp P (s0.readReg64 .lr) sm0
      (vecHdrPts p g ∗ vecGhostPayload A.repAlloc g ∗ A.pool lim st s0 ∗
        stackAt (s0.sp - 48#64) allocHookStack ∗ retPts ret r0 r1 r2 ∗ savedStack48 s0)
      (cloneBudgetPost A lim p ret g st R s0)
      (cloneBudgetPanic A lim p ret g st R s0)
      cloneBudgetOom := by
  have hf7 := fetch_seq_at 7 hCode; have hf8 := fetch_seq_at 8 hCode
  have hf9 := fetch_seq_at 9 hCode; have hf10 := fetch_seq_at 10 hCode
  have hf11 := fetch_seq_at 11 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
  have hspAl48b : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub48 hspAl0
  apply SepWPp.of_sepWP (mid := shimAddr)
  dsimp only [retPts, savedStack48, vecHdrPts]
  wp_step; wp_step
  refine sepWP_done_let (by simp only [arm64_norm]; try bv_omega)
    (by simp [arm64_norm, hrunm0]) fun sm1 hsm1 hpc1 hrun1 => ?_
  have hsp1 : sm1.sp = s0.sp - 48#64 := by rw [hsm1]; simp [arm64_norm, hspm0]
  have hlr1 : sm1.readReg64 .lr = fnAddr + 0x24#64 := by
    rw [hsm1]; simp only [arm64_norm]; try bv_omega
  have hx19_1 : sm1.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length := by
    rw [hsm1]; simp [arm64_norm, hx19_m0]
  have hx20_1 : sm1.readReg64 .x20 = ret := by
    rw [hsm1]; simp [arm64_norm, hx20_m0]
  have hx22_1 : sm1.readReg64 .x22 = g.ptr := by rw [hsm1]; simp [arm64_norm]
  have hcs1 : csUpperPreserved s0 sm1 := by
    rw [hsm1]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [arm64_norm] using hcsm0 _ (by simp)
  have hv1 : calleeSavedVRegs sm1 = calleeSavedVRegs s0 := by
    rw [hsm1]; simpa [calleeSavedVRegs, arm64_norm] using hvm0
  have htr1 : sm1.trace = s0.trace := by rw [hsm1]; simp [arm64_norm, htrm0]
  have hvm_sm0_sm1 : VmPreserved sm0 sm1 :=
    vmPreserved_of_fields
      (by rw [hsm1]; simp) (by rw [hsm1]; simp) (by rw [hsm1]; simp) (by rw [hsm1]; simp)
      (by rw [hsm1]; simp)
  have hvm_s0_sm1 : VmPreserved s0 sm1 := hvm_sm0.trans hvm_sm0_sm1
  clear hsm1
  let FrameShim :=
    vecHdrPts p g ∗ vecGhostPayload A.repAlloc g ∗ A.pool lim st s0 ∗
    stackAt (s0.sp - 48#64) allocHookStack ∗ retPts ret r0 r1 r2 ∗ savedStack48 s0
  refine SepWPp.call_wpp (x := ()) (ret_pc := fnAddr + 0x24#64)
    (F := FrameShim) hShim hpc1 hrun1
    (by simpa [State.spAligned, hsp1] using hspAl48b) hlr1
    (fun _ hm' => by
      dsimp only [LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionShimBudgetSpec, sessionShimSpec, FrameShim]
      rw [emp_sepConj]; exact hm')
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ ⟨_, hp⟩ => by
      dsimp only [LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionShimBudgetSpec, sessionShimSpec] at hp
      exact False.elim (not_satisfies_false_sepConj hp))
    ?_
    (fun _ _ _ ho => by
      dsimp only [LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionShimBudgetSpec, sessionShimSpec] at ho
      exact False.elim (not_satisfies_false_sepConj ho))
  intro sf1 hpc_sf1 hrun_sf1 hsp_sf1 hcs_sf1
  dsimp only [LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionShimBudgetSpec, sessionShimSpec, FrameShim]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hvm_sh => SepWPp.pure_elim fun htr_sh => ?_
  have hvm_s0_sf1 : VmPreserved s0 sf1 := hvm_s0_sm1.trans hvm_sh
  have hsp_sf1' : sf1.sp = s0.sp - 48#64 := hsp_sf1.trans hsp1
  have hx19_sf1 : sf1.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length :=
    hcs_sf1.readReg64_x19.trans hx19_1
  have hx20_sf1 : sf1.readReg64 .x20 = ret := hcs_sf1.readReg64_x20.trans hx20_1
  have hx22_sf1 : sf1.readReg64 .x22 = g.ptr := hcs_sf1.readReg64_x22.trans hx22_1
  have hcs_sf1_s0 : csUpperPreserved s0 sf1 := csUpperPreserved_trans hcs1 hcs_sf1
  have htr_sf1 : sf1.trace = s0.trace := htr_sh.trans htr1
  apply SepWPp.of_sepWP (mid := allocAddr)
  wp_step; wp_step; wp_step
  refine sepWP_done_let (by simp only [arm64_norm]; try bv_omega)
    (by simp [arm64_norm, hrun_sf1]) fun sm2 hsm2 hpc2 hrun2 => ?_
  have hsp2 : sm2.sp = s0.sp - 48#64 := by rw [hsm2]; simp [arm64_norm, hsp_sf1']
  have hlr2 : sm2.readReg64 .lr = fnAddr + 0x30#64 := by
    rw [hsm2]; simp only [arm64_norm]; try bv_omega
  have hx0_2 : sm2.readReg64 .x0 = BitVec.ofNat 64 g.bytes.length := by
    rw [hsm2]; simp [arm64_norm]
  have hx1_2 : sm2.readReg64 .x1 = 1#64 := by rw [hsm2]; simp [arm64_norm]
  have hx19_2 : sm2.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length := by
    rw [hsm2]; simp [arm64_norm, hx19_sf1]
  have hx20_2 : sm2.readReg64 .x20 = ret := by rw [hsm2]; simp [arm64_norm, hx20_sf1]
  have hx22_2 : sm2.readReg64 .x22 = g.ptr := by rw [hsm2]; simp [arm64_norm, hx22_sf1]
  have hcs2 : csUpperPreserved s0 sm2 := by
    rw [hsm2]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [arm64_norm] using hcs_sf1_s0 _ (by simp)
  have hv2 : calleeSavedVRegs sm2 = calleeSavedVRegs s0 := by
    rw [hsm2]; simpa [calleeSavedVRegs, arm64_norm] using hcs_sf1.vregs.trans hv1
  have htr2 : sm2.trace = s0.trace := by rw [hsm2]; simp [arm64_norm, htr_sf1]
  have hvm_sf1_sm2 : VmPreserved sf1 sm2 :=
    vmPreserved_of_fields
      (by rw [hsm2]; simp) (by rw [hsm2]; simp) (by rw [hsm2]; simp) (by rw [hsm2]; simp)
      (by rw [hsm2]; simp)
  have hvm_s0_sm2 : VmPreserved s0 sm2 := hvm_s0_sf1.trans hvm_sf1_sm2
  clear hsm2
  let FrameAl :=
    vecHdrPts p g ∗ vecGhostPayload A.repAlloc g ∗ retPts ret r0 r1 r2 ∗ savedStack48 s0
  have hx0_nat : (sm2.readReg64 .x0).toNat = g.bytes.length := by
    rw [hx0_2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx1_nat : (sm2.readReg64 .x1).toNat = 1 := by rw [hx1_2]; rfl
  have hLay : RustLayoutOk g.bytes.length 1 :=
    ⟨⟨hpos, ⟨0, rfl⟩, by omega⟩, by decide⟩
  refine SepWPp.call_wpp (x := (g.bytes.length, 1, st)) (ret_pc := fnAddr + 0x30#64)
    (F := FrameAl) hAlloc hpc2 hrun2
    (by simpa [State.spAligned, hsp2] using hspAl48b) hlr2 ?_
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ ⟨_, hp⟩ => by
      dsimp only [rustCliAllocBudgetSpec] at hp
      exact False.elim (not_satisfies_false_sepConj hp))
    ?_
    (fun _ _ _ ho => by
      dsimp only [rustCliAllocBudgetSpec] at ho
      rw [satisfies_pure_sepConj] at ho
      exact False.elim (ho.1.1 hFit))
  · intro R' hm'
    dsimp only [rustCliAllocBudgetSpec, FrameAl]
    rw [hsp2, A.pool_transport lim st s0 sm2 hvm_s0_sm2]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hx0_nat, hx1_nat, hLay, hlr2 ▸ hlr_al⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'⟩
  · intro sf2 hpc_sf2 hrun_sf2 hsp_sf2 hcs_sf2
    dsimp only [rustCliAllocBudgetSpec, FrameAl]
    rw [hsp2]
    have hsp_sf2' : sf2.sp = s0.sp - 48#64 := hsp_sf2.trans hsp2
    have hx19_sf2 : sf2.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length :=
      hcs_sf2.readReg64_x19.trans hx19_2
    have hx20_sf2 : sf2.readReg64 .x20 = ret := hcs_sf2.readReg64_x20.trans hx20_2
    have hx22_sf2 : sf2.readReg64 .x22 = g.ptr := hcs_sf2.readReg64_x22.trans hx22_2
    have hcs_s0_sf2 : csUpperPreserved s0 sf2 := csUpperPreserved_trans hcs2 hcs_sf2
    have hv_s0_sf2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0 :=
      hcs_sf2.vregs.trans hv2
    by_cases hnull : sf2.readReg64 .x0 = 0
    · simp only [hnull, ↓reduceIte]
      have hPullNull :
          (⌜AllocCallPreserved sm2 sf2⌝ ∗ A.pool lim st sf2 ∗
            stackAt (s0.sp - 48#64) allocHookStack ∗ ⌜NullAllowed g.bytes.length 1⌝) ∗
            (vecHdrPts p g ∗ vecGhostPayload A.repAlloc g ∗ retPts ret r0 r1 r2 ∗ savedStack48 s0) =
          ⌜NullAllowed g.bytes.length 1⌝ ∗
            (⌜AllocCallPreserved sm2 sf2⌝ ∗ A.pool lim st sf2 ∗
              stackAt (s0.sp - 48#64) allocHookStack ∗
              vecHdrPts p g ∗ vecGhostPayload A.repAlloc g ∗ retPts ret r0 r1 r2 ∗ savedStack48 s0) := by
        sep_ac_rfl
      rw [hPullNull]
      exact SepWPp.pure_elim fun hna =>
        False.elim (not_nullAllowed_of_fitsAllocEvents hLay hFit hna)
    · simp only [hnull, Bool.false_eq_true, ↓reduceIte]
      let newPtr := sf2.readReg64 .x0
      let st' := M.stepEvents (rustAllocEvents g.bytes.length 1) st
      have hpNe0 : newPtr ≠ 0#64 := hnull
      have hPullOk :
          (⌜AllocCallPreserved sm2 sf2⌝ ∗ A.pool lim st' sf2 ∗
            stackAt (s0.sp - 48#64) allocHookStack ∗
            (⌜newPtr.toNat % 1 = 0⌝ ∗ A.live newPtr g.bytes.length 1 ∗
              memRegion newPtr g.bytes.length)) ∗
            (vecHdrPts p g ∗ vecGhostPayload A.repAlloc g ∗ retPts ret r0 r1 r2 ∗ savedStack48 s0) =
          ⌜AllocCallPreserved sm2 sf2⌝ ∗
            (⌜newPtr.toNat % 1 = 0⌝ ∗
              (memRegion newPtr g.bytes.length ∗ vecGhostPayload A.repAlloc g ∗
                A.live newPtr g.bytes.length 1 ∗ A.pool lim st' sf2 ∗
                stackAt (s0.sp - 48#64) allocHookStack ∗ retPts ret r0 r1 r2 ∗
                vecHdrPts p g ∗ savedStack48 s0)) := by
        dsimp only [newPtr, st']; sep_ac_rfl
      rw [hPullOk]
      refine SepWPp.pure_elim fun hacp => SepWPp.pure_elim fun _ => ?_
      exact cloneBudget_memcpy_epilogue A lim hCode hMemcpy p ret newPtr g st
        r0 r1 r2 R s0 sf2 hpos hlt63 hsp0 hpNe0
        hpc_sf2 hrun_sf2 hsp_sf2' rfl hx19_sf2 hx20_sf2 hx22_sf2
        hcs_s0_sf2 hv_s0_sf2 (hacp.2.1.trans htr2)

private theorem stringCloneBudget_fetches_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program}
    {fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : FetchSeq P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr))
    (hShim : subroutine_ok P shimAddr LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionShimBudgetSpec)
    (hAlloc : subroutine_ok P allocAddr (rustCliAllocBudgetSpec M A lim false))
    (hMemcpy : subroutine_ok P memcpyAddr LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec)
    (hlr_al : LsRetAddr624 (fnAddr + 0x30#64)) :
    subroutine_ok P fnAddr (stringCloneBudgetSpec M A lim) := by
  apply subroutine_ok_of_sepWPp_pure_oom (φ := fun _ _ _ => False) (by rintro ⟨_, _, _, _⟩ _ _; rfl)
  rintro ⟨p, ret, g, st⟩ R s0 hpc hrun hpre hsp0
  dsimp only [stringCloneBudgetSpec] at hpre
  simp only [sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hEnv⟩, hrest⟩
  have hlt63 : g.bytes.length < 2 ^ 63 := by
    refine vecGhostAt_bytes_lt_2pow63 (A := A.repAlloc) (m := s0.mem) (p := p)
      (R := memRegion ret 24 ∗ (A.pool lim st s0 ∗ (stackAt s0.sp extHookStack ∗ R))) ?_
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest
  let P0 :=
    stackFrameAt s0.sp 48 ∗ memRegion ret 24 ∗ vecGhostAt A.repAlloc g p ∗
    A.pool lim st s0 ∗ stackAt (s0.sp - 48#64) allocHookStack
  have hm0 : s0.mem ⊨ P0 ∗ (cloneFrame0 s0 ∗ R) := by
    dsimp only [P0, cloneFrame0]
    rw [extHookStack_split_48 s0.sp] at hrest
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest
  refine ⟨P0, cloneFrame0 s0, hm0, ?_⟩
  dsimp only [P0]
  rw [stackFrameAt48_eq s0.sp, memRegion24_eq_exists_pts ret,
      vecGhostAt_eq_header_payload A.repAlloc g p]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun r0 => SepWPp.exists_elim fun r1 =>
    SepWPp.exists_elim fun r2 => SepWPp.exists_elim fun st0 =>
    SepWPp.exists_elim fun st1 => SepWPp.exists_elim fun st2 =>
    SepWPp.exists_elim fun st3 => SepWPp.exists_elim fun st4 =>
    SepWPp.exists_elim fun st5 => ?_
  have hf0 := fetch_seq_at0 hCode; have hf1 := fetch_seq_at 1 hCode
  have hf2 := fetch_seq_at 2 hCode; have hf3 := fetch_seq_at 3 hCode
  have hf4 := fetch_seq_at 4 hCode; have hf5 := fetch_seq_at 5 hCode
  have hf6 := fetch_seq_at 6 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
  have hspAl48 : decide ((s0.sp - 48#64) &&& 15#64 = 0#64) = true :=
    decide_eq_true (beq_iff_eq.mp (spAligned_sub48 hspAl0))
  by_cases hbs : g.bytes = []
  · have hlen0 : BitVec.ofNat 64 g.bytes.length = 0#64 := by simp [hbs]
    apply SepWPp.of_sepWP (mid := fnAddr + 0x5c#64)
    wp_stp64 hf0 m1 hm1; wp_stp64 hf1 m2 hm2; wp_stp64 hf2 m3 hm3
    wp_step; wp_step; wp_step; wp_step
    refine sepWP_done_let (by simp only [arm64_norm]; try bv_omega)
      (by simp [arm64_norm, hrun]) fun sm hsm hpcm hrunm => ?_
    have hspm : sm.sp = s0.sp - 48#64 := by rw [hsm]; simp [arm64_norm]
    have hx19m : sm.readReg64 .x19 = 0#64 := by rw [hsm]; simp [arm64_norm]
    have hx20m : sm.readReg64 .x20 = ret := by rw [hsm]; simp [arm64_norm]
    have hcsm : csUpperPreserved s0 sm := by
      rw [hsm]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [arm64_norm]
    have hvm : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
      rw [hsm]; simp [calleeSavedVRegs, arm64_norm]
    have htrm : sm.trace = s0.trace := by rw [hsm]; simp [arm64_norm]
    have hvm_sm : VmPreserved s0 sm := by
      simp only [mem_setMem_eq, mem_setPC_eq, mem_advancePC_eq, mem_setPState_eq,
        mem_writeReg64_eq, mem_writeReg32_eq, mem_writeReg_eq] at hm1 hm2 hm3
      exact vmPreserved_of_fields
        (by rw [hsm]; simp) (by rw [hsm]; simp) (by rw [hsm]; simp) (by rw [hsm]; simp)
        (by rw [hsm]; simp [hm3, hm2, hm1])
    clear hsm
    refine SepWPp.weaken_pre ?_ (cloneBudget_empty_epilogue A lim hCode p ret g st r0 r1 r2 R s0 sm
      hbs hsp0 hpcm hrunm hspm hx19m hx20m hcsm hvm htrm hvm_sm)
    exact Entails.of_eq (by
      dsimp only [retPts, savedStack48, vecHdrPts, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x29, Reg.lr]
      sep_ac_rfl)
  · have hpos : 0 < g.bytes.length := List.length_pos_iff.mpr hbs
    have hFit : FitsEvents M lim st (rustAllocEvents g.bytes.length 1) :=
      hEnv (rustAllocEvents g.bytes.length 1) (Or.inr ⟨hpos, rfl⟩)
    have hlenNe0 : BitVec.ofNat 64 g.bytes.length ≠ 0#64 := by
      intro h0; have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      change g.bytes.length = 0 at this; omega
    apply SepWPp.of_sepWP (mid := fnAddr + 0x1c#64)
    wp_stp64 hf0 m1 hm1; wp_stp64 hf1 m2 hm2; wp_stp64 hf2 m3 hm3
    wp_step; wp_step; wp_step; wp_step
    refine sepWP_done_let (by simp [arm64_norm, beq_false_of_ne hlenNe0]; try bv_omega)
      (by simp [arm64_norm, hrun]) fun sm0 hsm0 hpcm0 hrunm0 => ?_
    have hspm0 : sm0.sp = s0.sp - 48#64 := by rw [hsm0]; simp [arm64_norm]
    have hx0_m0 : sm0.readReg64 .x0 = p := by rw [hsm0]; simp [arm64_norm, hx0]
    have hx19_m0 : sm0.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length := by
      rw [hsm0]; simp [arm64_norm]
    have hx20_m0 : sm0.readReg64 .x20 = ret := by rw [hsm0]; simp [arm64_norm]
    have hcsm0 : csUpperPreserved s0 sm0 := by
      rw [hsm0]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [arm64_norm]
    have hvm0 : calleeSavedVRegs sm0 = calleeSavedVRegs s0 := by
      rw [hsm0]; simp [calleeSavedVRegs, arm64_norm]
    have htrm0 : sm0.trace = s0.trace := by rw [hsm0]; simp [arm64_norm]
    have hvm_sm0 : VmPreserved s0 sm0 := by
      simp only [mem_setMem_eq, mem_setPC_eq, mem_advancePC_eq, mem_setPState_eq,
        mem_writeReg64_eq, mem_writeReg32_eq, mem_writeReg_eq] at hm1 hm2 hm3
      exact vmPreserved_of_fields
        (by rw [hsm0]; simp) (by rw [hsm0]; simp) (by rw [hsm0]; simp) (by rw [hsm0]; simp)
        (by rw [hsm0]; simp [hm3, hm2, hm1])
    clear hsm0
    refine SepWPp.weaken_pre ?_ (cloneBudget_nonempty_branch A lim hCode hShim hAlloc hMemcpy hlr_al
      p ret g st r0 r1 r2 R s0 sm0 hpos hlt63 hFit hsp0 hpcm0 hrunm0 hspm0 hx0_m0 hx19_m0 hx20_m0
      hcsm0 hvm0 htrm0 hvm_sm0)
    exact Entails.of_eq (by
      dsimp only [retPts, savedStack48, vecHdrPts, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x29, Reg.lr]
      sep_ac_rfl)

private theorem stc_stringClone_hasInstrs_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program}
    {fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : hasInstrs P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr))
    (hShim : subroutine_ok P shimAddr LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionShimBudgetSpec)
    (hAlloc : subroutine_ok P allocAddr (rustCliAllocBudgetSpec M A lim false))
    (hMemcpy : subroutine_ok P memcpyAddr LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec)
    (hlr_al : LsRetAddr624 (fnAddr + 0x30#64)) :
    subroutine_ok P fnAddr (stringCloneBudgetSpec M A lim) :=
  stringCloneBudget_fetches_ok A lim
    (fun i hi => hCode.fetch_off i (BitVec.ofNat 64 (4 * i)) hi rfl)
    hShim hAlloc hMemcpy hlr_al

private theorem stc_ls_hook_ok_623 [LibsignalPlacement] {α : Type} {H : LibsignalHooks} {sym : String}
    {spec : Spec α} (hmem : sym ∈ libsignalSessionExterns := by decide) (h : HookSat H sym spec) :
    subroutine_ok (lsProg_623 H) (lsρ sym) spec := by
  obtain ⟨k, hlt, hk⟩ := List.getElem_of_mem hmem
  exact ls_hook_ok (prog := lsProg_623 H) (i := 623) (k := k)
    (by rw [List.getElem?_eq_getElem hlt, hk]) h

private theorem stc_stringClone_blk623_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hShim : HookSat H lsRustNoAllocShimPlacedSym LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionShimBudgetSpec)
    (hAlloc : HookSat H lsRustAllocPlacedSym (rustCliAllocBudgetSpec M A lim false))
    (hMemcpy : HookSat H "memcpy" LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_623 H) (lsmpl.base 623) (stringCloneBudgetSpec M A lim) :=
  stc_stringClone_hasInstrs_ok (lsProg_623_hasInstrs H)
    (stc_ls_hook_ok_623 (by decide) hShim)
    (stc_ls_hook_ok_623 (by decide) hAlloc)
    (stc_ls_hook_ok_623 (by decide) hMemcpy)
    (lsRetAddr624_base_add 623 0x30#64 (by decide) (by decide))

private theorem stc_stringClone_placed_codeLoaded_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hShim : HookSat H lsRustNoAllocShimPlacedSym LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionShimBudgetSpec)
    (hAlloc : HookSat H lsRustAllocPlacedSym (rustCliAllocBudgetSpec M A lim false))
    (hMemcpy : HookSat H "memcpy" LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec)
    {bi : Nat} [LsBlockBound bi] (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 623)
      (withLsCodeLoaded lsmpl (stringCloneBudgetSpec M A lim)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg)
    (subroutine_ok_withLsCodeLoaded_of_plain (stc_stringClone_blk623_ok hShim hAlloc hMemcpy))
    hi (by decide) (by decide)
end StringCloneEncProof

theorem stringClone_placed_ok_at_enc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop} {C : Crypto}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    (env : EncEnvBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk) :
    subroutine_ok (lsProg_198 Hk) (lsmpl.base 623)
      (StoreKit.withLsRoCl lsmpl (stringCloneBudgetSpec M A lim)) :=
  StoreKit.subroutine_ok_rocl_of_withLsCodeRoLoaded
    (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (stc_stringClone_placed_codeLoaded_ok
        (callerProg := lsProg_198 Hk) (i := 198) env.hooks.shimVm env.hooks.alloc env.hooks.memcpyVm))

/-! ## Relocatable Call Wrappers -/

theorem call_nopanic_placed {α : Type} [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {ctl : BitVec 64} {S : SpqrModel}
    {sendEnv : SpqrSendBudgetEnv} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {st_init : M.σ} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (lsProg_198 Hk) entry spec) (xc : α) {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hm : s.mem ⊨ spec.pre xc s ∗ (F ∗ R))
    (hnext : ∀ sm : State, Steps (lsProg_198 Hk) s sm → sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → sm.spAligned = true → CalleeSavedPreserved s sm →
      (sm.mem ⊨ spec.post xc s sm ∗ (F ∗ R)) →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk x st_init R0 s0 sm next)
    (hexit : ∀ code sf, spec.onExit xc code s sf = ⌜False⌝ := by intros; rfl)
    (hpanic : ∀ sf, spec.onPanic xc s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, spec.onOom xc s sf = ⌜False⌝ := by intros; rfl) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk x st_init R0 s0 s next := by
  refine SegExitBudget.call hcall xc hpc hrun hsp hlr hm
    (fun sf code R' _ h => by rw [hexit] at h; exact not_satisfies_false_sepConj h)
    (fun sf _ _ h => by rw [hpanic, sepConj_assoc] at h; exact (not_satisfies_false_sepConj h).elim)
    (fun sm _ hsteps hpcm hrunm hspm hcsm hpost => ?_)
    (fun sf R' _ h => by rw [hoom] at h; exact not_satisfies_false_sepConj h)
  rw [sepConj_assoc] at hpost
  exact hnext sm hsteps hpcm hrunm hspm (spAligned_of_sp_eq hsp hspm) hcsm hpost

theorem call_alloc_placed {α : Type} [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {ctl : BitVec 64} {S : SpqrModel}
    {sendEnv : SpqrSendBudgetEnv} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {st_init : M.σ} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (lsProg_198 Hk) entry spec) (xc : α) {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (_hpref0 : s0.trace <+: s.trace)
    (hm : s.mem ⊨ spec.pre xc s ∗ (F ∗ R))
    (hnext : ∀ sm : State, Steps (lsProg_198 Hk) s sm → sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → sm.spAligned = true → CalleeSavedPreserved s sm →
      (sm.mem ⊨ spec.post xc s sm ∗ (F ∗ R)) →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk x st_init R0 s0 sm next)
    (hexit : ∀ code sf, spec.onExit xc code s sf = ⌜False⌝ := by intros; rfl)
    (hpanic : ∀ sf, spec.onPanic xc s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, spec.onOom xc s sf = ⌜False⌝ := by intros; rfl) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk x st_init R0 s0 s next := by
  refine SegExitBudget.call hcall xc hpc hrun hsp hlr hm
    (fun sf code R' _ h => by rw [hexit] at h; exact not_satisfies_false_sepConj h)
    (fun sf _ _ h => by rw [hpanic] at h; exact Satisfies.mono alloc_onPanic_entails_placed h)
    (fun sm _ hsteps hpcm hrunm hspm hcsm hpost => ?_)
    (fun sf R' _ h => by rw [hoom] at h; exact not_satisfies_false_sepConj h)
  rw [sepConj_assoc] at hpost
  exact hnext sm hsteps hpcm hrunm hspm (spAligned_of_sp_eq hsp hspm) hcsm hpost

theorem call_rocl_alloc_placed {α : Type} [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {ctl : BitVec 64} {S : SpqrModel}
    {sendEnv : SpqrSendBudgetEnv} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {st_init : M.σ} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (lsProg_198 Hk) entry (StoreKit.withLsRoCl lsmpl spec)) (xc : α) {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hpref0 : s0.trace <+: s.trace)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hm : s.mem ⊨ spec.pre xc s ∗ (F ∗ R))
    (hnext : ∀ sm : State, Steps (lsProg_198 Hk) s sm → sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → sm.spAligned = true → CalleeSavedPreserved s sm →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → (sm.mem ⊨ spec.post xc s sm ∗ (F ∗ R)) →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk x st_init R0 s0 sm next)
    (hexit : ∀ code sf, spec.onExit xc code s sf = ⌜False⌝ := by intros; rfl)
    (hpanic : ∀ sf, spec.onPanic xc s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, spec.onOom xc s sf = ⌜False⌝ := by intros; rfl) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk x st_init R0 s0 s next := by
  have hm_rocl : s.mem ⊨ (StoreKit.withLsRoCl lsmpl spec).pre xc s ∗ (F ∗ R) := by
    dsimp only [StoreKit.withLsRoCl]; rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]; exact ⟨hcrl, hm⟩
  refine call_alloc_placed hcall xc hpc hrun hsp hlr hpref0 hm_rocl
    (fun sm hsteps hpcm hrunm hspm hsp_alm hcsm hpost => ?_)
    (hexit := hexit) (hpanic := hpanic) (hoom := hoom)
  dsimp only [StoreKit.withLsRoCl] at hpost; rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm hpost.1 hpost.2

theorem call_rocl_nopanic_placed {α : Type} [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {ctl : BitVec 64} {S : SpqrModel}
    {sendEnv : SpqrSendBudgetEnv} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {st_init : M.σ} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (lsProg_198 Hk) entry (StoreKit.withLsRoCl lsmpl spec)) (xc : α) {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hm : s.mem ⊨ spec.pre xc s ∗ (F ∗ R))
    (hnext : ∀ sm : State, Steps (lsProg_198 Hk) s sm → sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → sm.spAligned = true → CalleeSavedPreserved s sm →
      (sm.mem ⊨ spec.post xc s sm ∗ (F ∗ R)) →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk x st_init R0 s0 sm next)
    (hexit : ∀ code sf, spec.onExit xc code s sf = ⌜False⌝ := by intros; rfl)
    (hpanic : ∀ sf, spec.onPanic xc s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, spec.onOom xc s sf = ⌜False⌝ := by intros; rfl) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk x st_init R0 s0 s next := by
  have hm_rocl : s.mem ⊨ (StoreKit.withLsRoCl lsmpl spec).pre xc s ∗ (F ∗ R) := by
    dsimp only [StoreKit.withLsRoCl]; rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]; exact ⟨hcrl, hm⟩
  refine call_nopanic_placed (R0 := R0) hcall xc hpc hrun hsp hlr hm_rocl
    (fun sm hsteps hpcm hrunm hspm hsp_alm hcsm hpost => ?_)
    (hexit := hexit) (hpanic := hpanic) (hoom := hoom)
  dsimp only [StoreKit.withLsRoCl] at hpost; rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm hpost.2

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
