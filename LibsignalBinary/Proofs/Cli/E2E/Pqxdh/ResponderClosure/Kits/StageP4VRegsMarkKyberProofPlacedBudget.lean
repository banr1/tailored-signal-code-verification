/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrustTailsXExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsErrUnwindPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberProofPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsSaveIdProofPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4ErrUnwind
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4MarkKyber
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4MarkKyberProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsErrUnwind
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyber
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP4
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Stage P4.2 Dispatch Proof: `mark_kyber_pre_key_used`

Budget-threaded `[LibsignalPlacement]` Substage P4.2 dispatch proofs on Block `518`
(`lsProg_518 ext`), threading `A.pool` across `MarkStepEnv` on `Ok(())` and `StageP4MarkErrEnv`
on `Err(e)` unwind.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberProofPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees hiding dropSessionStructureLocal2Spec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit hiding KyberPreKeyStoreKitPlacedOk
  kitKpkMarkShimSpec kitKpkMarkPollSpec kitKpkMarkPollSpecE
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0 stackAt_sub_eq
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits hiding
  markKyberVtablesAt_placed_intro
  stageP4MarkKyberSharedPlaced stageP4MarkKyberPrePlaced
  stageP4MarkKyberOkPostPlaced stageP4MarkKyberErrPostPlaced
  KyberPreKeyMarkKitPlacedOk kyberPreKeyMarkKitPlacedOk_of_store
  stageP4_markKyber_to_38c_vregs_mark_placed
  stageP4_markKyber_none_dispatch_vregs_mark_placed
  stageP4_markKyber_some_dispatch_vregs_mark_placed
  stageP4_markKyber_to_38c_vregs_kits_placed
  stageP4_markKyber_none_dispatch_vregs_kits_placed
  stageP4_markKyber_some_dispatch_vregs_kits_placed
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SignalSession
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv futDropBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (
  KyberPreKeyStoreBudgetEnv kitKpkMarkShimSpec kitKpkMarkPollSpec kitKpkMarkPollSpecE
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (KyberPreKeyStoreKitPlacedOk)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrustTailsXExtPlacedBudget (
  bind_sepWP_steps_frame_placed call_rocl_entails_steps_frame_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsErrUnwindPlacedBudget (
  stageP4_err_unwind_550_vregs_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberPlacedBudget (
  markKyberVtablesAt_placed_intro
  p4_seg2a_vregs_placed_wp p4_seg2b_gen_vregs_placed_wp
  p4_seg2c_err_vregs_placed_wp p4_seg2c_none_vregs_placed_wp p4_seg2c_some_vregs_placed_wp
)

private theorem sepWPp_intro_ro {prog : Program} {ret : BitVec 64} {s : State}
    {R_ro P : SepProp} {Q Qp : State → SepProp → Prop}
    (hro : ∀ {R : SepProp}, s.mem ⊨ P ∗ R → s.mem ⊨ R_ro ∗ (P ∗ R))
    (h : SepWPp prog ret s (R_ro ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ (R_ro ∗ P) ∗ R := by
    rw [sepConj_assoc]
    exact hro hm
  exact h R hm' hL

private theorem markShim_pre_intro_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64} {s : State}
    {sp self baseKeyA : BitVec 64} {id signedId : BitVec 32}
    (hsp : s.sp = sp)
    (hx0 : s.readReg64 .x0 = self)
    (hx1 : s.readReg32 .x1 = id)
    (hx2 : s.readReg32 .x2 = signedId)
    (hx3 : s.readReg64 .x3 = baseKeyA)
    (hfits : FitsEnv M lim st (BoxAllocEnv kpkKit.markBoxSize)) :
    A.pool lim st s ∗ stackAt sp kpkKit.markShimStack ⊢
      (kitKpkMarkShimSpec M A lim kpkKit).pre
        (({ self := self, id := id, signedId := signedId, baseKeyA := baseKeyA }
            : KyberMarkShimCall), st) s := by
  dsimp only [kitKpkMarkShimSpec]
  rw [hsp]
  exact Entails.pure_right ⟨rfl, hx0, hx1, hx2, hx3, hfits⟩ (Entails.refl _)

private theorem markPoll_pre_intro_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64}
    {kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit}
    {kst0 : kpkKit.KpkState} {s : State}
    {sp fut self baseKeyA : BitVec 64} {id signedId : BitVec 32} {baseKey : PublicKey}
    (henv : kpkKit.envOk s.fs.files)
    (hsp : s.sp = sp)
    (hx0 : s.readReg64 .x0 = fut)
    (hx8 : s.readReg64 .x8 = sp + 0x3e0#64)
    (hmok : kpkKit.markOk id signedId baseKey)
    (hfits : FitsEnv M lim st (kpkKitEnv.markPollEnv kst0 id signedId baseKey)) :
    kpkKit.markBoxAt fut self baseKeyA id signedId 0#8 ∗
      kpkKit.storeAt self kst0 ∗
      memRegion (sp + 0x3e0#64) 48 ∗
      (baseKeyA ↦ₛ baseKey.bytes.toList) ∗
      A.pool lim st s ∗
      stackAt sp kpkKit.markPollStack ⊢
      (kitKpkMarkPollSpecE M A lim kpkKit kpkKitEnv).pre
        (({ fut := fut, out := sp + 0x3e0#64, self := self, baseKeyA := baseKeyA,
            id := id, signedId := signedId, baseKey := baseKey } : KyberMarkPollCall),
          kst0, st) s := by
  dsimp only [kitKpkMarkPollSpecE, withEnvPre, kitKpkMarkPollSpec]
  rw [hsp]
  exact Entails.pure_right henv (Entails.pure_right ⟨rfl, hx0, hx8, hmok, hfits⟩ (Entails.refl _))

/-! ## Allocation envelopes, spatial bundles, and mark-only kit -/

/-- `mark_kyber_pre_key_used` shim + poll + `Box` dealloc step envelope. -/
def MarkStepEnv {A : RustAlloc} {b : BitVec 64}
    (kpkKit : KyberPreKeyStoreSpec A b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (kst0 : kpkKit.KpkState) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (baseKey : PublicKey) : List AllocEvent → Prop :=
  SeqEnv (BoxAllocEnv kpkKit.markBoxSize)
    (SeqEnv (kpkKitEnv.markPollEnv kst0 kyberPreKeyId signedPreKeyId baseKey)
      (· = rustDeallocEvents kpkKit.markBoxSize 8))

/-- Allocation envelope on the `mark_kyber_pre_key_used = Err(e)` path of Stage P4.2:
`MarkStepEnv` followed by `FreeOnlyEvs` (`drop_glue<SessionStructure>` and `pt` buffer dealloc). -/
def StageP4MarkErrEnv {A : RustAlloc} {b : BitVec 64}
    (kpkKit : KyberPreKeyStoreSpec A b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (kst0 : kpkKit.KpkState) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (baseKey : PublicKey) : List AllocEvent → Prop :=
  SeqEnv (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey) FreeOnlyEvs

/-- Resources shared unchanged across Placed Substage P4.2 (`mark_kyber_pre_key_used`), separating
the stack-frame anchor `s` from the pool state `s_pool`. -/
def stageP4MarkKyberSharedPlaced {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (s0 s s_pool : State)
    (coroPtr msgPtr prevStatesPtr : BitVec 64)
    (baseKey : PublicKey) : SepProp :=
  ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
  ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
  ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
  ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
  memRegion (s.sp + 0x2e0#64) 36 ∗
  memRegion (s.sp + 0x370#64) 36 ∗
  memRegion (s.sp + 0x3e0#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
  A.pool lim st s_pool ∗
  stackAt s.sp (markKyberCallStack kpkKit)

/-- Spatial precondition of Placed Substage P4.2 at `0#64 + kpkKit.markShimOff`. -/
def stageP4MarkKyberPrePlaced {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (s0 s : State)
    (coroPtr msgPtr outPtr kyberStorePtr prevStatesPtr ptCap ptPtr : BitVec 64)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (baseKey : PublicKey) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ssSt : SessionState (List (BitVec 8))) : SepProp :=
  stageP4MarkKyberSharedPlaced A lim st0 kpkKit s0 s s coroPtr msgPtr prevStatesPtr baseKey ∗
  memRegion (coroPtr + 0x2c8#64) 16 ∗
  sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G ssSt ∗
  ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
  ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
  ((coroPtr + 0x290#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  memRegion outPtr 48 ∗
  kpkKit.storeAt kyberStorePtr kst0

/-- Spatial postcondition of Placed Substage P4.2 after `Ok(())` (at `+0x38c` or after deallocation). -/
def stageP4MarkKyberOkPostPlaced {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st1 : M.σ)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (s0 s s1 : State)
    (coroPtr msgPtr outPtr kyberStorePtr prevStatesPtr ptCap ptPtr : BitVec 64)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (baseKey : PublicKey) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ssSt : SessionState (List (BitVec 8))) : SepProp :=
  stageP4MarkKyberSharedPlaced A lim st1 kpkKit s0 s s1 coroPtr msgPtr prevStatesPtr baseKey ∗
  markKyberVtablesAt kpkKit ∗
  memRegion (coroPtr + 0x2c8#64) 16 ∗
  sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G ssSt ∗
  ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
  ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
  ((coroPtr + 0x290#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  memRegion outPtr 48 ∗
  kpkKit.storeAt kyberStorePtr (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()))

/-- Spatial postcondition of Placed Substage P4.2 on `Err(e)` at `s0.readReg64 .x30`. -/
def stageP4MarkKyberErrPostPlaced {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stf : M.σ)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (s0 s sf : State)
    (coroPtr msgPtr outPtr kyberStorePtr prevStatesPtr : BitVec 64)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (baseKey : PublicKey) (kst0 : kpkKit.KpkState) (e : kpkKit.MarkErr) : SepProp :=
  stageP4MarkKyberSharedPlaced A lim stf kpkKit s0 s sf coroPtr msgPtr prevStatesPtr baseKey ∗
  markKyberVtablesAt kpkKit ∗
  memRegion (coroPtr + 0x2c8#64) 16 ∗
  speErrAt kpkKit.markErr outPtr e ∗
  memRegion (coroPtr + 0xf8#64) 344 ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  kpkKit.storeAt kyberStorePtr
    (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.error e))

/-- Mark-only subset of budget-threaded `KyberPreKeyStoreKitPlacedOk` used by Stage P4.2. -/
structure KyberPreKeyMarkKitPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : KyberPreKeyStoreSpec A.repAlloc 0#64) (kitEnv : KyberPreKeyStoreBudgetEnv kit)
    (H : LibsignalHooks) : Prop where
  markShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.markShimOff)
      (withLsRoCl lsmpl (kitKpkMarkShimSpec M A lim kit))
  markPoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.markPollOff)
      (withLsRoCl lsmpl (kitKpkMarkPollSpecE M A lim kit kitEnv))
  markFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.markFutDropOff)
      (withLsRoCl lsmpl futDropBudgetSpec)

theorem kyberPreKeyMarkKitPlacedOk_of_store [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : KyberPreKeyStoreSpec A.repAlloc 0#64} {kitEnv : KyberPreKeyStoreBudgetEnv kit}
    {H : LibsignalHooks}
    (h : KyberPreKeyStoreKitPlacedOk A lim kit kitEnv H) :
    KyberPreKeyMarkKitPlacedOk A lim kit kitEnv H :=
  ⟨h.markShim, h.markPoll, h.markFutDrop⟩

/-! ## Budget-threaded Substage P4.2 dispatch proofs -/

set_option maxHeartbeats 1200000 in
theorem stageP4_markKyber_to_38c_vregs_mark_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hkpkKit : KyberPreKeyMarkKitPlacedOk A lim kpkKit kpkKitEnv ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qfs : Prop} {Qp : State → SepProp → Prop}
    (st0 : M.σ) (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr kyberStorePtr prevStatesPtr ptCap ptPtr : BitVec 64)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (baseKey : PublicKey) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ssSt : SessionState (List (BitVec 8)))
    (F : SepProp) (Q : State → SepProp → Prop)
    (hmarkOk : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hfits : FitsEnv M lim st0 (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : markKyberCallStack kpkKit ≤ 2 ^ 64)
    (hfs : FsAt kpkKit.envOk Qfs (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = 0#64 + kpkKit.markShimOff)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = kyberStorePtr)
    (hx1 : s.readReg64 .x1 = kyberPreKeyId.zeroExtend 64)
    (hx2 : s.readReg64 .x2 = signedPreKeyId.zeroExtend 64)
    (hx3 : s.readReg64 .x3 = msgPtr + 0xa8#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (_hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hlr : s.readReg64 .x30 = (blkPl_518).base + 0x350#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hOk38c : ∀ (boxPtr : BitVec 64) (evs_shim evs_poll : List AllocEvent)
      (s5 : State) (P5 : SepProp),
      BoxAllocEnv kpkKit.markBoxSize evs_shim →
      kpkKitEnv.markPollEnv kst0 kyberPreKeyId signedPreKeyId baseKey evs_poll →
      Steps (lsProg_518 ext) s s5 →
      kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()) →
      s5.pc = (blkPl_518).base + 0x38c#64 →
      s5.status = .Running →
      s5.sp = s.sp →
      s5.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) →
      s5.readReg64 .x19 = coroPtr →
      s5.readReg64 .x21 = boxPtr →
      s5.readReg64 .x23 = 0#64 + kpkKit.markFutVtOff →
      s5.readReg64 .x24 = s.sp + 0x370#64 →
      s5.readReg64 .x25 = s.sp + 0x210#64 →
      s5.readReg64 .x26 = outPtr →
      s5.readReg64 .x27 = ctxPtr →
      s5.readReg64 .x28 = 0xfffffffffffffffe#64 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s5.mem →
      calleeSavedVRegs s5 = calleeSavedVRegs s0 →
      (P5 ⊢
        A.live boxPtr (BitVec.ofNat 64 kpkKit.markBoxSize).toNat (8#64).toNat ∗
        memRegion boxPtr (BitVec.ofNat 64 kpkKit.markBoxSize).toNat ∗
        stageP4MarkKyberOkPostPlaced A lim
          (M.stepEvents evs_poll (M.stepEvents evs_shim st0))
          kpkKit s0 s s5 coroPtr msgPtr outPtr kyberStorePtr prevStatesPtr
          ptCap ptPtr kyberPreKeyId signedPreKeyId b_2c0 pt baseKey kst0 G ssSt ∗ F) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s5 P5 Q Qp)
    (hErr : ∀ (e : kpkKit.MarkErr) (evs : List AllocEvent) (sf : State) (Pf : SepProp),
      StageP4MarkErrEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey evs →
      Steps (lsProg_518 ext) s sf →
      kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢ stageP4MarkKyberErrPostPlaced A lim (M.stepEvents evs st0) kpkKit s0 s sf coroPtr
        msgPtr outPtr kyberStorePtr prevStatesPtr kyberPreKeyId signedPreKeyId baseKey kst0 e ∗ F) →
      Q sf Pf) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4MarkKyberPrePlaced A lim st0 kpkKit s0 s coroPtr msgPtr outPtr kyberStorePtr
        prevStatesPtr ptCap ptPtr b_2c0 pt baseKey kst0 G ssSt ∗ F)
      Q Qp := by
  have herr_ub : stageP4ErrUnwindStack ≤ 2 ^ 64 :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hsp_ub
  have hbox_eq : kpkKit.markBoxSize = (BitVec.ofNat 64 kpkKit.markBoxSize).toNat :=
    (Nat.mod_eq_of_lt kpkKit.markBoxSize_lt).symm
  have hsp_al : s.spAligned = true := hsp_align
  have hx1_w : s.readReg32 .x1 = kyberPreKeyId := by
    simp only [State.readReg32, hx1]; bv_omega
  have hx2_w : s.readReg32 .x2 = signedPreKeyId := by
    simp only [State.readReg32, hx2]; bv_omega
  refine sepWPp_intro_ro (R_ro := markKyberVtablesAt kpkKit)
    (fun hm => markKyberVtablesAt_placed_intro hkVt hcro.2 hm) ?_
  unfold stageP4MarkKyberPrePlaced stageP4MarkKyberSharedPlaced markKyberVtablesAt
  simp only [sepConj_assoc]
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_markKyber_to_shim kpkKit s.sp hsp_ub))
    (by sep_focus) ?_
  have hfits_box : FitsEnv M lim st0 (BoxAllocEnv kpkKit.markBoxSize) := hfits.seq_left
  refine call_rocl_entails_steps_frame_placed
    (spec := kitKpkMarkShimSpec M A lim kpkKit)
    (x := (({ self := kyberStorePtr, id := kyberPreKeyId,
              signedId := signedPreKeyId, baseKeyA := msgPtr + 0xa8#64 } : KyberMarkShimCall), st0))
    (P_spec := A.pool lim st0 s ∗ stackAt s.sp kpkKit.markShimStack)
    hcro (hkpkKit.markShim (by decide)) hpc hrun hsp_al hlr
    (markShim_pre_intro_placed rfl hx0 hx1_w hx2_w hx3 hfits_box)
    (by sep_focus)
    (hnext := fun s1 hst1 hpc1 hrun1 hsp1 hsp1_al hcs1 hcro1 => ?_)
    (hpan_false := fun _ => by unfold kitKpkMarkShimSpec; rfl)
    (hexit_false := fun _ _ => by unfold kitKpkMarkShimSpec; rfl)
    (hoom_false := fun _ => by unfold kitKpkMarkShimSpec; rfl)
  dsimp only [kitKpkMarkShimSpec]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_shim => ?_
  refine SepWPp.pure_elim fun ⟨hx1_1, _, _, htr1, hevs_shim⟩ => ?_
  have hfits_after_shim := hfits.seq_right hevs_shim
  have hfits_poll :
      FitsEnv M lim (M.stepEvents evs_shim st0)
        (kpkKitEnv.markPollEnv kst0 kyberPreKeyId signedPreKeyId baseKey) :=
    hfits_after_shim.seq_left
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_markKyber_to_shim kpkKit s.sp hsp_ub).symm)
    (by sep_focus) ?_
  rcases hcs1 with ⟨hx19_cs1, _, _, _, _, hx24_cs1, hx25_cs1, hx26_cs1, hx27_cs1, hx28_cs1, _, hvregs_cs1⟩
  have hfs1 := hfs.of_steps_nil hst1 htr1
  let boxPtr := s1.readReg64 .x0
  have h2c8_un :
      memRegion (coroPtr + 0x2c8#64) 16 =
      ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        ((coroPtr + 0x2c8#64) ↦₆₄ u0) ∗ ((coroPtr + 0x2d0#64) ↦₆₄ u1) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using memRegion16_eq_cells (coroPtr + 0x2c8#64)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq h2c8_un) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_2d0 => SepWPp.exists_elim fun u_2c8 => ?_
  have h2a := p4_seg2a_vregs_placed_wp (A := A) (lim := lim) ext (M.stepEvents evs_shim st0) s1
    coroPtr ctxPtr boxPtr (0#64 + kpkKit.markFutVtOff) (0#64 + kpkKit.markPollOff) u_2c8 u_2d0
    hpc1 hrun1 rfl hx1_1 (hx19_cs1.trans hx19) (hx27_cs1.trans hx27)
  refine bind_sepWP_steps_frame_placed hcro1 h2a (by sep_focus)
    fun s2 hst2 hpc2 hrun2 hcro2 ⟨hsp2_1, htr2_1, hx0_2, _, hx8_2,
      hx19_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _, hlr2, hvregs2_1⟩ => ?_
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_al : s2.spAligned = true := by simpa [State.spAligned, hsp2] using hsp_al
  have hfs2 := hfs1.of_steps_nil hst2 htr2_1
  rw [hsp1] at hx8_2
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_markKyber_to_poll kpkKit s.sp hsp_ub))
    (by sep_focus) ?_
  let pollCall : KyberMarkPollCall :=
    { fut := boxPtr
      out := s.sp + 0x3e0#64
      self := kyberStorePtr
      baseKeyA := msgPtr + 0xa8#64
      id := kyberPreKeyId
      signedId := signedPreKeyId
      baseKey := baseKey }
  refine call_rocl_entails_steps_frame_placed
    (spec := kitKpkMarkPollSpecE M A lim kpkKit kpkKitEnv)
    (x := (pollCall, kst0, M.stepEvents evs_shim st0))
    (P_spec := kpkKit.markBoxAt boxPtr kyberStorePtr (msgPtr + 0xa8#64) kyberPreKeyId signedPreKeyId 0#8 ∗
          kpkKit.storeAt kyberStorePtr kst0 ∗ memRegion (s.sp + 0x3e0#64) 48 ∗
          ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
          A.pool lim (M.stepEvents evs_shim st0) s2 ∗ stackAt s.sp kpkKit.markPollStack)
    hcro2 (hkpkKit.markPoll (by decide)) hpc2 hrun2 hsp2_al hlr2
    (markPoll_pre_intro_placed hfs2.envOk_here hsp2 hx0_2 hx8_2 hmarkOk hfits_poll)
    (by sep_focus)
    (hnext := fun s3 hst3 hpc3 hrun3 hsp3_2 hsp3_al hcs3 hcro3 => ?_)
  dsimp only [kitKpkMarkPollSpecE, withEnvPre, kitKpkMarkPollSpec, pollCall]
  rw [hsp2]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun ans => SepWPp.exists_elim fun evs_poll => ?_
  refine SepWPp.pure_elim fun ⟨hrel, htr3_2, hevs_poll⟩ => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_markKyber_to_poll kpkKit s.sp hsp_ub).symm)
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (memRegion36_eq_exists_stagingCells (s.sp + 0x2e0#64))) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_300s => SepWPp.exists_elim fun u_2f8s =>
    SepWPp.exists_elim fun u_2f0s => SepWPp.exists_elim fun u_2e8s =>
    SepWPp.exists_elim fun u_2e0s => ?_
  have hsp3 : s3.sp = s.sp := hsp3_2.trans hsp2
  rcases hcs3 with ⟨hx19_cs3, _, _, _, _, hx24_cs3, hx25_cs3, hx26_cs3, hx27_cs3, _, _, hvregs_cs3⟩
  have hvregs_3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 :=
    hvregs_cs3.trans (hvregs2_1.trans (hvregs_cs1.trans hvregs))
  have hx19_3 : s3.readReg64 .x19 = coroPtr := hx19_cs3.trans hx19_2
  have hx24_3 : s3.readReg64 .x24 = s3.sp + 0x370#64 := by
    rw [hx24_cs3, hx24_2, hx24_cs1, hx24, hsp3]
  have hx25_3 : s3.readReg64 .x25 = s3.sp + 0x210#64 := by
    rw [hx25_cs3, hx25_2, hx25_cs1, hx25, hsp3]
  have hx26_3 : s3.readReg64 .x26 = outPtr :=
    hx26_cs3.trans (hx26_2.trans (hx26_cs1.trans hx26))
  have hx27_3 : s3.readReg64 .x27 = ctxPtr := hx27_cs3.trans hx27_2
  have htr2_s : s2.trace = s.trace := htr2_1.trans htr1
  have hst_to3 : Steps (lsProg_518 ext) s s3 :=
    hst1.trans (hst2.trans hst3)
  have hfold_2c8 :
      ((coroPtr + 0x2c8#64) ↦₆₄ boxPtr) ∗
      ((coroPtr + 0x2d0#64) ↦₆₄ (0#64 + kpkKit.markFutVtOff)) ⊢
      memRegion (coroPtr + 0x2c8#64) 16 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      cells16_entails_memRegion16 (coroPtr + 0x2c8#64) _ _
  have hbox_dealloc :
      A.live boxPtr kpkKit.markBoxSize 8 ∗
      kpkKit.markBoxAt boxPtr kyberStorePtr (msgPtr + 0xa8#64) kyberPreKeyId signedPreKeyId 1#8 ⊢
      A.live boxPtr (BitVec.ofNat 64 kpkKit.markBoxSize).toNat (8#64).toNat ∗
      memRegion boxPtr (BitVec.ofNat 64 kpkKit.markBoxSize).toNat := by
    refine Entails.trans (sepConj_mono_right (kpkKit.markBoxAt_memRegion _ _ _ _ _ _)) ?_
    rw [← hbox_eq]; exact Entails.refl _
  let st_poll := M.stepEvents evs_poll (M.stepEvents evs_shim st0)
  rcases ans with e | ⟨⟩
  · -- Err(e): +0x180 → markFutDrop → +0x38c → +0x550 → x30
    let evs_mark := evs_shim ++ (evs_poll ++ rustDeallocEvents kpkKit.markBoxSize 8)
    have hevs_mark : MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey evs_mark :=
      SeqEnv.append hevs_shim (SeqEnv.append hevs_poll rfl)
    have hst_mark_eq :
        M.stepEvents (rustDeallocEvents (BitVec.ofNat 64 kpkKit.markBoxSize).toNat (8#64).toNat) st_poll =
        M.stepEvents evs_mark st0 := by
      have h8 : (8#64).toNat = 8 := rfl
      rw [← hbox_eq, h8]
      dsimp only [st_poll, evs_mark]
      simp only [AllocCostModel.stepEvents_append]
    dsimp only [kpkMarkPollOutAt, unitSpePollOutAt, speErrAt]
    simp only [sepConj_assoc]
    let S := kpkKit.markErr
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (speWordsAt_eq_pollCellsAt (s.sp + 0x3e0#64)
        (S.w0 e) (S.w1 e) (S.w2 e) (S.w3 e) (S.w4 e) (S.w5 e)))
      (by sep_focus) ?_
    have h2b := p4_seg2b_gen_vregs_placed_wp (A := A) (lim := lim) ext st_poll s3 coroPtr boxPtr
      (0#64 + kpkKit.markFutVtOff) (0#64 + kpkKit.markFutDropOff)
      (S.w0 e)
      ((S.w2 e).extractLsb' 0 32 ++ (S.w1 e).extractLsb' 32 32)
      ((S.w3 e).extractLsb' 0 32 ++ (S.w2 e).extractLsb' 32 32)
      ((S.w4 e).extractLsb' 0 32 ++ (S.w3 e).extractLsb' 32 32)
      ((S.w5 e).extractLsb' 0 32 ++ (S.w4 e).extractLsb' 32 32)
      u_2e0s u_2e8s u_2f0s u_2f8s
      ((S.w1 e).extractLsb' 0 32) ((S.w5 e).extractLsb' 32 32) u_300s
      (speErrSpec_w0_ne_pend S e) (kpkKit.markFutDrop_ne_zero rfl)
      hpc3 hrun3 hsp3_al hx19_3 hx24_3 hx25_3
    rw [hsp3] at h2b
    refine bind_sepWP_steps_frame_placed hcro3 h2b (by sep_focus)
      fun s4 hst4 hpc4 hrun4 hcro4 ⟨hsp4_3, htr4_3, _, hx19_4, hx21_4, hx22_4, hx23_4,
        hx24_4, hx25_4, hx26_4, _, hx28_4, _, hlr4, hvregs4_3⟩ => ?_
    have hsp4 : s4.sp = s.sp := hsp4_3
    have hsp4_al : s4.spAligned = true := by simpa [State.spAligned, hsp4] using hsp_al
    refine call_rocl_entails_steps_frame_placed
      (spec := futDropBudgetSpec) (x := ()) (P_spec := emp)
      hcro4 (hkpkKit.markFutDrop (by decide)) hpc4 hrun4 hsp4_al hlr4
      (Entails.refl _) (by sep_focus)
      (hpan_false := fun _ => by unfold futDropBudgetSpec; rfl)
      (hexit_false := fun _ _ => by unfold futDropBudgetSpec; rfl)
      (hoom_false := fun _ => by unfold futDropBudgetSpec; rfl)
      (hnext := fun s5 hst5 hpc5 hrun5 hsp5_4 hsp5_al hcs5 hcro5 => ?_)
    dsimp only [futDropBudgetSpec]
    refine SepWPp.pure_elim fun ⟨htr5_4, hvm5⟩ => ?_
    rw [← A.pool_transport lim st_poll s4 s5 hvm5]
    have hsp5 : s5.sp = s.sp := hsp5_4.trans hsp4
    rcases hcs5 with ⟨hx19_cs5, _, hx21_cs5, hx22_cs5, hx23_cs5, hx24_cs5, hx25_cs5,
      hx26_cs5, _, hx28_cs5, _, hvregs_cs5⟩
    refine P3P4.SepWPp.weaken_frame hbox_dealloc (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_markKyber_to_errUnwind kpkKit s.sp hsp_ub))
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub))
      (by sep_focus) ?_
    have h2c_err := p4_seg2c_err_vregs_placed_wp (A := A) (lim := lim) ext hdealloc st_poll s5
      coroPtr boxPtr (0#64 + kpkKit.markFutVtOff) (BitVec.ofNat 64 kpkKit.markBoxSize) 8#64
      (S.w0 e) kpkKit.markBoxSize_ne_zero (speErrSpec_w0_ne_ok S e) hpc5 hrun5 hsp5_al
      (hx19_cs5.trans hx19_4) (hx21_cs5.trans hx21_4) (hx23_cs5.trans hx23_4)
      (hx28_cs5.trans hx28_4)
    rw [hsp5] at h2c_err
    refine bind_sepWP_steps_frame_placed hcro5 h2c_err (by sep_focus)
      fun s6 hst6 hpc6 hrun6 hcro6 ⟨hsp6_5, htr6_5, hx8_6, hx19_6, hx22_6,
        hx24_6, hx25_6, hx26_6, _, hx28_6, _, hvregs6_5⟩ => ?_
    rw [hst_mark_eq]
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub).symm)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (pollCellsAt_entails_memRegion48 (s.sp + 0x3e0#64) _ _ _ _ _ _ _)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame hfold_2c8 (by sep_focus) ?_
    have hsp6 : s6.sp = s.sp := hsp6_5
    have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6]; exact hsp_align
    have hx22_6' : s6.readReg64 .x22 = ((S.w1 e).extractLsb' 0 32).zeroExtend 64 :=
      hx22_6.trans (hx22_cs5.trans hx22_4)
    have hx24_6' : s6.readReg64 .x24 = s6.sp + 0x370#64 := by
      rw [hx24_6, hx24_cs5, hx24_4, hsp6]
    have hx25_6' : s6.readReg64 .x25 = s6.sp + 0x210#64 := by
      rw [hx25_6, hx25_cs5, hx25_4, hsp6]
    have hx26_6' : s6.readReg64 .x26 = outPtr :=
      hx26_6.trans (hx26_cs5.trans (hx26_4.trans hx26_3))
    have hunwind := stageP4_err_unwind_550_vregs_placed_ok ext hdealloc hDropSS3
      (M.stepEvents evs_mark st0) s0 s6 coroPtr
      (s.sp + 0x2e0#64) ptCap ptPtr outPtr (S.w0 e) prevStatesPtr
      ((S.w2 e).extractLsb' 0 32 ++ (S.w1 e).extractLsb' 32 32)
      ((S.w3 e).extractLsb' 0 32 ++ (S.w2 e).extractLsb' 32 32)
      ((S.w4 e).extractLsb' 0 32 ++ (S.w3 e).extractLsb' 32 32)
      ((S.w5 e).extractLsb' 0 32 ++ (S.w4 e).extractLsb' 32 32)
      ((S.w1 e).extractLsb' 0 32) ((S.w5 e).extractLsb' 32 32)
      b_2c0 pt G ssSt (fun _ _ => False)
      hpt_le herr_ub hcro6 hpc6 hrun6 hsp6_align hx8_6 hx19_6 hx22_6'
      hx24_6' hx25_6' hx26_6' hx28_6
      (hvregs6_5.trans (hvregs_cs5.trans (hvregs4_3.trans hvregs_3)))
    rw [hsp6] at hunwind
    refine CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.SepWPp.bind_false_frame
      hunwind (by sep_focus)
      fun sf P1 hpcf hrunf ⟨hst_unw, ⟨evs_unw, hfree_unw, hP1⟩, hspf, htrf, hcsf, hvregsf, hcrof⟩ => ?_
    refine SepWPp.weaken_pre (sepConj_mono_left hP1) ?_
    have hst_all : Steps (lsProg_518 ext) s sf :=
      hst_to3.trans (hst4.trans (hst5.trans (hst6.trans hst_unw)))
    have htr_all :
        sf.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e) := by
      rw [htrf, htr6_5, htr5_4, htr4_3, htr3_2, htr2_s]
    have hevs_err :
        StageP4MarkErrEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey
          (evs_mark ++ evs_unw) :=
      SeqEnv.append hevs_mark hfree_unw
    have hst_err_eq :
        M.stepEvents evs_unw (M.stepEvents evs_mark st0) =
        M.stepEvents (evs_mark ++ evs_unw) st0 :=
      (M.stepEvents_append evs_mark evs_unw st0).symm
    refine SepWPp.done hpcf hrunf ?_
    refine hErr e (evs_mark ++ evs_unw) sf _ hevs_err hst_all hrel hpcf hrunf hspf htr_all
      hcsf hvregsf hcrof ?_
    rw [hst_err_eq]
    unfold stageP4MarkKyberErrPostPlaced stageP4MarkKyberSharedPlaced markKyberVtablesAt speErrAt
    rw [stack_markKyber_to_errUnwind kpkKit s.sp hsp_ub,
        speWordsAt_eq_pollCellsAt outPtr (S.w0 e) (S.w1 e) (S.w2 e) (S.w3 e) (S.w4 e) (S.w5 e)]
    exact Entails.of_eq (by sep_ac_rfl)
  · -- Ok(()) arm: +0x180 → markFutDrop → +0x38c
    dsimp only [kpkMarkPollOutAt]
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (unitSpePollOk_eq_exists_pollCells kpkKit.markErr (s.sp + 0x3e0#64)))
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun o1 => SepWPp.exists_elim fun o6 =>
      SepWPp.exists_elim fun o5 => SepWPp.exists_elim fun o4 =>
      SepWPp.exists_elim fun o3 => SepWPp.exists_elim fun o2 => ?_
    have h2b := p4_seg2b_gen_vregs_placed_wp (A := A) (lim := lim) ext st_poll s3 coroPtr boxPtr
      (0#64 + kpkKit.markFutVtOff) (0#64 + kpkKit.markFutDropOff)
      0xfffffffffffffffe#64 o2 o3 o4 o5 u_2e0s u_2e8s u_2f0s u_2f8s o1 o6 u_300s
      (by decide) (kpkKit.markFutDrop_ne_zero rfl)
      hpc3 hrun3 hsp3_al hx19_3 hx24_3 hx25_3
    rw [hsp3] at h2b
    refine bind_sepWP_steps_frame_placed hcro3 h2b (by sep_focus)
      fun s4 hst4 hpc4 hrun4 hcro4 ⟨hsp4_3, htr4_3, _, hx19_4, hx21_4, _, hx23_4,
        hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, _, hlr4, hvregs4_3⟩ => ?_
    have hsp4 : s4.sp = s.sp := hsp4_3
    have hsp4_al : s4.spAligned = true := by simpa [State.spAligned, hsp4] using hsp_al
    refine call_rocl_entails_steps_frame_placed
      (spec := futDropBudgetSpec) (x := ()) (P_spec := emp)
      hcro4 (hkpkKit.markFutDrop (by decide)) hpc4 hrun4 hsp4_al hlr4
      (Entails.refl _) (by sep_focus)
      (hpan_false := fun _ => by unfold futDropBudgetSpec; rfl)
      (hexit_false := fun _ _ => by unfold futDropBudgetSpec; rfl)
      (hoom_false := fun _ => by unfold futDropBudgetSpec; rfl)
      (hnext := fun s5 hst5 hpc5 hrun5 hsp5_4 _ hcs5 hcro5 => ?_)
    dsimp only [futDropBudgetSpec]
    refine SepWPp.pure_elim fun ⟨htr5_4, hvm5⟩ => ?_
    rw [← A.pool_transport lim st_poll s4 s5 hvm5]
    have hsp5 : s5.sp = s.sp := hsp5_4.trans hsp4
    rcases hcs5 with ⟨hx19_cs5, _, hx21_cs5, _, hx23_cs5, hx24_cs5, hx25_cs5,
      hx26_cs5, hx27_cs5, hx28_cs5, _, hvregs_cs5⟩
    refine P3P4.SepWPp.weaken_frame hbox_dealloc (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (stagingCellsAt_entails_memRegion36 (s.sp + 0x2e0#64) _ _ _ _ _)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (pollCellsAt_entails_memRegion48 (s.sp + 0x3e0#64) _ _ _ _ _ _ _)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame hfold_2c8 (by sep_focus) ?_
    have hst_all : Steps (lsProg_518 ext) s s5 :=
      hst_to3.trans (hst4.trans hst5)
    have htr_all :
        s5.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) := by
      rw [htr5_4, htr4_3, htr3_2, htr2_s]
    refine hOk38c boxPtr evs_shim evs_poll s5 _ hevs_shim hevs_poll hst_all hrel hpc5 hrun5 hsp5
      htr_all
      (hx19_cs5.trans hx19_4) (hx21_cs5.trans hx21_4) (hx23_cs5.trans hx23_4)
      (hx24_cs5.trans hx24_4) (hx25_cs5.trans hx25_4)
      (hx26_cs5.trans (hx26_4.trans hx26_3))
      (hx27_cs5.trans (hx27_4.trans hx27_3))
      (hx28_cs5.trans hx28_4) hcro5
      (hvregs_cs5.trans (hvregs4_3.trans hvregs_3)) ?_
    unfold stageP4MarkKyberOkPostPlaced stageP4MarkKyberSharedPlaced markKyberVtablesAt
    exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 800000 in
/-- Budget-threaded `[LibsignalPlacement]` Substage P4.2 (`None` OPK ID,
`markShim → +0x3cc` / `x30`) preserving `calleeSavedVRegs`. -/
theorem stageP4_markKyber_none_dispatch_vregs_mark_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hkpkKit : KyberPreKeyMarkKitPlacedOk A lim kpkKit kpkKitEnv ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qfs : Prop} {Qp : State → SepProp → Prop}
    (st0 : M.σ) (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr kyberStorePtr prevStatesPtr ptCap ptPtr : BitVec 64)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (baseKey : PublicKey) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ssSt : SessionState (List (BitVec 8)))
    (F : SepProp) (Q : State → SepProp → Prop)
    (hmarkOk : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hfits : FitsEnv M lim st0 (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : markKyberCallStack kpkKit ≤ 2 ^ 64)
    (hfs : FsAt kpkKit.envOk Qfs (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = 0#64 + kpkKit.markShimOff)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = kyberStorePtr)
    (hx1 : s.readReg64 .x1 = kyberPreKeyId.zeroExtend 64)
    (hx2 : s.readReg64 .x2 = signedPreKeyId.zeroExtend 64)
    (hx3 : s.readReg64 .x3 = msgPtr + 0xa8#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hlr : s.readReg64 .x30 = (blkPl_518).base + 0x350#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hOk : ∀ (evs : List AllocEvent) (s1 : State) (P1 : SepProp),
      MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey evs →
      Steps (lsProg_518 ext) s s1 →
      kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()) →
      s1.pc = (blkPl_518).base + 0x3cc#64 →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) →
      s1.readReg64 .x19 = coroPtr →
      s1.readReg64 .x24 = s.sp + 0x370#64 →
      s1.readReg64 .x25 = s.sp + 0x210#64 →
      s1.readReg64 .x26 = outPtr →
      s1.readReg64 .x27 = ctxPtr →
      s1.readReg64 .x28 = 0xfffffffffffffffe#64 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      (P1 ⊢
        stageP4MarkKyberOkPostPlaced A lim (M.stepEvents evs st0) kpkKit s0 s s1 coroPtr msgPtr
          outPtr kyberStorePtr prevStatesPtr ptCap ptPtr kyberPreKeyId signedPreKeyId b_2c0 pt
          baseKey kst0 G ssSt ∗
        ((coroPtr + 0x2ac#64) ↦₃₂ 0#32) ∗ F) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 P1 Q Qp)
    (hErr : ∀ (e : kpkKit.MarkErr) (evs : List AllocEvent) (sf : State) (Pf : SepProp),
      StageP4MarkErrEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey evs →
      Steps (lsProg_518 ext) s sf →
      kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢
        stageP4MarkKyberErrPostPlaced A lim (M.stepEvents evs st0) kpkKit s0 s sf coroPtr msgPtr
          outPtr kyberStorePtr prevStatesPtr kyberPreKeyId signedPreKeyId baseKey kst0 e ∗
        ((coroPtr + 0x2ac#64) ↦₃₂ 0#32) ∗ F) →
      Q sf Pf) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4MarkKyberPrePlaced A lim st0 kpkKit s0 s coroPtr msgPtr outPtr kyberStorePtr
        prevStatesPtr ptCap ptPtr b_2c0 pt baseKey kst0 G ssSt ∗
       ((coroPtr + 0x2ac#64) ↦₃₂ 0#32) ∗ F)
      Q Qp := by
  have herr_ub : stageP4ErrUnwindStack ≤ 2 ^ 64 :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hsp_ub
  have hbox_eq : kpkKit.markBoxSize = (BitVec.ofNat 64 kpkKit.markBoxSize).toNat :=
    (Nat.mod_eq_of_lt kpkKit.markBoxSize_lt).symm
  refine stageP4_markKyber_to_38c_vregs_mark_placed ext kpkKit kpkKitEnv hdealloc hDropSS3 hkpkKit
    hkVt st0 s0 s coroPtr ctxPtr msgPtr outPtr kyberStorePtr prevStatesPtr ptCap ptPtr
    kyberPreKeyId signedPreKeyId b_2c0 pt baseKey kst0 G ssSt
    (((coroPtr + 0x2ac#64) ↦₃₂ 0#32) ∗ F) Q
    hmarkOk hfits hpt_le hsp_ub hfs hcro hpc hrun hsp_align
    hx0 hx1 hx2 hx3 hx19 hx24 hx25 hx26 hx27 hx28 hlr hvregs
    (fun boxPtr evs_shim evs_poll s5 P5 hevs_shim hevs_poll hst5 hrel hpc5 hrun5 hsp5 htr5
      hx19_5 hx21_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx28_5 hcro5 hvregs5 hP5 => ?_)
    (fun e evs sf Pf hevs hstf hrel hpcf hrunf hspf htrf hcsf hvregsf hcrof hPf =>
      hErr e evs sf Pf hevs hstf hrel hpcf hrunf hspf htrf hcsf hvregsf hcrof
        (Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))))
  refine SepWPp.weaken_pre hP5 ?_
  unfold stageP4MarkKyberOkPostPlaced stageP4MarkKyberSharedPlaced markKyberVtablesAt
  simp only [sepConj_assoc]
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_markKyber_to_errUnwind kpkKit s.sp hsp_ub))
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub))
    (by sep_focus) ?_
  let st_poll := M.stepEvents evs_poll (M.stepEvents evs_shim st0)
  let evs_mark := evs_shim ++ (evs_poll ++ rustDeallocEvents kpkKit.markBoxSize 8)
  have hevs_mark : MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey evs_mark :=
    SeqEnv.append hevs_shim (SeqEnv.append hevs_poll rfl)
  have hst_mark_eq :
      M.stepEvents (rustDeallocEvents (BitVec.ofNat 64 kpkKit.markBoxSize).toNat (8#64).toNat) st_poll =
      M.stepEvents evs_mark st0 := by
    have h8 : (8#64).toNat = 8 := rfl
    rw [← hbox_eq, h8]
    dsimp only [st_poll, evs_mark]
    simp only [AllocCostModel.stepEvents_append]
  have hsp5_al : s5.spAligned = true := by simpa [State.spAligned, hsp5] using hsp_align
  have h2c := p4_seg2c_none_vregs_placed_wp (A := A) (lim := lim) ext hdealloc st_poll s5 coroPtr
    boxPtr (0#64 + kpkKit.markFutVtOff) (BitVec.ofNat 64 kpkKit.markBoxSize) 8#64
    kpkKit.markBoxSize_ne_zero hpc5 hrun5 hsp5_al hx19_5 hx21_5 hx23_5 hx28_5
  rw [hsp5] at h2c
  refine bind_sepWP_steps_frame_placed hcro5 h2c (by sep_focus)
    fun s6 hst6 hpc6 hrun6 hcro6 ⟨hsp6_5, htr6_5, hx19_6, hx24_6, hx25_6,
      hx26_6, hx27_6, hx28_6, _, hvregs6_5⟩ => ?_
  rw [hst_mark_eq]
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub).symm)
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_markKyber_to_errUnwind kpkKit s.sp hsp_ub).symm)
    (by sep_focus) ?_
  refine hOk evs_mark s6 _ hevs_mark (hst5.trans hst6) hrel hpc6 hrun6 hsp6_5 (htr6_5.trans htr5)
    hx19_6 (hx24_6.trans hx24_5) (hx25_6.trans hx25_5)
    (hx26_6.trans hx26_5) (hx27_6.trans hx27_5) hx28_6
    hcro6 (hvregs6_5.trans hvregs5) ?_
  unfold stageP4MarkKyberOkPostPlaced stageP4MarkKyberSharedPlaced markKyberVtablesAt
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 800000 in
/-- Budget-threaded `[LibsignalPlacement]` Substage P4.2 (`Some` OPK ID,
`markShim → removePreKeyShimAddr` / `x30`) preserving `calleeSavedVRegs`. -/
theorem stageP4_markKyber_some_dispatch_vregs_mark_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hkpkKit : KyberPreKeyMarkKitPlacedOk A lim kpkKit kpkKitEnv ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qfs : Prop} {Qp : State → SepProp → Prop}
    (st0 : M.σ) (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr kyberStorePtr preKeyStorePtr preKeyStoreVt
     removePreKeyShimAddr prevStatesPtr ptCap ptPtr : BitVec 64)
    (opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (baseKey : PublicKey) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ssSt : SessionState (List (BitVec 8)))
    (F : SepProp) (Q : State → SepProp → Prop)
    (hmarkOk : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hfits : FitsEnv M lim st0 (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : markKyberCallStack kpkKit ≤ 2 ^ 64)
    (hpSlot : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
      m ⊨ ((preKeyStoreVt + 0x28#64) ↦₆₄ᵣ removePreKeyShimAddr) ∗ P)
    (hfs : FsAt kpkKit.envOk Qfs (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = 0#64 + kpkKit.markShimOff)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = kyberStorePtr)
    (hx1 : s.readReg64 .x1 = kyberPreKeyId.zeroExtend 64)
    (hx2 : s.readReg64 .x2 = signedPreKeyId.zeroExtend 64)
    (hx3 : s.readReg64 .x3 = msgPtr + 0xa8#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hlr : s.readReg64 .x30 = (blkPl_518).base + 0x350#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hOk : ∀ (evs : List AllocEvent) (s1 : State) (P1 : SepProp),
      MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey evs →
      Steps (lsProg_518 ext) s s1 →
      kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()) →
      s1.pc = removePreKeyShimAddr →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) →
      s1.readReg64 .x0 = preKeyStorePtr →
      s1.readReg64 .x1 = opkId.zeroExtend 64 →
      s1.readReg64 .x19 = coroPtr →
      s1.readReg64 .x24 = s.sp + 0x370#64 →
      s1.readReg64 .x25 = s.sp + 0x210#64 →
      s1.readReg64 .x26 = outPtr →
      s1.readReg64 .x27 = ctxPtr →
      s1.readReg64 .x28 = 0xfffffffffffffffe#64 →
      s1.readReg64 .x30 = (blkPl_518).base + 0x3c0#64 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      (P1 ⊢
        stageP4MarkKyberOkPostPlaced A lim (M.stepEvents evs st0) kpkKit s0 s s1 coroPtr msgPtr
          outPtr kyberStorePtr prevStatesPtr ptCap ptPtr kyberPreKeyId signedPreKeyId b_2c0 pt
          baseKey kst0 G ssSt ∗
        ((preKeyStoreVt + 0x28#64) ↦₆₄ᵣ removePreKeyShimAddr) ∗
        ((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
        ((coroPtr + 0xb0#64) ↦₆₄ preKeyStoreVt) ∗
        ((coroPtr + 0x2ac#64) ↦₃₂ 1#32) ∗
        ((coroPtr + 0x2b0#64) ↦₃₂ opkId) ∗ F) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 P1 Q Qp)
    (hErr : ∀ (e : kpkKit.MarkErr) (evs : List AllocEvent) (sf : State) (Pf : SepProp),
      StageP4MarkErrEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey evs →
      Steps (lsProg_518 ext) s sf →
      kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢
        stageP4MarkKyberErrPostPlaced A lim (M.stepEvents evs st0) kpkKit s0 s sf coroPtr msgPtr
          outPtr kyberStorePtr prevStatesPtr kyberPreKeyId signedPreKeyId baseKey kst0 e ∗
        ((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
        ((coroPtr + 0xb0#64) ↦₆₄ preKeyStoreVt) ∗
        ((coroPtr + 0x2ac#64) ↦₃₂ 1#32) ∗
        ((coroPtr + 0x2b0#64) ↦₃₂ opkId) ∗ F) →
      Q sf Pf) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4MarkKyberPrePlaced A lim st0 kpkKit s0 s coroPtr msgPtr outPtr kyberStorePtr
        prevStatesPtr ptCap ptPtr b_2c0 pt baseKey kst0 G ssSt ∗
       ((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
       ((coroPtr + 0xb0#64) ↦₆₄ preKeyStoreVt) ∗
       ((coroPtr + 0x2ac#64) ↦₃₂ 1#32) ∗
       ((coroPtr + 0x2b0#64) ↦₃₂ opkId) ∗ F)
      Q Qp := by
  have herr_ub : stageP4ErrUnwindStack ≤ 2 ^ 64 :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hsp_ub
  have hbox_eq : kpkKit.markBoxSize = (BitVec.ofNat 64 kpkKit.markBoxSize).toNat :=
    (Nat.mod_eq_of_lt kpkKit.markBoxSize_lt).symm
  refine stageP4_markKyber_to_38c_vregs_mark_placed ext kpkKit kpkKitEnv hdealloc hDropSS3 hkpkKit
    hkVt st0 s0 s coroPtr ctxPtr msgPtr outPtr kyberStorePtr prevStatesPtr ptCap ptPtr
    kyberPreKeyId signedPreKeyId b_2c0 pt baseKey kst0 G ssSt
    (((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
     ((coroPtr + 0xb0#64) ↦₆₄ preKeyStoreVt) ∗
     ((coroPtr + 0x2ac#64) ↦₃₂ 1#32) ∗
     ((coroPtr + 0x2b0#64) ↦₃₂ opkId) ∗ F) Q
    hmarkOk hfits hpt_le hsp_ub hfs hcro hpc hrun hsp_align
    hx0 hx1 hx2 hx3 hx19 hx24 hx25 hx26 hx27 hx28 hlr hvregs
    (fun boxPtr evs_shim evs_poll s5 P5 hevs_shim hevs_poll hst5 hrel hpc5 hrun5 hsp5 htr5
      hx19_5 hx21_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx28_5 hcro5 hvregs5 hP5 => ?_)
    (fun e evs sf Pf hevs hstf hrel hpcf hrunf hspf htrf hcsf hvregsf hcrof hPf =>
      hErr e evs sf Pf hevs hstf hrel hpcf hrunf hspf htrf hcsf hvregsf hcrof
        (Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))))
  refine SepWPp.weaken_pre hP5 ?_
  refine sepWPp_intro_ro (R_ro := ((preKeyStoreVt + 0x28#64) ↦₆₄ᵣ removePreKeyShimAddr))
    (fun hm => hpSlot hcro5.2 hm) ?_
  unfold stageP4MarkKyberOkPostPlaced stageP4MarkKyberSharedPlaced markKyberVtablesAt
  simp only [sepConj_assoc]
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_markKyber_to_errUnwind kpkKit s.sp hsp_ub))
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub))
    (by sep_focus) ?_
  let st_poll := M.stepEvents evs_poll (M.stepEvents evs_shim st0)
  let evs_mark := evs_shim ++ (evs_poll ++ rustDeallocEvents kpkKit.markBoxSize 8)
  have hevs_mark : MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey evs_mark :=
    SeqEnv.append hevs_shim (SeqEnv.append hevs_poll rfl)
  have hst_mark_eq :
      M.stepEvents (rustDeallocEvents (BitVec.ofNat 64 kpkKit.markBoxSize).toNat (8#64).toNat) st_poll =
      M.stepEvents evs_mark st0 := by
    have h8 : (8#64).toNat = 8 := rfl
    rw [← hbox_eq, h8]
    dsimp only [st_poll, evs_mark]
    simp only [AllocCostModel.stepEvents_append]
  have hsp5_al : s5.spAligned = true := by simpa [State.spAligned, hsp5] using hsp_align
  have h2c := p4_seg2c_some_vregs_placed_wp (A := A) (lim := lim) ext hdealloc st_poll s5 coroPtr
    preKeyStorePtr preKeyStoreVt removePreKeyShimAddr boxPtr (0#64 + kpkKit.markFutVtOff)
    (BitVec.ofNat 64 kpkKit.markBoxSize) 8#64 opkId
    kpkKit.markBoxSize_ne_zero hpc5 hrun5 hsp5_al hx19_5 hx21_5 hx23_5 hx28_5
  rw [hsp5] at h2c
  refine bind_sepWP_steps_frame_placed hcro5 h2c (by sep_focus)
    fun s6 hst6 hpc6 hrun6 hcro6 ⟨hsp6_5, htr6_5, hx0_6, hx1_6, hx19_6,
      hx24_6, hx25_6, hx26_6, hx27_6, hx28_6, _, hlr6, hvregs6_5⟩ => ?_
  rw [hst_mark_eq]
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub).symm)
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_markKyber_to_errUnwind kpkKit s.sp hsp_ub).symm)
    (by sep_focus) ?_
  refine hOk evs_mark s6 _ hevs_mark (hst5.trans hst6) hrel hpc6 hrun6 hsp6_5 (htr6_5.trans htr5)
    hx0_6 hx1_6 hx19_6 (hx24_6.trans hx24_5) (hx25_6.trans hx25_5)
    (hx26_6.trans hx26_5) (hx27_6.trans hx27_5) hx28_6 hlr6
    hcro6 (hvregs6_5.trans hvregs5) ?_
  unfold stageP4MarkKyberOkPostPlaced stageP4MarkKyberSharedPlaced markKyberVtablesAt
  exact Entails.of_eq (by sep_ac_rfl)

theorem stageP4_markKyber_to_38c_vregs_kits_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hkpkKit : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkKitEnv ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qfs : Prop} {Qp : State → SepProp → Prop}
    (st0 : M.σ) (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr kyberStorePtr prevStatesPtr ptCap ptPtr : BitVec 64)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (baseKey : PublicKey) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ssSt : SessionState (List (BitVec 8)))
    (F : SepProp) (Q : State → SepProp → Prop)
    (hmarkOk : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hfits : FitsEnv M lim st0 (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : markKyberCallStack kpkKit ≤ 2 ^ 64)
    (hfs : FsAt kpkKit.envOk Qfs (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = 0#64 + kpkKit.markShimOff)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = kyberStorePtr)
    (hx1 : s.readReg64 .x1 = kyberPreKeyId.zeroExtend 64)
    (hx2 : s.readReg64 .x2 = signedPreKeyId.zeroExtend 64)
    (hx3 : s.readReg64 .x3 = msgPtr + 0xa8#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hlr : s.readReg64 .x30 = (blkPl_518).base + 0x350#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hOk38c : ∀ (boxPtr : BitVec 64) (evs_shim evs_poll : List AllocEvent)
      (s5 : State) (P5 : SepProp),
      BoxAllocEnv kpkKit.markBoxSize evs_shim →
      kpkKitEnv.markPollEnv kst0 kyberPreKeyId signedPreKeyId baseKey evs_poll →
      Steps (lsProg_518 ext) s s5 →
      kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()) →
      s5.pc = (blkPl_518).base + 0x38c#64 →
      s5.status = .Running →
      s5.sp = s.sp →
      s5.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) →
      s5.readReg64 .x19 = coroPtr →
      s5.readReg64 .x21 = boxPtr →
      s5.readReg64 .x23 = 0#64 + kpkKit.markFutVtOff →
      s5.readReg64 .x24 = s.sp + 0x370#64 →
      s5.readReg64 .x25 = s.sp + 0x210#64 →
      s5.readReg64 .x26 = outPtr →
      s5.readReg64 .x27 = ctxPtr →
      s5.readReg64 .x28 = 0xfffffffffffffffe#64 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s5.mem →
      calleeSavedVRegs s5 = calleeSavedVRegs s0 →
      (P5 ⊢
        A.live boxPtr (BitVec.ofNat 64 kpkKit.markBoxSize).toNat (8#64).toNat ∗
        memRegion boxPtr (BitVec.ofNat 64 kpkKit.markBoxSize).toNat ∗
        stageP4MarkKyberOkPostPlaced A lim
          (M.stepEvents evs_poll (M.stepEvents evs_shim st0))
          kpkKit s0 s s5 coroPtr msgPtr outPtr kyberStorePtr prevStatesPtr
          ptCap ptPtr kyberPreKeyId signedPreKeyId b_2c0 pt baseKey kst0 G ssSt ∗ F) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s5 P5 Q Qp)
    (hErr : ∀ (e : kpkKit.MarkErr) (evs : List AllocEvent) (sf : State) (Pf : SepProp),
      StageP4MarkErrEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey evs →
      Steps (lsProg_518 ext) s sf →
      kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢ stageP4MarkKyberErrPostPlaced A lim (M.stepEvents evs st0) kpkKit s0 s sf coroPtr
        msgPtr outPtr kyberStorePtr prevStatesPtr kyberPreKeyId signedPreKeyId baseKey kst0 e ∗ F) →
      Q sf Pf) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4MarkKyberPrePlaced A lim st0 kpkKit s0 s coroPtr msgPtr outPtr kyberStorePtr
        prevStatesPtr ptCap ptPtr b_2c0 pt baseKey kst0 G ssSt ∗ F)
      Q Qp :=
  stageP4_markKyber_to_38c_vregs_mark_placed ext kpkKit kpkKitEnv hdealloc hDropSS3
    (kyberPreKeyMarkKitPlacedOk_of_store hkpkKit) hkVt st0 s0 s coroPtr ctxPtr msgPtr outPtr
    kyberStorePtr prevStatesPtr ptCap ptPtr kyberPreKeyId signedPreKeyId b_2c0 pt baseKey kst0
    G ssSt F Q hmarkOk hfits hpt_le hsp_ub hfs hcro hpc hrun hsp_align hx0 hx1 hx2 hx3 hx19
    hx24 hx25 hx26 hx27 hx28 hlr hvregs hOk38c hErr

theorem stageP4_markKyber_none_dispatch_vregs_kits_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hkpkKit : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkKitEnv ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qfs : Prop} {Qp : State → SepProp → Prop}
    (st0 : M.σ) (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr kyberStorePtr prevStatesPtr ptCap ptPtr : BitVec 64)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (baseKey : PublicKey) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ssSt : SessionState (List (BitVec 8)))
    (F : SepProp) (Q : State → SepProp → Prop)
    (hmarkOk : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hfits : FitsEnv M lim st0 (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : markKyberCallStack kpkKit ≤ 2 ^ 64)
    (hfs : FsAt kpkKit.envOk Qfs (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = 0#64 + kpkKit.markShimOff)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = kyberStorePtr)
    (hx1 : s.readReg64 .x1 = kyberPreKeyId.zeroExtend 64)
    (hx2 : s.readReg64 .x2 = signedPreKeyId.zeroExtend 64)
    (hx3 : s.readReg64 .x3 = msgPtr + 0xa8#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hlr : s.readReg64 .x30 = (blkPl_518).base + 0x350#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hOk : ∀ (evs : List AllocEvent) (s1 : State) (P1 : SepProp),
      MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey evs →
      Steps (lsProg_518 ext) s s1 →
      kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()) →
      s1.pc = (blkPl_518).base + 0x3cc#64 →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) →
      s1.readReg64 .x19 = coroPtr →
      s1.readReg64 .x24 = s.sp + 0x370#64 →
      s1.readReg64 .x25 = s.sp + 0x210#64 →
      s1.readReg64 .x26 = outPtr →
      s1.readReg64 .x27 = ctxPtr →
      s1.readReg64 .x28 = 0xfffffffffffffffe#64 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      (P1 ⊢
        stageP4MarkKyberOkPostPlaced A lim (M.stepEvents evs st0) kpkKit s0 s s1 coroPtr msgPtr
          outPtr kyberStorePtr prevStatesPtr ptCap ptPtr kyberPreKeyId signedPreKeyId b_2c0 pt
          baseKey kst0 G ssSt ∗
        ((coroPtr + 0x2ac#64) ↦₃₂ 0#32) ∗ F) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 P1 Q Qp)
    (hErr : ∀ (e : kpkKit.MarkErr) (evs : List AllocEvent) (sf : State) (Pf : SepProp),
      StageP4MarkErrEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey evs →
      Steps (lsProg_518 ext) s sf →
      kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢
        stageP4MarkKyberErrPostPlaced A lim (M.stepEvents evs st0) kpkKit s0 s sf coroPtr msgPtr
          outPtr kyberStorePtr prevStatesPtr kyberPreKeyId signedPreKeyId baseKey kst0 e ∗
        ((coroPtr + 0x2ac#64) ↦₃₂ 0#32) ∗ F) →
      Q sf Pf) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4MarkKyberPrePlaced A lim st0 kpkKit s0 s coroPtr msgPtr outPtr kyberStorePtr
        prevStatesPtr ptCap ptPtr b_2c0 pt baseKey kst0 G ssSt ∗
       ((coroPtr + 0x2ac#64) ↦₃₂ 0#32) ∗ F)
      Q Qp :=
  stageP4_markKyber_none_dispatch_vregs_mark_placed ext kpkKit kpkKitEnv hdealloc hDropSS3
    (kyberPreKeyMarkKitPlacedOk_of_store hkpkKit) hkVt st0 s0 s coroPtr ctxPtr msgPtr outPtr
    kyberStorePtr prevStatesPtr ptCap ptPtr kyberPreKeyId signedPreKeyId b_2c0 pt baseKey kst0
    G ssSt F Q hmarkOk hfits hpt_le hsp_ub hfs hcro hpc hrun hsp_align hx0 hx1 hx2 hx3 hx19
    hx24 hx25 hx26 hx27 hx28 hlr hvregs hOk hErr

theorem stageP4_markKyber_some_dispatch_vregs_kits_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hkpkKit : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkKitEnv ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qfs : Prop} {Qp : State → SepProp → Prop}
    (st0 : M.σ) (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr kyberStorePtr preKeyStorePtr preKeyStoreVt
     removePreKeyShimAddr prevStatesPtr ptCap ptPtr : BitVec 64)
    (opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (baseKey : PublicKey) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ssSt : SessionState (List (BitVec 8)))
    (F : SepProp) (Q : State → SepProp → Prop)
    (hmarkOk : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hfits : FitsEnv M lim st0 (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : markKyberCallStack kpkKit ≤ 2 ^ 64)
    (hpSlot : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
      m ⊨ ((preKeyStoreVt + 0x28#64) ↦₆₄ᵣ removePreKeyShimAddr) ∗ P)
    (hfs : FsAt kpkKit.envOk Qfs (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = 0#64 + kpkKit.markShimOff)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = kyberStorePtr)
    (hx1 : s.readReg64 .x1 = kyberPreKeyId.zeroExtend 64)
    (hx2 : s.readReg64 .x2 = signedPreKeyId.zeroExtend 64)
    (hx3 : s.readReg64 .x3 = msgPtr + 0xa8#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hlr : s.readReg64 .x30 = (blkPl_518).base + 0x350#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hOk : ∀ (evs : List AllocEvent) (s1 : State) (P1 : SepProp),
      MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey evs →
      Steps (lsProg_518 ext) s s1 →
      kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()) →
      s1.pc = removePreKeyShimAddr →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) →
      s1.readReg64 .x0 = preKeyStorePtr →
      s1.readReg64 .x1 = opkId.zeroExtend 64 →
      s1.readReg64 .x19 = coroPtr →
      s1.readReg64 .x24 = s.sp + 0x370#64 →
      s1.readReg64 .x25 = s.sp + 0x210#64 →
      s1.readReg64 .x26 = outPtr →
      s1.readReg64 .x27 = ctxPtr →
      s1.readReg64 .x28 = 0xfffffffffffffffe#64 →
      s1.readReg64 .x30 = (blkPl_518).base + 0x3c0#64 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      (P1 ⊢
        stageP4MarkKyberOkPostPlaced A lim (M.stepEvents evs st0) kpkKit s0 s s1 coroPtr msgPtr
          outPtr kyberStorePtr prevStatesPtr ptCap ptPtr kyberPreKeyId signedPreKeyId b_2c0 pt
          baseKey kst0 G ssSt ∗
        ((preKeyStoreVt + 0x28#64) ↦₆₄ᵣ removePreKeyShimAddr) ∗
        ((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
        ((coroPtr + 0xb0#64) ↦₆₄ preKeyStoreVt) ∗
        ((coroPtr + 0x2ac#64) ↦₃₂ 1#32) ∗
        ((coroPtr + 0x2b0#64) ↦₃₂ opkId) ∗ F) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 P1 Q Qp)
    (hErr : ∀ (e : kpkKit.MarkErr) (evs : List AllocEvent) (sf : State) (Pf : SepProp),
      StageP4MarkErrEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey evs →
      Steps (lsProg_518 ext) s sf →
      kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢
        stageP4MarkKyberErrPostPlaced A lim (M.stepEvents evs st0) kpkKit s0 s sf coroPtr msgPtr
          outPtr kyberStorePtr prevStatesPtr kyberPreKeyId signedPreKeyId baseKey kst0 e ∗
        ((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
        ((coroPtr + 0xb0#64) ↦₆₄ preKeyStoreVt) ∗
        ((coroPtr + 0x2ac#64) ↦₃₂ 1#32) ∗
        ((coroPtr + 0x2b0#64) ↦₃₂ opkId) ∗ F) →
      Q sf Pf) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4MarkKyberPrePlaced A lim st0 kpkKit s0 s coroPtr msgPtr outPtr kyberStorePtr
        prevStatesPtr ptCap ptPtr b_2c0 pt baseKey kst0 G ssSt ∗
       ((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
       ((coroPtr + 0xb0#64) ↦₆₄ preKeyStoreVt) ∗
       ((coroPtr + 0x2ac#64) ↦₃₂ 1#32) ∗
       ((coroPtr + 0x2b0#64) ↦₃₂ opkId) ∗ F)
      Q Qp :=
  stageP4_markKyber_some_dispatch_vregs_mark_placed ext kpkKit kpkKitEnv hdealloc hDropSS3
    (kyberPreKeyMarkKitPlacedOk_of_store hkpkKit) hkVt st0 s0 s coroPtr ctxPtr msgPtr outPtr
    kyberStorePtr preKeyStorePtr preKeyStoreVt removePreKeyShimAddr prevStatesPtr ptCap ptPtr opkId
    kyberPreKeyId signedPreKeyId b_2c0 pt baseKey kst0 G ssSt F Q hmarkOk hfits hpt_le hsp_ub
    hpSlot hfs hcro hpc hrun hsp_align hx0 hx1 hx2 hx3 hx19 hx24 hx25 hx26 hx27 hx28 hlr hvregs
    hOk hErr

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberProofPlacedBudget
