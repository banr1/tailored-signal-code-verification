/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1TrustExtPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrap
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Stage P1 `is_trusted_identity` Step

Proves `RustCliAllocBudget M` / `VmPreserved` `is_trusted_identity` call and trusted-continuation
theorems (`0#64 + ikit.trustShimOff → +0x6e4` / `+0x868`) on Block `518` under `TrustStepEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1TrustExtPlacedBudget

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit hiding kitTrustPollPlacedSpecI kitTrustShimSpec
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity hiding kitTrustShimSpec
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv VmPreserved
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv futDropBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (
  IdentityStoreBudgetEnv TrustStepEnv kitTrustShimSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (kitTrustPollPlacedSpecI)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlacedBudget (
  p1_seg5_vregs_wp_ext_placed p1_post_dealloc_true_vregs_wp_ext_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrustTailsXExtPlacedBudget (
  bind_sepWP_steps_frame_placed ret_sepWP_steps_frame_placed call_rocl_entails_steps_frame_placed
  trustShim_pre_intro_placed trustPoll_pre_intro_placed stageP1_trust_call_tail_x_ext_placed
)

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

private theorem sepWPp_perm_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hwp : SepWPp prog ret s P' Q Qp) (h : P = P' ∗ emp) :
    SepWPp prog ret s P Q Qp := by
  rw [h, sepConj_emp]; exact hwp

private theorem sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Q' Qp : State → SepProp → Prop}
    (hwp : SepWPp prog ret s P Q Qp)
    (hq : ∀ sf P_f, Q sf P_f → Q' sf P_f) :
    SepWPp prog ret s P Q' Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpc, hrun, P_f, hmf, hQ⟩ | hrest
  · exact Or.inl ⟨hpc, hrun, P_f, hmf, hq sf P_f hQ⟩
  · exact Or.inr hrest

private theorem bind_sepWPp_nopanic_frame {prog : Program}
    {mid ret : BitVec 64} {s : State}
    {P P_call F : SepProp}
    {Q1 Q Qp : State → SepProp → Prop}
    (hcall : SepWPp prog mid s P_call Q1 (fun _ _ => False))
    (hP : P = P_call ∗ F)
    (hnext : ∀ (sm : State) (P_m : SepProp), Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Q1 sm P_m → SepWPp prog ret sm (P_m ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hQ1⟩ | ⟨_, _, _, hfalse⟩ | ⟨_, hoom⟩⟩ :=
    hcall (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm P_m hsteps hpcm hrunm hQ1 R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact hfalse.elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem trust_call_wp_specialize_true_prog_placed [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist : ikit.IdState}
    {peer : AddrGhost} {remoteIdKey : IdentityKey}
    {s : State} {P : SepProp} {Qp : State → SepProp → Prop}
    {outPtr coroPtr ctxPtr msgPtr remoteAddrPtr idStorePtr : BitVec 64}
    (htrust_true : ∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok true)
    (hcall : SepWPp prog ret s P
      (fun sm P_m =>
        (∃ (ans : Except Unit Bool) (evs : List AllocEvent),
          ikit.trustRel ist peer.val remoteIdKey .receiving ans ∧
          TrustStepEnv ikit ikitEnv ist peer.val remoteIdKey .receiving evs ∧
          sm.trace = s.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving ans ∧
          sm.readReg64 .x20 = trustPollTag ans ∧
          (ans = .ok true → sm.readReg64 .x23 = 1#64) ∧
          (ans = .ok false → sm.readReg64 .x23 = 0#64) ∧
          (P_m ⊢
            ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
              cells (coroPtr + 0x398#64) 2 ∗
              ((s.sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((s.sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
              ((s.sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
              ((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗
              memRegion (s.sp + 0x3e0#64) 368 ∗
              ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
              ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
              ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
              ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
              (if ans.isOk then emp
               else (∃∗ strPtr : BitVec 64, strPtr ↦ᵣ storeHookStr)) ∗
              FromRecordCallees.lsLogOff ∗
              ikit.identityAt idStorePtr
                (ikit.trustUpdate ist peer.val remoteIdKey .receiving ans) ∗
              protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
              ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
              A.pool lim (M.stepEvents evs st0) sm ∗
              stackAt s.sp (trustCallStack ikit))) ∧
        sm.sp = s.sp ∧
        sm.readReg64 .x19 = coroPtr ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem)
      Qp) :
    SepWPp prog ret s P
      (fun sm P_m =>
        (∃ evs : List AllocEvent,
          TrustStepEnv ikit ikitEnv ist peer.val remoteIdKey .receiving evs ∧
          (P_m ⊢
            ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
              cells (coroPtr + 0x398#64) 2 ∗
              ((s.sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((s.sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
              ((s.sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
              ((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗
              memRegion (s.sp + 0x3e0#64) 368 ∗
              ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
              ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
              ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
              ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
              FromRecordCallees.lsLogOff ∗
              ikit.identityAt idStorePtr
                (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok true)) ∗
              protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
              ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
              A.pool lim (M.stepEvents evs st0) sm ∗
              stackAt s.sp (trustCallStack ikit))) ∧
        ikit.trustRel ist peer.val remoteIdKey .receiving (.ok true) ∧
        sm.trace = s.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving (.ok true) ∧
        sm.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        sm.readReg64 .x23 = 1#64 ∧
        sm.sp = s.sp ∧
        sm.readReg64 .x19 = coroPtr ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem)
      Qp := by
  refine sepWPp_mono_post hcall fun sm P_m h => ?_
  rcases h with ⟨⟨ans, evs, hrel, henv, htrm, hx20, htrue, _, hent⟩, hsp, hx19, hx29, hvregs, hcrlm⟩
  have hans : ans = .ok true := htrust_true ans hrel
  subst hans
  dsimp only [Except.isOk, Except.toBool, trustPollTag] at hent hx20
  simp only [↓reduceIte, emp_sepConj] at hent
  exact ⟨⟨evs, henv, hent⟩, hrel, htrm, hx20, htrue rfl, hsp, hx19, hx29, hvregs, hcrlm⟩

theorem trust_call_wp_specialize_false_prog_placed [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist : ikit.IdState}
    {peer : AddrGhost} {remoteIdKey : IdentityKey}
    {s : State} {P : SepProp} {Qp : State → SepProp → Prop}
    {outPtr coroPtr ctxPtr msgPtr remoteAddrPtr idStorePtr : BitVec 64}
    (htrust_false : ∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok false)
    (hcall : SepWPp prog ret s P
      (fun sm P_m =>
        (∃ (ans : Except Unit Bool) (evs : List AllocEvent),
          ikit.trustRel ist peer.val remoteIdKey .receiving ans ∧
          TrustStepEnv ikit ikitEnv ist peer.val remoteIdKey .receiving evs ∧
          sm.trace = s.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving ans ∧
          sm.readReg64 .x20 = trustPollTag ans ∧
          (ans = .ok true → sm.readReg64 .x23 = 1#64) ∧
          (ans = .ok false → sm.readReg64 .x23 = 0#64) ∧
          (P_m ⊢
            ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
              cells (coroPtr + 0x398#64) 2 ∗
              ((s.sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((s.sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
              ((s.sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
              ((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗
              memRegion (s.sp + 0x3e0#64) 368 ∗
              ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
              ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
              ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
              ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
              (if ans.isOk then emp
               else (∃∗ strPtr : BitVec 64, strPtr ↦ᵣ storeHookStr)) ∗
              FromRecordCallees.lsLogOff ∗
              ikit.identityAt idStorePtr
                (ikit.trustUpdate ist peer.val remoteIdKey .receiving ans) ∗
              protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
              ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
              A.pool lim (M.stepEvents evs st0) sm ∗
              stackAt s.sp (trustCallStack ikit))) ∧
        sm.sp = s.sp ∧
        sm.readReg64 .x19 = coroPtr ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem)
      Qp) :
    SepWPp prog ret s P
      (fun sm P_m =>
        (∃ evs : List AllocEvent,
          TrustStepEnv ikit ikitEnv ist peer.val remoteIdKey .receiving evs ∧
          (P_m ⊢
            ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
              cells (coroPtr + 0x398#64) 2 ∗
              ((s.sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((s.sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
              ((s.sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
              ((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗
              memRegion (s.sp + 0x3e0#64) 368 ∗
              ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
              ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
              ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
              ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
              FromRecordCallees.lsLogOff ∗
              ikit.identityAt idStorePtr
                (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
              protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
              ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
              A.pool lim (M.stepEvents evs st0) sm ∗
              stackAt s.sp (trustCallStack ikit))) ∧
        ikit.trustRel ist peer.val remoteIdKey .receiving (.ok false) ∧
        sm.trace = s.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving (.ok false) ∧
        sm.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        sm.readReg64 .x23 = 0#64 ∧
        sm.sp = s.sp ∧
        sm.readReg64 .x19 = coroPtr ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem)
      Qp := by
  refine sepWPp_mono_post hcall fun sm P_m h => ?_
  rcases h with ⟨⟨ans, evs, hrel, henv, htrm, hx20, _, hfalse, hent⟩, hsp, hx19, hx29, hvregs, hcrlm⟩
  have hans : ans = .ok false := htrust_false ans hrel
  subst hans
  dsimp only [Except.isOk, Except.toBool, trustPollTag] at hent hx20
  simp only [↓reduceIte, emp_sepConj] at hent
  exact ⟨⟨evs, henv, hent⟩, hrel, htrm, hx20, hfalse rfl, hsp, hx19, hx29, hvregs, hcrlm⟩

set_option maxHeartbeats 1200000 in
theorem stageP1_trust_call_wp_kit_x_ext_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ}
    {ext : String → Option (State → State)}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist : ikit.IdState} {Q : Prop}
    {Qp : State → SepProp → Prop}
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hikit_shim : subroutine_ok (stageP1ProgPlaced ext) (0#64 + ikit.trustShimOff)
      (StoreKit.withLsRoCl lsmpl (kitTrustShimSpec M A lim ikit)))
    (hikit_poll : subroutine_ok (stageP1ProgPlaced ext) (0#64 + ikit.trustPollOff)
      (StoreKit.withLsRoCl lsmpl (kitTrustPollPlacedSpecI M A lim ikit ikitEnv)))
    (hikit_drop : subroutine_ok (stageP1ProgPlaced ext) (0#64 + ikit.trustFutDropOff)
      (StoreKit.withLsRoCl lsmpl futDropBudgetSpec))
    (hstack_lt : trustCallStack ikit ≤ 2 ^ 64)
    (haddr_id : ikit.addrOk peer.val)
    (hfits : FitsEnv M lim st0 (TrustStepEnv ikit ikitEnv ist peer.val remoteIdKey .receiving))
    (s : State)
    (outPtr coroPtr ctxPtr msgPtr remoteAddrPtr
     idStorePtr
     u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hfs : FsAt ikit.envOk Q (stageP1ProgPlaced ext) s)
    (hpc : s.pc = 0#64 + ikit.trustShimOff)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = idStorePtr)
    (hx1 : s.readReg64 .x1 = remoteAddrPtr)
    (hx2 : s.readReg64 .x2 = msgPtr + 0xc8#64)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = coroPtr + 0x390#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx30 : s.readReg64 .x30 = stageP1EntryPlaced + 0x650#64) :
    SepWPp (stageP1ProgPlaced ext)
      (stageP1EntryPlaced + 0x6e4#64) s
      (((coroPtr + 0x398#64) ↦₆₄ u_398) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ u_3a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((s.sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (s.sp + 0x3e0#64) 368 ∗
       ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
       ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
       ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
       FromRecordCallees.lsLogOff ∗
       ikit.identityAt idStorePtr ist ∗
       protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
       ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
       A.pool lim st0 s ∗
       stackAt s.sp (trustCallStack ikit))
      (fun sm P_m =>
        (∃ (ans : Except Unit Bool) (evs : List AllocEvent),
          ikit.trustRel ist peer.val remoteIdKey .receiving ans ∧
          TrustStepEnv ikit ikitEnv ist peer.val remoteIdKey .receiving evs ∧
          sm.trace = s.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving ans ∧
          sm.readReg64 .x20 = trustPollTag ans ∧
          (ans = .ok true → sm.readReg64 .x23 = 1#64) ∧
          (ans = .ok false → sm.readReg64 .x23 = 0#64) ∧
          (P_m ⊢
            ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
              cells (coroPtr + 0x398#64) 2 ∗
              ((s.sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((s.sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
              ((s.sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
              ((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗
              memRegion (s.sp + 0x3e0#64) 368 ∗
              ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
              ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
              ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
              ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
              (if ans.isOk then emp
               else (∃∗ strPtr : BitVec 64, strPtr ↦ᵣ storeHookStr)) ∗
              FromRecordCallees.lsLogOff ∗
              ikit.identityAt idStorePtr
                (ikit.trustUpdate ist peer.val remoteIdKey .receiving ans) ∗
              protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
              ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
              A.pool lim (M.stepEvents evs st0) sm ∗
              stackAt s.sp (trustCallStack ikit))) ∧
        sm.sp = s.sp ∧
        sm.readReg64 .x19 = coroPtr ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem)
      Qp := by
  have hsp_al : s.spAligned = true := by simpa only [State.spAligned] using hsp_align
  have hdrop_nz : 0#64 + ikit.trustFutDropOff ≠ 0#64 := ikit.trustFutDrop_ne_zero rfl
  have hbs_nz : BitVec.ofNat 64 ikit.trustBoxSize ≠ 0#64 := ikit.trustBoxSize_ne_zero
  have hbs_lt : ikit.trustBoxSize < 2 ^ 64 := ikit.trustBoxSize_lt
  have hx3_8 : (s.readReg64 .x3).setWidth 8 = 1#8 := by rw [hx3]; rfl
  have hfits_shim : FitsEnv M lim st0 (BoxAllocEnv ikit.trustBoxSize) := hfits.seq_left
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_trustCall_to_trustShim ikit s.sp hstack_lt))
    (by sep_focus) ?_
  sep_norm
  refine call_rocl_entails_steps_frame_placed
    (x := (({ self := idStorePtr, addrA := remoteAddrPtr,
              keyA := msgPtr + 0xc8#64 } : IdentityShimCall), 1#8, st0))
    hcrl hikit_shim hpc hrun hsp_al hx30
    (trustShim_pre_intro_placed hx0 hx1 hx2 hx3_8 hfits_shim)
    (by sep_focus)
    (hnext := fun s7 hsteps67 hpc7 hrun7 hsp7_s _ hcs7 hcrl7 => ?_)
    (hpan_false := fun _ => by unfold kitTrustShimSpec; rfl)
    (hexit_false := fun _ _ => by unfold kitTrustShimSpec; rfl)
    (hoom_false := fun _ => by unfold kitTrustShimSpec; rfl)
  dsimp only [kitTrustShimSpec]
  sep_norm
  refine SepWPp.exists_elim fun evs_shim => ?_
  refine SepWPp.pure_elim fun ⟨hx1_7, _, _, htr7_s, hbox_shim⟩ => ?_
  let st7 := M.stepEvents evs_shim st0
  have hfits_poll :
      FitsEnv M lim st7 (ikitEnv.trustPollEnv ist peer.val remoteIdKey .receiving) :=
    (hfits.seq_right hbox_shim).seq_left
  have hfs7 : FsAt ikit.envOk Q (stageP1ProgPlaced ext) s7 :=
    hfs.of_steps hsteps67 (evs := []) (by simpa using htr7_s) (fun _ => NoFsEv.nil)
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_trustCall_to_trustShim ikit s.sp hstack_lt).symm)
    (by sep_focus) ?_
  have hsp7_align : (s7.sp &&& 15#64 == 0#64) = true := by rw [hsp7_s]; exact hsp_align
  rcases hcs7 with ⟨hx19_cs7, _, hx21_cs7, _, _, _, _, hx26_cs7, hx27_cs7, _, hx29_cs7, hvregs_cs7⟩
  have hx19_7 : s7.readReg64 .x19 = coroPtr := hx19_cs7.trans hx19
  have hx21_7 : s7.readReg64 .x21 = coroPtr + 0x390#64 := hx21_cs7.trans hx21
  have hx26_7 : s7.readReg64 .x26 = outPtr := hx26_cs7.trans hx26
  have hx27_7 : s7.readReg64 .x27 = ctxPtr := hx27_cs7.trans hx27
  have hstep8_raw := p1_seg5_vregs_wp_ext_placed ext s7 coroPtr ctxPtr
    (s7.readReg64 .x0) (0#64 + ikit.trustFutVtOff) (0#64 + ikit.trustPollOff)
    u_398 u_3a0 u_c0
    hpc7 hrun7 hsp7_align rfl hx1_7 hx19_7 hx27_7
  rw [hsp7_s] at hstep8_raw
  simp only [BitVec.add_assoc] at hstep8_raw
  have hstep8 := SepWP.mono hstep8_raw (fun _ _ _ _ h => And.intro h.1.1 (And.intro h.1.2 h.2))
  refine bind_sepWP_steps_frame_placed hcrl7 hstep8 (by sep_focus)
    fun s8 hsteps78 hpc8 hrun8 hcrl8 ⟨hregs8, hvm78⟩ => ?_
  rcases hregs8 with ⟨hsp8_s, htr8_7, hx0_8, _, hx8_8, hx19_8, hx21_8, hx26_8, _, hx29_8,
    hx30_8, hvregs8_7⟩
  have hsp8_al : s8.spAligned = true := by simpa only [State.spAligned, hsp8_s] using hsp_align
  have hfs8 : FsAt ikit.envOk Q (stageP1ProgPlaced ext) s8 :=
    hfs7.of_steps hsteps78 (evs := []) (by simpa using htr8_7) (fun _ => NoFsEv.nil)
  refine SepWPp.weaken_frame
    (Entails.of_eq (A.pool_of_vmPreserved hvm78).symm)
    (by sep_focus) ?_
  have hmr_3e0 : memRegion (s.sp + 0x3e0#64) 368 =
      memRegion (s.sp + 0x3e0#64) 48 ∗ memRegion (s.sp + 0x410#64) 320 :=
    ProofLib.memRegion_split' (b := s.sp + 0x3e0#64) (n := 48) (k := 320)
      (b' := s.sp + 0x410#64) rfl (by bv_omega) (by decide)
  refine SepWPp.weaken_frame (Entails.of_eq hmr_3e0) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_trustCall_to_trustPoll ikit s.sp hstack_lt))
    (by sep_focus) ?_
  sep_norm
  refine call_rocl_entails_steps_frame_placed
    (x := (({ fut := s7.readReg64 .x0, out := s.sp + 0x3e0#64,
              call := { addrA := remoteAddrPtr, addr := peer,
                        keyA := msgPtr + 0xc8#64, key := remoteIdKey } } : IdentityPollCall),
           Direction.receiving, idStorePtr, ist, st7))
    hcrl8 hikit_poll hpc8 hrun8 hsp8_al hx30_8
    (trustPoll_pre_intro_placed hfs8.envOk_here hsp8_s hx0_8 hx8_8 haddr_id hfits_poll)
    (by sep_focus)
    (hnext := fun s9 _ hpc9 hrun9 hsp9_8 _ hcs9 hcrl9 => ?_)
    (hpan_false := fun _ => by
      dsimp only [kitTrustPollPlacedSpecI, StoreKit.withLsLogOff,
        LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget.kitTrustPollPlacedSpecE,
        withEnvPre, LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget.kitTrustPollPlacedSpec])
    (hexit_false := fun _ _ => by
      dsimp only [kitTrustPollPlacedSpecI, StoreKit.withLsLogOff,
        LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget.kitTrustPollPlacedSpecE,
        withEnvPre, LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget.kitTrustPollPlacedSpec])
    (hoom_false := fun _ => by
      dsimp only [kitTrustPollPlacedSpecI, StoreKit.withLsLogOff,
        LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget.kitTrustPollPlacedSpecE,
        withEnvPre, LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget.kitTrustPollPlacedSpec])
  dsimp only [kitTrustPollPlacedSpecI, StoreKit.withLsLogOff,
    LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget.kitTrustPollPlacedSpecE,
    withEnvPre, LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget.kitTrustPollPlacedSpec]
  rw [hsp8_s]
  sep_norm
  refine SepWPp.exists_elim fun ans => ?_
  refine SepWPp.exists_elim fun evs_poll => ?_
  refine SepWPp.pure_elim fun ⟨hrel, htr9_8, hpoll_env⟩ => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_trustCall_to_trustPoll ikit s.sp hstack_lt).symm)
    (by sep_focus) ?_
  let st9 := M.stepEvents evs_poll st7
  have hsp9_s : s9.sp = s.sp := hsp9_8.trans hsp8_s
  rcases hcs9 with ⟨hx19_cs9, _, hx21_cs9, _, _, _, _, hx26_cs9, _, _, hx29_cs9, hvregs_cs9⟩
  have hx19_9 : s9.readReg64 .x19 = coroPtr := hx19_cs9.trans hx19_8
  have hx21_9 : s9.readReg64 .x21 = coroPtr + 0x390#64 :=
    by rw [hx21_cs9, hx21_8, hx21_7]
  have hx26_9 : s9.readReg64 .x26 = outPtr :=
    by rw [hx26_cs9, hx26_8, hx26_7]
  have hx29_9 : s9.readReg64 .x29 = s.readReg64 .x29 :=
    by rw [hx29_cs9, hx29_8, hx29_cs7]
  have hvregs9 : calleeSavedVRegs s9 = calleeSavedVRegs s :=
    by rw [hvregs_cs9, hvregs8_7, hvregs_cs7]
  have htr9_s : s9.trace = s.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving ans := by
    rw [htr9_8, htr8_7, htr7_s]
  let evs_tot := evs_shim ++ (evs_poll ++ rustDeallocEvents ikit.trustBoxSize 8)
  have henv_tot : TrustStepEnv ikit ikitEnv ist peer.val remoteIdKey .receiving evs_tot :=
    SeqEnv.append hbox_shim (SeqEnv.append hpoll_env rfl)
  have hstm_eq :
      M.stepEvents (rustDeallocEvents ikit.trustBoxSize 8) st9 = M.stepEvents evs_tot st0 := by
    dsimp only [st9, st7, evs_tot]
    rw [M.stepEvents_append, M.stepEvents_append]
  have htail := stageP1_trust_call_tail_x_ext_placed (st9 := st9) (Qp := Qp)
    peer remoteIdKey ans hdealloc hikit_drop hstack_lt s s9
    (s7.readReg64 .x0) outPtr coroPtr ctxPtr msgPtr remoteAddrPtr idStorePtr
    u_a8 u_b0 u_b8 u_c8 u_d0
    hdrop_nz hbs_nz hbs_lt hrel htr9_s hcrl9 hpc9 hrun9 hsp_align hsp9_s
    hx19_9 hx21_9 hx26_9 hx29_9 hvregs9
  simp only [BitVec.add_assoc] at htail
  refine sepWPp_mono_post (sepWPp_perm_pre htail (by sep_focus)) (fun sm P_m hq => ?_)
  rcases hq with ⟨⟨ans', hrel', htrm, _hlivem, hx20_m, htrue_m, hfalse_m, hentm⟩, hregsm⟩
  rw [hstm_eq] at hentm
  exact ⟨⟨ans', evs_tot, hrel', henv_tot, htrm, hx20_m, htrue_m, hfalse_m, hentm⟩, hregsm⟩

set_option maxHeartbeats 1200000 in
theorem stageP1_trust_ok_kit_x_ext_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ}
    {ext : String → Option (State → State)}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist : ikit.IdState} {Q : Prop}
    {Qp : State → SepProp → Prop}
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hikit_shim : subroutine_ok (stageP1ProgPlaced ext) (0#64 + ikit.trustShimOff)
      (StoreKit.withLsRoCl lsmpl (kitTrustShimSpec M A lim ikit)))
    (hikit_poll : subroutine_ok (stageP1ProgPlaced ext) (0#64 + ikit.trustPollOff)
      (StoreKit.withLsRoCl lsmpl (kitTrustPollPlacedSpecI M A lim ikit ikitEnv)))
    (hikit_drop : subroutine_ok (stageP1ProgPlaced ext) (0#64 + ikit.trustFutDropOff)
      (StoreKit.withLsRoCl lsmpl futDropBudgetSpec))
    (hstack_lt : trustCallStack ikit ≤ 2 ^ 64)
    (haddr_id : ikit.addrOk peer.val)
    (htrust_true : ∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok true)
    (hfits : FitsEnv M lim st0 (TrustStepEnv ikit ikitEnv ist peer.val remoteIdKey .receiving))
    (s : State)
    (outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt
     u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
    (b_4f2 : BitVec 8)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hfs : FsAt ikit.envOk Q (stageP1ProgPlaced ext) s)
    (hpc : s.pc = 0#64 + ikit.trustShimOff)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = idStorePtr)
    (hx1 : s.readReg64 .x1 = remoteAddrPtr)
    (hx2 : s.readReg64 .x2 = msgPtr + 0xc8#64)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = coroPtr + 0x390#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx30 : s.readReg64 .x30 = stageP1EntryPlaced + 0x650#64) :
    SepWPp (stageP1ProgPlaced ext)
      (stageP1EntryPlaced + 0x868#64) s
      (processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
         spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
       ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
       ((coroPtr + 0x398#64) ↦₆₄ u_398) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ u_3a0) ∗
       cells (coroPtr + 0x428#64) 8 ∗
       cells (coroPtr + 0x490#64) 4 ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((s.sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (s.sp + 0x3e0#64) 368 ∗
       ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
       ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
       ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
       FromRecordCallees.lsLogOff ∗
       ikit.identityAt idStorePtr ist ∗
       protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
       ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
       A.pool lim st0 s ∗
       stackAt s.sp (trustCallStack ikit))
      (fun sf P_f =>
        (∃ evs : List AllocEvent,
          ikit.trustRel ist peer.val remoteIdKey .receiving (.ok true) ∧
          TrustStepEnv ikit ikitEnv ist peer.val remoteIdKey .receiving evs ∧
          sf.trace = s.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving (.ok true) ∧
          (P_f ⊢
            ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
              processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
                spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
              processPrekeyPostTrustAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
                spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
              ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
              cells (coroPtr + 0x398#64) 2 ∗
              ((coroPtr + 0x4f2#64) ↦₈ 0#8) ∗
              ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
              ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
              ((s.sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((s.sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
              ((s.sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
              ((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗
              memRegion (s.sp + 0x3e0#64) 368 ∗
              ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
              ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
              ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
              ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
              FromRecordCallees.lsLogOff ∗
              ikit.identityAt idStorePtr
                (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok true)) ∗
              protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
              ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
              A.pool lim (M.stepEvents evs st0) sf ∗
              stackAt s.sp (trustCallStack ikit))) ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x8 = kyberStorePtr ∧
        sf.readReg64 .x9 = msgPtr ∧
        sf.readReg64 .x10 = kyberStoreVt ∧
        sf.readReg64 .x11 = preKeyStorePtr ∧
        sf.readReg64 .x12 = remoteAddrPtr ∧
        sf.readReg64 .x13 = preKeyStoreVt ∧
        sf.readReg64 .x14 = localAddrPtr ∧
        sf.readReg64 .x15 = idStorePtr ∧
        sf.readReg64 .x16 = ikit.id_vt ∧
        sf.readReg64 .x17 = coroPtr + 0x4f2#64 ∧
        sf.readReg64 .x19 = coroPtr ∧
        sf.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        sf.readReg64 .x22 = spkStorePtr ∧
        sf.readReg64 .x23 = coroPtr + 0xe0#64 ∧
        sf.readReg64 .x24 = spkStoreVt ∧
        sf.readReg64 .x25 = s.sp + 0x210#64 ∧
        sf.readReg64 .x28 = s.sp + 0xa90#64 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  have hcall := stageP1_trust_call_wp_kit_x_ext_placed (ist := ist) (Qp := fun _ _ => False)
    peer remoteIdKey hdealloc hikit_shim hikit_poll hikit_drop hstack_lt haddr_id hfits
    s outPtr coroPtr ctxPtr msgPtr remoteAddrPtr idStorePtr
    u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    hcrl hfs hpc hrun hsp_align
    hx0 hx1 hx2 hx3 hx19 hx21 hx26 hx27 hx30
  have hcall_true := trust_call_wp_specialize_true_prog_placed htrust_true hcall
  refine bind_sepWPp_nopanic_frame hcall_true (by sep_focus)
    fun sm P_m _ hpcm hrunm hQ1 => ?_
  rcases hQ1 with ⟨⟨evs, henv, hent⟩, hrel, htrm, hx20_m, hx23_m, hspm, hx19_m, hx29_m,
    hvregsm, hcrlm⟩
  refine SepWPp.weaken_frame hent rfl ?_
  have hsp_align_m : (sm.sp &&& 15#64 == 0#64) = true := by rw [hspm]; exact hsp_align
  sep_norm
  refine SepWPp.exists_elim fun v_a8 =>
    SepWPp.exists_elim fun v_b8 =>
    SepWPp.exists_elim fun v_d0 => ?_
  have hpost_raw := p1_post_dealloc_true_vregs_wp_ext_placed
    ext sm coroPtr
    msgPtr remoteAddrPtr localAddrPtr
    idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt
    u_98 u_a0 b_4f2
    hpcm hrunm hsp_align_m hx19_m hx20_m hx23_m
  rw [hspm] at hpost_raw
  have hpost := SepWP.mono hpost_raw (fun _ _ _ _ h => And.intro h.1.1 (And.intro h.1.2 h.2))
  refine ret_sepWP_steps_frame_placed hcrlm hpost (by sep_focus)
    fun sf _ _ _ hcrlf ⟨hregsf, hvm⟩ => ?_
  rcases hregsf with ⟨hsp_f, htr_f, hx8_f, hx9_f, hx10_f, hx11_f, hx12_f, hx13_f, hx14_f,
    hx15_f, hx16_f, hx17_f, hx19_f, hx20_f, hx22_f, hx23_f, hx24_f, hx25_f, hx28_f, hx29_f,
    hvregsf_m⟩
  refine ⟨⟨evs, hrel, henv, by rw [htr_f, htrm], ?_⟩,
    hsp_f, hx8_f, hx9_f, hx10_f, hx11_f, hx12_f, hx13_f, hx14_f, hx15_f, hx16_f, hx17_f,
    hx19_f, hx20_f, hx22_f, hx23_f, hx24_f, hx25_f, hx28_f, hx29_f.trans hx29_m,
    hvregsf_m.trans hvregsm, hcrlf⟩
  rw [(A.pool_of_vmPreserved hvm).symm]
  refine Entails.sepExists_right v_a8
    (Entails.sepExists_right v_b8
      (Entails.sepExists_right v_d0 ?_))
  sep_norm
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1TrustExtPlacedBudget
