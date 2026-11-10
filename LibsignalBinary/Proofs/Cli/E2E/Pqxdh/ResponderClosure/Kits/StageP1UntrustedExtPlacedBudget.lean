/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedExtPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAux
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.PublicApi.StoreKit.RecordMove
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Stage P1 Untrusted-Identity Error Exit

Defines `StageP1UntrustedErrEnv` and `StageP1UntrustedFromTrustEnv`, and proves budget-threaded
placed untrusted-identity error cleanup (`+0x6e4 → s0.readReg64 .x30`) on Block `518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedExtPlacedBudget

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees hiding
  dropSessionStructureLocal2Spec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit hiding
  kitTrustShimSpec kitTrustPollPlacedSpecI
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity hiding kitTrustShimSpec
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
  rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (StringCloneEnv stringCloneBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (futDropBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (
  IdentityStoreBudgetEnv TrustStepEnv kitTrustShimSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (kitTrustPollPlacedSpecI)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrustTailsXExtPlacedBudget (
  bind_sepWP_steps_frame_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1TrustExtPlacedBudget (
  stageP1_trust_call_wp_kit_x_ext_placed trust_call_wp_specialize_false_prog_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedExtPlaced (
  lsStringCloneSym call_raw_nopanic_steps_frame_placed call_lscro_nopanic_steps_frame_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedExtPlacedBudgetAux (
  decryptPrekeyClosure_stringClone_ok_placed decryptPrekeyClosure_stringClone_ok_ext_placed
  p1_err_drop_none_vregs_wp_ext_placed p1_err_drop_ss_to_call_vregs_wp_ext_placed
  p1_untrusted_to_clone_vregs_wp_ext_placed p1_untrusted_post_clone_vregs_wp_ext_placed
  p3_err_tail_b_vregs_wp_ext_placed p1_err_tail_prev_dealloc_core_wp_placed
  p1_err_drop_record_core_wp_placed p1_err_tail_prev_core_wp_placed
)

export LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedExtPlaced (
  lsStringCloneSym call_raw_nopanic_steps_frame_placed call_lscro_nopanic_steps_frame_placed
)
export LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedExtPlacedBudgetAux (
  decryptPrekeyClosure_stringClone_ok_placed decryptPrekeyClosure_stringClone_ok_ext_placed
  p1_err_drop_none_vregs_wp_ext_placed p1_err_drop_ss_to_call_vregs_wp_ext_placed
  p1_untrusted_to_clone_vregs_wp_ext_placed p1_untrusted_post_clone_vregs_wp_ext_placed
  p3_err_tail_b_vregs_wp_ext_placed p1_err_tail_prev_dealloc_core_wp_placed
  p1_err_drop_record_core_wp_placed p1_err_tail_prev_core_wp_placed
)

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

/-- Allocation envelope for the Stage P1 untrusted-identity error branch (`+0x6e4 → ret`):
    `<String as Clone>::clone` on `g` followed by `FreeOnlyEvs` drops. -/
def StageP1UntrustedErrEnv (g : VecGhost) : List AllocEvent → Prop :=
  SeqEnv (StringCloneEnv g) FreeOnlyEvs

/-- Allocation envelope for `is_trusted_identity == false` + untrusted-identity error exit
    (`trustShim → +0x6e4 → ret`). -/
def StageP1UntrustedFromTrustEnv {A : RustAlloc}
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist : ikit.IdState) (rem : AddrVal) (remoteIdKey : IdentityKey) (g : VecGhost) :
    List AllocEvent → Prop :=
  SeqEnv (TrustStepEnv ikit ikitEnv ist rem remoteIdKey .receiving)
    (StageP1UntrustedErrEnv g)

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

set_option maxHeartbeats 1200000 in
theorem p1_err_drop_and_return_vregs_wp_ext_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Qp : State → SepProp → Prop}
    (hdrop_ss : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (StoreKit.withLsCodeRoLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hstack_lt : untrustedErrCallStack ≤ 2 ^ 64)
    (opt : Option (SessionRecord (List (BitVec 8))))
    (s0 s3 : State) (sp coroPtr outPtr cap ptr devWord u_278 : BitVec 64)
    (b_2c0 : BitVec 8)
    (peer : AddrGhost) (pad : List (BitVec 8))
    (hpad : pad.length = 7)
    (hw4 : peer.device :: pad = unpack64 devWord)
    (hcrl3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem)
    (hsp3_s : s3.sp = sp)
    (hpc3 : s3.pc = stageP1EntryPlaced + 0x3588#64)
    (hrun3 : s3.status = .Running)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hx19_3 : s3.readReg64 .x19 = coroPtr)
    (hx22_3 : s3.readReg64 .x22 = (cap.extractLsb' 0 32).zeroExtend 64)
    (hx25_3 : s3.readReg64 .x25 = sp + 0x210#64)
    (hx26_3 : s3.readReg64 .x26 = outPtr)
    (hx28_3 : s3.readReg64 .x28 = 0x800000000000000c#64) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s3
      (p1LoadedRecordAt Scope A.repAlloc coroPtr opt ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗
       SegUntrusted.vecU8Buf A.repAlloc cap ptr peer.name.bytes ∗
       ((sp + 0x370#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
       ((sp + 0x378#64) ↦₆₄ ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
       ((sp + 0x380#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)) ∗
       ((sp + 0x388#64) ↦₆₄ (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
       ((sp + 0x390#64) ↦₃₂ u_278.extractLsb' 32 32) ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       A.pool lim st0 s3 ∗
       stackAt sp untrustedErrCallStack)
      (fun sf P_f =>
        (∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P_f ⊢
            memRegion (coroPtr + 0xe0#64) 368 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            apiDecResultAt A.repAlloc outPtr (.error (.untrustedIdentity peer.val)) ∗
            memRegion (sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackAt sp untrustedErrCallStack)) ∧
        sf.sp = sp + 0xcd0#64 ∧
        sf.trace = s3.trace ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s3 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3_s]; exact hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_dropSS sp hstack_lt))
    (by sep_focus) ?_
  have hdrop := p1_err_drop_record_core_wp_placed (Scope := Scope) (st0 := st0)
    (Qp := fun _ _ => False) hdrop_ss opt s3 coroPtr hcrl3 hpc3 hrun3 hsp3_align hx19_3
  rw [hsp3_s] at hdrop
  refine bind_sepWPp_nopanic_frame hdrop (by sep_focus)
    fun s4 P_4 _ hpc4 hrun4 hQ4 => ?_
  rcases hQ4 with ⟨⟨evs1, hevs1, hent4⟩,
    hsp4_s, htr4_3, hx19_4, hx22_4, hx25_4, hx26_4, hx28_4, hvregs4_3, hcrl4⟩
  refine SepWPp.weaken_frame hent4 rfl ?_
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4_s]; exact hsp_align
  sep_norm
  refine SepWPp.exists_elim fun prevCap => SepWPp.exists_elim fun prevPtr => ?_
  refine SepWPp.pure_elim fun hprev_lt => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_dropSS sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_alloc sp hstack_lt))
    (by sep_focus) ?_
  have hret := p1_err_tail_prev_core_wp_placed (st0 := M.stepEvents evs1 st0)
    (Qp := fun _ _ => False) hdealloc s0 s4 sp coroPtr outPtr
    prevCap prevPtr cap ptr devWord u_278 b_2c0 peer pad
    hprev_lt hpad hw4 hcrl4 hsp4_s hpc4 hrun4 hsp4_align
    hx19_4 (hx22_4.trans hx22_3) (hx25_4.trans hx25_3)
    (hx26_4.trans hx26_3) (hx28_4.trans hx28_3)
  refine bind_sepWPp_nopanic_frame hret (by sep_focus)
    fun sf P_f _ hpcf hrunf hQf => ?_
  rcases hQf with ⟨⟨evs2, hevs2, hentf⟩, hspf, htrf_4, hcs_f, hvregsf_4, hcrlf⟩
  refine SepWPp.weaken_frame hentf rfl ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_alloc sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨⟨evs1 ++ evs2, FreeOnlyEvs.append hevs1 hevs2, ?_⟩,
    hspf, htrf_4.trans htr4_3, hcs_f, hvregsf_4.trans hvregs4_3, hcrlf⟩
  rw [M.stepEvents_append]
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
theorem stageP1_untrusted_err_ok_kit_x_ext_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {kit : SessionStoreSpec A.repAlloc 0#64}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {st : kit.StoreState} {ist : ikit.IdState}
    {Qp : State → SepProp → Prop}
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (opt : Option (SessionRecord (List (BitVec 8))))
    (hdrop_ss : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (StoreKit.withLsCodeRoLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hclone : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 623) (StoreKit.withLsCodeRoLoaded lsmpl (stringCloneBudgetSpec M A lim)))
    (hstack_lt : untrustedErrCallStack ≤ 2 ^ 64)
    (hfits : FitsEnv M lim st0 (StageP1UntrustedErrEnv peer.name))
    (s0 s : State)
    (outPtr coroPtr msgPtr remoteAddrPtr sessStorePtr idStorePtr : BitVec 64)
    (b_2c0 b_390 : BitVec 8)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = stageP1EntryPlaced + 0x6e4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = 0xfffffffffffffffe#64)
    (hx23 : s.readReg64 .x23 = 0#64) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (((coroPtr + 0x330#64) ↦₆₄ remoteAddrPtr) ∗
       p1LoadedRecordAt Scope A.repAlloc coroPtr opt ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       memRegion (s.sp + 0x370#64) 36 ∗
       memRegion (s.sp + 0x3e0#64) 368 ∗
       cells (s.sp + 0xa90#64) 6 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗
       FromRecordCallees.lsLogOff ∗
       kit.storeAt sessStorePtr st ∗
       ikit.identityAt idStorePtr
         (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
       protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
       ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
       A.pool lim st0 s ∗
       stackAt s.sp untrustedErrCallStack)
      (fun sf P_f =>
        (∃ evs : List AllocEvent,
          StageP1UntrustedErrEnv peer.name evs ∧
          sf.trace = s.trace ∧
          (P_f ⊢
            ((coroPtr + 0x330#64) ↦₆₄ remoteAddrPtr) ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗
            cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
            memRegion (s.sp + 0x370#64) 36 ∗
            memRegion (s.sp + 0x3e0#64) 368 ∗
            cells (s.sp + 0xa90#64) 6 ∗
            decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            apiDecResultAt A.repAlloc outPtr (.error (.untrustedIdentity peer.val)) ∗
            FromRecordCallees.lsLogOff ∗
            kit.storeAt sessStorePtr st ∗
            ikit.identityAt idStorePtr
              (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
            protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
            ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackAt s.sp untrustedErrCallStack)) ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  have hfits_clone : FitsEnv M lim st0 (StringCloneEnv peer.name) := hfits.seq_left
  have hstep1 := p1_untrusted_to_clone_vregs_wp_ext_placed ext s
    coroPtr remoteAddrPtr hpc hrun hsp_align hx19 hx20 hx23
  refine bind_sepWP_steps_frame_placed hcrl hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hcrl1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx8_1, hx19_1, hx21_1, hx25_1, _, hx30_1, hvregs1, hvm1⟩
  refine SepWPp.weaken_frame
    (Entails.of_eq (A.pool_of_vmPreserved hvm1).symm)
    (by sep_focus) ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  refine SepWPp.weaken_frame (memRegion_368_untrusted_entails s.sp) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun pad => ?_
  refine SepWPp.pure_elim fun hpad => ?_
  have haddr_eq :
      protocolAddressAt A.repAlloc peer remoteAddrPtr =
        vecGhostAt A.repAlloc peer.name remoteAddrPtr ∗
          ((remoteAddrPtr + 0x18#64) ↦₈ peer.device) ∗
          memRegion (remoteAddrPtr + 0x19#64) 7 := rfl
  refine SepWPp.weaken_frame (Entails.of_eq haddr_eq) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_ext s.sp hstack_lt))
    (by sep_focus) ?_
  refine call_lscro_nopanic_steps_frame_placed
    (spec := stringCloneBudgetSpec M A lim)
    (x := (remoteAddrPtr, s.sp + 0x3e0#64, peer.name, st0))
    (φ := s1.readReg64 .x0 = remoteAddrPtr ∧
          s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
          FitsEnv M lim st0 (StringCloneEnv peer.name) ∧
          LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr (s1.readReg64 .lr))
    (T := vecGhostAt A.repAlloc peer.name remoteAddrPtr ∗ memRegion (s.sp + 0x3e0#64) 24 ∗
      A.pool lim st0 s1 ∗ stackAt s.sp extHookStack)
    hcrl1 hclone hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [stringCloneBudgetSpec]; rw [hsp1])
    ⟨hx0_1, hx8_1, hfits_clone,
      by simp (config := { decide := true }) [show s1.readReg64 .lr = _ from hx30_1, wp_norm]⟩
    (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hcrl2 => ?_)
  dsimp only [stringCloneBudgetSpec]
  rw [hsp1]
  sep_norm
  refine SepWPp.exists_elim fun evs_clone => ?_
  refine SepWPp.pure_elim fun ⟨htr2_1, henv_clone⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_ext s.sp hstack_lt).symm)
    (by sep_focus) ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2_s]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, _, _, _, hx25_cs2, _, _, _, _, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx21_2 : s2.readReg64 .x21 = remoteAddrPtr := hx21_cs2.trans hx21_1
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hsp2_s]
  refine SepWPp.weaken_frame (vecU8_unpack_3e0 A.repAlloc s.sp peer.name.bytes) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun cap => SepWPp.exists_elim fun ptr => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (cells6_eq (coroPtr + 0x250#64))) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u250 => SepWPp.exists_elim fun u258 =>
    SepWPp.exists_elim fun u260 => SepWPp.exists_elim fun u268 =>
    SepWPp.exists_elim fun u270 => SepWPp.exists_elim fun u278 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (cells6_eq (s.sp + 0xa90#64))) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun ua90 => SepWPp.exists_elim fun ua98 =>
    SepWPp.exists_elim fun uaa0 => SepWPp.exists_elim fun uaa8 =>
    SepWPp.exists_elim fun uab0 => SepWPp.exists_elim fun uab8 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (sp370_36_split_eq s.sp)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u390 => SepWPp.exists_elim fun u388 =>
    SepWPp.exists_elim fun u380 => SepWPp.exists_elim fun u378 =>
    SepWPp.exists_elim fun u370 => ?_
  have hw4_ex : ∃ devWord : BitVec 64, peer.device :: pad = unpack64 devWord := by
    rcases pad with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨p4, _ | ⟨p5, _ | ⟨p6, _ | ⟨p7, _ | _⟩⟩⟩⟩⟩⟩⟩ <;>
      try simp at hpad
    exact ⟨p7 ++ p6 ++ p5 ++ p4 ++ p3 ++ p2 ++ p1 ++ peer.device,
      (unpack64_pack64 peer.device p1 p2 p3 p4 p5 p6 p7).symm⟩
  obtain ⟨devWord, hw4⟩ := hw4_ex
  have hstep3 := p1_untrusted_post_clone_vregs_wp_ext_placed ext s2
    coroPtr remoteAddrPtr outPtr cap ptr (BitVec.ofNat 64 peer.name.bytes.length) devWord
    u250 u258 u260 u268 u270 u278
    ua90 ua98 uaa0 uaa8 uab0 uab8
    u370 u378 u380 u388 u390
    d0 b_390 peer pad
    hw4 hpc2 hrun2 hsp2_align hx19_2 hx21_2 hx25_2
  rw [hsp2_s] at hstep3
  refine bind_sepWP_steps_frame_placed hcrl2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hcrl3 hregs3 => ?_
  rcases hregs3 with ⟨hvm3, hsp3_s, htr3_2, hx19_3, hx22_3, hx25_3, hx26_3, hx28_3, _, hvregs3_2⟩
  refine SepWPp.weaken_frame
    (Entails.of_eq (A.pool_of_vmPreserved hvm3).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (cells_3e0_entails_memRegion_368 s.sp cap ptr (BitVec.ofNat 64 peer.name.bytes.length) devWord)
    (by sep_focus) ?_
  have hc250 := cells6_fold (coroPtr + 0x250#64)
    0x800000000000000c#64 cap ptr (BitVec.ofNat 64 peer.name.bytes.length) devWord (s2.readReg64 .x27)
  repeat (simp only [BitVec.add_assoc] at hc250); repeat (simp only [BitVec.reduceAdd] at hc250)
  refine SepWPp.weaken_frame hc250 (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (sp_a90_rejoin s.sp 0x800000000000000c#64 cap ptr
      (BitVec.ofNat 64 peer.name.bytes.length) devWord (s2.readReg64 .x27))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq haddr_eq.symm) (by sep_focus) ?_
  have hdrop_ret := p1_err_drop_and_return_vregs_wp_ext_placed
    (Scope := Scope) (st0 := M.stepEvents evs_clone st0) (Qp := fun _ _ => False)
    hdrop_ss hdealloc hstack_lt opt s0 s3 s.sp coroPtr outPtr cap ptr devWord (s2.readReg64 .x27) b_2c0
    peer pad hpad hw4 hcrl3 hsp3_s hpc3 hrun3 hsp_align
    hx19_3 hx22_3 hx25_3 hx26_3 hx28_3
  refine bind_sepWPp_nopanic_frame hdrop_ret (by sep_focus)
    fun sf P_f _ hpcf hrunf hQf => ?_
  rcases hQf with ⟨⟨evs_drop, hevs_drop, hentf⟩, hspf, htrf_3, hcs_f, hvregsf_3, hcrlf⟩
  refine SepWPp.weaken_frame hentf rfl ?_
  refine SepWPp.done hpcf hrunf ?_
  have htr_full : sf.trace = s.trace := by
    rw [htrf_3, htr3_2, htr2_1, htr1]
  have hvregs_full : calleeSavedVRegs sf = calleeSavedVRegs s := by
    rw [hvregsf_3, hvregs3_2, hvregs_cs2, hvregs1]
  refine ⟨⟨evs_clone ++ evs_drop, SeqEnv.append henv_clone hevs_drop, htr_full, ?_⟩,
    hspf, hcs_f, hvregs_full, hcrlf⟩
  rw [M.stepEvents_append]
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
theorem stageP1_untrusted_from_trust_x_ext_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {kit : SessionStoreSpec A.repAlloc 0#64}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st : kit.StoreState} {ist : ikit.IdState} {Q : Prop}
    {Qp : State → SepProp → Prop}
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (opt : Option (SessionRecord (List (BitVec 8))))
    (hdrop_ss : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (StoreKit.withLsCodeRoLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hclone : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 623) (StoreKit.withLsCodeRoLoaded lsmpl (stringCloneBudgetSpec M A lim)))
    (hikit_shim : subroutine_ok (stageP1ProgPlaced ext) (0#64 + ikit.trustShimOff)
      (StoreKit.withLsRoCl lsmpl (kitTrustShimSpec M A lim ikit)))
    (hikit_poll : subroutine_ok (stageP1ProgPlaced ext) (0#64 + ikit.trustPollOff)
      (StoreKit.withLsRoCl lsmpl (kitTrustPollPlacedSpecI M A lim ikit ikitEnv)))
    (hikit_drop : subroutine_ok (stageP1ProgPlaced ext) (0#64 + ikit.trustFutDropOff)
      (StoreKit.withLsRoCl lsmpl futDropBudgetSpec))
    (hstack_lt : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64)
    (haddr_id : ikit.addrOk peer.val)
    (htrust_false : ∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok false)
    (hfits : FitsEnv M lim st0
      (StageP1UntrustedFromTrustEnv ikit ikitEnv ist peer.val remoteIdKey peer.name))
    (s0 s6 : State)
    (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt
     u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
    (hcrl6 : StoreKit.LibsignalCodeRoLoaded lsmpl s6.mem)
    (hfs6_ikit : FsAt ikit.envOk Q (stageP1ProgPlaced ext) s6)
    (hpc6 : s6.pc = 0#64 + ikit.trustShimOff)
    (hrun6 : s6.status = .Running)
    (hsp6_eq : s6.sp = sp)
    (hsp_saved : sp + 0xcd0#64 = s0.sp)
    (hsp6_align : (s6.sp &&& 15#64 == 0#64) = true)
    (hx0_6 : s6.readReg64 .x0 = idStorePtr)
    (hx1_6 : s6.readReg64 .x1 = remoteAddrPtr)
    (hx2_6 : s6.readReg64 .x2 = msgPtr + 0xc8#64)
    (hx3_6 : s6.readReg64 .x3 = 1#64)
    (hx19_6 : s6.readReg64 .x19 = coroPtr)
    (hx21_6 : s6.readReg64 .x21 = coroPtr + 0x390#64)
    (hx26_6 : s6.readReg64 .x26 = outPtr)
    (hx27_6 : s6.readReg64 .x27 = ctxPtr)
    (hx30_6 : s6.readReg64 .x30 = stageP1EntryPlaced + 0x650#64) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s6
      (p1LoadedRecordAt Scope A.repAlloc coroPtr opt ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
       processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
         spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
       ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
       ((coroPtr + 0x398#64) ↦₆₄ u_398) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ u_3a0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0x370#64) 36 ∗
       memRegion (sp + 0x3e0#64) 368 ∗
       cells (sp + 0xa90#64) 6 ∗
       decryptPrekeySavedRegsAt s0.sp s0 ∗
       memRegion outPtr 48 ∗
       ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
       ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
       ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
       FromRecordCallees.lsLogOff ∗
       kit.storeAt sessStorePtr st ∗
       ikit.identityAt idStorePtr ist ∗
       protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
       ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
       A.pool lim st0 s6 ∗
       stackAt sp (stageP1UntrustedCallStack kit ikit))
      (fun sf P_f =>
        (∃ evs : List AllocEvent,
          StageP1UntrustedFromTrustEnv ikit ikitEnv ist peer.val remoteIdKey peer.name evs ∧
          (P_f ⊢
            ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
              memRegion (coroPtr + 0xe0#64) 368 ∗
              cells (coroPtr + 0x250#64) 6 ∗
              ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
              processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
                spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
              ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
              cells (coroPtr + 0x398#64) 2 ∗
              ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
              ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
              ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
              memRegion (sp + 0x370#64) 36 ∗
              memRegion (sp + 0x3e0#64) 368 ∗
              cells (sp + 0xa90#64) 6 ∗
              decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
              apiDecResultAt A.repAlloc outPtr (.error (.untrustedIdentity peer.val)) ∗
              ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
              ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
              ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
              ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
              FromRecordCallees.lsLogOff ∗
              kit.storeAt sessStorePtr st ∗
              ikit.identityAt idStorePtr
                (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
              protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
              ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
              A.pool lim (M.stepEvents evs st0) sf ∗
              stackAt sp (stageP1UntrustedCallStack kit ikit))) ∧
        ikit.trustRel ist peer.val remoteIdKey .receiving (.ok false) ∧
        sf.trace = s6.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving (.ok false) ∧
        sf.sp = s0.sp ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s6 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  have hp1_le : stageP1CallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_left _ _) hstack_lt
  have herr_le : untrustedErrCallStack ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_right _ _) hstack_lt
  have htrust_le : trustCallStack ikit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_right _ _) hp1_le
  have hfits_trust : FitsEnv M lim st0
      (TrustStepEnv ikit ikitEnv ist peer.val remoteIdKey .receiving) := hfits.seq_left
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_p1 kit ikit sp hstack_lt))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_trust kit ikit sp hp1_le))
    (by sep_focus) ?_
  sep_norm
  have htrust_raw := stageP1_trust_call_wp_kit_x_ext_placed (ist := ist) (Qp := fun _ _ => False)
    peer remoteIdKey hdealloc hikit_shim hikit_poll hikit_drop htrust_le haddr_id hfits_trust
    s6 outPtr coroPtr ctxPtr msgPtr remoteAddrPtr idStorePtr
    u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    hcrl6 hfs6_ikit hpc6 hrun6 hsp6_align
    hx0_6 hx1_6 hx2_6 hx3_6 hx19_6 hx21_6 hx26_6 hx27_6 hx30_6
  have htrust := trust_call_wp_specialize_false_prog_placed htrust_false htrust_raw
  rw [hsp6_eq] at htrust
  simp only [BitVec.add_assoc] at htrust
  refine bind_sepWPp_nopanic_frame htrust (by sep_focus)
    fun sm P_m _ hpcm hrunm hQm => ?_
  rcases hQm with ⟨⟨evs_trust, henv_trust, hentm⟩,
    hrel_trust, htrm, hx20_m, hx23_m, hspm, hx19_m, _, hvregsm, hcrlm⟩
  refine SepWPp.weaken_frame hentm rfl ?_
  have hfits_err : FitsEnv M lim (M.stepEvents evs_trust st0)
      (StageP1UntrustedErrEnv peer.name) :=
    hfits.seq_right henv_trust
  have hspm_align : (sm.sp &&& 15#64 == 0#64) = true := by
    rw [hspm, ← hsp6_eq]; exact hsp6_align
  sep_norm
  refine SepWPp.exists_elim fun v_a8 =>
    SepWPp.exists_elim fun v_b8 =>
    SepWPp.exists_elim fun v_d0 => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_trust kit ikit sp hp1_le).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_p1 kit ikit sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_err kit ikit sp hstack_lt))
    (by sep_focus) ?_
  unfold processPrekeyInnerInitAt
  sep_norm
  have herr := stageP1_untrusted_err_ok_kit_x_ext_placed
    (Scope := Scope) (kit := kit) (ikit := ikit) (st := st) (ist := ist)
    (st0 := M.stepEvents evs_trust st0) (Qp := fun _ _ => False)
    peer remoteIdKey opt hdrop_ss hdealloc hclone herr_le hfits_err s0 sm
    outPtr coroPtr msgPtr remoteAddrPtr sessStorePtr idStorePtr
    0#8 0#8
    hcrlm hpcm hrunm hspm_align hx19_m hx20_m hx23_m
  rw [hspm, hsp_saved] at herr
  refine bind_sepWPp_nopanic_frame herr (by sep_focus)
    fun sf P_f _ hpcf hrunf hQf => ?_
  rcases hQf with ⟨⟨evs_err, henv_err, htrf, hentf⟩, hspf, hcs_f, hvregsf_m, hcrlf⟩
  refine SepWPp.weaken_frame hentf rfl ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_err kit ikit sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨⟨evs_trust ++ evs_err, SeqEnv.append henv_trust henv_err, ?_⟩,
    hrel_trust, htrf.trans htrm, hspf, hcs_f, hvregsf_m.trans hvregsm, hcrlf⟩
  rw [M.stepEvents_append]
  refine Entails.sepExists_right v_a8
    (Entails.sepExists_right v_b8
      (Entails.sepExists_right v_d0 ?_))
  rw [hsp_saved]
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedExtPlacedBudget
