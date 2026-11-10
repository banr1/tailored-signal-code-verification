/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadExtPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1TrustExtPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedOkTrapPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.PublicApi.StoreKit.RecordMove
import ProofLib.SepLogic.WPp

/-!
# Descriptor-Threaded Relocatable Stage P1 Untrusted-Identity Composition

Proves `fds = true` (`fdsOk`) placed untrusted-identity composition (`stageP1EntryPlaced →
s0.readReg64 .x30`) on Block `518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedOkTrapPlacedBudgetFd

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
  kitLoadShimSpec kitLoadPollPlacedSpecSE kitTrustShimSpec kitTrustPollPlacedSpecI
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
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv VmPreserved
  rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (session2MemcpyBudgetSpecX)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (futDropBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (
  LoadStepEnv SessionStoreBudgetEnv kitLoadShimSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (
  IdentityStoreBudgetEnv TrustStepEnv kitTrustShimSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  kitLoadPollPlacedSpecSE kitTrustPollPlacedSpecI
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlacedBudgetAux (
  p1_seg1_vregs_wp_ext_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlacedBudgetFd (
  FdsHiInvariant
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrustTailsXExtPlacedBudget (
  bind_sepWP_steps_frame_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadExtPlacedBudgetFd (
  stageP1_load_ok_kit_x_ext_placed_fd
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1TrustExtPlacedBudgetFd (
  stageP1_trust_call_wp_kit_x_ext_placed_fd trust_call_wp_specialize_false_prog_placed_fd
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedExtPlaced (
  lsStringCloneSym
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedExtPlacedBudget (
  StageP1UntrustedErrEnv StageP1UntrustedFromTrustEnv
  stageP1_untrusted_err_ok_kit_x_ext_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedOkTrapPlacedBudget (
  StageP1UntrustedOkEnv
)

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

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
theorem stageP1_untrusted_from_trust_x_ext_placed_fd [LibsignalPlacement] {M : AllocCostModel}
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
      (StoreKit.withLsRoCl lsmpl (kitTrustShimSpec M A lim ikit true)))
    (hikit_poll : subroutine_ok (stageP1ProgPlaced ext) (0#64 + ikit.trustPollOff)
      (StoreKit.withLsRoCl lsmpl (kitTrustPollPlacedSpecI M A lim ikit ikitEnv true)))
    (hikit_drop : subroutine_ok (stageP1ProgPlaced ext) (0#64 + ikit.trustFutDropOff)
      (StoreKit.withLsRoCl lsmpl (futDropBudgetSpec ikit.fdsOk true)))
    (hfds_hi : FdsHiInvariant ikit.fdsOk)
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
    (hfds6_ikit : ikit.fdsOk s6.fs)
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
  have htrust_raw := stageP1_trust_call_wp_kit_x_ext_placed_fd (ist := ist) (Qp := fun _ _ => False)
    peer remoteIdKey hdealloc hikit_shim hikit_poll hikit_drop hfds_hi htrust_le haddr_id
    hfits_trust s6 outPtr coroPtr ctxPtr msgPtr remoteAddrPtr idStorePtr
    u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    hcrl6 hfs6_ikit hfds6_ikit hpc6 hrun6 hsp6_align
    hx0_6 hx1_6 hx2_6 hx3_6 hx19_6 hx21_6 hx26_6 hx27_6 hx30_6
  have htrust := trust_call_wp_specialize_false_prog_placed_fd htrust_false htrust_raw
  rw [hsp6_eq] at htrust
  simp only [BitVec.add_assoc] at htrust
  refine bind_sepWPp_nopanic_frame htrust (by sep_focus)
    fun sm P_m _ hpcm hrunm hQm => ?_
  rcases hQm with ⟨⟨evs_trust, henv_trust, hentm⟩,
    hrel_trust, htrm, hx20_m, hx23_m, hspm, hx19_m, _, hvregsm, hcrlm, _hfdsm⟩
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

set_option maxHeartbeats 1200000 in
theorem stageP1_untrusted_ok_kit_x_ext_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64}
    {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {ikitEnv : IdentityStoreBudgetEnv ikit}
    {fdsOk : FsState → Prop}
    {st : kit.StoreState} {ist : ikit.IdState}
    {Qp : State → SepProp → Prop}
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (hdrop_ss : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (StoreKit.withLsCodeRoLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : subroutine_ok (stageP1ProgPlaced ext) (lsρ "memcpy")
      (StoreKit.withLsCodeRoLoaded lsmpl session2MemcpyBudgetSpecX))
    (hclone : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 623) (StoreKit.withLsCodeRoLoaded lsmpl (stringCloneBudgetSpec M A lim)))
    (hkit_shim : subroutine_ok (stageP1ProgPlaced ext) (0#64 + kit.loadShimOff)
      (StoreKit.withLsRoCl lsmpl (kitLoadShimSpec M A lim kit true)))
    (hkit_poll : subroutine_ok (stageP1ProgPlaced ext) (0#64 + kit.loadPollOff)
      (StoreKit.withLsRoCl lsmpl (kitLoadPollPlacedSpecSE M A lim kit kitEnv Scope encRecord true)))
    (hkit_drop : subroutine_ok (stageP1ProgPlaced ext) (0#64 + kit.loadFutDropOff)
      (StoreKit.withLsRoCl lsmpl (futDropBudgetSpec kit.fdsOk true)))
    (hikit_shim : subroutine_ok (stageP1ProgPlaced ext) (0#64 + ikit.trustShimOff)
      (StoreKit.withLsRoCl lsmpl (kitTrustShimSpec M A lim ikit true)))
    (hikit_poll : subroutine_ok (stageP1ProgPlaced ext) (0#64 + ikit.trustPollOff)
      (StoreKit.withLsRoCl lsmpl (kitTrustPollPlacedSpecI M A lim ikit ikitEnv true)))
    (hikit_drop : subroutine_ok (stageP1ProgPlaced ext) (0#64 + ikit.trustFutDropOff)
      (StoreKit.withLsRoCl lsmpl (futDropBudgetSpec ikit.fdsOk true)))
    (hfds_hi : FdsHiInvariant fdsOk)
    (hstack_lt : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64)
    (hext_load : extHookStack ≤ loadCallStack kit)
    (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val)
    (hload_ok : ∀ ans, kit.loadRel st peer.val ans → ans.isOk = true)
    (htrust_false : ∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok false)
    (hfits : FitsEnv M lim st0
      (StageP1UntrustedOkEnv kit kitEnv ikit ikitEnv st ist peer.val remoteIdKey peer.name))
    (s0 : State)
    (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt rngPtr
     v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
    (b_390 : BitVec 8)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem)
    (hfs : FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
      (stageP1ProgPlaced ext) s0)
    (hfds0 : fdsOk s0.fs)
    (hpc : s0.pc = stageP1EntryPlaced)
    (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsp_def : s0.sp - 0xcd0#64 = sp)
    (hx0 : s0.readReg64 .x0 = outPtr)
    (hx1 : s0.readReg64 .x1 = coroPtr)
    (hx2 : s0.readReg64 .x2 = ctxPtr)
    (hkit_fds : kit.fdsOk = fdsOk := by rfl)
    (hikit_fds : ikit.fdsOk = fdsOk := by rfl) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s0
      (decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr ∗
       cells (coroPtr + 0x70#64) 14 ∗
       cells (coroPtr + 0xe0#64) 4 ∗
       memRegion (coroPtr + 0x100#64) 336 ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
       cells (coroPtr + 0x2c8#64) 25 ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((coroPtr + 0x398#64) ↦₆₄ u_398) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ u_3a0) ∗
       (sp ↦₆₄ v_sp0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0xd8#64) 348 ∗
       memRegion (sp + 0x370#64) 36 ∗
       memRegion (sp + 0x3e0#64) 368 ∗
       cells (sp + 0xa90#64) 6 ∗
       cells (s0.sp - 0x60#64) 12 ∗
       memRegion outPtr 48 ∗
       ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (0#64 + kit.loadShimOff)) ∗
       ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff)) ∗
       ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
       ((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
       ((0#64 + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((0#64 + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
       ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
       ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
       ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
       FromRecordCallees.lsLogOff ∗
       kit.storeAt sessStorePtr st ∗
       ikit.identityAt idStorePtr ist ∗
       protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
       ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
       A.pool lim st0 s0 ∗
       stackAt sp (stageP1UntrustedCallStack kit ikit))
      (fun sf P_f =>
        (∃ (opt : Option (SessionRecord (List (BitVec 8)))) (evs : List AllocEvent),
          kit.loadRel st peer.val (.ok opt) ∧
          ikit.trustRel ist peer.val remoteIdKey .receiving (.ok false) ∧
          StageP1UntrustedOkEnv kit kitEnv ikit ikitEnv st ist peer.val remoteIdKey peer.name evs ∧
          sf.trace = s0.trace ++ kit.loadEvs encRecord peer.val (.ok opt) ++
            ikit.trustEvs peer.val remoteIdKey .receiving (.ok false) ∧
          (P_f ⊢
            ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
              decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
                preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
                kyberStorePtr kyberStoreVt rngPtr ∗
              decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
                preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
                kyberStorePtr kyberStoreVt rngPtr ∗
              memRegion (coroPtr + 0xe0#64) 368 ∗
              cells (coroPtr + 0x250#64) 6 ∗
              ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
              processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
                spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
              ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
              cells (coroPtr + 0x398#64) 2 ∗
              (sp ↦₆₄ 0#64) ∗
              ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
              ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
              ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
              memRegion (sp + 0xd8#64) 348 ∗
              memRegion (sp + 0x370#64) 36 ∗
              memRegion (sp + 0x3e0#64) 368 ∗
              cells (sp + 0xa90#64) 6 ∗
              decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
              apiDecResultAt A.repAlloc outPtr (.error (.untrustedIdentity peer.val)) ∗
              ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (0#64 + kit.loadShimOff)) ∗
              ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff)) ∗
              ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
              ((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
              ((0#64 + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
              ((0#64 + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
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
        sf.sp = s0.sp ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  have hkit_hi : FdsHiInvariant kit.fdsOk := hkit_fds ▸ hfds_hi
  have hikit_hi : FdsHiInvariant ikit.fdsOk := hikit_fds ▸ hfds_hi
  have hp1_le : stageP1CallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_left _ _) hstack_lt
  have hload_le : loadCallStack kit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_left _ _) hp1_le
  have hsp_saved : sp + 0xcd0#64 = s0.sp := by rw [← hsp_def]; bv_omega
  have hfits_load : FitsEnv M lim st0 (LoadStepEnv kit kitEnv st peer.val) := hfits.seq_left
  have hstep1_raw := p1_seg1_vregs_wp_ext_placed ext s0 outPtr coroPtr ctxPtr
    msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    (0#64 + kit.loadShimOff) v_sp0
    hpc hrun hsp_align hx0 hx1 hx2
  rw [hsp_def] at hstep1_raw
  have hstep1 := SepWP.mono hstep1_raw (fun _ _ _ _ h => And.intro h.1.1 (And.intro h.1.2 h.2))
  refine bind_sepWP_steps_frame_placed hcrl hstep1 (by sep_focus)
    fun s1 hsteps01 hpc1 hrun1 hcrl1 ⟨hregs1, hvm01⟩ => ?_
  have hfds1_kit : kit.fdsOk s1.fs := hkit_fds ▸ hfds_hi.of_vmPreserved hvm01 hfds0
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx19_1, _, _, _, _,
    hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _, hx30_1, hvregs1⟩
  refine SepWPp.weaken_frame
    (Entails.of_eq (A.pool_of_vmPreserved hvm01).symm)
    (by sep_focus) ?_
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by
    rw [hsp1, ← hsp_def]
    exact sp_sub_cd0_align_std3 hsp_align
  have hfs1 : FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
      (stageP1ProgPlaced ext) s1 :=
    hfs.of_steps hsteps01 (evs := []) (by simpa using htr1) (fun _ => NoFsEv.nil)
  have hfs1_kit : FsAt kit.envOk (kit.Quiet ∧ ikit.Quiet)
      (stageP1ProgPlaced ext) s1 :=
    hfs1.mono (fun _ h => h.1) id
  rw [← hsp1] at hx24_1 hx25_1 hx28_1
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_p1 kit ikit sp hstack_lt))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_load kit ikit sp hp1_le))
    (by sep_focus) ?_
  sep_norm
  have hload := stageP1_load_ok_kit_x_ext_placed_fd (Scope := Scope) (encRecord := encRecord)
    (kitEnv := kitEnv) (ikit := ikit) (st0 := st0) (Qp := fun _ _ => False)
    peer hdealloc hmemcpy hkit_shim hkit_poll hkit_drop hkit_hi
    hext_load hload_le haddr_ss hload_ok hfits_load s1
    outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr idStorePtr
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr b_390
    hcrl1 hfs1_kit hfds1_kit hpc1 hrun1 hsp1_align
    hx0_1 hx1_1 hx19_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx30_1
  rw [hsp1] at hload
  simp only [BitVec.add_assoc] at hload
  refine bind_sepWPp_nopanic_frame hload (by sep_focus)
    fun s6 P_m hsteps16 hpc6 hrun6 hQ1 => ?_
  rcases hQ1 with ⟨⟨opt, evs_load, hrel_load, henv_load, htr6, hent6⟩,
    hsp6, hx0_6, hx1_6, hx2_6, hx3_6,
    hx19_6, hx21_6, hx26_6, hx27_6, _, hx30_6, hvregs6, hcrl6, hfds6_kit⟩
  have hfds6_ikit : ikit.fdsOk s6.fs := hikit_fds ▸ (hkit_fds ▸ hfds6_kit)
  refine SepWPp.weaken_frame hent6 rfl ?_
  have hfits_tail : FitsEnv M lim (M.stepEvents evs_load st0)
      (StageP1UntrustedFromTrustEnv ikit ikitEnv ist peer.val remoteIdKey peer.name) :=
    hfits.seq_right henv_load
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by
    rw [hsp6, ← hsp1]; exact hsp1_align
  have hfs6 : FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
      (stageP1ProgPlaced ext) s6 :=
    hfs1.of_steps hsteps16 htr6 (fun hq => hq.1.1 encRecord peer.val (.ok opt))
  have hfs6_ikit : FsAt ikit.envOk (kit.Quiet ∧ ikit.Quiet)
      (stageP1ProgPlaced ext) s6 :=
    hfs6.mono (fun _ h => h.2) id
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_load kit ikit sp hp1_le).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_p1 kit ikit sp hstack_lt).symm)
    (by sep_focus) ?_
  sep_norm
  have htail := stageP1_untrusted_from_trust_x_ext_placed_fd
    (Scope := Scope) (kit := kit) (ikit := ikit) (ikitEnv := ikitEnv) (st := st) (ist := ist)
    (st0 := M.stepEvents evs_load st0) (Qp := fun _ _ => False)
    peer remoteIdKey opt hdrop_ss hdealloc hclone hikit_shim hikit_poll hikit_drop
    hikit_hi hstack_lt haddr_id htrust_false hfits_tail s0 s6
    sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr idStorePtr
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt
    u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    hcrl6 hfs6_ikit hfds6_ikit hpc6 hrun6 hsp6 hsp_saved hsp6_align
    hx0_6 hx1_6 hx2_6 hx3_6 hx19_6 hx21_6 hx26_6 hx27_6 hx30_6
  simp only [BitVec.add_assoc] at htail
  refine bind_sepWPp_nopanic_frame htail (by sep_focus)
    fun sf P_f _ hpcf hrunf hQf => ?_
  rcases hQf with ⟨⟨evs_tail, henv_tail, hent_f⟩,
    hrel_trust, htrf_6, hspf, hcs_f, hvregsf_6, hcrlf⟩
  refine SepWPp.weaken_frame hent_f rfl ?_
  sep_norm
  refine SepWPp.exists_elim fun v_a8 =>
    SepWPp.exists_elim fun v_b8 =>
    SepWPp.exists_elim fun v_d0 => ?_
  refine SepWPp.done hpcf hrunf ?_
  have htr_full : sf.trace = s0.trace ++ kit.loadEvs encRecord peer.val (.ok opt) ++
      ikit.trustEvs peer.val remoteIdKey .receiving (.ok false) := by
    rw [htrf_6, htr6, htr1]
  have hvregs_full : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    rw [hvregsf_6, hvregs6, hvregs1]
  have henv_tot : StageP1UntrustedOkEnv kit kitEnv ikit ikitEnv st ist
      peer.val remoteIdKey peer.name (evs_load ++ evs_tail) :=
    SeqEnv.append henv_load henv_tail
  refine ⟨⟨opt, evs_load ++ evs_tail, hrel_load, hrel_trust, henv_tot, htr_full, ?_⟩,
    hspf, hcs_f, hvregs_full, hcrlf⟩
  rw [M.stepEvents_append]
  refine Entails.sepExists_right v_a8
    (Entails.sepExists_right v_b8
      (Entails.sepExists_right v_d0 ?_))
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedOkTrapPlacedBudgetFd
