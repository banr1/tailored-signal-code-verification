/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrustTailsXExtPlacedBudgetFd
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.PublicApi.StoreKit.RecordMove
import ProofLib.SepLogic.WPp

/-!
# Descriptor-Threaded Relocatable Stage P1 `load_session` Step

Threads `kit.fdsOk` across the budget-threaded placed Stage P1 `load_session` step
(`0#64 + kit.loadShimOff → 0#64 + ikit.trustShimOff`) on Block `518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadExtPlacedBudgetFd

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit hiding kitLoadShimSpec kitLoadPollPlacedSpecSE
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
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
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (session2MemcpyBudgetSpecX)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv futDropBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (
  LoadStepEnv SessionStoreBudgetEnv kitLoadShimSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (kitLoadPollPlacedSpecSE)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlacedBudgetFd (
  FdsHiInvariant
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrustTailsXExtPlacedBudget (
  bind_sepWP_steps_frame_placed call_rocl_entails_steps_frame_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrustTailsXExtPlacedBudgetFd (
  loadPoll_pre_intro_placed_fd loadShim_pre_intro_placed_fd
  stageP1_load_none_tail_x_ext_placed_fd stageP1_load_some_tail_x_ext_placed_fd
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadExtPlacedBudget (
  p1_seg2_vregs_wp_ext_placed
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

set_option maxHeartbeats 1200000 in
theorem stageP1_load_ok_kit_x_ext_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64}
    {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {st : kit.StoreState} {Q : Prop}
    {Qp : State → SepProp → Prop}
    (peer : AddrGhost)
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : subroutine_ok (stageP1ProgPlaced ext) (lsρ "memcpy")
      (StoreKit.withLsCodeRoLoaded lsmpl session2MemcpyBudgetSpecX))
    (hkit_shim : subroutine_ok (stageP1ProgPlaced ext) (0#64 + kit.loadShimOff)
      (StoreKit.withLsRoCl lsmpl (kitLoadShimSpec M A lim kit true)))
    (hkit_poll : subroutine_ok (stageP1ProgPlaced ext) (0#64 + kit.loadPollOff)
      (StoreKit.withLsRoCl lsmpl (kitLoadPollPlacedSpecSE M A lim kit kitEnv Scope encRecord true)))
    (hkit_drop : subroutine_ok (stageP1ProgPlaced ext) (0#64 + kit.loadFutDropOff)
      (StoreKit.withLsRoCl lsmpl (futDropBudgetSpec kit.fdsOk true)))
    (hfds_hi : FdsHiInvariant kit.fdsOk)
    (hext_stack : extHookStack ≤ loadCallStack kit)
    (hstack_lt : loadCallStack kit ≤ 2 ^ 64)
    (haddr_ss : kit.addrOk peer.val)
    (hload_ok : ∀ ans, kit.loadRel st peer.val ans → ans.isOk = true)
    (hfits : FitsEnv M lim st0 (LoadStepEnv kit kitEnv st peer.val))
    (s : State)
    (outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt rngPtr : BitVec 64)
    (b_390 : BitVec 8)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hfs : FsAt kit.envOk Q (stageP1ProgPlaced ext) s)
    (hfds : kit.fdsOk s.fs)
    (hpc : s.pc = 0#64 + kit.loadShimOff)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = sessStorePtr)
    (hx1 : s.readReg64 .x1 = remoteAddrPtr)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64)
    (hx30 : s.readReg64 .x30 = stageP1EntryPlaced + 0x130#64) :
    SepWPp (stageP1ProgPlaced ext)
      (0#64 + ikit.trustShimOff) s
      (cells (coroPtr + 0x2c8#64) 25 ∗
       decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr ∗
       cells (coroPtr + 0xe0#64) 4 ∗
       memRegion (coroPtr + 0x100#64) 336 ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       memRegion (s.sp + 0xd8#64) 348 ∗
       memRegion (s.sp + 0x3e0#64) 368 ∗
       ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff)) ∗
       ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
       ((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
       ((0#64 + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((0#64 + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
       kit.storeAt sessStorePtr st ∗
       protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
       A.pool lim st0 s ∗
       stackAt s.sp (loadCallStack kit))
      (fun s6 P_f =>
        (∃ (opt : Option (SessionRecord (List (BitVec 8)))) (evs : List AllocEvent),
          kit.loadRel st peer.val (.ok opt) ∧
          LoadStepEnv kit kitEnv st peer.val evs ∧
          s6.trace = s.trace ++ kit.loadEvs encRecord peer.val (.ok opt) ∧
          (P_f ⊢
            decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
              sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
              preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
              kyberStorePtr kyberStoreVt rngPtr ∗
            p1LoadedRecordAt Scope A.repAlloc coroPtr opt ∗
            processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
              idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
              spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
            ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
            memRegion (s.sp + 0xd8#64) 348 ∗
            memRegion (s.sp + 0x3e0#64) 368 ∗
            ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff)) ∗
            ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
            ((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
            ((0#64 + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            ((0#64 + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
            kit.storeAt sessStorePtr st ∗
            protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
            A.pool lim (M.stepEvents evs st0) s6 ∗
            stackAt s.sp (loadCallStack kit))) ∧
        s6.sp = s.sp ∧
        s6.readReg64 .x0 = idStorePtr ∧
        s6.readReg64 .x1 = remoteAddrPtr ∧
        s6.readReg64 .x2 = msgPtr + 0xc8#64 ∧
        s6.readReg64 .x3 = 1#64 ∧
        s6.readReg64 .x19 = coroPtr ∧
        s6.readReg64 .x21 = coroPtr + 0x390#64 ∧
        s6.readReg64 .x26 = outPtr ∧
        s6.readReg64 .x27 = ctxPtr ∧
        s6.readReg64 .x29 = s.readReg64 .x29 ∧
        s6.readReg64 .x30 = stageP1EntryPlaced + 0x650#64 ∧
        calleeSavedVRegs s6 = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl s6.mem ∧
        kit.fdsOk s6.fs)
      Qp := by
  have hsp_al : s.spAligned = true := by simpa only [State.spAligned] using hsp_align
  have hdrop_nz : 0#64 + kit.loadFutDropOff ≠ 0#64 := kit.loadFutDrop_ne_zero rfl
  have hbs_nz : BitVec.ofNat 64 kit.loadBoxSize ≠ 0#64 := kit.loadBoxSize_ne_zero
  have hbs_lt : kit.loadBoxSize < 2 ^ 64 := kit.loadBoxSize_lt
  have hfits_shim : FitsEnv M lim st0 (BoxAllocEnv kit.loadBoxSize) := hfits.seq_left
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_loadCall_to_loadShim kit s.sp hstack_lt))
    (by sep_focus) ?_
  sep_norm
  refine call_rocl_entails_steps_frame_placed
    (x := (({ self := sessStorePtr, addrA := remoteAddrPtr } : LoadShimCall), st0))
    hcrl hkit_shim hpc hrun hsp_al hx30
    (loadShim_pre_intro_placed_fd hx0 hx1 hfits_shim hfds)
    (by sep_focus)
    (hnext := fun s1 hsteps01 hpc1 hrun1 hsp1 _ hcs1 hcrl1 => ?_)
    (hpan_false := fun _ => by unfold kitLoadShimSpec; rfl)
    (hexit_false := fun _ _ => by unfold kitLoadShimSpec; rfl)
    (hoom_false := fun _ => by unfold kitLoadShimSpec; rfl)
  dsimp only [kitLoadShimSpec]
  sep_norm
  refine SepWPp.exists_elim fun evs_shim => ?_
  refine SepWPp.pure_elim fun ⟨hx1_1, _, _, htr1, hbox_shim, hfds1⟩ => ?_
  let st1 := M.stepEvents evs_shim st0
  have hfits_poll : FitsEnv M lim st1 (kitEnv.loadPollEnv st peer.val) :=
    (hfits.seq_right hbox_shim).seq_left
  have hfs1 : FsAt kit.envOk Q (stageP1ProgPlaced ext) s1 :=
    hfs.of_steps hsteps01 (evs := []) (by simpa using htr1) (fun _ => NoFsEv.nil)
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_loadCall_to_loadShim kit s.sp hstack_lt).symm)
    (by sep_focus) ?_
  rcases hcs1 with ⟨hx19_cs1, _, _, _, _, hx24_cs1, hx25_cs1, hx26_cs1, hx27_cs1, hx28_cs1,
    hx29_cs1, hvregs_cs1⟩
  have hx19_1 : s1.readReg64 .x19 = coroPtr := hx19_cs1.trans hx19
  have hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs1.trans hx24
  have hx25_1 : s1.readReg64 .x25 = s.sp + 0x210#64 := hx25_cs1.trans hx25
  have hx26_1 : s1.readReg64 .x26 = outPtr := hx26_cs1.trans hx26
  have hx27_1 : s1.readReg64 .x27 = ctxPtr := hx27_cs1.trans hx27
  have hx28_1 : s1.readReg64 .x28 = s.sp + 0xa90#64 := hx28_cs1.trans hx28
  refine SepWPp.weaken_frame (Entails.of_eq (cells25_split2_eq coroPtr)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u2c8 => SepWPp.exists_elim fun u2d0 => ?_
  have hstep2 := p1_seg2_vregs_wp_ext_placed ext s1 coroPtr ctxPtr
    (s1.readReg64 .x0) (0#64 + kit.loadFutVtOff) (0#64 + kit.loadPollOff) u2c8 u2d0
    hpc1 hrun1 rfl hx1_1 hx19_1 hx27_1
  simp only [BitVec.add_assoc] at hstep2
  refine bind_sepWP_steps_frame_placed hcrl1 hstep2 (by sep_focus)
    fun s2 hsteps12 hpc2 hrun2 hcrl2 hregs2 => ?_
  rcases hregs2 with ⟨hvm12, hsp2_1, htr2_1, hx0_2, _, hx8_2, hx19_2, hx21_2,
    hx24_2, hx25_2, hx26_2, hx27_2, _, hx29_2, hx30_2, hvregs2_1⟩
  have hfds2 : kit.fdsOk s2.fs := hfds_hi.of_vmPreserved hvm12 hfds1
  refine SepWPp.transport_budgetPool hvm12 (hnext := ?_)
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_al : s2.spAligned = true := by simpa only [State.spAligned, hsp2_s] using hsp_align
  rw [hsp1] at hx8_2 hx21_2
  have hfs2 : FsAt kit.envOk Q (stageP1ProgPlaced ext) s2 :=
    hfs1.of_steps hsteps12 (evs := []) (by simpa using htr2_1) (fun _ => NoFsEv.nil)
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_loadCall_to_loadPoll kit s.sp hstack_lt))
    (by sep_focus) ?_
  sep_norm
  refine call_rocl_entails_steps_frame_placed
    (x := (({ fut := s1.readReg64 .x0, out := s.sp + 0x3e0#64,
              addrA := remoteAddrPtr, addr := peer } : LoadPollCall),
           sessStorePtr, st, st1))
    hcrl2 hkit_poll hpc2 hrun2 hsp2_al hx30_2
    (loadPoll_pre_intro_placed_fd hfs2.envOk_here hfds2 hsp2_s hx0_2 hx8_2 haddr_ss hfits_poll)
    (by sep_focus)
    (hnext := fun s3 _ hpc3 hrun3 hsp3_2 _ hcs3 hcrl3 => ?_)
  dsimp only [kitLoadPollPlacedSpecSE, withEnvPre,
    LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget.kitLoadPollPlacedSpecS]
  rw [hsp2_s]
  sep_norm
  refine SepWPp.exists_elim fun ans => ?_
  refine SepWPp.exists_elim fun evs_poll => ?_
  refine SepWPp.pure_elim fun ⟨hrel, htr3_2, hpoll_env, hfds3⟩ => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_loadCall_to_loadPoll kit s.sp hstack_lt).symm)
    (by sep_focus) ?_
  let st3 := M.stepEvents evs_poll st1
  have hsp3_s : s3.sp = s.sp := hsp3_2.trans hsp2_s
  rcases hcs3 with ⟨hx19_cs3, _, hx21_cs3, _, _, hx24_cs3, hx25_cs3, hx26_cs3, hx27_cs3, _,
    hx29_cs3, hvregs_cs3⟩
  have hx19_3 : s3.readReg64 .x19 = coroPtr := hx19_cs3.trans hx19_2
  have hx21_3 : s3.readReg64 .x21 = s3.sp + 0x3e0#64 := by rw [hx21_cs3, hx21_2, hsp3_s]
  have hx24_3 : s3.readReg64 .x24 = s3.sp + 0x370#64 := by rw [hx24_cs3, hx24_2, hx24_1, hsp3_s]
  have hx25_3 : s3.readReg64 .x25 = s3.sp + 0x210#64 := by rw [hx25_cs3, hx25_2, hx25_1, hsp3_s]
  have hx26_3 : s3.readReg64 .x26 = outPtr := by rw [hx26_cs3, hx26_2, hx26_1]
  have hx27_3 : s3.readReg64 .x27 = ctxPtr := by rw [hx27_cs3, hx27_2]
  have hx29_3 : s3.readReg64 .x29 = s.readReg64 .x29 := by rw [hx29_cs3, hx29_2, hx29_cs1]
  have hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s := by
    rw [hvregs_cs3, hvregs2_1, hvregs_cs1]
  have htr3_s : s3.trace = s.trace ++ kit.loadEvs encRecord peer.val ans := by
    rw [htr3_2, htr2_1, htr1]
  let evs_tot := evs_shim ++ (evs_poll ++ rustDeallocEvents kit.loadBoxSize 8)
  have henv_tot : LoadStepEnv kit kitEnv st peer.val evs_tot :=
    SeqEnv.append hbox_shim (SeqEnv.append hpoll_env rfl)
  have hst6_eq :
      M.stepEvents (rustDeallocEvents kit.loadBoxSize 8) st3 = M.stepEvents evs_tot st0 := by
    dsimp only [st3, st1, evs_tot]
    rw [M.stepEvents_append, M.stepEvents_append]
  rcases ans with ⟨⟨⟩⟩ | opt
  · exact absurd (hload_ok (.error ()) hrel) Bool.false_ne_true
  · cases opt with
    | none =>
      have htail := stageP1_load_none_tail_x_ext_placed_fd (Scope := Scope) (ikit := ikit)
        (st3 := st3) (Qp := Qp)
        peer hdealloc hmemcpy hkit_drop hfds_hi hext_stack hstack_lt s s3
        (s1.readReg64 .x0) outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
        sessStorePtr idStorePtr preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
        kyberStorePtr kyberStoreVt rngPtr b_390
        hdrop_nz hbs_nz hbs_lt hrel htr3_s hfds3 hcrl3 hpc3 hrun3 hsp_align hsp3_s
        hx19_3 hx21_3 hx24_3 hx25_3 hx26_3 hx27_3 hx29_3 hvregs3
      simp only [BitVec.add_assoc] at htail
      refine sepWPp_mono_post (sepWPp_perm_pre htail (by sep_focus)) (fun s6 P_f hq => ?_)
      rcases hq with ⟨⟨opt', hrel', htr6, _hlive6, hent6⟩, hregs6⟩
      rw [hst6_eq] at hent6
      exact ⟨⟨opt', evs_tot, hrel', henv_tot, htr6, hent6⟩, hregs6⟩
    | some r =>
      have htail := stageP1_load_some_tail_x_ext_placed_fd (Scope := Scope) (ikit := ikit)
        (st3 := st3) (Qp := Qp)
        peer r hdealloc hmemcpy hkit_drop hfds_hi hext_stack hstack_lt s s3
        (s1.readReg64 .x0) outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
        sessStorePtr idStorePtr preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
        kyberStorePtr kyberStoreVt rngPtr b_390
        hdrop_nz hbs_nz hbs_lt hrel htr3_s hfds3 hcrl3 hpc3 hrun3 hsp_align hsp3_s
        hx19_3 hx21_3 hx24_3 hx25_3 hx26_3 hx27_3 hx29_3 hvregs3
      simp only [BitVec.add_assoc] at htail
      refine sepWPp_mono_post (sepWPp_perm_pre htail (by sep_focus)) (fun s6 P_f hq => ?_)
      rcases hq with ⟨⟨opt', hrel', htr6, _hlive6, hent6⟩, hregs6⟩
      rw [hst6_eq] at hent6
      exact ⟨⟨opt', evs_tot, hrel', henv_tot, htr6, hent6⟩, hregs6⟩

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadExtPlacedBudgetFd
