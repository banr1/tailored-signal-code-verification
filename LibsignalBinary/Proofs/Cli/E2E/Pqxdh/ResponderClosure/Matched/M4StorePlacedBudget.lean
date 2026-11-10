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
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4StorePlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4StorePlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4UnwindPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4ErrUnwind
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4SaveId
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4SaveIdProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsStoreSession
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsStoreSessionProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4Unwind
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP4
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Matched-Session Substage P4.4 (`store_session`)

Budget-threaded `[LibsignalPlacement]` counterpart of `Matched.M4StorePlaced` on Block `518`
(`lsProg_518 (Rust.withPanics ext)`), advancing `A.pool` across `StoreStepEnv` followed by
`FreeOnlyEvs` (`+0x3cc → s0.readReg64 .x30`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4StorePlacedBudget

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees hiding dropSessionStructureLocal2Spec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit hiding SessionOnlyKitPlacedOkSE
  kitStoreShimSpec kitStorePollSpec kitStorePollSpecE
  kitStorePollPlacedSpec kitStorePollPlacedSpecE
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0 stackAt_sub_eq
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  prevSessionsEmptyAt storePollPlacedErr_unpack_repack
  storeSessionVtablesPlacedAt storeSessionVtablesPlacedAt_intro
)
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SignalSession
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv futDropBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (
  SessionStoreBudgetEnv StoreStepEnv kitStoreShimSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  SessionOnlyKitPlacedOkSE kitStorePollPlacedSpec kitStorePollPlacedSpecE
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrustTailsXExtPlacedBudget (
  bind_sepWP_steps_frame_placed call_rocl_entails_steps_frame_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4StorePlacedBudgetAux (
  coro2c8_16_fold_m4_placed coro2c8_16_split_eq_m4_placed
  p4_seg4a_placed_wp p4_seg4b_placed_wp p4_seg4c_gen_placed_wp p4_seg4d_err_placed_wp
  prevSessionsEmptyAt_sessionRecordAt_fold_placed
  prevSessionsEmptyAt_sessionRecordAt_unfold_placed
  stageP4_storeSession_ok_tail_prevEmpty_vregs_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4UnwindPlacedBudget (
  stageP4_err_unwind_550_prevEmpty_vregs_placed_ok
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

/-! ## Budget-threaded `store_session` precondition helpers -/

theorem storeShim_pre_intro_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {kit : SessionStoreSpec A.repAlloc 0#64} {s : State} {sp self addrA recA : BitVec 64}
    (hsp : s.sp = sp)
    (hx0 : s.readReg64 .x0 = self)
    (hx1 : s.readReg64 .x1 = addrA)
    (hx2 : s.readReg64 .x2 = recA)
    (hfits : FitsEnv M lim st (BoxAllocEnv kit.storeBoxSize)) :
    A.pool lim st s ∗ stackAt sp kit.storeShimStack ⊢
      (kitStoreShimSpec M A lim kit).pre
        (({ self := self, addrA := addrA, recA := recA } : StoreShimCall), st) s := by
  dsimp only [kitStoreShimSpec]
  rw [hsp]
  exact Entails.pure_right ⟨hx0, hx1, hx2, hfits⟩ (Entails.refl _)

theorem storePoll_pre_intro_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {sst0 : kit.StoreState}
    {s : State} {sp fut self addrA recA : BitVec 64}
    {peer : AddrGhost} {g : RecordGhost} {record : SessionRecord (List (BitVec 8))}
    (henv : kit.envOk s.fs.files)
    (hsp : s.sp = sp)
    (hx0 : s.readReg64 .x0 = fut)
    (hx8 : s.readReg64 .x8 = sp + 0x3e0#64)
    (hrok : kit.RecOk record)
    (haok : kit.addrOk peer.val)
    (hfits : FitsEnv M lim st (kitEnv.storePollEnv sst0 peer.val record)) :
    kit.storeBoxAt fut self addrA recA 0#8 ∗
      kit.storeAt self sst0 ∗
      memRegion (sp + 0x3e0#64) 48 ∗
      protocolAddressAt A.repAlloc peer addrA ∗
      sessionRecordAt A.repAlloc recA g record ∗
      A.pool lim st s ∗
      stackAt sp kit.storePollStack ⊢
      (kitStorePollPlacedSpecE M A lim kit kitEnv encRecord).pre
        (({ fut := fut, out := sp + 0x3e0#64,
            call := { addrA := addrA, addr := peer, recA := recA, g := g, record := record } }
            : StorePollCall),
          self, sst0, st) s := by
  dsimp only [kitStorePollPlacedSpecE, withEnvPre, kitStorePollPlacedSpec]
  rw [hsp]
  exact Entails.pure_right henv (Entails.pure_right ⟨hx0, hx8, hrok, haok, hfits⟩ (Entails.refl _))

/-! ## Spatial bundles and matched-session Substage P4.4 -/

/-- Shared resources across entry, `Ok(())` exit, and `Err(())` exit of matched `P4.4`
under `[LibsignalPlacement]`, separating the stack-frame anchor `s` from the pool state `s_pool`. -/
def stageP4MatchedStoreSharedPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (kit : SessionStoreSpec A.repAlloc 0#64)
    (s0 s s_pool : State)
    (coroPtr remoteAddrPtr sessionStorePtr : BitVec 64)
    (peer : AddrGhost) : SepProp :=
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x88#64) ↦₆₄ sessionStorePtr) ∗
  ((coroPtr + 0x90#64) ↦₆₄ kit.ss_vt) ∗
  memRegion (coroPtr + 0x2c8#64) 16 ∗
  memRegion (s.sp + 0x340#64) 36 ∗
  memRegion (s.sp + 0x370#64) 36 ∗
  memRegion (s.sp + 0x3e0#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
  protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
  A.pool lim st s_pool ∗
  stackAt s.sp (storeSessionCallStack kit)

def stageP4MatchedStorePrePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (kit : SessionStoreSpec A.repAlloc 0#64)
    (s0 s : State)
    (coroPtr outPtr remoteAddrPtr sessionStorePtr ptCap ptPtr : BitVec 64)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (sst0 : kit.StoreState)
    (g : RecordGhost) (G : SessionGhost) (ss : Session (List (BitVec 8))) : SepProp :=
  stageP4MatchedStoreSharedPlaced A lim st0 kit s0 s s coroPtr remoteAddrPtr sessionStorePtr peer ∗
  prevSessionsEmptyAt A.repAlloc coroPtr g ∗
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
  kit.storeAt sessionStorePtr sst0

def stageP4MatchedStoreOkPostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stf : M.σ)
    (kit : SessionStoreSpec A.repAlloc 0#64)
    (s0 s sf : State)
    (coroPtr outPtr remoteAddrPtr sessionStorePtr : BitVec 64)
    (pt : List (BitVec 8))
    (peer : AddrGhost) (sst0 : kit.StoreState) (ss : Session (List (BitVec 8))) : SepProp :=
  stageP4MatchedStoreSharedPlaced A lim stf kit s0 s sf coroPtr remoteAddrPtr sessionStorePtr peer ∗
  storeSessionVtablesPlacedAt kit ∗
  vecResultAt A.repAlloc outPtr (.ok pt) ∗
  memRegion (coroPtr + 0xe0#64) 368 ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  kit.storeAt sessionStorePtr (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.ok ()))

def stageP4MatchedStoreErrPostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stf : M.σ)
    (kit : SessionStoreSpec A.repAlloc 0#64)
    (s0 s sf : State)
    (coroPtr outPtr remoteAddrPtr sessionStorePtr : BitVec 64)
    (peer : AddrGhost) (sst0 : kit.StoreState) (ss : Session (List (BitVec 8))) : SepProp :=
  stageP4MatchedStoreSharedPlaced A lim stf kit s0 s sf coroPtr remoteAddrPtr sessionStorePtr peer ∗
  storeSessionVtablesPlacedAt kit ∗
  storePollPlacedOutAt outPtr (.error ()) ∗
  memRegion (coroPtr + 0xe0#64) 368 ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  kit.storeAt sessionStorePtr (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.error ()))

set_option maxHeartbeats 1200000 in
/-- Budget-threaded `[LibsignalPlacement]` matched-session Substage P4.4 (`store_session`,
`(blkPl_518).base + 0x3cc → s0.readReg64 .x30`) on general `prevSessionsEmptyAt A.repAlloc coroPtr g`. -/
theorem stageP4_matched_storeSession_vregs_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64)
    (kitEnv : SessionStoreBudgetEnv kit)
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hkit : SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encRecord (Rust.withPanics ext))
    (hsVt : SessionOnlyVtablesPlacedOk kit)
    {Qfs : Prop} {Qp : State → SepProp → Prop}
    (st0 : M.σ) (s0 s : State)
    (coroPtr ctxPtr outPtr remoteAddrPtr sessionStorePtr ptCap ptPtr : BitVec 64)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (sst0 : kit.StoreState)
    (g : RecordGhost) (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (F : SepProp) (Q : State → SepProp → Prop)
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : kit.RecOk ⟨some ss⟩)
    (haddr_ok : kit.addrOk peer.val)
    (hfits : FitsEnv M lim st0 (StoreStepEnv kit kitEnv sst0 peer.val ⟨some ss⟩))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : storeSessionCallStack kit ≤ 2 ^ 64)
    (hfs : FsAt kit.envOk Qfs (lsProg_518 (Rust.withPanics ext)) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x3cc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hOk : ∀ (evs : List AllocEvent) (sf : State) (Pf : SepProp),
      SeqEnv (StoreStepEnv kit kitEnv sst0 peer.val ⟨some ss⟩) FreeOnlyEvs evs →
      Steps (lsProg_518 (Rust.withPanics ext)) s sf →
      kit.storeRel sst0 peer.val ⟨some ss⟩ (.ok ()) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ kit.storeEvs encRecord peer.val ⟨some ss⟩ (.ok ()) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢ stageP4MatchedStoreOkPostPlaced A lim (M.stepEvents evs st0) kit s0 s sf
        coroPtr outPtr remoteAddrPtr sessionStorePtr pt peer sst0 ss ∗ F) →
      Q sf Pf)
    (hErr : ∀ (evs : List AllocEvent) (sf : State) (Pf : SepProp),
      SeqEnv (StoreStepEnv kit kitEnv sst0 peer.val ⟨some ss⟩) FreeOnlyEvs evs →
      Steps (lsProg_518 (Rust.withPanics ext)) s sf →
      kit.storeRel sst0 peer.val ⟨some ss⟩ (.error ()) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ kit.storeEvs encRecord peer.val ⟨some ss⟩ (.error ()) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢ stageP4MatchedStoreErrPostPlaced A lim (M.stepEvents evs st0) kit s0 s sf
        coroPtr outPtr remoteAddrPtr sessionStorePtr peer sst0 ss ∗ F) →
      Q sf Pf) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stageP4MatchedStorePrePlaced A lim st0 kit s0 s coroPtr outPtr remoteAddrPtr sessionStorePtr
        ptCap ptPtr b_2c0 pt peer sst0 g G ss ∗ F)
      Q Qp := by
  have herr_ub : stageP4ErrUnwindStack ≤ 2 ^ 64 :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hsp_ub
  have hbox_eq : kit.storeBoxSize = (BitVec.ofNat 64 kit.storeBoxSize).toNat :=
    (Nat.mod_eq_of_lt kit.storeBoxSize_lt).symm
  have hsp_al : s.spAligned = true := hsp_align
  refine sepWPp_intro_ro (R_ro := storeSessionVtablesPlacedAt kit)
    (fun hm => storeSessionVtablesPlacedAt_intro hsVt hcro.2 hm) ?_
  unfold stageP4MatchedStorePrePlaced stageP4MatchedStoreSharedPlaced storeSessionVtablesPlacedAt
  simp only [sepConj_assoc]
  have h4a := p4_seg4a_placed_wp (A := A) (lim := lim) ext st0 s coroPtr remoteAddrPtr
    sessionStorePtr kit.ss_vt (0#64 + kit.storeShimOff) hpc hrun hx19
  refine bind_sepWP_steps_frame_placed hcro h4a (by sep_focus)
    fun s1 hst1 hpc1 hrun1 hcro1 ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1,
      hx24_1, hx25_1, hx26_1, hx27_1, _, _, hlr1, hvregs1_0⟩ => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_storeSession_to_shim kit s.sp hsp_ub))
    (by sep_focus) ?_
  have hvregs1 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := hvregs1_0.trans hvregs
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hsp_al
  have hfits_box : FitsEnv M lim st0 (BoxAllocEnv kit.storeBoxSize) := hfits.seq_left
  refine call_rocl_entails_steps_frame_placed
    (spec := kitStoreShimSpec M A lim kit)
    (x := (({ self := sessionStorePtr, addrA := remoteAddrPtr,
              recA := coroPtr + 0xe0#64 } : StoreShimCall), st0))
    (P_spec := A.pool lim st0 s1 ∗ stackAt s.sp kit.storeShimStack)
    hcro1 (hkit.storeShim (by decide)) hpc1 hrun1 hsp1_al hlr1
    (storeShim_pre_intro_placed hsp1 hx0_1 hx1_1 hx2_1 hfits_box)
    (by sep_focus)
    (hnext := fun s2 hst2 hpc2 hrun2 hsp2_1 hsp2_al hcs2 hcro2 => ?_)
    (hpan_false := fun _ => by unfold kitStoreShimSpec; rfl)
    (hexit_false := fun _ _ => by unfold kitStoreShimSpec; rfl)
    (hoom_false := fun _ => by unfold kitStoreShimSpec; rfl)
  dsimp only [kitStoreShimSpec]
  rw [hsp1]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_shim => ?_
  refine SepWPp.pure_elim fun ⟨hx1_2, _, _, htr2_1, hevs_shim⟩ => ?_
  have hfits_after_shim := hfits.seq_right hevs_shim
  have hfits_poll :
      FitsEnv M lim (M.stepEvents evs_shim st0)
        (kitEnv.storePollEnv sst0 peer.val ⟨some ss⟩) :=
    hfits_after_shim.seq_left
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_storeSession_to_shim kit s.sp hsp_ub).symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (coro2c8_16_split_eq_m4_placed coroPtr))
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_2d0 => SepWPp.exists_elim fun u_2c8 => ?_
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, hx27_cs2, _, _, hvregs_cs2⟩
  have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs_cs2.trans hvregs1
  let boxPtr := s2.readReg64 .x0
  have h4b := p4_seg4b_placed_wp (A := A) (lim := lim) ext (M.stepEvents evs_shim st0) s2
    coroPtr ctxPtr boxPtr (0#64 + kit.storeFutVtOff) (0#64 + kit.storePollOff) u_2c8 u_2d0
    hpc2 hrun2 rfl hx1_2 (hx19_cs2.trans hx19_1) (hx27_cs2.trans (hx27_1.trans hx27))
  refine bind_sepWP_steps_frame_placed hcro2 h4b (by sep_focus)
    fun s3 hst3 hpc3 hrun3 hcro3 ⟨hsp3_2, htr3_2, hx0_3, _, hx8_3, hx19_3,
      hx24_3, hx25_3, hx26_3, _, _, _, hlr3, hvregs3_2⟩ => ?_
  have hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := hvregs3_2.trans hvregs2
  have hsp3 : s3.sp = s.sp := hsp3_2.trans hsp2
  have hsp3_al : s3.spAligned = true := by simpa [State.spAligned, hsp3] using hsp_al
  have hst_to3 : Steps (lsProg_518 (Rust.withPanics ext)) s s3 :=
    hst1.trans (hst2.trans hst3)
  have htr_to3 : s3.trace = s.trace := by rw [htr3_2, htr2_1, htr1]
  have henv3 : kit.envOk s3.fs.files := (hfs.of_steps_nil hst_to3 htr_to3).envOk_here
  have hrec_fold := prevSessionsEmptyAt_sessionRecordAt_fold_placed A.repAlloc coroPtr g G ss hExtra
  have hrec_unfold := prevSessionsEmptyAt_sessionRecordAt_unfold_placed A.repAlloc coroPtr g G ss
  refine P3P4.SepWPp.weaken_frame hrec_fold (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_storeSession_to_poll kit s.sp hsp_ub))
    (by sep_focus) ?_
  let pollCall : StorePollCall :=
    { fut := boxPtr
      out := s.sp + 0x3e0#64
      call := { addrA := remoteAddrPtr, addr := peer, recA := coroPtr + 0xe0#64,
                g := ⟨g.prevCap, g.prevPtr, some G⟩, record := ⟨some ss⟩ } }
  refine call_rocl_entails_steps_frame_placed
    (spec := kitStorePollPlacedSpecE M A lim kit kitEnv encRecord)
    (x := (pollCall, sessionStorePtr, sst0, M.stepEvents evs_shim st0))
    (P_spec := kit.storeBoxAt boxPtr sessionStorePtr remoteAddrPtr (coroPtr + 0xe0#64) 0#8 ∗
          kit.storeAt sessionStorePtr sst0 ∗ memRegion (s.sp + 0x3e0#64) 48 ∗
          protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
          sessionRecordAt A.repAlloc (coroPtr + 0xe0#64) ⟨g.prevCap, g.prevPtr, some G⟩ ⟨some ss⟩ ∗
          A.pool lim (M.stepEvents evs_shim st0) s3 ∗
          stackAt s.sp kit.storePollStack)
    hcro3 (hkit.storePoll (by decide)) hpc3 hrun3 hsp3_al hlr3
    (storePoll_pre_intro_placed henv3 hsp3 hx0_3 (by rw [hx8_3, hsp2]) hrec_ok haddr_ok hfits_poll)
    (by sep_focus)
    (hnext := fun s4 hst4 hpc4 hrun4 hsp4_3 hsp4_al hcs4 hcro4 => ?_)
    (hpan_false := fun _ => by unfold kitStorePollPlacedSpecE withEnvPre kitStorePollPlacedSpec; rfl)
    (hexit_false := fun _ _ => by unfold kitStorePollPlacedSpecE withEnvPre kitStorePollPlacedSpec; rfl)
    (hoom_false := fun _ => by unfold kitStorePollPlacedSpecE withEnvPre kitStorePollPlacedSpec; rfl)
  dsimp only [kitStorePollPlacedSpecE, withEnvPre, kitStorePollPlacedSpec, pollCall]
  rw [hsp3]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ans => SepWPp.exists_elim fun evs_poll => ?_
  refine SepWPp.pure_elim fun ⟨hrel, htr4_3, hevs_poll⟩ => ?_
  refine P3P4.SepWPp.weaken_frame hrec_unfold (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_storeSession_to_poll kit s.sp hsp_ub).symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (memRegion36_eq_exists_stagingCells (s.sp + 0x340#64))) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_360s => SepWPp.exists_elim fun u_358s =>
    SepWPp.exists_elim fun u_350s => SepWPp.exists_elim fun u_348s =>
    SepWPp.exists_elim fun u_340s => ?_
  have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
  rcases hcs4 with ⟨hx19_cs4, _, _, _, _, hx24_cs4, hx25_cs4, hx26_cs4, _, _, _, hvregs_cs4⟩
  have hvregs4 : calleeSavedVRegs s4 = calleeSavedVRegs s0 := hvregs_cs4.trans hvregs3
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hx19_cs4.trans hx19_3
  have hx24_4 : s4.readReg64 .x24 = s4.sp + 0x370#64 := by
    rw [hx24_cs4, hx24_3, hx24_cs2, hx24_1, hx24, hsp4]
  have hx25_4 : s4.readReg64 .x25 = s4.sp + 0x210#64 := by
    rw [hx25_cs4, hx25_3, hx25_cs2, hx25_1, hx25, hsp4]
  have hx26_4 : s4.readReg64 .x26 = outPtr :=
    hx26_cs4.trans (hx26_3.trans (hx26_cs2.trans (hx26_1.trans hx26)))
  have hbox_dealloc :
      A.live boxPtr kit.storeBoxSize 8 ∗
      kit.storeBoxAt boxPtr sessionStorePtr remoteAddrPtr (coroPtr + 0xe0#64) 1#8 ⊢
      A.live boxPtr (BitVec.ofNat 64 kit.storeBoxSize).toNat (8#64 : BitVec 64).toNat ∗
      memRegion boxPtr (BitVec.ofNat 64 kit.storeBoxSize).toNat := by
    refine Entails.trans (sepConj_mono_right
      (kit.storeBoxAt_memRegion boxPtr sessionStorePtr remoteAddrPtr (coroPtr + 0xe0#64) 1#8)) ?_
    rw [← hbox_eq]; exact Entails.refl _
  have hfold_2c8 := coro2c8_16_fold_m4_placed coroPtr boxPtr (0#64 + kit.storeFutVtOff)
  let st_poll := M.stepEvents evs_poll (M.stepEvents evs_shim st0)
  let evs_store := evs_shim ++ (evs_poll ++ rustDeallocEvents kit.storeBoxSize 8)
  have hevs_store : StoreStepEnv kit kitEnv sst0 peer.val ⟨some ss⟩ evs_store :=
    SeqEnv.append hevs_shim (SeqEnv.append hevs_poll rfl)
  have hst_store_eq :
      M.stepEvents
        (rustDeallocEvents (BitVec.ofNat 64 kit.storeBoxSize).toNat (8#64 : BitVec 64).toNat)
        st_poll =
      M.stepEvents evs_store st0 := by
    have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
    rw [← hbox_eq, h8]
    dsimp only [st_poll, evs_store]
    simp only [AllocCostModel.stepEvents_append]
  have hst_store_eq8 :
      M.stepEvents (rustDeallocEvents kit.storeBoxSize 8) st_poll =
      M.stepEvents evs_store st0 := by
    dsimp only [st_poll, evs_store]
    simp only [AllocCostModel.stepEvents_append]
  rcases ans with ⟨⟩ | ⟨⟩
  · -- Err () arm: +0x3f8 → storeFutDrop → +0x444 → +0x550 → x30
    refine P3P4.SepWPp.weaken_frame (storePollPlacedErr_unpack_repack (s.sp + 0x3e0#64))
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun o1 =>
      SepWPp.exists_elim fun o2 => SepWPp.exists_elim fun o3 =>
      SepWPp.exists_elim fun o4 => SepWPp.exists_elim fun o5 =>
      SepWPp.exists_elim fun o6 => SepWPp.exists_elim fun H_err =>
      SepWPp.pure_elim fun ⟨hw0_eq, hrepack⟩ => ?_
    have hw0_ne_pend : w0 + 3#64 ≠ 0#64 := by rw [hw0_eq]; decide
    have hw0_ne_ok : w0 + 2#64 ≠ 0#64 := by rw [hw0_eq]; decide
    have h4c := p4_seg4c_gen_placed_wp (A := A) (lim := lim) ext st_poll s4 coroPtr boxPtr
      (0#64 + kit.storeFutVtOff) (0#64 + kit.storeFutDropOff) w0
      o2 o3 o4 o5 u_340s u_348s u_350s u_358s o1 o6 u_360s
      hw0_ne_pend (kit.storeFutDrop_ne_zero rfl)
      hpc4 hrun4 hsp4_al hx19_4 hx24_4 hx25_4
    rw [hsp4] at h4c
    refine bind_sepWP_steps_frame_placed hcro4 h4c (by sep_focus)
      fun s5 hst5 hpc5 hrun5 hcro5 ⟨hsp5_4, htr5_4, _, hx19_5, hx21_5, hx22_5,
        hx23_5, hx24_5, hx25_5, hx26_5, _, hx28_5, _, hlr5, hvregs5_4⟩ => ?_
    have hsp5 : s5.sp = s.sp := hsp5_4
    have hsp5_al : s5.spAligned = true := by simpa [State.spAligned, hsp5] using hsp_al
    refine call_rocl_entails_steps_frame_placed
      (spec := futDropBudgetSpec) (x := ()) (P_spec := emp)
      hcro5 (hkit.storeFutDrop (by decide)) hpc5 hrun5 hsp5_al hlr5
      (Entails.refl _) (by sep_focus)
      (hpan_false := fun _ => by unfold futDropBudgetSpec; rfl)
      (hexit_false := fun _ _ => by unfold futDropBudgetSpec; rfl)
      (hoom_false := fun _ => by unfold futDropBudgetSpec; rfl)
      (hnext := fun s6 hst6 hpc6 hrun6 hsp6_5 hsp6_al hcs6 hcro6 => ?_)
    dsimp only [futDropBudgetSpec]
    refine SepWPp.pure_elim fun ⟨htr6_5, hvm6⟩ => ?_
    rw [← A.pool_transport lim st_poll s5 s6 hvm6]
    have hsp6 : s6.sp = s.sp := hsp6_5.trans hsp5
    rcases hcs6 with ⟨hx19_cs6, _, hx21_cs6, hx22_cs6, hx23_cs6, hx24_cs6, hx25_cs6,
      hx26_cs6, _, hx28_cs6, _, hvregs_cs6⟩
    refine P3P4.SepWPp.weaken_frame hbox_dealloc (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_storeSession_to_errUnwind kit s.sp hsp_ub))
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub))
      (by sep_focus) ?_
    have h4d_err := p4_seg4d_err_placed_wp (A := A) (lim := lim) ext hdealloc st_poll s6
      coroPtr boxPtr (0#64 + kit.storeFutVtOff) (BitVec.ofNat 64 kit.storeBoxSize) 8#64 w0
      kit.storeBoxSize_ne_zero hw0_ne_ok hpc6 hrun6 hsp6_al
      (hx19_cs6.trans hx19_5) (hx21_cs6.trans hx21_5) (hx23_cs6.trans hx23_5)
      (hx28_cs6.trans hx28_5)
    rw [hsp6] at h4d_err
    refine bind_sepWP_steps_frame_placed hcro6 h4d_err (by sep_focus)
      fun s7 hst7 hpc7 hrun7 hcro7 ⟨hsp7_6, htr7_6, hx8_7, hx19_7, hx22_7,
        hx24_7, hx25_7, hx26_7, _, hx28_7, _, hvregs7_6⟩ => ?_
    rw [hst_store_eq]
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub).symm)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (pollCellsAt_entails_memRegion48 (s.sp + 0x3e0#64) _ _ _ _ _ _ _)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame hfold_2c8 (by sep_focus) ?_
    have hsp7 : s7.sp = s.sp := hsp7_6
    have hsp7_align : (s7.sp &&& 15#64 == 0#64) = true := by rw [hsp7]; exact hsp_align
    have hx22_7' : s7.readReg64 .x22 = o1.zeroExtend 64 :=
      hx22_7.trans (hx22_cs6.trans hx22_5)
    have hx24_7' : s7.readReg64 .x24 = s7.sp + 0x370#64 := by
      rw [hx24_7, hx24_cs6, hx24_5, hsp7]
    have hx25_7' : s7.readReg64 .x25 = s7.sp + 0x210#64 := by
      rw [hx25_7, hx25_cs6, hx25_5, hsp7]
    have hx26_7' : s7.readReg64 .x26 = outPtr :=
      hx26_7.trans (hx26_cs6.trans (hx26_5.trans hx26_4))
    have hunwind := stageP4_err_unwind_550_prevEmpty_vregs_placed_ok ext hdealloc hDropSS3
      (M.stepEvents evs_store st0) s0 s7
      coroPtr (s.sp + 0x340#64) ptCap ptPtr outPtr w0 o2 o3 o4 o5 o1 o6 b_2c0 pt g G ss.state
      (fun _ _ => False) hpt_le herr_ub hcro7 hpc7 hrun7 hsp7_align hx8_7 hx19_7 hx22_7'
      hx24_7' hx25_7' hx26_7' hx28_7
      (hvregs7_6.trans (hvregs_cs6.trans (hvregs5_4.trans hvregs4)))
    rw [hsp7] at hunwind
    refine SepWPp.bind_false_frame hunwind (by sep_focus)
      fun sf P1 hpcf hrunf ⟨hst_unw, evs_unw, hfree_unw, hP1, hspf, htrf, hcsf, hvregsf, hcrof⟩ => ?_
    refine SepWPp.weaken_pre (sepConj_mono_left hP1) ?_
    have hst_all : Steps (lsProg_518 (Rust.withPanics ext)) s sf :=
      hst_to3.trans (hst4.trans (hst5.trans (hst6.trans (hst7.trans hst_unw))))
    have htr_all : sf.trace = s.trace ++ kit.storeEvs encRecord peer.val ⟨some ss⟩ (.error ()) := by
      rw [htrf, htr7_6, htr6_5, htr5_4, htr4_3, htr_to3]
    have hevs_err :
        SeqEnv (StoreStepEnv kit kitEnv sst0 peer.val ⟨some ss⟩) FreeOnlyEvs
          (evs_store ++ evs_unw) :=
      SeqEnv.append hevs_store hfree_unw
    have hst_err_eq :
        M.stepEvents evs_unw (M.stepEvents evs_store st0) =
        M.stepEvents (evs_store ++ evs_unw) st0 :=
      (M.stepEvents_append evs_store evs_unw st0).symm
    refine SepWPp.done hpcf hrunf ?_
    refine hErr (evs_store ++ evs_unw) sf _ hevs_err hst_all hrel hpcf hrunf hspf htr_all
      hcsf hvregsf hcrof ?_
    have hreplace :
        ∀ {A B R P Q : SepProp},
          (A ⊢ B) → P = A ∗ R → B ∗ R = Q → (P ⊢ Q) := by
      intro A B R P Q hab hp hq
      rw [hp, ← hq]
      exact sepConj_mono_left hab
    rw [hst_err_eq]
    unfold stageP4MatchedStoreErrPostPlaced stageP4MatchedStoreSharedPlaced storeSessionVtablesPlacedAt
    try simp only [sepConj_assoc]
    rw [stack_storeSession_to_errUnwind kit s.sp hsp_ub]
    exact hreplace (hrepack outPtr) (by sep_focus) (by sep_ac_rfl)
  · -- Ok () arm: +0x3f8 → storeFutDrop → +0x444 → x30
    have hstore_ok_eq :
        storePollPlacedOutAt (s.sp + 0x3e0#64) (.ok ()) =
        storePollOutAt 0#64 (s.sp + 0x3e0#64) (.ok ()) := rfl
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (hstore_ok_eq.trans (storePollOk_eq_exists_pollCells 0#64 (s.sp + 0x3e0#64))))
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun o1 => SepWPp.exists_elim fun o6 =>
      SepWPp.exists_elim fun o5 => SepWPp.exists_elim fun o4 =>
      SepWPp.exists_elim fun o3 => SepWPp.exists_elim fun o2 => ?_
    have h4c := p4_seg4c_gen_placed_wp (A := A) (lim := lim) ext st_poll s4 coroPtr boxPtr
      (0#64 + kit.storeFutVtOff) (0#64 + kit.storeFutDropOff)
      0xfffffffffffffffe#64 o2 o3 o4 o5 u_340s u_348s u_350s u_358s o1 o6 u_360s
      (by decide) (kit.storeFutDrop_ne_zero rfl)
      hpc4 hrun4 hsp4_al hx19_4 hx24_4 hx25_4
    rw [hsp4] at h4c
    refine bind_sepWP_steps_frame_placed hcro4 h4c (by sep_focus)
      fun s5 hst5 hpc5 hrun5 hcro5 ⟨hsp5_4, htr5_4, _, hx19_5, hx21_5, _,
        hx23_5, hx24_5, hx25_5, hx26_5, _, hx28_5, _, hlr5, hvregs5_4⟩ => ?_
    have hsp5 : s5.sp = s.sp := hsp5_4
    have hsp5_al : s5.spAligned = true := by simpa [State.spAligned, hsp5] using hsp_al
    refine call_rocl_entails_steps_frame_placed
      (spec := futDropBudgetSpec) (x := ()) (P_spec := emp)
      hcro5 (hkit.storeFutDrop (by decide)) hpc5 hrun5 hsp5_al hlr5
      (Entails.refl _) (by sep_focus)
      (hpan_false := fun _ => by unfold futDropBudgetSpec; rfl)
      (hexit_false := fun _ _ => by unfold futDropBudgetSpec; rfl)
      (hoom_false := fun _ => by unfold futDropBudgetSpec; rfl)
      (hnext := fun s6 hst6 hpc6 hrun6 hsp6_5 _ hcs6 hcro6 => ?_)
    dsimp only [futDropBudgetSpec]
    refine SepWPp.pure_elim fun ⟨htr6_5, hvm6⟩ => ?_
    rw [← A.pool_transport lim st_poll s5 s6 hvm6]
    have hsp6 : s6.sp = s.sp := hsp6_5.trans hsp5
    have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6]; exact hsp_align
    rcases hcs6 with ⟨hx19_cs6, _, hx21_cs6, _, hx23_cs6, hx24_cs6, hx25_cs6,
      hx26_cs6, _, hx28_cs6, _, hvregs_cs6⟩
    have hbox_dealloc_ok :
        A.live boxPtr kit.storeBoxSize 8 ∗
        kit.storeBoxAt boxPtr sessionStorePtr remoteAddrPtr (coroPtr + 0xe0#64) 1#8 ⊢
        A.live boxPtr kit.storeBoxSize 8 ∗ memRegion boxPtr kit.storeBoxSize :=
      sepConj_mono_right
        (kit.storeBoxAt_memRegion boxPtr sessionStorePtr remoteAddrPtr (coroPtr + 0xe0#64) 1#8)
    refine P3P4.SepWPp.weaken_frame hbox_dealloc_ok (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (stagingCellsAt_entails_memRegion36 (s.sp + 0x340#64) _ _ _ _ _)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (pollCellsAt_entails_memRegion48 (s.sp + 0x3e0#64) _ _ _ _ _ _ _)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame hfold_2c8 (by sep_focus) ?_
    have hx24_6' : s6.readReg64 .x24 = s6.sp + 0x370#64 := by
      rw [hx24_cs6, hx24_5, hsp6]
    have hx25_6' : s6.readReg64 .x25 = s6.sp + 0x210#64 := by
      rw [hx25_cs6, hx25_5, hsp6]
    have hx26_6' : s6.readReg64 .x26 = outPtr :=
      hx26_cs6.trans (hx26_5.trans hx26_4)
    have htail := stageP4_storeSession_ok_tail_prevEmpty_vregs_placed ext kit hdealloc hDropSS3
      st_poll s0 s6 coroPtr boxPtr outPtr ptCap ptPtr b_2c0 pt g G ss.state (fun _ _ => False)
      hpt_le hcap_lt hptr_nz hsp_ub hcro6 hpc6 hrun6 hsp6_align
      (hx19_cs6.trans hx19_5) (hx21_cs6.trans hx21_5) (hx23_cs6.trans hx23_5)
      hx24_6' hx25_6' hx26_6' (hx28_cs6.trans hx28_5)
      (hvregs_cs6.trans (hvregs5_4.trans hvregs4))
    rw [hsp6] at htail
    refine SepWPp.bind_false_frame htail (by sep_focus)
      fun sf P1 hpcf hrunf ⟨hst_tail, evs_tail, hfree_tail, hP1, hspf, htrf, hcsf, hvregsf, hcrof⟩ => ?_
    refine SepWPp.weaken_pre (sepConj_mono_left hP1) ?_
    have hst_all : Steps (lsProg_518 (Rust.withPanics ext)) s sf :=
      hst_to3.trans (hst4.trans (hst5.trans (hst6.trans hst_tail)))
    have htr_all : sf.trace = s.trace ++ kit.storeEvs encRecord peer.val ⟨some ss⟩ (.ok ()) := by
      rw [htrf, htr6_5, htr5_4, htr4_3, htr_to3]
    have hevs_ok :
        SeqEnv (StoreStepEnv kit kitEnv sst0 peer.val ⟨some ss⟩) FreeOnlyEvs
          (evs_store ++ evs_tail) :=
      SeqEnv.append hevs_store hfree_tail
    have hst_ok_eq :
        M.stepEvents evs_tail (M.stepEvents (rustDeallocEvents kit.storeBoxSize 8) st_poll) =
        M.stepEvents (evs_store ++ evs_tail) st0 := by
      rw [hst_store_eq8]
      exact (M.stepEvents_append evs_store evs_tail st0).symm
    refine SepWPp.done hpcf hrunf ?_
    refine hOk (evs_store ++ evs_tail) sf _ hevs_ok hst_all hrel hpcf hrunf hspf htr_all
      hcsf hvregsf hcrof ?_
    rw [hst_ok_eq]
    unfold stageP4MatchedStoreOkPostPlaced stageP4MatchedStoreSharedPlaced storeSessionVtablesPlacedAt
    try simp only [sepConj_assoc]
    exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4StorePlacedBudget
