/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec
public import LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.PeakBudget.W4OuterHelpers
public import LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
public import LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
public import LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget

/-!
# Codec, I/O, and Poll `fineCostModel` Credit Helpers for Untyped/Bad-KEM Rejection

Proves small-regime `fineCostModel` `PhaseCreditSpec` and `PhaseGroupSpec` lemmas for Stage P2
record codecs, bounded `cliIo.rd` reads, and SPK/KPK poll steps.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvBPlacedBudget

open CryptoVerification.LibsignalProtoCodec (WireType mergeBytes)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule StoresGhost decimalText keyName pathOf)
open CryptoVerification.SignalSession.Cli.Decimal.Helpers (decimalText_length_le)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo)
open LibsignalBinary.Heap (
  AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents rustReallocEvents
)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (
  fineCostModel_smallMaxReq_eq smallAllocCost_le_two_mul_add smallReallocCost_le_two_mul_add
)
open LibsignalBinary.Heap.SpecBudget (
  allocBytes1Events cliIoCap cliIoCapIdx cliIoCapsEvents cliIoReadScheduleCaps
)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (
  DirDomainCaps dirDomainCaps_opened_kpkLr dirDomainCaps_opened_kpkOt dirDomainCaps_opened_opk
  dirDomainCaps_opened_signed
)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (NonFreeBound PhaseGroupSpec nonFreeCount)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers (phaseCreditSpec_seq_freeOnly_exact)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux (PhaseCreditSpec.zero_live_peak_of_small)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (
  PreKeyDeserializeEnv RecordCodecLoopEnv ikpSubEnv_phaseCreditSpec pkSubEnv_phaseCreditSpec
  recordCodecLoopEnv_phaseCreditSpec
)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget (
  DecodeErrorPushBoundedEnv DropDecodeErrorEnv OptByteFreeEnv SpkCaps SpkDecodeEnv
  SpkEpilogueFreeEnv SpkErrTailEnv SpkField SpkLoopBoundedEnv SpkLoopEnv
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget (
  DecPkKeyFilesBounded
)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (
  DecimalEnv decimalEvents
)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (
  DirGetAfterReadEnv DirGetEnv DirGetErrAllocEnv DirGetMissEnv DirGetPathEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux (
  CliPkDecodeEnv CliSpkDecodeEnv cliPollKpkGetPollEnv cliPollPkGetPollEnv cliPollSpkGetPollEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget (
  OptIkpTryFromEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget (
  CliKpkGetPollEnv KpkPassEnv OptKpkDecodeEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux (
  dirGetEnv_path_readFile_groupSpec pathEnv_fine_phaseCredit_tight
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget (
  CliPkGetPollEnv OptPkDecodeEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget (
  CliSpkGetPollEnv OptSpkDecodeEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (pushBytesEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (
  bytesMergeEventsCore doReserveClearEvents
)

/-! ## 1. Small-Regime `PhaseCreditSpec` & `PhaseGroupSpec` Helpers for Stage P2 -/

theorem smallAlloc_fine_phaseCredit {req al : Nat} (hal : al ≤ 16) (hreq : req ≤ 9808) :
    PhaseCreditSpec fineCostModel (· = rustAllocEvents req al) (2 * req + 9539) 0 0 req := by
  have hmax : req ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; omega
  exact (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps hal hmax).mono
    (smallAllocCost_le_two_mul_add req) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl req)

theorem smallAlloc_fine_groupSpec (req al : Nat) :
    PhaseGroupSpec fineCostModel (· = rustAllocEvents req al) (3 * FineScale) :=
  PhaseGroupSpec.of_nonFreeBound fineCostModel (maxOps := 1) (by
    rintro _ rfl
    unfold rustAllocEvents
    split_ifs <;> simp [nonFreeCount])

theorem decimalText_length_le_10 (n : BitVec 32) :
    (decimalText n.toNat).length ≤ 10 := by
  have hn : n.toNat < 10 ^ 10 := Nat.lt_trans n.isLt (by decide)
  exact decimalText_length_le 10 n.toNat (by decide) hn

theorem pushBytesEvents_le_10_cases (k : Nat) (hk : k ≤ 10) :
    pushBytesEvents k 0 0 = [] ∨
    pushBytesEvents k 0 0 = rustAllocEvents 8 1 ∨
    pushBytesEvents k 0 0 = rustAllocEvents 8 1 ++ rustReallocEvents 8 16 1 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem decimalEnv_fine_phaseCredit (n : BitVec 32) :
    PhaseCreditSpec fineCostModel (DecimalEnv n) 19126 0 0 16 := by
  have hnil : PhaseCreditSpec fineCostModel (· = []) 19126 0 0 16 :=
    (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
  have h8 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 8 1) 9555 0 0 8 :=
    smallAlloc_fine_phaseCredit (by decide) (by decide)
  have hmax8 : 8 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hmax16 : 16 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hre : PhaseCreditSpec fineCostModel (· = rustReallocEvents 8 16 1) 9571 0 0 16 :=
    (PhaseCreditSpec.rustRealloc_small_small fineCostModel (old := 8) (new := 16) (al := 1)
      (by decide) (by decide) (by decide) hmax8 (by decide) hmax16).mono
      (smallReallocCost_le_two_mul_add 16) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 16)
  have h8_16 : PhaseCreditSpec fineCostModel
      (ConcatEnv (· = rustAllocEvents 8 1) (· = rustReallocEvents 8 16 1)) 19126 0 0 16 :=
    (h8.concat hre).mono (by decide) (by decide) (by decide) (by decide)
  have h8' : PhaseCreditSpec fineCostModel (· = rustAllocEvents 8 1) 19126 0 0 16 :=
    h8.mono (by decide) (by decide) (by decide) (by decide)
  exact ((hnil.or h8').or h8_16).of_imp fun evs he => by
    unfold DecimalEnv decimalEvents at he
    rcases pushBytesEvents_le_10_cases (decimalText n.toNat).length (decimalText_length_le_10 n) with
      h | h | h
    · rw [he, h]; exact Or.inl (Or.inl rfl)
    · rw [he, h]; exact Or.inl (Or.inr rfl)
    · rw [he, h]; exact Or.inr (ConcatEnv.append rfl rfl)

theorem decimalEnv_fine_groupSpec (n : BitVec 32) :
    PhaseGroupSpec fineCostModel (DecimalEnv n) (6 * FineScale) :=
  (PhaseGroupSpec.of_nonFreeBound fineCostModel (maxOps := 2) (by
    intro evs he
    unfold DecimalEnv decimalEvents at he
    rcases pushBytesEvents_le_10_cases (decimalText n.toNat).length (decimalText_length_le_10 n) with
      h | h | h <;> (rw [he, h]; decide))).mono (by decide)

def SpkCapsMaxLe (caps : SpkCaps) (B : Nat) : Prop :=
  caps.pub ≤ B ∧ caps.priv ≤ B ∧ caps.sig ≤ B

theorem spkCaps_get_le {caps : SpkCaps} {B : Nat}
    (h : SpkCapsMaxLe caps B) (f : SpkField) : caps.get f ≤ B := by
  rcases h with ⟨hpub, hpriv, hsig⟩
  cases f <;> simp only [SpkCaps.get] <;> omega

theorem spkCaps_set_le {caps : SpkCaps} {B v : Nat}
    (h : SpkCapsMaxLe caps B) (hv : v ≤ B) (f : SpkField) :
    SpkCapsMaxLe (caps.set f v) B := by
  rcases h with ⟨hpub, hpriv, hsig⟩
  cases f <;> exact ⟨by simpa [SpkCaps.set], by simpa [SpkCaps.set], by simpa [SpkCaps.set]⟩

theorem decodeErrorPushBounded0_fine_phaseCredit :
    PhaseCreditSpec fineCostModel (DecodeErrorPushBoundedEnv 0) 9795 0 0 128 := by
  have h128 := smallAlloc_fine_phaseCredit (req := 128) (al := 8) (by decide) (by decide)
  have hnil : PhaseCreditSpec fineCostModel (· = []) 9795 0 0 128 :=
    (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
  exact (hnil.or h128).of_imp fun evs hp => by
    rcases hp with rfl | ⟨_, rfl⟩ | ⟨hlt, _⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · omega

theorem spkErrTail_fine_phaseCredit :
    PhaseCreditSpec fineCostModel SpkErrTailEnv 19590 0 0 128 := by
  have h72 := smallAlloc_fine_phaseCredit (req := 72) (al := 8) (by decide) (by decide)
  have hfp : PhaseCreditSpec fineCostModel
      (ConcatEnv (· = rustAllocEvents 72 8) (DecodeErrorPushBoundedEnv 0)) 19590 0 0 128 :=
    (h72.concat decodeErrorPushBounded0_fine_phaseCredit).mono
      (by decide) (by decide) (by decide) (by decide)
  have hnil : PhaseCreditSpec fineCostModel (· = []) 19590 0 0 128 :=
    (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
  have h72' : PhaseCreditSpec fineCostModel (· = rustAllocEvents 72 8) 19590 0 0 128 :=
    h72.mono (by decide) (by decide) (by decide) (by decide)
  exact ((hnil.or h72').or hfp).of_imp fun evs he => by
    cases he with
    | nil => exact Or.inl (Or.inl rfl)
    | fromOnly => exact Or.inl (Or.inr rfl)
    | fromPush hp => exact Or.inr (ConcatEnv.append rfl hp)

theorem spkBytesMergeStep_4900_phaseCredit {wt : WireType} {bs v rest : List (BitVec 8)}
    {c : Nat} (hm : mergeBytes wt bs = some (v, rest)) (hv : v.length ≤ 4900) (hc : c ≤ 9808) :
    PhaseCreditSpec fineCostModel (· = bytesMergeEventsCore wt (BitVec.ofNat 64 c) bs)
      (19348 * (v.length + 1)) 0 0 9808 := by
  have hmax : 9808 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hc_toNat : (BitVec.ofNat 64 c).toNat = c := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcore : bytesMergeEventsCore wt (BitVec.ofNat 64 c) bs =
      if v.length = 0 then []
      else rustAllocEvents v.length 1 ++ doReserveClearEvents c v.length ++
        rustDeallocEvents v.length 1 := by
    simp [bytesMergeEventsCore, hm, hc_toNat]
  rw [show (· = bytesMergeEventsCore wt (BitVec.ofNat 64 c) bs) =
      (· = if v.length = 0 then []
        else rustAllocEvents v.length 1 ++ doReserveClearEvents c v.length ++
          rustDeallocEvents v.length 1) by rw [hcore]]
  split_ifs with hv0
  · exact (PhaseCreditSpec.nil fineCostModel).mono (by omega) (by decide) (by decide) (by decide)
  · have hv_pos : 1 ≤ v.length := by omega
    have halloc : PhaseCreditSpec fineCostModel (· = rustAllocEvents v.length 1)
        (2 * v.length + 9539) 0 0 9808 :=
      (smallAlloc_fine_phaseCredit (al := 1) (by decide) (by omega)).mono
        (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
    have hres : PhaseCreditSpec fineCostModel (· = doReserveClearEvents c v.length)
        29155 0 0 9808 := by
      unfold doReserveClearEvents
      split_ifs with hle hc0
      · exact (PhaseCreditSpec.nil fineCostModel).mono
          (by decide) (by decide) (by decide) (by decide)
      · have hnc_le : reserveCap c 0 v.length ≤ 9808 := by
          dsimp only [reserveCap]; omega
        exact (smallAlloc_fine_phaseCredit (al := 1) (by decide) hnc_le).mono
          (by omega) (Nat.le_refl 0) (Nat.le_refl 0) hnc_le
      · have hnc_le : reserveCap c 0 v.length ≤ 9808 := by
          dsimp only [reserveCap]; omega
        have hnc_pos : 1 ≤ reserveCap c 0 v.length := by
          dsimp only [reserveCap]; omega
        exact (PhaseCreditSpec.rustRealloc_small_small fineCostModel (old := c)
          (new := reserveCap c 0 v.length) (al := 1) (by decide) hnc_pos (by omega)
          (Nat.le_trans hc hmax) (by omega) (Nat.le_trans hnc_le hmax)).mono
          (Nat.le_trans (smallReallocCost_le_two_mul_add _) (by omega))
          (Nat.le_refl 0) (Nat.le_refl 0) hnc_le
    have hfree : PhaseCreditSpec fineCostModel (· = rustDeallocEvents v.length 1) 0 0 0 0 :=
      PhaseCreditSpec.rustDealloc_align16 fineCostModel (by decide)
    have hsum : (2 * v.length + 9539) + 29155 + 0 ≤ 19348 * (v.length + 1) := by omega
    exact (((halloc.concat hres).concat hfree).mono
      hsum (by decide) (by decide) (by decide)).of_imp fun evs he => by
        subst he
        exact ConcatEnv.append (ConcatEnv.append rfl rfl) rfl

theorem spkLoop_4900_phaseCredit :
    ∀ (rem : Nat) {caps : SpkCaps},
      rem ≤ 4900 → SpkCapsMaxLe caps 9808 →
      PhaseCreditSpec fineCostModel (SpkLoopBoundedEnv rem caps)
        (19348 * rem + 19590) 0 0 9808 := by
  intro rem
  induction rem using Nat.strongRecOn with
  | ind rem ih =>
    intro caps hrem hcaps
    refine {
      req_align := fun evs he => ?_
      credit_le := fun st0 {_} he => ?_
    }
    · cases he with
      | done herr =>
        exact (show PhaseCreditSpec fineCostModel SpkErrTailEnv (19348 * rem + 19590) 0 0 9808 from
          spkErrTail_fine_phaseCredit.mono
            (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)).req_align evs herr
      | @skipStep _ rem' _ _ hlt hnext =>
        exact (ih rem' hlt (by omega) hcaps).req_align evs hnext
      | @bytesStep f _ rem' _ wt bs v rest evs₂ hm hbs_le hprog _ hnext =>
        have hc : caps.get f ≤ 9808 := spkCaps_get_le hcaps f
        have hnc : (if v.length ≤ caps.get f then caps.get f
            else reserveCap (caps.get f) 0 v.length) ≤ 9808 := by
          split_ifs
          · exact hc
          · dsimp only [reserveCap]; omega
        have h1 := spkBytesMergeStep_4900_phaseCredit hm (by omega) hc
        have h2 := ih rem' (by omega) (by omega) (spkCaps_set_le hcaps hnc f)
        have hmul : 19348 * (v.length + 1) + (19348 * rem' + 19590) ≤ 19348 * rem + 19590 := by
          have hv1 : v.length + 1 + rem' ≤ rem := by omega
          calc 19348 * (v.length + 1) + (19348 * rem' + 19590)
              = 19348 * (v.length + 1 + rem') + 19590 := by rw [Nat.mul_add]; omega
            _ ≤ 19348 * rem + 19590 := Nat.add_le_add_right (Nat.mul_le_mul_left 19348 hv1) 19590
        exact (show PhaseCreditSpec fineCostModel _ (19348 * rem + 19590) 0 0 9808 from
          (h1.concat h2).mono hmul (Nat.le_refl 0) (Nat.le_refl 0) (by decide)).req_align _
          (ConcatEnv.append rfl hnext)
    · cases he with
      | done herr =>
        exact (show PhaseCreditSpec fineCostModel SpkErrTailEnv (19348 * rem + 19590) 0 0 9808 from
          spkErrTail_fine_phaseCredit.mono
            (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)).credit_le st0 herr
      | @skipStep _ rem' _ _ hlt hnext =>
        exact (show PhaseCreditSpec fineCostModel (SpkLoopBoundedEnv rem' caps)
            (19348 * rem + 19590) 0 0 9808 from
          (ih rem' hlt (by omega) hcaps).mono
            (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 9808)).credit_le st0 hnext
      | @bytesStep f _ rem' _ wt bs v rest evs₂ hm hbs_le hprog _ hnext =>
        have hc : caps.get f ≤ 9808 := spkCaps_get_le hcaps f
        have hnc : (if v.length ≤ caps.get f then caps.get f
            else reserveCap (caps.get f) 0 v.length) ≤ 9808 := by
          split_ifs
          · exact hc
          · dsimp only [reserveCap]; omega
        have h1 := spkBytesMergeStep_4900_phaseCredit hm (by omega) hc
        have h2 := ih rem' (by omega) (by omega) (spkCaps_set_le hcaps hnc f)
        have hmul : 19348 * (v.length + 1) + (19348 * rem' + 19590) ≤ 19348 * rem + 19590 := by
          have hv1 : v.length + 1 + rem' ≤ rem := by omega
          calc 19348 * (v.length + 1) + (19348 * rem' + 19590)
              = 19348 * (v.length + 1 + rem') + 19590 := by rw [Nat.mul_add]; omega
            _ ≤ 19348 * rem + 19590 := Nat.add_le_add_right (Nat.mul_le_mul_left 19348 hv1) 19590
        exact (show PhaseCreditSpec fineCostModel _ (19348 * rem + 19590) 0 0 9808 from
          (h1.concat h2).mono hmul (Nat.le_refl 0) (Nat.le_refl 0) (by decide)).credit_le st0
          (ConcatEnv.append rfl hnext)

theorem nonFreeCount_append (a b : List AllocEvent) :
    nonFreeCount (a ++ b) = nonFreeCount a + nonFreeCount b := by
  induction a with
  | nil => simp [nonFreeCount]
  | cons e tl ih =>
    cases e <;> simp [nonFreeCount, ih] <;> omega

theorem nonFreeCount_rustDealloc_zero (sz al : Nat) :
    nonFreeCount (rustDeallocEvents sz al) = 0 := by
  simp [rustDeallocEvents, nonFreeCount]

theorem nonFreeCount_rustAlloc_le_one (sz al : Nat) :
    nonFreeCount (rustAllocEvents sz al) ≤ 1 := by
  unfold rustAllocEvents
  split_ifs <;> simp [nonFreeCount]

theorem nonFreeCount_rustRealloc_le_one (old new al : Nat) :
    nonFreeCount (rustReallocEvents old new al) ≤ 1 := by
  unfold rustReallocEvents
  split_ifs <;> simp [nonFreeCount]

theorem nonFreeCount_bytesMergeCore {wt : WireType} {c : Nat} {bs v rest : List (BitVec 8)}
    (hm : mergeBytes wt bs = some (v, rest)) (hc : c < 2 ^ 63) :
    nonFreeCount (bytesMergeEventsCore wt (BitVec.ofNat 64 c) bs) ≤ v.length + 1 := by
  have hc_toNat : (BitVec.ofNat 64 c).toNat = c := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcore : bytesMergeEventsCore wt (BitVec.ofNat 64 c) bs =
      if v.length = 0 then []
      else rustAllocEvents v.length 1 ++ doReserveClearEvents c v.length ++
        rustDeallocEvents v.length 1 := by
    simp [bytesMergeEventsCore, hm, hc_toNat]
  rw [hcore]
  split_ifs with hv0
  · exact Nat.zero_le _
  · rw [nonFreeCount_append, nonFreeCount_append, nonFreeCount_rustDealloc_zero]
    have ha := nonFreeCount_rustAlloc_le_one v.length 1
    have hr : nonFreeCount (doReserveClearEvents c v.length) ≤ 1 := by
      unfold doReserveClearEvents
      split_ifs
      · simp [nonFreeCount]
      · exact nonFreeCount_rustAlloc_le_one _ 1
      · exact nonFreeCount_rustRealloc_le_one _ _ 1
    omega

theorem spkLoop_nonFreeBound :
    ∀ (rem : Nat) (caps : SpkCaps),
      NonFreeBound (SpkLoopBoundedEnv rem caps) (rem + 2) := by
  intro rem
  induction rem using Nat.strongRecOn with
  | ind rem ih =>
    intro caps evs he
    cases he with
    | done herr =>
      cases herr with
      | nil => exact Nat.zero_le _
      | fromOnly =>
        have h1 := nonFreeCount_rustAlloc_le_one 72 8
        omega
      | @fromPush evs_p hp =>
        rw [nonFreeCount_append]
        have h1 := nonFreeCount_rustAlloc_le_one 72 8
        have h2 : nonFreeCount evs_p ≤ 1 := by
          rcases hp with rfl | ⟨_, rfl⟩ | ⟨hlt, _⟩
          · exact Nat.zero_le _
          · exact nonFreeCount_rustAlloc_le_one 128 8
          · omega
        omega
    | @skipStep _ rem' _ _ hlt hnext =>
      have h := ih rem' hlt _ evs hnext
      omega
    | @bytesStep f _ rem' _ wt bs v rest evs₂ hm _ hprog hcap_lt hnext =>
      rw [nonFreeCount_append]
      have h1 := nonFreeCount_bytesMergeCore hm hcap_lt
      have h2 := ih rem' (by omega) _ evs₂ hnext
      omega

theorem optByteFree_freeOnly {evs : List AllocEvent} (h : OptByteFreeEnv evs) :
    FreeOnlyEvs evs := by
  rcases h with rfl | ⟨cap, _, _, rfl⟩
  · exact FreeOnlyEvs.nil
  · simp [rustDeallocEvents, FreeOnlyEvs]

theorem spkEpilogueFree_freeOnly {evs : List AllocEvent} (h : SpkEpilogueFreeEnv evs) :
    FreeOnlyEvs evs := by
  rcases h with ⟨e1, e2, e3, h1, h2, h3, rfl⟩
  exact FreeOnlyEvs.append (FreeOnlyEvs.append (optByteFree_freeOnly h1) (optByteFree_freeOnly h2))
    (optByteFree_freeOnly h3)

theorem dropDecodeError_freeOnly {evs : List AllocEvent} (h : DropDecodeErrorEnv evs) :
    FreeOnlyEvs evs := by
  rcases h with rfl | ⟨c, _, _, rfl⟩
  · simp [rustDeallocEvents, FreeOnlyEvs]
  · exact FreeOnlyEvs.append (by simp [rustDeallocEvents, FreeOnlyEvs])
      (by simp [rustDeallocEvents, FreeOnlyEvs])

theorem cliSpkDecode_imp_seq_freeOnly {bs : List (BitVec 8)} {evs : List AllocEvent}
    (h : CliSpkDecodeEnv bs evs) :
    SeqEnv (SpkLoopEnv (2 * bs.length + 3) bs.length) FreeOnlyEvs evs := by
  have toSeq {e : List AllocEvent} (hd : SpkDecodeEnv bs.length e) :
      SeqEnv (SpkLoopEnv (2 * bs.length + 3) bs.length) FreeOnlyEvs e := by
    rcases hd with hl | ⟨e1, e2, hl, hf, rfl⟩
    · exact Or.inl hl
    · exact Or.inr ⟨e1, e2, rfl, hl, spkEpilogueFree_freeOnly hf⟩
  rcases h with hl | hk
  · exact Or.inl hl
  · rcases hk with hd | ⟨e1, e2, hd, hdrop, rfl⟩
    · exact toSeq hd
    · rcases toSeq hd with hl | ⟨e1a, e1b, rfl, hl, hf1⟩
      · exact Or.inr ⟨e1, e2, rfl, hl, dropDecodeError_freeOnly hdrop⟩
      · exact Or.inr ⟨e1a, e1b ++ e2, List.append_assoc e1a e1b e2, hl,
          FreeOnlyEvs.append hf1 (dropDecodeError_freeOnly hdrop)⟩

theorem cliSpkDecode_fine_phaseCredit {bs : List (BitVec 8)} {cap : Nat}
    (hbs : bs.length ≤ cap) (hcap : cap ≤ 4900) :
    PhaseCreditSpec fineCostModel (CliSpkDecodeEnv bs)
      (19348 * cap + 19590) 0 0 9808 := by
  have hloop : PhaseCreditSpec fineCostModel (SpkLoopEnv (2 * bs.length + 3) bs.length)
      (19348 * cap + 19590) 0 0 9808 :=
    (spkLoop_4900_phaseCredit bs.length (Nat.le_trans hbs hcap)
      ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩).mono
      (Nat.add_le_add_right (Nat.mul_le_mul_left 19348 hbs) 19590)
      (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 9808)
  exact (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hloop).of_imp
    fun _ h => cliSpkDecode_imp_seq_freeOnly h

theorem cliSpkDecode_fine_groupSpec {bs : List (BitVec 8)} {cap : Nat}
    (hbs : bs.length ≤ cap) :
    PhaseGroupSpec fineCostModel (CliSpkDecodeEnv bs) (3 * FineScale * (cap + 2)) := by
  have hloop : PhaseGroupSpec fineCostModel (SpkLoopEnv (2 * bs.length + 3) bs.length)
      (3 * FineScale * (cap + 2)) :=
    (PhaseGroupSpec.of_nonFreeBound fineCostModel (spkLoop_nonFreeBound bs.length SpkCaps.zero)).mono
      (Nat.mul_le_mul_left (3 * FineScale) (by omega))
  have hseq := (hloop.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
    (Nat.le_of_eq (Nat.add_zero _))
  exact { groups_le := fun st0 {_} h => hseq.groups_le st0 (cliSpkDecode_imp_seq_freeOnly h) }

theorem recordCodecLoop_nonFreeBound :
    ∀ (budget maxLen : Nat),
      NonFreeBound (RecordCodecLoopEnv budget maxLen) (2 * budget) := by
  intro budget maxLen evs he
  induction he with
  | nil => exact Nat.zero_le _
  | @step fuel _ evs₁ evs₂ hstep _ ih =>
    rw [nonFreeCount_append]
    have hs : nonFreeCount evs₁ ≤ 1 := by
      cases hstep with
      | nil => exact Nat.zero_le 1
      | fromErr => exact nonFreeCount_rustAlloc_le_one 72 8
      | push0 hp =>
        rcases hp with rfl | ⟨_, rfl⟩ | ⟨hlt, _⟩
        · exact Nat.zero_le 1
        · exact nonFreeCount_rustAlloc_le_one 128 8
        · omega
    omega
  | @bytesStep fuel _ wt valCap bs v rest evs₁ evs₂ hm _ heq _ ih =>
    subst heq
    rw [nonFreeCount_append]
    have hr : nonFreeCount (bytesMergeEventsCore wt valCap bs) ≤ 2 := by
      unfold bytesMergeEventsCore
      simp only [hm]
      split_ifs
      · exact Nat.zero_le _
      · rw [nonFreeCount_append, nonFreeCount_append, nonFreeCount_rustDealloc_zero]
        have ha := nonFreeCount_rustAlloc_le_one v.length 1
        have hd : nonFreeCount (doReserveClearEvents valCap.toNat v.length) ≤ 1 := by
          unfold doReserveClearEvents
          split_ifs
          · simp [nonFreeCount]
          · exact nonFreeCount_rustAlloc_le_one _ 1
          · exact nonFreeCount_rustRealloc_le_one _ _ 1
        omega
    omega

theorem cliPkDecode_256_phaseCredit {bs : List (BitVec 8)} (hbs : bs.length ≤ 256) :
    PhaseCreditSpec fineCostModel (CliPkDecodeEnv bs) (19110 * 515) 0 0 520 := by
  have hmax : max 128 (2 * bs.length + 8) ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; omega
  have hmul : 19110 * (2 * bs.length + 3) ≤ 19110 * 515 :=
    Nat.mul_le_mul_left 19110 (by omega)
  have h1 : PhaseCreditSpec fineCostModel
      (RecordCodecLoopEnv (2 * bs.length + 3) bs.length) (19110 * 515) 0 0 520 :=
    (PhaseCreditSpec.zero_live_peak_of_small fineCostModel_modelHyps hmax
      (recordCodecLoopEnv_phaseCreditSpec fineCostModel_modelHyps (2 * bs.length + 3) bs.length)).mono
      hmul (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
  have h2 : PhaseCreditSpec fineCostModel (PreKeyDeserializeEnv bs.length) (19110 * 515) 0 0 520 :=
    (PhaseCreditSpec.zero_live_peak_of_small fineCostModel_modelHyps hmax
      (pkSubEnv_phaseCreditSpec fineCostModel_modelHyps (2 * bs.length + 3) bs.length)).mono
      hmul (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
  exact (h1.or h2).mono (Nat.max_self _).le (Nat.max_self _).le (Nat.max_self _).le (Nat.max_self _).le

theorem cliPkDecode_256_groupSpec {bs : List (BitVec 8)} (hbs : bs.length ≤ 256) :
    PhaseGroupSpec fineCostModel (CliPkDecodeEnv bs) (3 * FineScale * 1030) := by
  have hloop : PhaseGroupSpec fineCostModel
      (RecordCodecLoopEnv (2 * bs.length + 3) bs.length) (3 * FineScale * 1030) :=
    (PhaseGroupSpec.of_nonFreeBound fineCostModel
      (recordCodecLoop_nonFreeBound (2 * bs.length + 3) bs.length)).mono
      (Nat.mul_le_mul_left (3 * FineScale) (by omega))
  have hseq := (hloop.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
    (Nat.le_of_eq (Nat.add_zero _))
  refine ⟨fun st0 {_} h => hseq.groups_le st0 ?_⟩
  rcases h with hl | hpk
  · exact Or.inl hl
  · rcases hpk with hl | ⟨e1, e2, hl, hc, rfl⟩
    · exact Or.inl hl
    · refine Or.inr ⟨e1, e2, rfl, hl, ?_⟩
      rcases hc with ⟨_, evsD, ⟨b1, b2, hb1, hb2, rfl⟩, hd, rfl⟩
      exact FreeOnlyEvs.append
        (FreeOnlyEvs.append (optByteFree_freeOnly hb1) (optByteFree_freeOnly hb2))
        (dropDecodeError_freeOnly hd)

theorem optIkpTryFrom_256_phaseCredit {gr : Except Unit (List (BitVec 8))}
    (hcap : ∀ bs, gr = .ok bs → bs.length ≤ 256) :
    PhaseCreditSpec fineCostModel (OptIkpTryFromEnv gr) (19110 * 515) 0 0 520 := by
  cases gr with
  | error u =>
    cases u
    unfold OptIkpTryFromEnv
    exact (PhaseCreditSpec.nil fineCostModel).mono
      (by decide) (by decide) (by decide) (by decide)
  | ok bs =>
    have hbs := hcap bs rfl
    unfold OptIkpTryFromEnv
    have hmax : max 128 (2 * bs.length + 8) ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]; omega
    have hmul : 19110 * (2 * bs.length + 3) ≤ 19110 * 515 :=
      Nat.mul_le_mul_left 19110 (by omega)
    exact (PhaseCreditSpec.zero_live_peak_of_small fineCostModel_modelHyps hmax
      (ikpSubEnv_phaseCreditSpec fineCostModel_modelHyps (2 * bs.length + 3) bs.length)).mono
      hmul (Nat.le_refl 0) (Nat.le_refl 0) (by omega)

theorem optIkpTryFrom_256_groupSpec {gr : Except Unit (List (BitVec 8))}
    (hcap : ∀ bs, gr = .ok bs → bs.length ≤ 256) :
    PhaseGroupSpec fineCostModel (OptIkpTryFromEnv gr) (3 * FineScale * 1030) := by
  cases gr with
  | error u =>
    cases u
    unfold OptIkpTryFromEnv
    exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  | ok bs =>
    have hbs := hcap bs rfl
    unfold OptIkpTryFromEnv
    have hloop : PhaseGroupSpec fineCostModel
        (RecordCodecLoopEnv (2 * bs.length + 3) bs.length) (3 * FineScale * 1030) :=
      (PhaseGroupSpec.of_nonFreeBound fineCostModel
        (recordCodecLoop_nonFreeBound (2 * bs.length + 3) bs.length)).mono
        (Nat.mul_le_mul_left (3 * FineScale) (by omega))
    have hseq := (hloop.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
      (Nat.le_of_eq (Nat.add_zero _))
    refine ⟨fun st0 {_} ⟨e1, e2, hl, hc, heq⟩ => hseq.groups_le st0 ?_⟩
    subst heq
    refine Or.inr ⟨e1, e2, rfl, hl, ?_⟩
    rcases hc with ⟨b1, b2, hb1, hb2, rfl⟩ | ⟨_, evsD, ⟨b1, b2, hb1, hb2, rfl⟩, hd, rfl⟩
    · exact FreeOnlyEvs.append (optByteFree_freeOnly hb1) (optByteFree_freeOnly hb2)
    · exact FreeOnlyEvs.append
        (FreeOnlyEvs.append (optByteFree_freeOnly hb1) (optByteFree_freeOnly hb2))
        (dropDecodeError_freeOnly hd)

theorem allocBytes1_le_9808_fine_phaseCredit {bs : List (BitVec 8)}
    (hbs : bs.length ≤ 9808) :
    PhaseCreditSpec fineCostModel (· = allocBytes1Events bs) (2 * bs.length + 9539) 0 0 bs.length := by
  unfold allocBytes1Events
  split_ifs with hz
  · exact (PhaseCreditSpec.nil fineCostModel).mono (by omega) (by decide) (by decide) (by omega)
  · exact smallAlloc_fine_phaseCredit (al := 1) (by decide) hbs

theorem cliIoCapIdx_le_of_le :
    ∀ (K j r : Nat), j ≤ K → r ≤ cliIoCap j → cliIoCapIdx K r = cliIoCapIdx j r
  | 0, j, _, hj, _ => by cases Nat.eq_zero_of_le_zero hj; rfl
  | K + 1, j, r, hj, hr => by
    by_cases hjk : j = K + 1
    · subst hjk; rfl
    · have hle : j ≤ K := by omega
      rw [show cliIoCapIdx (K + 1) r = if r ≤ cliIoCap K then cliIoCapIdx K r else K + 1 from rfl]
      have hpow : 2 ^ j ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) hle
      have hcap : r ≤ cliIoCap K :=
        Nat.le_trans hr (by unfold cliIoCap; exact Nat.mul_le_mul_left 4096 hpow)
      simp only [hcap, ↓reduceIte]
      exact cliIoCapIdx_le_of_le K j r hle hr

theorem readFile_le_8192_fine_phaseCredit {rd : ReadRule} {F0 : FsFiles}
    {path : List (BitVec 8)} (hcap : ∀ bs, rd F0 path = .ok bs → bs.length ≤ 8192) :
    PhaseCreditSpec fineCostModel (ReadFileRuleEnv rd F0 path) 43654 0 0 8192 := by
  unfold ReadFileRuleEnv
  cases hrd : rd F0 path with
  | error u =>
    cases u
    exact (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
  | ok bs =>
    dsimp only
    have hbs : bs.length ≤ 8192 := hcap bs hrd
    have hNil : PhaseCreditSpec fineCostModel (· = []) 43654 0 0 8192 :=
      (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
    have hAllocBs : PhaseCreditSpec fineCostModel (· = allocBytes1Events bs) 43654 0 0 8192 :=
      (allocBytes1_le_9808_fine_phaseCredit (by omega)).mono
        (by omega) (Nat.le_refl 0) (Nat.le_refl 0) hbs
    have h4096_raw : PhaseCreditSpec fineCostModel (· = rustAllocEvents 4096 1) 17731 0 0 4096 :=
      smallAlloc_fine_phaseCredit (al := 1) (by decide) (by decide)
    have h4096 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 4096 1) 43654 0 0 8192 :=
      h4096_raw.mono (by decide) (by decide) (by decide) (by decide)
    have hre8192 : PhaseCreditSpec fineCostModel
        (· = rustReallocEvents 4096 8192 1) 25923 0 0 8192 :=
      (PhaseCreditSpec.rustRealloc_small_small fineCostModel (old := 4096) (new := 8192) (al := 1)
        (by decide) (by decide) (by decide)
        (by rw [fineCostModel_smallMaxReq_eq]; decide)
        (by decide)
        (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
        (smallReallocCost_le_two_mul_add 8192) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 8192)
    have h4096_8192 : PhaseCreditSpec fineCostModel
        (ConcatEnv (· = rustAllocEvents 4096 1) (· = rustReallocEvents 4096 8192 1))
        43654 0 0 8192 :=
      (h4096_raw.concat hre8192).mono (by decide) (by decide) (by decide) (by decide)
    exact (((hNil.or hAllocBs).or h4096).or h4096_8192).of_imp fun evs h => by
      rcases h with h1 | ⟨_, h2⟩ | ⟨_, h3⟩ | ⟨hgt, _⟩
      · exact Or.inl (Or.inl (Or.inr h1))
      · exact Or.inl (Or.inl (Or.inl h2))
      · by_cases hbs0 : bs.length = 0
        · have hnil : evs = [] := by
            rw [h3]
            unfold cliIoReadScheduleCaps
            simp only [hbs0, ↓reduceIte, cliIoCapsEvents]
          exact Or.inl (Or.inl (Or.inl hnil))
        · by_cases hbs4096 : bs.length ≤ 4096
          · have hidx0 : cliIoCapIdx 9 bs.length = 0 :=
              cliIoCapIdx_le_of_le 9 0 bs.length (by decide) hbs4096
            have heq : evs = rustAllocEvents 4096 1 := by
              rw [h3]
              unfold cliIoReadScheduleCaps
              simp only [hbs0, ↓reduceIte, hidx0]
              rfl
            exact Or.inl (Or.inr heq)
          · have hidx1 : cliIoCapIdx 9 bs.length = 1 := by
              rw [cliIoCapIdx_le_of_le 9 1 bs.length (by decide) hbs]
              unfold cliIoCapIdx
              have hn0 : ¬ bs.length ≤ cliIoCap 0 := by change ¬ bs.length ≤ 4096; omega
              simp only [hn0, ↓reduceIte]
            have heq : evs = rustAllocEvents 4096 1 ++ rustReallocEvents 4096 8192 1 := by
              rw [h3]
              unfold cliIoReadScheduleCaps
              simp only [hbs0, ↓reduceIte, hidx1]
              rfl
            rw [heq]
            exact Or.inr (ConcatEnv.append rfl rfl)
      · omega

theorem dirGet_small_fine_phaseCredit {F0 : FsFiles} {dir : DirGhost}
    {name : List (BitVec 8)} {fileCap : Nat} (hdc : DirDomainCaps 64 0 0 dir)
    (hname : name.length ≤ 64) (hfcap : fileCap ≤ 4900)
    (hcap : ∀ bs, cliIo.rd F0 (pathOf dir.path name) = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec fineCostModel
      (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd F0 dir name)
      65000 0 0 8192 := by
  unfold DirGetEnv
  cases hfind : dir.changed.find? (fun e => e.1 == name) with
  | some e =>
    have hmem : e ∈ dir.changed := List.mem_of_find?_eq_some hfind
    have hv : e.2.length ≤ 0 := hdc.changed_val_le e.1 e.2 hmem
    exact (allocBytes1_le_9808_fine_phaseCredit (bs := e.2) (by omega)).mono
      (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
  | none =>
    unfold DirGetMissEnv
    have hp : PhaseCreditSpec fineCostModel
        (DirGetPathEnv PathEnv dir.path name) 21185 0 0 256 := by
      unfold DirGetPathEnv
      split_ifs
      · exact (allocBytes1_le_9808_fine_phaseCredit (bs := name) (by omega)).mono
          (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
      · exact pathEnv_fine_phaseCredit_tight hdc.path_len_le hname
    cases hrd : cliIo.rd F0 (pathOf dir.path name) with
    | error u =>
      cases u
      have hr0 : PhaseCreditSpec fineCostModel
          (ReadFileRuleEnv cliIo.rd F0 (pathOf dir.path name)) 0 0 0 0 := by
        unfold ReadFileRuleEnv
        rw [hrd]
        exact PhaseCreditSpec.nil fineCostModel
      have herr22 : PhaseCreditSpec fineCostModel
          (DirGetAfterReadEnv cliIo.rd F0 (pathOf dir.path name)) 9583 0 0 22 := by
        unfold DirGetAfterReadEnv DirGetErrAllocEnv
        rw [hrd]
        exact phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
          (smallAlloc_fine_phaseCredit (req := 22) (al := 1) (by decide) (by decide))
      exact (hp.seq (hr0.seq herr22)).mono
        (by decide) (by decide) (by decide) (by decide)
    | ok bs =>
      have hrOk := readFile_le_8192_fine_phaseCredit (rd := cliIo.rd) (F0 := F0)
        (path := pathOf dir.path name) (fun bs' h' => Nat.le_trans (hcap bs' h') (by omega))
      have herr0 : PhaseCreditSpec fineCostModel
          (DirGetAfterReadEnv cliIo.rd F0 (pathOf dir.path name)) 0 0 0 0 := by
        unfold DirGetAfterReadEnv DirGetErrAllocEnv
        rw [hrd]
        exact phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
          (PhaseCreditSpec.nil fineCostModel)
      exact (hp.seq (hrOk.seq herr0)).mono
        (by decide) (by decide) (by decide) (by decide)

/-! ## 2. Stage P2 Poll Step & Arm Bounds -/

def spkPollFineCum : Nat := 19126 + 65000 + (19348 * 512 + 19590)
def kpkPassFineCum : Nat := 19126 + 65000 + (19348 * 4900 + 19590)
def kpkPollFineCum : Nat := 2 * kpkPassFineCum
def pkPollFineCum : Nat := 19126 + 65000 + 19110 * 515
def kpPollFineCum : Nat := 65000 + 19110 * 515

def spkPollFineGrpS : Nat := (6 + 39 + 3 * 514) * FineScale
def kpkPassFineGrpS : Nat := (6 + 39 + 3 * 4902) * FineScale
def kpkPollFineGrpS : Nat := 2 * kpkPassFineGrpS
def pkPollFineGrpS : Nat := (6 + 39 + 3 * 1030) * FineScale
def kpPollFineGrpS : Nat := (39 + 3 * 1030) * FineScale

theorem spkPoll_fine_specs {F0 : FsFiles} (spkId : BitVec 32)
    (hkf : DecPkKeyFilesBounded F0) :
    PhaseCreditSpec fineCostModel
      (cliPollSpkGetPollEnv (ReadFileRuleEnv cliIo.rd) F0 StoresGhost.opened.signed spkId)
      spkPollFineCum 0 0 9808 ∧
    PhaseGroupSpec fineCostModel
      (cliPollSpkGetPollEnv (ReadFileRuleEnv cliIo.rd) F0 StoresGhost.opened.signed spkId)
      spkPollFineGrpS := by
  have hdcSpk : DirDomainCaps 64 0 0 StoresGhost.opened.signed :=
    dirDomainCaps_opened_signed.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0)
  have hkn : (keyName spkId).length ≤ 64 :=
    Nat.le_trans (decimalText_length_le_10 spkId) (by decide)
  have hDecC := decimalEnv_fine_phaseCredit spkId
  have hGetC := dirGet_small_fine_phaseCredit (F0 := F0) hdcSpk hkn (by decide) (hkf.2.1 spkId)
  have hOptC : PhaseCreditSpec fineCostModel
      (OptSpkDecodeEnv CliSpkDecodeEnv
        (StoresGhost.opened.signed.get cliIo.rd F0 (keyName spkId)))
      (19348 * 512 + 19590) 0 0 9808 := by
    unfold OptSpkDecodeEnv
    have hget_eq : StoresGhost.opened.signed.get cliIo.rd F0 (keyName spkId) =
        cliIo.rd F0 (pathOf StoresGhost.opened.signed.path (keyName spkId)) := rfl
    rw [hget_eq]
    cases hrd : cliIo.rd F0 (pathOf StoresGhost.opened.signed.path (keyName spkId)) with
    | error _ =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (by decide) (by decide) (by decide) (by decide)
    | ok bs =>
      cases bs with
      | nil =>
        exact (PhaseCreditSpec.nil fineCostModel).mono
          (by decide) (by decide) (by decide) (by decide)
      | cons b rest =>
        exact cliSpkDecode_fine_phaseCredit (hkf.2.1 spkId (b :: rest) hrd) (by decide)
  have hDecG := decimalEnv_fine_groupSpec spkId
  have hGetG := dirGetEnv_path_readFile_groupSpec fineCostModel cliIo.rd F0
    StoresGhost.opened.signed (keyName spkId)
  have hOptG : PhaseGroupSpec fineCostModel
      (OptSpkDecodeEnv CliSpkDecodeEnv
        (StoresGhost.opened.signed.get cliIo.rd F0 (keyName spkId)))
      (3 * FineScale * 514) := by
    unfold OptSpkDecodeEnv
    have hget_eq : StoresGhost.opened.signed.get cliIo.rd F0 (keyName spkId) =
        cliIo.rd F0 (pathOf StoresGhost.opened.signed.path (keyName spkId)) := rfl
    rw [hget_eq]
    cases hrd : cliIo.rd F0 (pathOf StoresGhost.opened.signed.path (keyName spkId)) with
    | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
      | cons b rest => exact cliSpkDecode_fine_groupSpec (hkf.2.1 spkId (b :: rest) hrd)
  unfold cliPollSpkGetPollEnv CliSpkGetPollEnv spkPollFineCum spkPollFineGrpS
  refine ⟨?_, ?_⟩
  · exact (hDecC.seq (hGetC.seq
      (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hOptC))).mono
      (by decide) (by decide) (by decide) (by decide)
  · exact (hDecG.seq (hGetG.seq
      ((hOptG.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
        (Nat.le_of_eq (Nat.add_zero _))))).mono (by decide)

theorem kpkPass_fine_specs {F0 : FsFiles} {dir : DirGhost} (kpkId : BitVec 32)
    (hdc : DirDomainCaps 64 0 0 dir)
    (hcap : ∀ bs, cliIo.rd F0 (pathOf dir.path (keyName kpkId)) = .ok bs → bs.length ≤ 4900)
    (hget_eq : dir.get cliIo.rd F0 (keyName kpkId) =
      cliIo.rd F0 (pathOf dir.path (keyName kpkId))) :
    PhaseCreditSpec fineCostModel
      (KpkPassEnv DecimalEnv
        (fun d k => DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd F0 d (keyName k))
        CliSpkDecodeEnv cliIo.rd F0 dir kpkId)
      kpkPassFineCum 0 0 9808 ∧
    PhaseGroupSpec fineCostModel
      (KpkPassEnv DecimalEnv
        (fun d k => DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd F0 d (keyName k))
        CliSpkDecodeEnv cliIo.rd F0 dir kpkId)
      kpkPassFineGrpS := by
  have hkn : (keyName kpkId).length ≤ 64 :=
    Nat.le_trans (decimalText_length_le_10 kpkId) (by decide)
  have hDecC := decimalEnv_fine_phaseCredit kpkId
  have hGetC := dirGet_small_fine_phaseCredit (F0 := F0) hdc hkn (by decide) hcap
  have hOptC : PhaseCreditSpec fineCostModel
      (OptKpkDecodeEnv CliSpkDecodeEnv (dir.get cliIo.rd F0 (keyName kpkId)))
      (19348 * 4900 + 19590) 0 0 9808 := by
    unfold OptKpkDecodeEnv
    rw [hget_eq]
    cases hrd : cliIo.rd F0 (pathOf dir.path (keyName kpkId)) with
    | error _ =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (by decide) (by decide) (by decide) (by decide)
    | ok bs =>
      cases bs with
      | nil =>
        exact (PhaseCreditSpec.nil fineCostModel).mono
          (by decide) (by decide) (by decide) (by decide)
      | cons b rest =>
        exact cliSpkDecode_fine_phaseCredit (hcap (b :: rest) hrd) (by decide)
  have hDecG := decimalEnv_fine_groupSpec kpkId
  have hGetG := dirGetEnv_path_readFile_groupSpec fineCostModel cliIo.rd F0 dir (keyName kpkId)
  have hOptG : PhaseGroupSpec fineCostModel
      (OptKpkDecodeEnv CliSpkDecodeEnv (dir.get cliIo.rd F0 (keyName kpkId)))
      (3 * FineScale * 4902) := by
    unfold OptKpkDecodeEnv
    rw [hget_eq]
    cases hrd : cliIo.rd F0 (pathOf dir.path (keyName kpkId)) with
    | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
      | cons b rest => exact cliSpkDecode_fine_groupSpec (hcap (b :: rest) hrd)
  unfold KpkPassEnv kpkPassFineCum kpkPassFineGrpS
  refine ⟨?_, ?_⟩
  · exact (hDecC.seq (hGetC.seq
      (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hOptC))).mono
      (by decide) (by decide) (by decide) (by decide)
  · exact (hDecG.seq (hGetG.seq
      ((hOptG.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
        (Nat.le_of_eq (Nat.add_zero _))))).mono (by decide)

theorem kpkPoll_fine_specs {F0 : FsFiles} (kpkId : BitVec 32)
    (hkf : DecPkKeyFilesBounded F0) :
    PhaseCreditSpec fineCostModel
      (cliPollKpkGetPollEnv (ReadFileRuleEnv cliIo.rd) F0 StoresGhost.opened.kyber kpkId)
      kpkPollFineCum 0 0 9808 ∧
    PhaseGroupSpec fineCostModel
      (cliPollKpkGetPollEnv (ReadFileRuleEnv cliIo.rd) F0 StoresGhost.opened.kyber kpkId)
      kpkPollFineGrpS := by
  have hdcKot : DirDomainCaps 64 0 0 StoresGhost.opened.kyber.oneTime :=
    dirDomainCaps_opened_kpkOt.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0)
  have hdcKlr : DirDomainCaps 64 0 0 StoresGhost.opened.kyber.lastResort :=
    dirDomainCaps_opened_kpkLr.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0)
  have ⟨hC1, hG1⟩ := kpkPass_fine_specs kpkId hdcKot (hkf.2.2.2.1 kpkId) rfl
  have ⟨hC2, hG2⟩ := kpkPass_fine_specs kpkId hdcKlr (hkf.2.2.2.2 kpkId) rfl
  unfold cliPollKpkGetPollEnv CliKpkGetPollEnv kpkPollFineCum kpkPollFineGrpS
  dsimp only
  split
  · exact ⟨(hC1.seq hC2).mono (by decide) (by decide) (by decide) (by decide),
      (hG1.seq hG2).mono (by decide)⟩
  · exact ⟨hC1.mono (by decide) (by decide) (by decide) (by decide),
      hG1.mono (by decide)⟩

theorem pkPoll_fine_specs {F0 : FsFiles} (pkId : BitVec 32)
    (hkf : DecPkKeyFilesBounded F0) :
    PhaseCreditSpec fineCostModel
      (cliPollPkGetPollEnv (ReadFileRuleEnv cliIo.rd) F0 StoresGhost.opened.oneTime pkId)
      pkPollFineCum 0 0 8192 ∧
    PhaseGroupSpec fineCostModel
      (cliPollPkGetPollEnv (ReadFileRuleEnv cliIo.rd) F0 StoresGhost.opened.oneTime pkId)
      pkPollFineGrpS := by
  have hdcOpk : DirDomainCaps 64 0 0 StoresGhost.opened.oneTime :=
    dirDomainCaps_opened_opk.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0)
  have hkn : (keyName pkId).length ≤ 64 :=
    Nat.le_trans (decimalText_length_le_10 pkId) (by decide)
  have hDecC := decimalEnv_fine_phaseCredit pkId
  have hGetC := dirGet_small_fine_phaseCredit (F0 := F0) hdcOpk hkn (by decide) (hkf.2.2.1 pkId)
  have hOptC : PhaseCreditSpec fineCostModel
      (OptPkDecodeEnv CliPkDecodeEnv
        (StoresGhost.opened.oneTime.get cliIo.rd F0 (keyName pkId)))
      (19110 * 515) 0 0 520 := by
    unfold OptPkDecodeEnv
    have hget_eq : StoresGhost.opened.oneTime.get cliIo.rd F0 (keyName pkId) =
        cliIo.rd F0 (pathOf StoresGhost.opened.oneTime.path (keyName pkId)) := rfl
    rw [hget_eq]
    cases hrd : cliIo.rd F0 (pathOf StoresGhost.opened.oneTime.path (keyName pkId)) with
    | error _ =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (by decide) (by decide) (by decide) (by decide)
    | ok bs =>
      cases bs with
      | nil =>
        exact (PhaseCreditSpec.nil fineCostModel).mono
          (by decide) (by decide) (by decide) (by decide)
      | cons b rest =>
        exact cliPkDecode_256_phaseCredit (hkf.2.2.1 pkId (b :: rest) hrd)
  have hDecG := decimalEnv_fine_groupSpec pkId
  have hGetG := dirGetEnv_path_readFile_groupSpec fineCostModel cliIo.rd F0
    StoresGhost.opened.oneTime (keyName pkId)
  have hOptG : PhaseGroupSpec fineCostModel
      (OptPkDecodeEnv CliPkDecodeEnv
        (StoresGhost.opened.oneTime.get cliIo.rd F0 (keyName pkId)))
      (3 * FineScale * 1030) := by
    unfold OptPkDecodeEnv
    have hget_eq : StoresGhost.opened.oneTime.get cliIo.rd F0 (keyName pkId) =
        cliIo.rd F0 (pathOf StoresGhost.opened.oneTime.path (keyName pkId)) := rfl
    rw [hget_eq]
    cases hrd : cliIo.rd F0 (pathOf StoresGhost.opened.oneTime.path (keyName pkId)) with
    | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
      | cons b rest => exact cliPkDecode_256_groupSpec (hkf.2.2.1 pkId (b :: rest) hrd)
  unfold cliPollPkGetPollEnv CliPkGetPollEnv pkPollFineCum pkPollFineGrpS
  refine ⟨?_, ?_⟩
  · exact (hDecC.seq (hGetC.seq
      (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hOptC))).mono
      (by decide) (by decide) (by decide) (by decide)
  · exact (hDecG.seq (hGetG.seq
      ((hOptG.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
        (Nat.le_of_eq (Nat.add_zero _))))).mono (by decide)

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvBPlacedBudget
