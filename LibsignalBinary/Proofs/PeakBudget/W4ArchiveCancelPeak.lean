/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.W4InnerHelpers
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone4PlacedMidBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# W4 Archive and Clone `sc = 63` Free Cancellation

Parametric `(M : AllocCostModel) [HasFineReallocCredit M]` sequential `PhaseCreditSpec` bounds in
binary call order for W4 archive/clone operations: FIFO double-clone cancellation
(`SerializePrev1Env`), `Chain::clone` trial cancellation, the `≤ 4` archived-session trial-decrypt
loop (`ArchivedTrialIterEnv`, `1×` peak), and `SessionRecord::promote_state` (`PromoteStateArchiveEnv`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak

open CryptoGames.LibsignalSession (ReceiverChain)
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification.LibsignalSessionRepr (ChainGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent FreeOnlyEvs SeqEnv
  rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (
  ConcatEnv DeallocCreditSpec IterSeqEnv ModelHyps PhaseCreditSpec
)
open LibsignalBinary.Proofs.PeakBudget.W4InnerHelpers (
  OptRustDeallocEnv
  phaseCredit_chainCloneMk_body_free_cancel
  phaseCredit_chainClonePreMk
  phaseCredit_concat_freeOnly
  phaseCredit_iter_zero_live_le
  phaseCredit_vecVecClone1
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsBudget (
  SerializePrev1Env encodeRecordPrev1Mem
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsBudget (
  vecVecClone1Events VecVecClone1Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone4PlacedMidBudget (
  chainCloneMkEvents chainClonePreMkEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv)

/-! ## 1. FIFO Double-Clone Cancellation and `SerializePrev1Env` -/

/-- FIFO double-temporary cancellation (`((A ++ (B ++ Out)) ++ FreeA) ++ FreeB`): cancels both
`SessionStructure::clone` (`A`) and `<Vec<Vec<u8>> as Clone>::clone` (`B`) in epilogue drop order,
leaving `Δlive = l_out`. -/
theorem phaseCredit_fifo_two_clones_cancel {M : AllocCostModel} [HasFineReallocCredit M]
    {AllocA AllocB Out FreeA FreeB : List AllocEvent → Prop}
    {c_A p_A r_A c_B l_B p_B r_B c_out l_out p_out r_out : Nat}
    (hCancelA : ∀ {Body : List AllocEvent → Prop} {c_b l_b p_b r_b : Nat},
      PhaseCreditSpec M Body c_b l_b p_b r_b →
      PhaseCreditSpec M (ConcatEnv (ConcatEnv AllocA Body) FreeA)
        (c_A + c_b) l_b (p_A + p_b) (max r_A r_b))
    (hB : PhaseCreditSpec M AllocB c_B l_B p_B r_B)
    (hOut : PhaseCreditSpec M Out c_out l_out p_out r_out)
    (hFreeB : DeallocCreditSpec M FreeB l_B) :
    PhaseCreditSpec M
      (ConcatEnv (ConcatEnv (ConcatEnv AllocA (ConcatEnv AllocB Out)) FreeA) FreeB)
      (c_A + c_B + c_out)
      l_out
      (p_A + max p_B (l_B + p_out))
      (max r_A (max r_B r_out)) := by
  have hBO : PhaseCreditSpec M (ConcatEnv AllocB Out)
      (c_B + c_out) (l_out + l_B) (max p_B (l_B + p_out)) (max r_B r_out) :=
    (hB.concat hOut).mono (Nat.le_refl _) (by omega) (Nat.le_refl _) (Nat.le_refl _)
  have hAfterFreeA := hCancelA hBO
  have hAfterFreeB := hAfterFreeA.concat_dealloc_cancel hFreeB
  exact hAfterFreeB.mono (by omega) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- Sequential `PhaseCreditSpec` for `SerializePrev1Env G sess enc`. -/
theorem phaseCredit_serializePrev1Env_seqFree {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {G : SessionGhost} {sess : Session (List (BitVec 8))}
    {enc : List (BitVec 8)} {c_seg l_seg p_seg r_seg encCap outCap : Nat}
    (hSmall24 : 24 ≤ HasFineReallocCredit.smallMaxReq M)
    (henc : enc.length ≤ encCap)
    (hout : (encodeRecordPrev1Mem G sess enc).length ≤ outCap)
    (hSeg : PhaseCreditSpec M (SegCloneEnv G sess.state) c_seg l_seg p_seg r_seg) :
    PhaseCreditSpec M (SerializePrev1Env G sess enc)
      (c_seg + (9587 + (2 * encCap + 9539)) + (2 * outCap + 9539))
      (l_seg + (encCap + 8195) + (outCap + 8195))
      (max p_seg (l_seg + (encCap + 8195) + (outCap + 8195)))
      (max r_seg (max 24 (max encCap outCap))) := by
  have hv : PhaseCreditSpec M (· = vecVecClone1Events enc)
      (9587 + (2 * encCap + 9539)) (encCap + 8195) (encCap + 8195) (max 24 encCap) := by
    have hv0 := phaseCredit_vecVecClone1 hM (x := ⟨0#64, 0#64, enc⟩) hSmall24 henc
    exact hv0.of_imp fun evs he => he
  have ho : PhaseCreditSpec M
      (· = rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1)
      (2 * outCap + 9539) (outCap + 8195) (outCap + 8195) outCap :=
    (PhaseCreditSpec.rustAlloc_aff hM (by decide : 1 ≤ 16)).mono
      (by omega) (by omega) (by omega) hout
  have ho_free : PhaseCreditSpec M
      (SeqEnv (· = rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1) FreeOnlyEvs)
      (2 * outCap + 9539) (outCap + 8195) (outCap + 8195) outCap :=
    (ho.seq (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
      (by omega) (by omega) (by omega) (by omega)
  have hvo := hv.seq ho_free
  have hfull := hSeg.seq hvo
  exact (hfull.of_imp fun _ h => h).mono (by omega) (by omega) (by omega) (by omega)

/-! ## 2. `Chain::clone` + Trial Body + `ErrTail` Drop Cancellation -/

/-- Allocation trace of `Chain::clone` on `gc`. -/
def chainCloneFullEvents (gc : ChainGhost × ReceiverChain) : List AllocEvent :=
  chainClonePreMkEvents gc ++ chainCloneMkEvents gc.2.messageKeys

/-- Cancels the cloned `Chain`'s `104 * mks.length` `Vec<MessageKey>` buffer across `E_body` and `E_dropChain`, leaving `Δlive = l_b`.
-/
theorem phaseCredit_chainCloneFull_body_free_cancel {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {gc : ChainGhost × ReceiverChain} {mkCap seedCap : Nat}
    {E_body E_dropChain : List AllocEvent → Prop} {c_b l_b p_b r_b : Nat}
    (hsrk : gc.1.srk.bytes.length ≤ 33)
    (hpriv : gc.1.priv.bytes.length ≤ 32)
    (hSmall33 : 33 ≤ HasFineReallocCredit.smallMaxReq M)
    (hlen : gc.2.messageKeys.length ≤ mkCap)
    (hseed : ∀ mkg ∈ gc.2.messageKeys, mkg.seed.length ≤ seedCap)
    (hSmallSeed : seedCap ≤ HasFineReallocCredit.smallMaxReq M)
    (hbody : PhaseCreditSpec M E_body c_b l_b p_b r_b)
    (hdrop : ∀ evs, E_dropChain evs →
      if gc.2.messageKeys = [] then FreeOnlyEvs evs
      else ConcatEnv FreeOnlyEvs
        (ConcatEnv (· = rustDeallocEvents (104 * gc.2.messageKeys.length) 8) FreeOnlyEvs) evs) :
    PhaseCreditSpec M
      (ConcatEnv (ConcatEnv (· = chainCloneFullEvents gc) E_body) E_dropChain)
      (3 * (2 * 33 + 9539) + (2 * (104 * mkCap) + 9539) + mkCap * (2 * seedCap + 9539) + c_b)
      l_b
      (((104 * mkCap) + 8195) + p_b)
      (max 33 (max (104 * mkCap) (max seedCap r_b))) := by
  have hpre := phaseCredit_chainClonePreMk hM hsrk hpriv hSmall33
  have hmkCancel := phaseCredit_chainCloneMk_body_free_cancel hM hlen hseed hSmallSeed hbody hdrop
  have hfull := hpre.concat hmkCancel
  have himp : ∀ evs,
      ConcatEnv (ConcatEnv (· = chainCloneFullEvents gc) E_body) E_dropChain evs →
      ConcatEnv (· = chainClonePreMkEvents gc)
        (ConcatEnv (ConcatEnv (· = chainCloneMkEvents gc.2.messageKeys) E_body) E_dropChain)
        evs := by
    rintro _ ⟨e12, e3, rfl, ⟨e1, e2, rfl, rfl, hb⟩, hd⟩
    refine ⟨chainClonePreMkEvents gc,
      (chainCloneMkEvents gc.2.messageKeys ++ e2) ++ e3,
      by simp [chainCloneFullEvents, List.append_assoc], rfl, ?_⟩
    exact ⟨chainCloneMkEvents gc.2.messageKeys ++ e2, e3, rfl, ⟨_, e2, rfl, rfl, hb⟩, hd⟩
  exact (hfull.of_imp himp).mono (by omega) (by omega) (by omega) (by omega)

/-! ## 3. `≤ 4` Archived-Session Trial-Decrypt Loop -/

/-- Single failed archived-session iteration envelope (`DecEnv x → TrialEnv x → DropEnv x`). -/
def ArchivedTrialIterEnv {α : Type}
    (DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop) (x : α) :
    List AllocEvent → Prop :=
  ConcatEnv (ConcatEnv (DecEnv x) (TrialEnv x)) (DropEnv x)

/-- Per-iteration `sc = 63` cancellation for `ArchivedTrialIterEnv`, leaving `Δlive = 0` and peak `≤ p_dec + p_tr`.
-/
theorem phaseCredit_archivedTrialIter_cancel {α : Type}
    {M : AllocCostModel} [HasFineReallocCredit M]
    {DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop}
    {c_dec p_dec r_dec c_tr p_tr r_tr : Nat} {l_dec : α → Nat} {x : α}
    (hl_le_p : l_dec x ≤ p_dec)
    (hDec : PhaseCreditSpec M (DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : PhaseCreditSpec M (TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : DeallocCreditSpec M (DropEnv x) (l_dec x)) :
    PhaseCreditSpec M (ArchivedTrialIterEnv DecEnv TrialEnv DropEnv x)
      (c_dec + c_tr) 0 (p_dec + p_tr) (max r_dec r_tr) := by
  have h12 : PhaseCreditSpec M (ConcatEnv (DecEnv x) (TrialEnv x))
      (c_dec + c_tr) (0 + l_dec x) (p_dec + p_tr) (max r_dec r_tr) :=
    (hDec.concat hTrial).mono (Nat.le_refl _) (by omega) (by omega) (Nat.le_refl _)
  exact h12.concat_dealloc_cancel hDrop

/-- `PhaseCreditSpec` across `xs.length ≤ 4` failed archived-session iterations (`Δlive = 0`, `Δpeak ≤ p_dec + p_tr`).
-/
theorem phaseCredit_archivedTrialLoop_le4 {α : Type}
    {M : AllocCostModel} [HasFineReallocCredit M]
    {DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop}
    {c_dec p_dec r_dec c_tr p_tr r_tr : Nat} {l_dec : α → Nat}
    {xs : List α} (hlen4 : xs.length ≤ 4)
    (hl_le_p : ∀ x ∈ xs, l_dec x ≤ p_dec)
    (hDec : ∀ x ∈ xs, PhaseCreditSpec M (DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : ∀ x ∈ xs, PhaseCreditSpec M (TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : ∀ x ∈ xs, DeallocCreditSpec M (DropEnv x) (l_dec x)) :
    PhaseCreditSpec M (IterSeqEnv (ArchivedTrialIterEnv DecEnv TrialEnv DropEnv) xs)
      (4 * (c_dec + c_tr)) 0 (p_dec + p_tr) (max r_dec r_tr) := by
  refine phaseCredit_iter_zero_live_le hlen4 fun x hx => ?_
  exact phaseCredit_archivedTrialIter_cancel
    (hl_le_p x hx) (hDec x hx) (hTrial x hx) (hDrop x hx)

/-! ## 4. `promote_state` (`archive_current_state`) Envelope Bound -/

/-- Envelope for `SessionRecord::promote_state` (`SerializeArchivedEnv → VecPushEnv → FreeOnlyEvs`).
-/
def PromoteStateArchiveEnv
    (SerializeArchivedEnv VecPushEnv : List AllocEvent → Prop) :
    List AllocEvent → Prop :=
  ConcatEnv (ConcatEnv SerializeArchivedEnv VecPushEnv) FreeOnlyEvs

/-- Parametric `PhaseCreditSpec` for `PromoteStateArchiveEnv`. -/
theorem phaseCredit_promoteStateArchive {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    {SerializeArchivedEnv VecPushEnv : List AllocEvent → Prop}
    {c_ser l_ser p_ser r_ser c_push r_push : Nat}
    (hSer : PhaseCreditSpec M SerializeArchivedEnv c_ser l_ser p_ser r_ser)
    (hPush : PhaseCreditSpec M VecPushEnv c_push 0 0 r_push) :
    PhaseCreditSpec M (PromoteStateArchiveEnv SerializeArchivedEnv VecPushEnv)
      (c_ser + c_push)
      l_ser
      (max p_ser l_ser)
      (max r_ser r_push) := by
  have h12 := hSer.concat hPush
  have h123 := phaseCredit_concat_freeOnly hM h12
  exact h123.mono (by omega) (by omega) (by omega) (by omega)

end LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak
