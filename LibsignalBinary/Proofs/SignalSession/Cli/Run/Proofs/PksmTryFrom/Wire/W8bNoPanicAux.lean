/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bNoPanicAuxA
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bNoPanicAuxB
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bNoPanicAuxC
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWIdent
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWIdentPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWSharedPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCWPlacedBudget
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bSigMsg
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bSigMsgPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.SigMsgWPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWSigMsg
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWSigMsgPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bPack
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bPackWPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.PackWPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCPlacedBudget
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
meta import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCleanup
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

/-!
# Panic-Free Budget-Threaded Post-Loop Assembly (`+0x460 → ret`)

Proves the budget-pool panic-free `identity_key` error (`+0x830 → +0x978 → ret`),
`SignalMessage::try_from` `Ok` / `Err` (`+0x864 → +0x8c0` / `+0x9f0 → ret`), and `sret`
pack (`+0x8c0 → +0x970 → +0x504 → ret`) continuations, assembling
`preKeyPostLoopOkNoPanicW_of_codecHooks` (`+0x460 → ret`) on `preKeyPlacedProg H`.
-/

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bNoPanicAux

section TopExports

open Arm64
open ProofLib hiding SepWPp
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget (PksmCalleesPlaced pksmCalleesPlaced_of_codecHooks)

abbrev preKeyNoPanicQp :=
  LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget.preKeyNoPanicQp

abbrev w8b_of_sepWP_end_noPanic_pk :=
  @LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget.SepWPp.of_sepWP_end_noPanic_pk

abbrev w8b_frame_noPanic :=
  @LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget.SepWPp.frame_noPanic_pk

abbrev w8b_call_noPanic_pk :=
  @LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget.SepWPp.call_noPanic_budget_pk

theorem w8b_bind_frame_noPanic {prog : Program} {mid ret : BitVec 64}
    {s : State} {P F : SepProp} {Q' Q : State → SepProp → Prop}
    (h1 : CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp prog mid s P Q' preKeyNoPanicQp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Q' sm Pm →
      CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp prog ret sm (Pm ∗ F) Q preKeyNoPanicQp) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp prog ret s (P ∗ F) Q preKeyNoPanicQp :=
  W8bNoPanicAuxA.w8b_bind_frame_noPanic h1 h2

abbrev w8b_errTail_close_noPanic_placed := @W8bNoPanicAuxA.w8b_errTail_close_noPanic_placed

abbrev PreKeyPostLoopOkNoPanicWPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) : Prop :=
  W8bNoPanicAuxA.PreKeyPostLoopOkNoPanicWPlaced M A lim H

abbrev preKeyPostLoopOkNoPanicW_placed_of_5b4 := @W8bNoPanicAuxA.preKeyPostLoopOkNoPanicW_placed_of_5b4
abbrev preKey5b4OkNoPanicW_placed_of_684 := @W8bNoPanicAuxA.preKey5b4OkNoPanicW_placed_of_684
abbrev preKeyPresenceErrNoPanicW_placed_proof := @W8bNoPanicAuxB.preKeyPresenceErrNoPanicW_placed_proof
abbrev preKeyBaseKeyErrNoPanicW_placed_proof := @W8bNoPanicAuxC.preKeyBaseKeyErrNoPanicW_placed_proof
abbrev preKey684OkNoPanicW_placed_of_830 := @W8bNoPanicAuxC.preKey684OkNoPanicW_placed_of_830
abbrev preKeyKyberErrNoPanicW_placed_proof := @W8bNoPanicAuxC.preKeyKyberErrNoPanicW_placed_proof
abbrev preKey830OkNoPanicW_placed_of_864 := @W8bNoPanicAuxC.preKey830OkNoPanicW_placed_of_864

end TopExports

section ErrIdent

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bNoPanicAuxC (PreKeyIdentErrNoPanicWPlaced w8bRowIFrame_pull_pool_noPanic)
open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoGames.LibsignalSession (InvalidMessageReason SignalProtocolError)
open CryptoVerification (LibsignalHooks LibsignalPlacement blkLib_eq_111 blkPC_111 blkPl_111 lsmpl)
open CryptoVerification.E2E.Pqxdh.ResponderWire (bv_sub_add_lit' bv_sub_sub_lit keepsFrozenInv_codeRoLoaded preKeyPlacedProg)
open CryptoVerification.LibsignalTripleRatchet (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Wire (PostEpilogueStatePlaced deallocSlot entails_of_eq stackAt_sub_split)
open CryptoVerification.LibsignalTripleRatchetRepr (invalidMessageStrAt noneCap speAt speWord)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire (IdentErrStatePlaced boxSlot identityKeyTryFromSliceWordsErrPlacedSpec ikErrWords ikErrWords_entails_speAt pksmErrE pksmParse_ikErr w8bIdErrRestPlaced w8bIdErr_exists4_pre w8bIdErr_open_placed w8bIdErr_placed_pack w8bRowYFramePlaced w8bRowY_open_ident_placed w8b_skipFieldStackX100_bounds)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCWPlacedBudget (e_978_placed_wpE)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget (pksmFrom830Env_of_err_freeOnly)

open Arm64 ProofLib.ProgramReflection
open ProofLib hiding SepWPp
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget (blk111_noSvc0)

private abbrev eik_ikw_done := @CryptoVerification.LibsignalTripleRatchet.Wire.SepWP.done
private abbrev eik_ikw_pure_pre := @CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre
private abbrev eik_ikw_exists_pre := @CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre
private abbrev eik_ikw_of_sepWP_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk
private abbrev eik_ikw_of_sepWP_end_pk := @w8b_of_sepWP_end_noPanic_pk
private abbrev eik_ikw_call_noPanic_pk := @w8b_call_noPanic_pk

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero

private theorem eik_vecU8_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (v : BitVec 64) (bs : List (BitVec 8)) :
    CryptoVerification.RustHeap.vecU8 (A.atState lim st s) v bs = CryptoVerification.RustHeap.vecU8 A.repAlloc v bs := by
  simp only [CryptoVerification.RustHeap.vecU8, CryptoVerification.RustHeap.vecU8At,
    LibsignalBinary.Heap.RustCliAllocBudget.atState, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]

private theorem eik_invalidMessageStrAt_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (a : BitVec 64) (r : InvalidMessageReason) :
    invalidMessageStrAt (A.atState lim st s) a r = invalidMessageStrAt A.repAlloc a r := by
  cases r <;> simp only [invalidMessageStrAt, eik_vecU8_atState_eq]

private theorem eik_speAt_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (fn : List (BitVec 8))
    (a : BitVec 64) (e : SignalProtocolError) :
    speAt (A.atState lim st s) fn a e = speAt A.repAlloc fn a e := by
  cases e <;> simp only [speAt, eik_vecU8_atState_eq, eik_invalidMessageStrAt_atState_eq]

private theorem eik_pksmErrE_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (fn : List (BitVec 8))
    (sret : BitVec 64) (e : SignalProtocolError) :
    pksmErrE (A.atState lim st s) fn sret e = pksmErrE A.repAlloc fn sret e := by
  simp only [pksmErrE, eik_speAt_atState_eq]

private theorem eik_boxSlot_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (ptr len : BitVec 64) (act : Bool) :
    boxSlot (A.atState lim st s) ptr len act = boxSlot A.repAlloc ptr len act := by
  cases act <;> rfl

private theorem eik_deallocSlot_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (cap ptr : BitVec 64) (act : Bool) :
    deallocSlot (A.atState lim st s) cap ptr act = deallocSlot A.repAlloc cap ptr act := by
  cases act <;> rfl

private theorem eik_ikw_let_state {prog : Program} {ret : BitVec 64} {s : Arm64.State}
    {P : SepProp} {Q Qp : Arm64.State → SepProp → Prop}
    (k : let sc := s; CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp prog ret sc P Q Qp) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp prog ret s P Q Qp := k

private theorem eik_ikw_words3_to_memRegion24 (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  rw [CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.memRegion24_words3 a]
  exact sepConj_mono (Entails.sepExists_intro w0)
    (sepConj_mono (Entails.sepExists_intro w1) (Entails.sepExists_intro w2))

private theorem eik_ikw_errWords5_memRegion8_entails_speAt (A : RustAlloc) (fn : List (BitVec 8))
    {ik : List (BitVec 8)} {e : SignalProtocolError} (hik : CryptoGames.LibsignalSession.PublicKey.deserialize ik = .error e)
    (sp' w2 w3 w4 : BitVec 64) :
    ((sp' + 312#64) ↦₆₄ (ikErrWords e).1) ∗ ((sp' + 320#64) ↦₆₄ (ikErrWords e).2) ∗
      ((sp' + 328#64) ↦₆₄ w2) ∗ ((sp' + 336#64) ↦₆₄ w3) ∗ ((sp' + 344#64) ↦₆₄ w4) ∗
      memRegion (sp' + 352#64) 8 ⊢
      speAt A fn (sp' + 312#64) e := by
  have hm24 := eik_ikw_words3_to_memRegion24 (sp' + 328#64) w2 w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm24
  have hm32 :
      ((sp' + 328#64) ↦₆₄ w2) ∗ ((sp' + 336#64) ↦₆₄ w3) ∗ ((sp' + 344#64) ↦₆₄ w4) ∗
        memRegion (sp' + 352#64) 8 ⊢
      memRegion (sp' + 328#64) 32 := by
    rw [show (32 : Nat) = 24 + 8 by decide,
      ProofLib.memRegion_split (sp' + 328#64) 24 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, ← sepConj_assoc]
    exact sepConj_mono_left (by simpa only [sepConj_assoc] using hm24)
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right hm32)) ?_
  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
    ikErrWords_entails_speAt hik A fn (sp' + 312#64)

/-- (``+0x830 → +0x978`, `2096 → 2424`, `[LibsignalPlacement]``):
threads `A.pool lim st s` to `A.pool lim st sf` with zero heap events. -/
theorem preKey_ident_err_830_to_978_noPanic_placed_wpE [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (fn : List (BitVec 8))
    {H : LibsignalHooks} (hC : CalleesPlacedBudget.PksmCalleesPlaced M A lim H)
    {s0 s : State}
    {sp' sret kyberBoxPtr kyberBoxLen ikCap msgCap ikPtr ikLen : BitVec 64}
    {regTag regVal : BitVec 32}
    {ik : List (BitVec 8)} {e : SignalProtocolError} {S : Nat}
    (hS : 96 ≤ S) (hS64 : S ≤ 2 ^ 64)
    (hik : CryptoGames.LibsignalSession.PublicKey.deserialize ik = .error e) (hik_len : ikLen.toNat = ik.length)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2096#64)
    (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberBoxPtr)
    (hx26 : s.readReg64 .x26 = msgCap) (hx25 : s.readReg64 .x25 = kyberBoxLen)
    (hx24 : s.readReg64 .x24 = sp' + 312#64)
    (hx23 : s.readReg64 .x23 = ikCap) (hx19 : s.readReg64 .x19 = sret) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H)
      ((blkPl_111).base + 2424#64) s
      ((((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
          ((sp' + 56#64) ↦₆₄ ikLen) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ (ikPtr ↦ₛ ik) ∗
          memRegion (sp' + 144#64) 32 ∗ memRegion (sp' + 312#64) 48 ∗
          lsLogOff ∗ stackAt sp' S) ∗ A.pool lim st s)
      (fun sf Pf =>
        IdentErrStatePlaced s0 sp' sret kyberBoxPtr kyberBoxLen ikCap msgCap sf ∧
        sf.readReg64 .x8 = (ikErrWords e).1 ∧
        (Pf ⊢ (((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
            ((sp' + 56#64) ↦₆₄ ikLen) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ (ikPtr ↦ₛ ik) ∗
            ((sp' + 144#64) ↦₆₄ (ikErrWords e).2) ∗ memRegion (sp' + 152#64) 24 ∗
            speAt A.repAlloc fn (sp' + 312#64) e ∗
            lsLogOff ∗ stackAt sp' S) ∗ A.pool lim st sf))
      preKeyNoPanicQp := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcallIk := hC.identityKeyWordsErr
  clear hC
  have hstackIk := stackAt_sub_split sp' 96 S (by omega) hS64
  have h48_split : memRegion (sp' + 312#64) 48 =
      memRegion (sp' + 312#64) 40 ∗ memRegion (sp' + 352#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      ProofLib.memRegion_split (sp' + 312#64) 40 8 (by decide)
  rw [h48_split]
  simp only [sepConj_assoc]
  refine eik_ikw_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 116) ?_
  wp_steps_sync_111 (lsmpl.base 116)
  refine eik_ikw_done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hcl1 => ?_
  refine eik_ikw_let_state ?_; intro sc1
  refine eik_ikw_call_noPanic_pk keepsFrozenInv_codeRoLoaded (ikPtr, ik, e, sp' + 312#64) hcallIk
    (by simp_all [sc1, arm64_norm]) (by simp_all [sc1, arm64_norm])
    (by dsimp only [sc1]; simpa [State.spAligned, arm64_norm] using hsp) hcl1
    (ret_pc := (blkPl_111).base + 2124#64) (by simp_all [sc1, arm64_norm])
    (T := (ikPtr ↦ₛ ik) ∗ memRegion (sp' + 312#64) 40 ∗ lsLogOff ∗ stackAt sp' 96)
    (φ := ikPtr = ikPtr ∧ ikLen.toNat = ik.length ∧
      sp' + 312#64 = sp' + 312#64 ∧ CryptoGames.LibsignalSession.PublicKey.deserialize ik = .error e)
    (by simp_all [sc1, CalleesPlacedBudget.identityKeyTryFromSliceWordsErrPlacedSpec,
      withVmPreserved, identityKeyTryFromSliceWordsErrPlacedSpec, arm64_norm])
    ⟨rfl, hik_len, rfl, hik⟩ (by rw [hstackIk]; sep_focus)
    ?_
  clear hcallIk
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [CalleesPlacedBudget.identityKeyTryFromSliceWordsErrPlacedSpec,
    withVmPreserved, identityKeyTryFromSliceWordsErrPlacedSpec]
  simp only [sepConj_assoc]
  refine eik_ikw_pure_pre fun hvm2 => eik_ikw_pure_pre fun htr2 => ?_
  have hpool2 : A.pool lim st sc1 = A.pool lim st s2 :=
    (A.pool_transport lim st sc1 s2 hvm2).symm
  rw [hpool2]; clear hvm2 hpool2
  have hsc1_sp : sc1.sp = sp' := by simp [sc1, hsp_eq, arm64_norm]
  rw [hsc1_sp] at hsp2 ⊢
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2,
    hx29_2, _⟩
  dsimp only [sc1] at htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
  have hsp2_eq : s2.sp = sp' := hsp2
  have h29_2 : s2.readReg64 .x29 = sp' + 512#64 := by simp [hx29_2, hx29, arm64_norm]
  have h24_2 : s2.readReg64 .x24 = sp' + 312#64 := by simp [hx24_2, hx24, arm64_norm]
  clear hsc1_sp
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.memRegion24_words3 (sp' + 328#64), CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.memRegion32_words4 (sp' + 144#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    BitVec.add_assoc, BitVec.reduceAdd]
  refine eik_ikw_exists_pre fun _ => eik_ikw_exists_pre fun _ =>
    eik_ikw_exists_pre fun _ => eik_ikw_exists_pre fun _ =>
    eik_ikw_exists_pre fun w4 => eik_ikw_exists_pre fun w3 => eik_ikw_exists_pre fun w2 => ?_
  have hne : ((ikErrWords e).1 + 2#64 != 0#64) = true := by
    rcases CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.deserialize_error_cases hik with rfl | ⟨t, rfl⟩ | ⟨n, rfl⟩ <;>
      (dsimp only [ikErrWords, speWord]; decide)
  refine eik_ikw_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2 ?_
  wp_steps_sync_111 ((blkPl_111).base + 2424#64)
  refine eik_ikw_done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hcl3 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp2_eq], by tryFromPost_sp_align hsp2_align, hcl3,
      by simp [htr2, htr, arm64_norm]⟩,
    by simp [h29_2, arm64_norm], by simp [hx28_2, arm64_norm, hx28],
    by simp [hx25_2, hx25, arm64_norm], by simp [hx26_2, hx26, arm64_norm],
    by simp [hx23_2, hx23, arm64_norm], by simp [hx19_2, hx19, arm64_norm]⟩,
    by simp [arm64_norm], ?_⟩
  have hm24 := eik_ikw_words3_to_memRegion24 (sp' + 152#64) w2 w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm24
  have hspe := eik_ikw_errWords5_memRegion8_entails_speAt A.repAlloc fn hik sp' w2 w3 w4
  refine Entails.trans
    (Q := ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
      ((sp' + 56#64) ↦₆₄ ikLen) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ (ikPtr ↦ₛ ik) ∗
      ((sp' + 144#64) ↦₆₄ (ikErrWords e).2) ∗
      (((sp' + 152#64) ↦₆₄ w2) ∗ ((sp' + 160#64) ↦₆₄ w3) ∗ ((sp' + 168#64) ↦₆₄ w4)) ∗
      (((sp' + 312#64) ↦₆₄ (ikErrWords e).1) ∗ ((sp' + 320#64) ↦₆₄ (ikErrWords e).2) ∗
        ((sp' + 328#64) ↦₆₄ w2) ∗ ((sp' + 336#64) ↦₆₄ w3) ∗ ((sp' + 344#64) ↦₆₄ w4) ∗
        memRegion (sp' + 352#64) 8) ∗
      lsLogOff ∗ (memRegion (sp' - BitVec.ofNat 64 S) (S - 96) ∗ stackAt sp' 96) ∗
      A.pool lim st _)
    (by simp only [sepConj_assoc]; apply entails_of_eq; sep_ac_rfl) ?_
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono hm24 (sepConj_mono_left hspe)))))))) ?_
  rw [hstackIk]
  simp only [sepConj_assoc]
  apply entails_of_eq; sep_ac_rfl

/-- Budget-pool `PreKeyIdentErrNoPanicWPlaced` from `preKey_ident_err_830_to_978_noPanic_placed_wpE`,
`e_978_placed_wpE`, and `w8b_errTail_close_noPanic_placed`. -/
theorem preKeyIdentErrNoPanicW_placed_proof [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : CalleesPlacedBudget.PksmCalleesPlaced M A lim H) :
    PreKeyIdentErrNoPanicWPlaced M A lim H := by
  intro x st s0 sf vb b1 bs1 m bk ik msg spkId _pk e bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberLen
    regTag regVal opkTag opkVal _kpkTag kpkVal kyberBoxPtr kyberBoxLen p0 p1 p2 p3 p4 p5 p6 p7 p8
    p31 w9 w13 w15 w23 _hfit hcons _hv3 _hv4 _hlen hdec _hbkO hikO _hmsgO _hspkO _hreg _hopk _hkpk
    _hd _hokY _hpkb hik hkst hbkC hikC hmsgC hpc hrun
  have hparse : CryptoVerification.SignalSession.Cli.RunProofs.Pksm.pksmParse x.bytes = none := hcons ▸ pksmParse_ikErr hdec hikO hik
  have hbkNe : bkCap ≠ noneCap := by rintro rfl; revert hbkC; decide
  have hikNe : ikCap ≠ noneCap := by rintro rfl; revert hikC; decide
  have hmsgNe : msgCap ≠ noneCap := by rintro rfl; revert hmsgC; decide
  rw [show w8bRowYFramePlaced A.repAlloc s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr ikCap
          ikPtr msgCap msgPtr bk ik msg x.bytes =
        w8bRowYFramePlaced (A.atState lim st sf) s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr ikCap
          ikPtr msgCap msgPtr bk ik msg x.bytes from rfl,
    w8bRowY_open_ident_placed (A.atState lim st sf)]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun ⟨hikLe, hikLt, _⟩ => ?_
  rw [w8bRowIFrame_pull_pool_noPanic A lim st sf s0]
  have hik_len : (BitVec.ofNat 64 ik.length).toNat = ik.length := by
    have h63 : (2 : Nat) ^ 63 < 2 ^ 64 := by decide
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rcases hkst with ⟨hpost, _hbk_ok, _hpk_eq, _hpk_bytes, hx29, hx28, _hx27, hx26, hx25, hx24,
    hx23, _hx22, _hx21, _hx20, hx19⟩
  refine w8b_bind_frame_noPanic
    (preKey_ident_err_830_to_978_noPanic_placed_wpE A lim st [] hC
      w8b_skipFieldStackX100_bounds.1 w8b_skipFieldStackX100_bounds.2 hik hik_len hpost
      hpc hrun hx29 hx28 hx26 hx25 hx24 hx23 hx19) ?_
  rintro sm Pm hpcm hrunm ⟨hist, hx8, hPm⟩
  have hopen := w8bIdErr_open_placed (A := A.atState lim st sm) (s0 := s0)
    (sp' := s0.sp - 608#64) (sret := x.ret) (ptr := x.ptr) (bkCap := bkCap) (bkPtr := bkPtr)
    (kyberLen := kyberLen) (ikCap := ikCap) (ikPtr := ikPtr) (msgCap := msgCap) (msgPtr := msgPtr)
    (kbPtr := kyberBoxPtr) (kbLen := kyberBoxLen) (ikLen := BitVec.ofNat 64 ik.length)
    (regTag := regTag) (regVal := regVal) (opkTag := opkTag) (opkVal := opkVal)
    (spkId := spkId) (kpkVal := kpkVal) (p0 := p0) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4)
    (p5 := p5) (p6 := p6) (p7 := p7) (p8 := p8) (p31 := p31) (w9 := w9) (w13 := w13)
    (w15 := w15) (w23 := w23) (vb := vb) (kpkOpt := m.kyberPreKeyId)
    (kyberOpt := m.kyberCiphertext) (bk := bk) (ik := ik) (msg := msg) (bytes := x.bytes) (e := e)
  rw [eik_speAt_atState_eq] at hopen
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (Entails.trans (sepConj_mono_left hPm)
      (Entails.trans
        (Entails.of_eq (w8bRowIFrame_pull_pool_noPanic A lim st sm s0 (s0.sp - 608#64) x.ret x.ptr bkCap
          bkPtr kyberLen ikCap ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen opkTag opkVal spkId
          kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 vb m.kyberPreKeyId m.kyberCiphertext
          bk ik msg x.bytes _).symm)
        hopen)) ?_
  refine w8bIdErr_exists4_pre fun boxAct msgAct ikAct bkAct => ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.bind
    (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
      (by
        simp only [eik_boxSlot_atState_eq, eik_deallocSlot_atState_eq]
        dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]
        apply entails_of_eq; sep_ac_rfl)
      (e_978_placed_wpE (M := M) (A := A) (lim := lim) (st := st)
        (msgPtr := msgPtr) (ikPtr := ikPtr) (bkPtr := bkPtr)
        (R := w8bIdErrRestPlaced s0 (s0.sp - 608#64) x.ptr kyberLen (BitVec.ofNat 64 ik.length)
          (BitVec.ofNat 64 msg.length) w15 w23 regTag regVal opkTag opkVal spkId kpkVal
          p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 x.bytes)
        hC [] boxAct msgAct ikAct bkAct hik hist hpcm hrunm hx8 hmsgNe hikNe hbkNe)) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hst2, _hx19', evs₁, hfree₁, hP2⟩
  have hpk := w8bIdErr_placed_pack (A := A.atState lim (M.stepEvents evs₁ st) s2) (s0 := s0)
    (sp' := s0.sp - 608#64) (sret := x.ret) (ptr := x.ptr) (kyberLen := kyberLen)
    (ikLen := BitVec.ofNat 64 ik.length) (msgLen := BitVec.ofNat 64 msg.length)
    (w15 := w15) (w23 := w23) (msgPtr := msgPtr) (ikPtr := ikPtr) (bkPtr := bkPtr) (bkCap := bkCap)
    (regTag := regTag) (regVal := regVal) (opkTag := opkTag) (opkVal := opkVal)
    (spkId := spkId) (kpkVal := kpkVal) (p0 := p0) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4)
    (p5 := p5) (p6 := p6) (p7 := p7) (p8 := p8) (p31 := p31) (w9 := w9) (w13 := w13)
    (e := e) (bytes := x.bytes)
  rw [eik_pksmErrE_atState_eq] at hpk
  exact CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (Entails.trans hP2
      (Entails.trans (by dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]; apply entails_of_eq; sep_ac_rfl)
        hpk))
    (w8b_errTail_close_noPanic_placed hparse (pksmFrom830Env_of_err_freeOnly hik hfree₁) hst2 hpc2 hrun2)

end ErrIdent

section SigMsg

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bNoPanicAuxC (PreKey864OkNoPanicWPlaced)
open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoGames.LibsignalSession (InvalidMessageReason PublicKey SignalMessage SignalProtocolError)
open CryptoGames.LibsignalSessionApi (ProtoPreKeySignalMessage)
open CryptoVerification (LibsignalHooks LibsignalPlacement blkPl_111)
open CryptoVerification.E2E.Pqxdh.ResponderWire (preKeyPlacedProg)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalTripleRatchet (lsLogOff smallRootStack)
open CryptoVerification.LibsignalTripleRatchet.Wire (entails_of_eq pkBytesOf)
open CryptoVerification.LibsignalTripleRatchetRepr (SignalMessageGhost errResultAt invalidMessageStrAt signalMessageResultAt speAt)
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire (IdentOkStatePlaced SigMsgOkStatePlaced identRegId pksmErrE w8bOptU32Cells w8bRowIFrame w8bRowIPostPlaced w8bRowI_open_sigCall_placed w8bRowSFramePlaced w8bRowSPost w8bRowSRestPlaced w8bSigCallFrame w8bSigCall_post_open_ok_placed w8b_decodePreKey_message_length_le)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget fitsEvents_append)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.SigMsgWPlacedBudget (preKey_sigMsg_call_864_to_878_from_ident_placed_wpX preKey_sigMsg_ok_878_to_8c0_placed_wpX)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget (PksmFrom864Env SigMsgCallEnv fitsEnv_pksmFrom864_call fitsEnv_pksmFrom864_ok_clone pksmFrom864Env_of_ok w8bRetPost w8bRetPost_prepend)

open Arm64 ProofLib.ProgramReflection
open ProofLib hiding SepWPp
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxesBudget (TryCloneBytesEnv)

theorem w8b_sigMsgCallEnv_eq_noPanic (msg : List (BitVec 8)) :
    SigMsgCallEnv msg = SigMsgWPlacedBudget.SigMsgCallEnv msg :=
  SigMsgWPlacedBudget.tryFromEnvGen_eq_sigMsgCallEnv 0#64 0#64 msg

private theorem sm_vecU8_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (v : BitVec 64) (bs : List (BitVec 8)) :
    CryptoVerification.RustHeap.vecU8 (A.atState lim st s) v bs = CryptoVerification.RustHeap.vecU8 A.repAlloc v bs := by
  simp only [CryptoVerification.RustHeap.vecU8, CryptoVerification.RustHeap.vecU8At,
    LibsignalBinary.Heap.RustCliAllocBudget.atState, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]

private theorem sm_invalidMessageStrAt_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (a : BitVec 64) (r : InvalidMessageReason) :
    invalidMessageStrAt (A.atState lim st s) a r = invalidMessageStrAt A.repAlloc a r := by
  cases r <;> simp only [invalidMessageStrAt, sm_vecU8_atState_eq]

private theorem sm_speAt_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (fn : List (BitVec 8))
    (a : BitVec 64) (e : SignalProtocolError) :
    speAt (A.atState lim st s) fn a e = speAt A.repAlloc fn a e := by
  cases e <;> simp only [speAt, sm_vecU8_atState_eq, sm_invalidMessageStrAt_atState_eq]

theorem w8b_pksmErrE_atState_eq_noPanic {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (fn : List (BitVec 8))
    (sret : BitVec 64) (e : SignalProtocolError) :
    pksmErrE (A.atState lim st s) fn sret e = pksmErrE A.repAlloc fn sret e := by
  simp only [pksmErrE, sm_speAt_atState_eq]

theorem w8b_signalMessageResultAt_atState_eq_noPanic {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (fn : List (BitVec 8)) (a : BitVec 64)
    (r : Except SignalProtocolError SignalMessage) :
    signalMessageResultAt (A.atState lim st s) fn a r =
      signalMessageResultAt A.repAlloc fn a r := by
  cases r with
  | error e => simp only [signalMessageResultAt, errResultAt, sm_speAt_atState_eq]
  | ok _ => rfl

/-- `+0x8c0` (`2240`) → `ret` after `SignalMessage::try_from` and byte-slice cloning succeed (`FreeOnlyEvs`). -/
def PreKey8c0OkNoPanicWPlaced [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  ∀ (x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost) (st : M.σ) (s0 sf : State) (vb b1 : BitVec 8)
    (bs1 : List (BitVec 8)) (m : ProtoPreKeySignalMessage) (bk ik msg : List (BitVec 8))
    (spkId : BitVec 32) (pk ipk : PublicKey)
    (bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberLen : BitVec 64)
    (regTag regVal opkTag opkVal kpkTag kpkVal : BitVec 32)
    (kyberBoxPtr kyberBoxLen : BitVec 64)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64)
    (innerMsg : SignalMessage) (msgG : SignalMessageGhost)
    (rk0 rk1 rk2 rk3 addrW0 addrW1 : BitVec 64) (verHi56 : BitVec 56) (clonePtr : BitVec 64),
    x.bytes = vb :: b1 :: bs1 → ¬ (vb >>> 4) < 3#8 → ¬ 4#8 < (vb >>> 4) →
    x.bytes.length < 2 ^ 32 →
    CryptoVerification.SignalSession.Cli.RunProofs.Pksm.decodeProto (b1 :: bs1) = some m →
    m.baseKey = some bk → m.identityKey = some ik → m.message = some msg →
    m.signedPreKeyId = some spkId →
    w8bOptU32Cells m.registrationId (regTag, regVal) →
    w8bOptU32Cells m.preKeyId (opkTag, opkVal) →
    w8bOptU32Cells m.kyberPreKeyId (kpkTag, kpkVal) →
    CryptoGames.LibsignalSession.PublicKey.deserialize bk = .ok pk →
    ((m.kyberPreKeyId.isSome && m.kyberCiphertext.isSome) = true ∨
      (m.kyberPreKeyId = none ∧ m.kyberCiphertext = none ∧ vb.toNat < 0x40)) →
    (bk.take 33).drop 1 = pkBytesOf p0 p1 p2 p3 p4 p5 p6 p7 p8 w9 w13 w15 w23 p31 →
    CryptoGames.LibsignalSession.PublicKey.deserialize ik = .ok ipk →
    CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec msg = .ok innerMsg →
    (∀ a : BitVec 64, (a ↦ₛ innerMsg.senderRatchetKey.bytes.toList) =
      (a ↦₆₄ rk0) ∗ ((a + 8#64) ↦₆₄ rk1) ∗ ((a + 16#64) ↦₆₄ rk2) ∗ ((a + 24#64) ↦₆₄ rk3)) →
    SigMsgOkStatePlaced s0 (s0.sp - 608#64) x.ret (BitVec.ofNat 64 x.bytes.length) x.ptr
      kyberBoxPtr kyberBoxLen ikCap msgCap vb msgG.pqCap clonePtr bk pk ik ipk sf →
    bkCap.toNat < 2 ^ 63 → ikCap.toNat < 2 ^ 63 → msgCap.toNat < 2 ^ 63 →
    FitsEnv M lim st FreeOnlyEvs →
    sf.pc = (blkPl_111).base + 2240#64 →
    sf.status = .Running →
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) sf
      (w8bRowSPost A.repAlloc (s0.sp - 608#64) clonePtr x.bytes innerMsg msgG rk0 rk1 rk2 rk3
          addrW0 addrW1 verHi56 ∗
        w8bRowSFramePlaced (A.atState lim st sf) s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr
          kyberLen ikCap ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen regTag regVal opkTag opkVal
          spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 vb m.kyberPreKeyId
          m.kyberCiphertext bk ik msg x.bytes ipk)
      (w8bRetPost A lim FreeOnlyEvs x st s0)
      preKeyNoPanicQp

/-- `PreKey864OkNoPanicWPlaced` restricted to `SignalMessage::try_from` failure
(`SignalMessage.tryFrom protoSignalCodec msg = .error e`; `+0x864 → +0x878 → +0x9f0` → ret). -/
def PreKeySigMsgErrNoPanicWPlaced [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  ∀ (x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost) (st : M.σ) (s0 sf : State) (vb b1 : BitVec 8)
    (bs1 : List (BitVec 8)) (m : ProtoPreKeySignalMessage) (bk ik msg : List (BitVec 8))
    (spkId : BitVec 32) (pk ipk : PublicKey) (e : SignalProtocolError)
    (bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberLen : BitVec 64)
    (regTag regVal opkTag opkVal kpkTag kpkVal : BitVec 32)
    (kyberBoxPtr kyberBoxLen : BitVec 64)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64),
    x.bytes = vb :: b1 :: bs1 → ¬ (vb >>> 4) < 3#8 → ¬ 4#8 < (vb >>> 4) →
    x.bytes.length < 2 ^ 32 →
    CryptoVerification.SignalSession.Cli.RunProofs.Pksm.decodeProto (b1 :: bs1) = some m →
    m.baseKey = some bk → m.identityKey = some ik → m.message = some msg →
    m.signedPreKeyId = some spkId →
    w8bOptU32Cells m.registrationId (regTag, regVal) →
    w8bOptU32Cells m.preKeyId (opkTag, opkVal) →
    w8bOptU32Cells m.kyberPreKeyId (kpkTag, kpkVal) →
    CryptoGames.LibsignalSession.PublicKey.deserialize bk = .ok pk →
    ((m.kyberPreKeyId.isSome && m.kyberCiphertext.isSome) = true ∨
      (m.kyberPreKeyId = none ∧ m.kyberCiphertext = none ∧ vb.toNat < 0x40)) →
    (bk.take 33).drop 1 = pkBytesOf p0 p1 p2 p3 p4 p5 p6 p7 p8 w9 w13 w15 w23 p31 →
    CryptoGames.LibsignalSession.PublicKey.deserialize ik = .ok ipk →
    CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec msg = .error e →
    IdentOkStatePlaced s0 (s0.sp - 608#64) x.ret (BitVec.ofNat 64 x.bytes.length) x.ptr
      kyberBoxPtr kyberBoxLen ikCap msgCap vb (identRegId regTag regVal) bk pk ik ipk sf →
    bkCap.toNat < 2 ^ 63 → ikCap.toNat < 2 ^ 63 → msgCap.toNat < 2 ^ 63 →
    FitsEnv M lim st (PksmFrom864Env x.bytes msg) →
    sf.pc = (blkPl_111).base + 2148#64 →
    sf.status = .Running →
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) sf
      (w8bRowIPostPlaced (s0.sp - 608#64) ikPtr regTag regVal ik ipk ∗
        w8bRowIFrame (A.atState lim st sf) s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr kyberLen
          ikCap ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen opkTag opkVal spkId kpkVal p0 p1 p2 p3
          p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 vb m.kyberPreKeyId m.kyberCiphertext bk ik msg x.bytes)
      (w8bRetPost A lim (PksmFrom864Env x.bytes msg) x st s0)
      preKeyNoPanicQp

private theorem sm_fitsEnv_pksmFrom864_ok_free {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {xBytes msg : List (BitVec 8)} {inner : SignalMessage} {evsS evsC : List AllocEvent}
    (hok : CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec msg = .ok inner)
    (hS : SigMsgCallEnv msg evsS) (hC : TryCloneBytesEnv xBytes evsC)
    (hfit : FitsEnv M lim st (PksmFrom864Env xBytes msg)) :
    FitsEnv M lim (M.stepEvents evsC (M.stepEvents evsS st)) FreeOnlyEvs := by
  intro evsF hF
  have hcomb := pksmFrom864Env_of_ok hok hS hC hF
  have h12 := ((fitsEvents_append M lim evsS (evsC ++ evsF) st).mp (hfit _ hcomb)).2
  exact ((fitsEvents_append M lim evsC evsF (M.stepEvents evsS st)).mp h12).2

theorem preKey864OkNoPanicW_placed_of_8c0 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : CalleesPlacedBudget.PksmCalleesPlaced M A lim H)
    (hErr : PreKeySigMsgErrNoPanicWPlaced M A lim H)
    (hOk : PreKey8c0OkNoPanicWPlaced M A lim H) :
    PreKey864OkNoPanicWPlaced M A lim H := by
  intro x st s0 sf vb b1 bs1 m bk ik msg spkId pk ipk bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberLen
    regTag regVal opkTag opkVal kpkTag kpkVal kyberBoxPtr kyberBoxLen p0 p1 p2 p3 p4 p5 p6 p7 p8
    p31 w9 w13 w15 w23 hcons hv3 hv4 hlen hdec hbkO hikO hmsgO hspkO hreg hopk hkpk hd hokY hpkb
    hik hkst hbkC hikC hmsgC hfit hpc hrun
  cases hsig : CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec msg with
  | error e =>
    exact hErr x st s0 sf vb b1 bs1 m bk ik msg spkId pk ipk e bkCap bkPtr ikCap ikPtr msgCap msgPtr
      kyberLen regTag regVal opkTag opkVal kpkTag kpkVal kyberBoxPtr kyberBoxLen p0 p1 p2 p3 p4 p5
      p6 p7 p8 p31 w9 w13 w15 w23 hcons hv3 hv4 hlen hdec hbkO hikO hmsgO hspkO hreg hopk hkpk hd
      hokY hpkb hik hsig hkst hbkC hikC hmsgC hfit hpc hrun
  | ok innerMsg =>
    have hmsg_lt : msg.length < 2 ^ 32 := by
      have hle := w8b_decodePreKey_message_length_le hdec hmsgO
      have hlen' := hlen
      rw [hcons] at hlen'
      exact Nat.lt_of_le_of_lt hle (Nat.lt_of_succ_lt hlen')
    have hfitCall : FitsEnv M lim st (SigMsgWPlacedBudget.SigMsgCallEnv msg) :=
      w8b_sigMsgCallEnv_eq_noPanic msg ▸ fitsEnv_pksmFrom864_call hfit
    rw [w8bRowI_open_sigCall_placed (A.atState lim st sf)]
    change CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) sf
      ((((s0.sp - 608#64 + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
          ((s0.sp - 608#64 + 56#64) ↦₆₄ BitVec.ofNat 64 ik.length) ∗
          ((s0.sp - 608#64 + 96#64) ↦₆₄ msgPtr) ∗
          ((s0.sp - 608#64 + 312#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((s0.sp - 608#64 + 320#64) ↦ₛ ipk.bytes.toList) ∗
          memRegion (s0.sp - 608#64 + 352#64) 8 ∗ memRegion (s0.sp - 608#64 + 360#64) 72 ∗
          CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc msgCap msgPtr msg ∗
          lsLogOff ∗ A.pool lim st sf ∗ stackAt (s0.sp - 608#64) smallRootStack) ∗
        w8bSigCallFrame A.repAlloc s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr kyberLen ikCap ikPtr
          kyberBoxPtr kyberBoxLen regTag regVal opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7
          p8 p31 w9 w13 w15 w23 vb m.kyberPreKeyId m.kyberCiphertext bk ik x.bytes ipk) _ _
    refine w8b_bind_frame_noPanic
      (preKey_sigMsg_call_864_to_878_from_ident_placed_wpX (M := M) (A := A) (lim := lim) (st := st)
        (msgPtr := msgPtr) (w56 := BitVec.ofNat 64 ik.length) (tag := 0xfffffffffffffffe#64)
        hC hfitCall hmsg_lt hkst hpc hrun) ?_
    rintro sm1 Pm1 hpc1 hrun1 ⟨evs₁, hevs₁, hist1, hPm1⟩
    rw [← w8b_sigMsgCallEnv_eq_noPanic msg] at hevs₁
    have hopen1 := w8bSigCall_post_open_ok_placed
      (A.atState lim (M.stepEvents evs₁ st) sm1) s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr
      kyberLen ikCap ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen regTag regVal opkTag opkVal spkId
      kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 vb m.kyberPreKeyId m.kyberCiphertext
      bk ik msg x.bytes ipk (CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec msg)
    rw [w8b_signalMessageResultAt_atState_eq_noPanic] at hopen1
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
      (Entails.trans (sepConj_mono_left hPm1) (Entails.of_eq hopen1)) ?_
    change CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) sm1
      ((signalMessageResultAt A.repAlloc [] (s0.sp - 608#64 + 312#64)
            (CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec msg) ∗
          memRegion (s0.sp - 608#64 + 176#64) 112 ∗
          (x.ptr ↦ₛ x.bytes) ∗ A.pool lim (M.stepEvents evs₁ st) sm1 ∗
          stackAt (s0.sp - 608#64) (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)) ∗
        w8bRowSRestPlaced A.repAlloc s0 (s0.sp - 608#64) x.ret bkCap bkPtr kyberLen ikCap ikPtr
          msgCap msgPtr kyberBoxPtr kyberBoxLen regTag regVal opkTag opkVal spkId kpkVal p0 p1 p2
          p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 vb m.kyberPreKeyId m.kyberCiphertext bk ik msg ipk)
      _ _
    have hfitClone : FitsEnv M lim (M.stepEvents evs₁ st) (TryCloneBytesEnv x.bytes) :=
      fitsEnv_pksmFrom864_ok_clone hsig hevs₁ hfit
    refine w8b_bind_frame_noPanic
      (preKey_sigMsg_ok_878_to_8c0_placed_wpX (M := M) (A := A) (lim := lim)
        (st := M.stepEvents evs₁ st) hC hfitClone hsig hlen hist1 hpc1 hrun1) ?_
    rintro sm3 Pm3 hpc3 hrun3
      ⟨evs₂, msgG, rk0, rk1, rk2, rk3, addrW0, addrW1, verHi56, clonePtr,
        hevs₂, hrk, hok3, hPm3⟩
    have hfitFree : FitsEnv M lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) FreeOnlyEvs :=
      sm_fitsEnv_pksmFrom864_ok_free hsig hevs₁ hevs₂ hfit
    refine CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.SepWPp.mono_post
      (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (Entails.trans (sepConj_mono_left hPm3) ?_)
        (hOk x (M.stepEvents evs₂ (M.stepEvents evs₁ st)) s0 sm3 vb b1 bs1 m bk ik msg spkId pk
          ipk bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberLen regTag regVal opkTag opkVal kpkTag
          kpkVal kyberBoxPtr kyberBoxLen p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 innerMsg
          msgG rk0 rk1 rk2 rk3 addrW0 addrW1 verHi56 clonePtr hcons hv3 hv4 hlen hdec
          hbkO hikO hmsgO hspkO hreg hopk hkpk hd hokY hpkb hik hsig hrk hok3 hbkC hikC hmsgC
          hfitFree hpc3 hrun3)) ?_
    · unfold w8bRowSPost w8bRowSFramePlaced
      change _ ⊢
        w8bRowSPost A.repAlloc (s0.sp - 608#64) clonePtr x.bytes innerMsg msgG rk0 rk1 rk2 rk3
            addrW0 addrW1 verHi56 ∗
          (w8bRowSRestPlaced A.repAlloc s0 (s0.sp - 608#64) x.ret bkCap bkPtr kyberLen ikCap ikPtr
              msgCap msgPtr kyberBoxPtr kyberBoxLen regTag regVal opkTag opkVal spkId kpkVal p0 p1
              p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 vb m.kyberPreKeyId m.kyberCiphertext bk ik
              msg ipk ∗
            memRegion (s0.sp - 608#64 + 312#64) 120 ∗ (x.ptr ↦ₛ x.bytes) ∗
            A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) sm3 ∗
            stackAt (s0.sp - 608#64) (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100))
      unfold w8bRowSPost
      apply entails_of_eq; sep_ac_rfl
    · rintro sf' Pf' _ _ hret
      exact w8bRetPost_prepend (evs₁ := evs₁ ++ evs₂)
        (fun evs₃ hfree₃ => by
          rw [List.append_assoc]
          exact pksmFrom864Env_of_ok hsig hevs₁ hevs₂ hfree₃)
        (by rw [M.stepEvents_append]; exact hret)

end SigMsg

section ErrSigMsg

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.E2E.Pqxdh.ResponderWire (preKeyCalleeSavedAt preKeyPlacedProg preKeyTryFromSubStack)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalTripleRatchet (lsLogOff smallRootStack)
open CryptoVerification.LibsignalTripleRatchet.Wire (deallocSlot entails_of_eq)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap signalMessageResultAt)
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire (boxSlot identRegId pksmErrE pksmParse_msgErr w8bErrW_exists_pre_frame w8bRowI_open_sigCall_placed w8bSigCallFrame w8bSigCall_post_open_err_placed w8bSigErr878FramePlaced w8bSigErr9f0RestPlaced w8bSigErr_open_9f0_placed w8bSigErr_placed_pack w8b_decodePreKey_message_length_le)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCWPlacedBudget (e_9f0_words2_placed_wpE)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.SigMsgWPlacedBudget (preKey_sigMsg_call_864_to_878_from_ident_placed_wpX preKey_sigMsg_err_878_to_9f0_placed_wpX)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget (fitsEnv_pksmFrom864_call pksmFrom864Env_of_err)

open Arm64 ProofLib.ProgramReflection
open ProofLib hiding SepWPp

private theorem esm_w8bSigErr878FramePlaced_pull_pool [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (sm s0 : State)
    (sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen : BitVec 64)
    (regTag regVal opkTag opkVal spkId kpkVal : BitVec 32)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64) (vb : BitVec 8)
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8)))
    (bk ik msg bytes : List (BitVec 8)) (ipk : PublicKey) (L : SepProp) :
    L ∗ w8bSigErr878FramePlaced (A.atState lim st sm) s0 sp' sret ptr bkCap bkPtr kyberLen ikCap
      ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen regTag regVal opkTag opkVal spkId kpkVal p0 p1
      p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 vb kpkOpt kyberOpt bk ik msg bytes ipk =
    (L ∗ A.pool lim st sm) ∗
      w8bSigErr878FramePlaced A.repAlloc s0 sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap
        msgPtr kyberBoxPtr kyberBoxLen regTag regVal opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5
        p6 p7 p8 p31 w9 w13 w15 w23 vb kpkOpt kyberOpt bk ik msg bytes ipk := by
  unfold w8bSigErr878FramePlaced
  change L ∗ _ = (L ∗ A.pool lim st sm) ∗ _
  have hemp : (A.repAlloc).pool = SepProp.emp := rfl
  have hpool : (A.atState lim st sm).pool = A.pool lim st sm := rfl
  have hbuf : ∀ c p b, CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf (A.atState lim st sm) c p b =
      CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc c p b := fun _ _ _ => rfl
  have hrest : CryptoVerification.E2E.Pqxdh.ResponderWire.vecU8Rest (A.atState lim st sm) ikCap ikPtr ik =
      CryptoVerification.E2E.Pqxdh.ResponderWire.vecU8Rest A.repAlloc ikCap ikPtr ik := rfl
  have hky : CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.kyberStageOut (A.atState lim st sm)
        kpkVal vb kpkOpt kyberOpt kyberBoxPtr kyberBoxLen =
      CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.kyberStageOut A.repAlloc
        kpkVal vb kpkOpt kyberOpt kyberBoxPtr kyberBoxLen := by
    cases kpkOpt <;> cases kyberOpt <;> rfl
  rw [hpool, hemp, emp_sepConj, hrest, hbuf msgCap msgPtr msg, hbuf bkCap bkPtr bk, hky]
  sep_ac_rfl

private theorem esm_boxSlot_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (ptr len : BitVec 64) (act : Bool) :
    boxSlot (A.atState lim st s) ptr len act = boxSlot A.repAlloc ptr len act := by
  cases act <;> rfl

private theorem esm_deallocSlot_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (cap ptr : BitVec 64) (act : Bool) :
    deallocSlot (A.atState lim st s) cap ptr act = deallocSlot A.repAlloc cap ptr act := by
  cases act <;> rfl

/-- Budget-pool `PreKeySigMsgErrNoPanicWPlaced` (`+0x864 → +0x878 → +0x9f0 → +0x504 → ret`). -/
theorem preKeySigMsgErrNoPanicW_placed_proof [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : CalleesPlacedBudget.PksmCalleesPlaced M A lim H) :
    PreKeySigMsgErrNoPanicWPlaced M A lim H := by
  intro x st s0 sf vb b1 bs1 m bk ik msg spkId _pk ipk e bkCap bkPtr ikCap ikPtr msgCap msgPtr
    kyberLen regTag regVal opkTag opkVal _kpkTag kpkVal kyberBoxPtr kyberBoxLen p0 p1 p2 p3 p4 p5
    p6 p7 p8 p31 w9 w13 w15 w23 hcons _hv3 _hv4 hlen hdec _hbkO _hikO hmsgO _hspkO _hreg _hopk
    _hkpk _hd _hokY _hpkb _hik hsig hkst hbkC hikC hmsgC hfit hpc hrun
  have hparse : CryptoVerification.SignalSession.Cli.RunProofs.Pksm.pksmParse x.bytes = none := hcons ▸ pksmParse_msgErr hdec hmsgO hsig
  have hbkNe : bkCap ≠ noneCap := by rintro rfl; revert hbkC; decide
  have hikNe : ikCap ≠ noneCap := by rintro rfl; revert hikC; decide
  have hmsgNe : msgCap ≠ noneCap := by rintro rfl; revert hmsgC; decide
  have hmsg_lt : msg.length < 2 ^ 32 := by
    have hle := w8b_decodePreKey_message_length_le hdec hmsgO
    have hlen' := hlen
    rw [hcons] at hlen'
    exact Nat.lt_of_le_of_lt hle (Nat.lt_of_succ_lt hlen')
  have hfitCall : FitsEnv M lim st (SigMsgWPlacedBudget.SigMsgCallEnv msg) :=
    w8b_sigMsgCallEnv_eq_noPanic msg ▸ fitsEnv_pksmFrom864_call hfit
  rw [w8bRowI_open_sigCall_placed (A.atState lim st sf)]
  change CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) sf
    ((((s0.sp - 608#64 + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
        ((s0.sp - 608#64 + 56#64) ↦₆₄ BitVec.ofNat 64 ik.length) ∗
        ((s0.sp - 608#64 + 96#64) ↦₆₄ msgPtr) ∗
        ((s0.sp - 608#64 + 312#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
        ((s0.sp - 608#64 + 320#64) ↦ₛ ipk.bytes.toList) ∗
        memRegion (s0.sp - 608#64 + 352#64) 8 ∗ memRegion (s0.sp - 608#64 + 360#64) 72 ∗
        CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc msgCap msgPtr msg ∗
        lsLogOff ∗ A.pool lim st sf ∗ stackAt (s0.sp - 608#64) smallRootStack) ∗
      w8bSigCallFrame A.repAlloc s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr kyberLen ikCap ikPtr
        kyberBoxPtr kyberBoxLen regTag regVal opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7
        p8 p31 w9 w13 w15 w23 vb m.kyberPreKeyId m.kyberCiphertext bk ik x.bytes ipk) _ _
  refine w8b_bind_frame_noPanic
    (preKey_sigMsg_call_864_to_878_from_ident_placed_wpX (M := M) (A := A) (lim := lim) (st := st)
      (msgPtr := msgPtr) (w56 := BitVec.ofNat 64 ik.length) (tag := 0xfffffffffffffffe#64)
      hC hfitCall hmsg_lt hkst hpc hrun) ?_
  rintro sm1 Pm1 hpc1 hrun1 ⟨evs₁, hevs₁, hist1, hPm1⟩
  rw [← w8b_sigMsgCallEnv_eq_noPanic msg] at hevs₁
  have hopenErr := w8bSigCall_post_open_err_placed
    (A.atState lim (M.stepEvents evs₁ st) sm1) s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr kyberLen
    ikCap ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen regTag regVal opkTag opkVal spkId kpkVal p0
    p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 vb m.kyberPreKeyId m.kyberCiphertext bk ik msg
    x.bytes ipk (CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec msg)
  rw [w8b_signalMessageResultAt_atState_eq_noPanic] at hopenErr
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (Entails.trans (sepConj_mono_left hPm1)
      (Entails.of_eq (hopenErr.trans (esm_w8bSigErr878FramePlaced_pull_pool A lim
        (M.stepEvents evs₁ st) sm1 s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr kyberLen ikCap
        ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen regTag regVal opkTag opkVal spkId kpkVal p0 p1
        p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 vb m.kyberPreKeyId m.kyberCiphertext bk ik msg
        x.bytes ipk _)))) ?_
  change CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) sm1
    (((signalMessageResultAt A.repAlloc [] (s0.sp - 608#64 + 312#64)
          (CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec msg) ∗
        memRegion (s0.sp - 608#64 + 176#64) 48) ∗
        A.pool lim (M.stepEvents evs₁ st) sm1) ∗
      w8bSigErr878FramePlaced A.repAlloc s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr kyberLen ikCap
        ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen regTag regVal opkTag opkVal spkId kpkVal p0 p1
        p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 vb m.kyberPreKeyId m.kyberCiphertext bk ik msg
        x.bytes ipk) _ _
  refine w8b_bind_frame_noPanic
    (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (Entails.of_eq (sepConj_assoc _ _ _))
      (preKey_sigMsg_err_878_to_9f0_placed_wpX (M := M) (A := A) (lim := lim)
        (st := M.stepEvents evs₁ st) hsig hist1 hpc1 hrun1)) ?_
  rintro sm2 Pm2 hpc2 hrun2 ⟨hst2, hPm2⟩
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (Entails.trans (sepConj_mono_left hPm2)
      (Entails.of_eq (esm_w8bSigErr878FramePlaced_pull_pool A lim (M.stepEvents evs₁ st) sm2 s0
        (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr kyberBoxPtr
        kyberBoxLen regTag regVal opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13
        w15 w23 vb m.kyberPreKeyId m.kyberCiphertext bk ik msg x.bytes ipk _).symm)) ?_
  refine w8bErrW_exists_pre_frame fun ew0 => w8bErrW_exists_pre_frame fun ew1 =>
    w8bErrW_exists_pre_frame fun ew2 => w8bErrW_exists_pre_frame fun ew3 =>
    w8bErrW_exists_pre_frame fun ew4 => w8bErrW_exists_pre_frame fun ew5 => ?_
  rw [sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hpack => ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (w8bSigErr_open_9f0_placed (A.atState lim (M.stepEvents evs₁ st) sm2) s0 (s0.sp - 608#64)
      x.ret x.ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen ew0 ew1
      ew2 ew3 ew4 ew5 regTag regVal opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9
      w13 w15 w23 vb m.kyberPreKeyId m.kyberCiphertext bk ik msg x.bytes ipk) ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun boxAct => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun msgAct =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun ikAct => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun bkAct => ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.bind
    (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
      (by
        simp only [esm_boxSlot_atState_eq, esm_deallocSlot_atState_eq]
        dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]
        apply entails_of_eq; sep_ac_rfl)
      (e_9f0_words2_placed_wpE (M := M) (A := A) (lim := lim) (st := M.stepEvents evs₁ st)
        (msgPtr := msgPtr) (ikPtr := ikPtr) (bkPtr := bkPtr)
        (ew2 := ew2) (ew3 := ew3) (ew4 := ew4) (ew5 := ew5)
        (R := w8bSigErr9f0RestPlaced s0 (s0.sp - 608#64) x.ptr (BitVec.ofNat 64 msg.length)
          kyberLen w15 regTag regVal opkTag opkVal spkId kpkVal (identRegId regTag regVal)
          (BitVec.extractLsb' 32 32 (BitVec.ofNat 64 ik.length)) (p8.zeroExtend 32) x.bytes)
        hC [] boxAct msgAct ikAct bkAct hpack hst2 hpc2 hrun2 hmsgNe hikNe hbkNe)) ?_
  rintro sm3 Pm3 hpc3 hrun3 ⟨hst3, _, evs₂, hfree₂, hPm3⟩
  have hpack' : Pm3 ⊢
      pksmErrE A.repAlloc [] x.ret e ∗ SepProp.emp ∗
        stackAt (s0.sp - 608#64) preKeyTryFromSubStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool lim (M.stepEvents (evs₁ ++ evs₂) st) sm3 := by
    rw [M.stepEvents_append]
    have hpk := w8bSigErr_placed_pack
      (A := A.atState lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) sm3) (s0 := s0)
      (sp' := s0.sp - 608#64) (sret := x.ret) (ptr := x.ptr)
      (msgLen := BitVec.ofNat 64 msg.length) (kyberLen := kyberLen) (w15 := w15)
      (msgPtr := msgPtr) (ikPtr := ikPtr) (bkPtr := bkPtr) (bkCap := bkCap)
      (regTag := regTag) (regVal := regVal) (opkTag := opkTag) (opkVal := opkVal)
      (spkId := spkId) (kpkVal := kpkVal) (regId := identRegId regTag regVal)
      (ikHi := BitVec.extractLsb' 32 32 (BitVec.ofNat 64 ik.length))
      (p8z := p8.zeroExtend 32) (e := e) (bytes := x.bytes)
    rw [w8b_pksmErrE_atState_eq_noPanic] at hpk
    exact Entails.trans hPm3
      (Entails.trans (by dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]; apply entails_of_eq; sep_ac_rfl)
        hpk)
  exact CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre hpack'
    (w8b_errTail_close_noPanic_placed hparse (pksmFrom864Env_of_err hsig hevs₁ hfree₂) hst3 hpc3 hrun3)

end ErrSigMsg

section PackW

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue (msgHeapAt optBoxU8Heap vecU8Heap)
open CryptoVerification.LibsignalTripleRatchet (boxU8Buf)
open CryptoVerification.LibsignalTripleRatchet.Wire (deallocSlot entails_of_eq)
open CryptoVerification.LibsignalTripleRatchetRepr (SignalMessageGhost)
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire (ecKeyParses ecKeyParses_of_deserialize_ok kyberStageOut pkOf pkOf_bytes_of_ecKeyParses pkOf_of_deserialize_ok sret_cells_entails_pksmResAt vb_lsr4_toNat w8bPackJunkPlaced w8bPack_epi_regroup_placed w8bPack_opk w8bPack_pre_open_placed w8bPack_regId w8bRowSPost w8b_exists_words4_of_vector32)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCPlacedBudget (err_epilogue_504_placed_wp)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCWPlacedBudget (deallocChain_970_placed_wpX)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.PackWPlacedBudget (preKey_pack_8c0_to_970_dealloc_res_placed_wpX)

open Arm64 ProofLib.ProgramReflection
open ProofLib hiding SepWPp
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWSharedPlacedBudget (spAligned_of_postEpilogueStatePlaced)

private theorem pk_boxU8Buf_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (ptr : BitVec 64) (bs : List (BitVec 8)) :
    boxU8Buf (A.atState lim st s) ptr bs = boxU8Buf A.repAlloc ptr bs := rfl

private theorem pk_vecU8Heap_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Heap (A.atState lim st s) cap ptr bs = vecU8Heap A.repAlloc cap ptr bs := by
  by_cases hc : cap = 0 <;> simp only [vecU8Heap, hc, ↓reduceIte,
    LibsignalBinary.Heap.RustCliAllocBudget.atState, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]

private theorem pk_optBoxU8Heap_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (ptr w0 w1 : BitVec 64)
    (o : Option (List (BitVec 8))) :
    optBoxU8Heap (A.atState lim st s) ptr w0 w1 o = optBoxU8Heap A.repAlloc ptr w0 w1 o := by
  cases o <;> rfl

private theorem pk_msgHeapAt_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (g : SignalMessageGhost) (m : SignalMessage)
    (addrW0 addrW1 : BitVec 64) :
    msgHeapAt (A.atState lim st s) g m addrW0 addrW1 =
      msgHeapAt A.repAlloc g m addrW0 addrW1 := by
  simp only [msgHeapAt, pk_vecU8Heap_atState_eq, pk_boxU8Buf_atState_eq, pk_optBoxU8Heap_atState_eq]

private theorem pk_w8bRowSPost_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (sp' clonePtr : BitVec 64) (b : List (BitVec 8))
    (innerMsg : SignalMessage) (msgG : SignalMessageGhost)
    (rk0 rk1 rk2 rk3 addrW0 addrW1 : BitVec 64) (verHi56 : BitVec 56) :
    w8bRowSPost (A.atState lim st s) sp' clonePtr b innerMsg msgG rk0 rk1 rk2 rk3 addrW0 addrW1
        verHi56 =
      w8bRowSPost A.repAlloc sp' clonePtr b innerMsg msgG rk0 rk1 rk2 rk3 addrW0 addrW1 verHi56 := by
  simp only [w8bRowSPost, pk_msgHeapAt_atState_eq, pk_boxU8Buf_atState_eq]

private theorem pk_kyberStageOut_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (kpkVal : BitVec 32) (vb : BitVec 8)
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8)))
    (kbPtr kbLen : BitVec 64) :
    kyberStageOut (A.atState lim st s) kpkVal vb kpkOpt kyberOpt kbPtr kbLen =
      kyberStageOut A.repAlloc kpkVal vb kpkOpt kyberOpt kbPtr kbLen := by
  cases kpkOpt <;> cases kyberOpt <;> simp only [kyberStageOut, pk_boxU8Buf_atState_eq]

private theorem pk_deallocSlot_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (cap ptr : BitVec 64) (act : Bool) :
    deallocSlot (A.atState lim st s) cap ptr act = deallocSlot A.repAlloc cap ptr act := by
  cases act <;> rfl

/-- the `+0x8c0` (`2240`) Ok edge returns with
`w8bRetPost A lim FreeOnlyEvs x st s0`. -/
theorem preKey8c0OkNoPanicW_placed_proof [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : CalleesPlacedBudget.PksmCalleesPlaced M A lim H) :
    PreKey8c0OkNoPanicWPlaced M A lim H := by
  intro x st s0 sf vb b1 bs1 m bk ik msg spkId _pk ipk bkCap bkPtr ikCap ikPtr msgCap msgPtr
    kyberLen regTag regVal opkTag opkVal _kpkTag kpkVal kyberBoxPtr kyberBoxLen p0 p1 p2 p3 p4 p5
    p6 p7 p8 p31 w9 w13 w15 w23 innerMsg msgG rk0 rk1 rk2 rk3 addrW0 addrW1 verHi56 clonePtr
    hx hge3 hle4 _hlen hdec hbk hik hmsg hsid hreg hopk _hkpk hpkD _hkyb hpkB hikD hinner hrk hst
    _hbkCap _hikCap _hmsgCap _hfit hpc hrun
  have hvlt := vb.isLt
  simp only [BitVec.lt_def, vb_lsr4_toNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    at hge3 hle4
  have hlo : 0x30 ≤ vb.toNat := by omega
  have hhi : vb.toNat ≤ 0x4f := by omega
  have hbk_ok : ecKeyParses bk = true := ecKeyParses_of_deserialize_ok hpkD
  have hpkb1 : (pkOf bk).bytes.toList = (bk.take 33).drop 1 := pkOf_bytes_of_ecKeyParses hbk_ok
  have hik_ok : ecKeyParses ik = true := ecKeyParses_of_deserialize_ok hikD
  have hikpk : pkOf ik = ipk := pkOf_of_deserialize_ok hikD
  obtain ⟨ik0, ik1, ik2, ik3, hipk⟩ := w8b_exists_words4_of_vector32 ipk.bytes
  have hikw : ∀ a : BitVec 64, (a ↦ₛ (pkOf ik).bytes.toList) =
      (a ↦₆₄ ik0) ∗ ((a + 8#64) ↦₆₄ ik1) ∗ ((a + 16#64) ↦₆₄ ik2) ∗ ((a + 24#64) ↦₆₄ ik3) := by
    rw [hikpk]; exact hipk
  obtain ⟨hopkTag, hopkVal⟩ := w8bPack_opk hopk
  have hregId := w8bPack_regId hreg
  have hBridge := sret_cells_entails_pksmResAt A.repAlloc x.ret vb (b1 :: bs1) m bk ik msg spkId
    innerMsg msgG clonePtr kyberBoxPtr kyberBoxLen rk0 rk1 rk2 rk3 addrW0 addrW1 verHi56 ik0 ik1
    ik2 ik3 opkTag opkVal kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 emp hlo hhi hdec
    hbk hik hmsg hsid hbk_ok hik_ok hinner hopkTag hopkVal (hpkb1.trans hpkB) hrk hikw
  rw [hx] at hst
  rw [← pk_w8bRowSPost_atState_eq A lim st sf]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (w8bPack_pre_open_placed (A.atState lim st sf) s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr
      kyberLen ikCap ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen clonePtr regTag regVal opkTag
      opkVal spkId kpkVal (m.registrationId.getD 0#32) p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15
      w23 vb (b1 :: bs1) m.kyberPreKeyId m.kyberCiphertext bk ik msg x.bytes ipk innerMsg msgG rk0
      rk1 rk2 rk3 addrW0 addrW1 verHi56 ik0 ik1 ik2 ik3 hx hregId hipk) ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun msgAct => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun ikAct =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun bkAct => ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.bind
    (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
      (by
        simp only [pk_msgHeapAt_atState_eq, pk_boxU8Buf_atState_eq, pk_kyberStageOut_atState_eq,
          pk_deallocSlot_atState_eq]
        dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]
        apply entails_of_eq; sep_ac_rfl)
      (preKey_pack_8c0_to_970_dealloc_res_placed_wpX (M := M) (A := A) (lim := lim) (st := st)
        (bkPtr := bkPtr) (bkCap := bkCap) (msgPtr := msgPtr) (ikPtr := ikPtr)
        (msgAct := msgAct) (ikAct := ikAct) (bkAct := bkAct)
        (stackSz := CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100) (R_heap := emp)
        (frame := w8bPackJunkPlaced s0 (s0.sp - 608#64) x.ptr regTag regVal ik msg x.bytes kyberLen)
        hopkTag hBridge hst hpc hrun)) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hst1, hent1⟩
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre hent1 ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.bind
    (deallocChain_970_placed_wpX (M := M) (A := A) (lim := lim) (st := st)
      hC msgAct ikAct bkAct hst1 hpc1 hrun1) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hst2, _, evs, hfree, hent2⟩
  refine CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.SepWPp.mono_post
    (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
      (Entails.trans hent2
        (Entails.trans
          (by dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]; apply entails_of_eq; sep_ac_rfl)
          (w8bPack_epi_regroup_placed (A.atState lim (M.stepEvents evs st) s2) s0 x.ptr bkCap bkPtr
            msgPtr ikPtr kyberLen regTag regVal opkTag opkVal spkId kpkVal
            (m.registrationId.getD 0#32) p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 ik0 ik1 ik2
            ik3 ik msg x.bytes
            (CryptoVerification.SignalSession.Cli.RunCompose.pksmResAt A.repAlloc x.ret (CryptoVerification.SignalSession.Cli.RunProofs.Pksm.pksmParse (vb :: b1 :: bs1))))))
      (err_epilogue_504_placed_wp (M := M) (A := A) (lim := lim) (x := x)
        (st := M.stepEvents evs st) (H := H)
        (sretOut := CryptoVerification.SignalSession.Cli.RunCompose.pksmResAt A.repAlloc x.ret (CryptoVerification.SignalSession.Cli.RunProofs.Pksm.pksmParse (vb :: b1 :: bs1)))
        (spAligned_of_postEpilogueStatePlaced hst2) hst2 hpc2 hrun2)) ?_
  rintro sf' Pf' _ _ ⟨hsp', hcs', hent'⟩
  rw [← hx] at hent'
  exact ⟨hsp', hcs', evs, hfree, hent'⟩

end PackW

section FinalAssembly

open CryptoVerification (LibsignalHooks LibsignalPlacement)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget (PksmCalleesPlaced pksmCalleesPlaced_of_codecHooks)

/-- Full post-loop `preKeyNoPanicQp` chain `+0x460 → ret` under `[LibsignalPlacement]`,
assembled from `(hH : CodecHooksPlaced M A lim H)` and `(hC : PksmCalleesPlaced M A lim H)`. -/
theorem preKeyPostLoopOkNoPanicW_of_codecHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hH : CodecHooksPlaced M A lim H)
    (hC : PksmCalleesPlaced M A lim H) :
    PreKeyPostLoopOkNoPanicWPlaced M A lim H :=
  preKeyPostLoopOkNoPanicW_placed_of_5b4 hC (preKeyPresenceErrNoPanicW_placed_proof hC)
    (preKey5b4OkNoPanicW_placed_of_684 hC (preKeyBaseKeyErrNoPanicW_placed_proof hC)
      (preKey684OkNoPanicW_placed_of_830 hC (preKeyKyberErrNoPanicW_placed_proof hH hC)
        (preKey830OkNoPanicW_placed_of_864 hC (preKeyIdentErrNoPanicW_placed_proof hC)
          (preKey864OkNoPanicW_placed_of_8c0 hC (preKeySigMsgErrNoPanicW_placed_proof hC)
            (preKey8c0OkNoPanicW_placed_proof hC)))))

/-- Convenience corollary deriving `PksmCalleesPlaced` from `CodecHooksPlaced`. -/
theorem preKeyPostLoopOkNoPanicW_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hH : CodecHooksPlaced M A lim H) :
    PreKeyPostLoopOkNoPanicWPlaced M A lim H :=
  preKeyPostLoopOkNoPanicW_of_codecHooks hH (pksmCalleesPlaced_of_codecHooks hH)

end FinalAssembly

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bNoPanicAux
