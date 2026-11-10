/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWSharedPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ParseLemmas
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bPostLoop
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bPostLoopPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aPresenceWPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aPresenceBPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bBaseKey
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bBaseKeyPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aBaseKeyWPlaced
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCleanup
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSome

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bNoPanicAuxA

section Shared

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet.Prost
open Arm64 ProofLib.ProgramReflection
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession (SignalProtocolError)
open CryptoGames.LibsignalSessionApi (ProtoPreKeySignalMessage)
open CryptoVerification (LibsignalHooks LibsignalPlacement blkPl_111)
open CryptoVerification.E2E.Pqxdh.ResponderWire (preKeyCalleeSavedAt preKeyPlacedProg preKeyTryFromSubStack)
open CryptoVerification.LibsignalTripleRatchet (lsLogOff smallRootStack)
open CryptoVerification.LibsignalTripleRatchet.Wire (PostEpilogueStatePlaced entails_of_eq)
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire (PreKeyLoopExitStatePlaced pksmErrE wirePreKeyOf)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCPlacedBudget (err_epilogue_504_placed_wp)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget (PksmPostEnv w8bRetPost w8b_errRetPost_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWSharedPlacedBudget (spAligned_of_postEpilogueStatePlaced)

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
  CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.bind
    (Qm := fun sm Pmf => ∃ Pm, Q' sm Pm ∧ (Pmf ⊢ Pm ∗ F))
    (w8b_frame_noPanic h1 fun _ Pm hq => ⟨Pm, hq, Entails.refl _⟩)
    fun sm _ hpcm hrunm ⟨Pm, hqm, hent⟩ =>
      CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre hent (h2 sm Pm hpcm hrunm hqm)

theorem w8b_errTail_close_noPanic_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RemEnv : List AllocEvent → Prop}
    {H : LibsignalHooks} {x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost}
    {st : M.σ} {evs : List AllocEvent}
    {s0 s : State} {R : SepProp} {fn : List (BitVec 8)} {e : SignalProtocolError}
    (hparse : CryptoVerification.SignalSession.Cli.RunProofs.Pksm.pksmParse x.bytes = none)
    (hevs : RemEnv evs)
    (hst : PostEpilogueStatePlaced s0 (s0.sp - 608#64) s)
    (hpc : s.pc = (blkPl_111).base + 1284#64)
    (hrun : s.status = .Running) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s
      (pksmErrE A.repAlloc fn x.ret e ∗ R ∗
        stackAt (s0.sp - 608#64) preKeyTryFromSubStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool lim (M.stepEvents evs st) s)
      (w8bRetPost A lim RemEnv x st s0)
      preKeyNoPanicQp := by
  have hsp0 : s0.spAligned = true := spAligned_of_postEpilogueStatePlaced hst
  have hsub_eq : smallRootStack = preKeyTryFromSubStack := rfl
  refine CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.SepWPp.mono_post
    (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
      (P' := stackAt (s0.sp - 608#64) smallRootStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        (pksmErrE A.repAlloc fn x.ret e ∗ R) ∗
        (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool lim (M.stepEvents evs st) s)
      (by rw [hsub_eq]; apply entails_of_eq; sep_ac_rfl)
      (err_epilogue_504_placed_wp (A := A) (lim := lim) (x := x)
        (sretOut := pksmErrE A.repAlloc fn x.ret e ∗ R)
        (st := M.stepEvents evs st) hsp0 hst hpc hrun)) ?_
  intro sf Pf _ _ hq
  exact w8b_errRetPost_placed hparse hevs hq

def PreKeyPostLoopOkNoPanicWPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) : Prop :=
  ∀ (x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost) (st : M.σ) (s0 s : State)
    (vb b1 : BitVec 8) (bs1 : List (BitVec 8)) (m : ProtoPreKeySignalMessage),
    FitsEnv M lim st (PksmPostEnv vb x.bytes m) →
    x.bytes = vb :: b1 :: bs1 → ¬ (vb >>> 4) < 3#8 → ¬ 4#8 < (vb >>> 4) →
    x.bytes.length < 2 ^ 32 →
    CryptoVerification.SignalSession.Cli.RunProofs.Pksm.decodeProto (b1 :: bs1) = some m →
    PreKeyLoopExitStatePlaced s0 (s0.sp - 608#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.ptr vb s →
    s.pc = (blkPl_111).base + 1120#64 →
    s.status = .Running →
    s.readReg64 .x24 = 0#64 →
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s
      (wirePreKeyOf A.repAlloc (s0.sp - 608#64 + 312#64) m ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 16 ∗
        memRegion (s0.sp - 608#64 + 440#64) 8 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        memRegion x.ret 248 ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗
        A.pool lim st s ∗ stackAt (s0.sp - 608#64) preKeyTryFromSubStack)
      (w8bRetPost A lim (PksmPostEnv vb x.bytes m) x st s0)
      preKeyNoPanicQp

end Shared

section PostLoop

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoGames.LibsignalSessionApi (ProtoPreKeySignalMessage)
open CryptoVerification (LibsignalHooks LibsignalPlacement blkPl_111 lsmpl)
open CryptoVerification.E2E.Pqxdh.ResponderWire (bv_add_neg_104 bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_16 bv_add_neg_160 bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191 bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40 bv_add_neg_48 bv_add_neg_512 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72 bv_add_neg_8 bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_sub_add_lit' bv_sub_sub_lit keepsFrozenInv_codeRoLoaded memRegion96_seg1_unpack post_memRegion48_split8 preKeyCalleeSavedAt preKeyPlacedProg)
open CryptoVerification.LibsignalTripleRatchet (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup (words5At words5At_entails_memRegion)
open CryptoVerification.LibsignalTripleRatchet.Getters (DropSpeGhost)
open CryptoVerification.LibsignalTripleRatchet.Wire (SepWPp cap_add1_eq_of_lt entails_of_eq optVecU8Buf stackAt_sub_split)
open CryptoVerification.LibsignalTripleRatchetRepr (speAt speWord)
open CryptoVerification.RustHeap (vecHeader)
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire (PreKeyLoopExitStatePlaced PresenceErrTailStatePlaced PresenceOkStatePlaced optVecU8Buf_cap_add2_ne post_headers_entails_memRegion80W seg1SpillsAtW stackAt_preKeyTryFromSubStack_skipField vecU8Buf_cap_lt_len w8bOptU32Cells w8bPostLoopFramePlaced w8bXokPost w8b_memRegion296_split w8b_optU32At_entails w8b_wirePreKeyAt_some_eq wirePreKeyOf)
open Arm64 ProofLib.ProgramReflection
open ProofLib hiding SepWP SepWPp
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpecX)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget (PksmCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget (w8bRetPost w8bRetPost_prepend PksmPostEnv PksmFrom5b4Env fitsEnv_pksmPost_step_freeOnly pksmPostEnv_prepend_some)

private abbrev pl_of_sepWP_frozen_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk
private abbrev pl_of_sepWP_end_pk :=
  @w8b_of_sepWP_end_noPanic_pk
private abbrev pl_call_noPanic_pk :=
  @w8b_call_noPanic_pk

private theorem pl_sepWPp_introState {prog : Program} {ret : BitVec 64} {s1 : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ s_mid, s_mid = s1 → SepWPp prog ret s_mid P Q Qp) :
    SepWPp prog ret s1 P Q Qp :=
  h s1 rfl

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512

theorem post_bk_some_to_57c_noPanic_placed_wpW [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen bkCap bkPtr
      ikCap ikPtr ikLen msgCap msgPtr msgLen : BitVec 64} {vb : BitVec 8}
    {regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal : BitVec 32}
    {kyberOpt : Option (List (BitVec 8))} {bk : List (BitVec 8)}
    (hst : PreKeyLoopExitStatePlaced s0 sp' sret len ptr0 vb s)
    (hpc : s.pc = (blkPl_111).base + 1120#64)
    (hrun : s.status = .Running) (hx24 : s.readReg64 .x24 = 0#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1404#64) s
      (memRegion (sp' + 16#64) 96 ∗
        vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
        optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
        vecHeader (sp' + 336#64) bkCap bkPtr (BitVec.ofNat 64 bk.length) ∗
        CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗
        vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
        vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
        ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
        ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
        ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal) ∗
        A.pool lim st s ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100))
      (fun sf Pf =>
        PresenceErrTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap
          (spkTag.zeroExtend 64) vb sf ∧
        bk.length ≤ bkCap.toNat ∧ bkCap.toNat < 2 ^ 63 ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ seg1SpillsAtW sp' bkCap bkPtr (BitVec.ofNat 64 bk.length) kyberLen ikPtr ikLen msgPtr msgLen
              regTag regVal opkTag opkVal spkVal kpkTag kpkVal ∗
            memRegion (sp' + 312#64) 48 ∗ memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
            optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
            CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)))
      preKeyNoPanicQp := by
  rcases hst with ⟨hregs, hsp, hcl, htr⟩
  have hcallSpe := hC.dropSpeX
  have hsp_eq := hregs.sp; have h29 := hregs.x29; have h27 := hregs.x27
  have h22 := hregs.x22; have h21 := hregs.x21; have h20 := hregs.x20; have h19 := hregs.x19
  have hstackSpe := stackAt_sub_split sp' CryptoVerification.LibsignalTripleRatchet.Getters.dropSpeStackX (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (sepConj_mono (memRegion96_seg1_unpack sp')
      (sepConj_mono_right (sepConj_mono (optVecU8Buf_cap_add2_ne A.repAlloc kyberCap kyberPtr kyberLen kyberOpt)
        (sepConj_mono_right (sepConj_mono_left (vecU8Buf_cap_lt_len A.repAlloc bkCap bkPtr bk)))))) ?_
  simp only [sepConj_assoc, sepExists_sepConj_left]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w16 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w20 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w24 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w28 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w32 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w40 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w48 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w52 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w56 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w68 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w72 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w80 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w88 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w96 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w104 => ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (P' :=
      ⌜(kyberCap + 2#64 != 0#64) = true⌝ ∗
      ⌜bk.length ≤ bkCap.toNat ∧ bkCap.toNat < 2 ^ 63 ∧ bkPtr ≠ 0⌝ ∗
      (((sp' + 16#64) ↦₃₂ w16) ∗ ((sp' + 20#64) ↦₃₂ w20) ∗
        ((sp' + 24#64) ↦₃₂ w24) ∗ ((sp' + 28#64) ↦₃₂ w28) ∗
        ((sp' + 32#64) ↦₆₄ w32) ∗ ((sp' + 40#64) ↦₆₄ w40) ∗
        ((sp' + 48#64) ↦₃₂ w48) ∗ ((sp' + 52#64) ↦₃₂ w52) ∗
        ((sp' + 56#64) ↦₆₄ w56) ∗ memRegion (sp' + 64#64) 4 ∗
        ((sp' + 68#64) ↦₃₂ w68) ∗ ((sp' + 72#64) ↦₆₄ w72) ∗
        ((sp' + 80#64) ↦₆₄ w80) ∗ ((sp' + 88#64) ↦₆₄ w88) ∗
        ((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w104) ∗
        vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
        optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
        vecHeader (sp' + 336#64) bkCap bkPtr (BitVec.ofNat 64 bk.length) ∗
        CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗
        vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
        vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
        ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
        ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
        ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal) ∗
        A.pool lim st s ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hky_ne => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun ⟨hbk_le, hbk_lt, _⟩ => ?_
  have hbk_eq := cap_add1_eq_of_lt hbk_lt
  dsimp only [vecHeader]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine pl_of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 5) ?_
  wp_steps_sync_pool (lsmpl.base 5)
  refine CryptoVerification.E2E.Pqxdh.ResponderWire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hcl1 => ?_
  refine pl_sepWPp_introState fun s1 hs1 => ?_
  rw [← hs1]
  have hsp1_eq : s1.sp = sp' := by subst hs1; tryFromPost_sp [hsp_eq]
  have hw5 :
      ((sp' + 320#64) ↦₆₄ kyberPtr) ∗ ((sp' + 328#64) ↦₆₄ kyberLen) ∗
        ((sp' + 336#64) ↦₆₄ bkCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
        ((sp' + 352#64) ↦₆₄ BitVec.ofNat 64 bk.length) ⊢ memRegion (sp' + 320#64) 40 := by
    simpa [words5At, BitVec.add_assoc, BitVec.reduceAdd] using
      words5At_entails_memRegion (sp' + 320#64) kyberPtr kyberLen bkCap bkPtr (BitVec.ofNat 64 bk.length)
  have hhdr80 := post_headers_entails_memRegion80W sp' ikCap ikPtr ikLen msgCap msgPtr msgLen
    regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal
  dsimp only [vecHeader] at hhdr80
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hhdr80
  have hspe : speAt A.repAlloc [] (sp' + 312#64) .invalidProtobufEncoding =
      ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40 := by
    simp [speAt, speWord, BitVec.reduceAdd]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (P' := (speAt A.repAlloc [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool lim st s1 ∗
      stackAt s1.sp CryptoVerification.LibsignalTripleRatchet.Getters.dropSpeStackX) ∗
      (seg1SpillsAtW sp' bkCap bkPtr (BitVec.ofNat 64 bk.length) kyberLen ikPtr ikLen msgPtr msgLen
          regTag regVal opkTag opkVal spkVal kpkTag kpkVal ∗
        memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
        optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
        CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗
        memRegion (sp' - BitVec.ofNat 64 (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100))
          (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100 - CryptoVerification.LibsignalTripleRatchet.Getters.dropSpeStackX)))
    (by
      rw [hspe, hsp1_eq, hstackSpe]; dsimp only [seg1SpillsAtW]
      refine Entails.trans (Q :=
        (((sp' + 320#64) ↦₆₄ kyberPtr) ∗ ((sp' + 328#64) ↦₆₄ kyberLen) ∗
          ((sp' + 336#64) ↦₆₄ bkCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
          ((sp' + 352#64) ↦₆₄ BitVec.ofNat 64 bk.length)) ∗
        (((sp' + 360#64) ↦₆₄ ikCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗ ((sp' + 376#64) ↦₆₄ ikLen) ∗
          ((sp' + 384#64) ↦₆₄ msgCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗ ((sp' + 400#64) ↦₆₄ msgLen) ∗
          ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
          ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
          ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
          ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal)) ∗
        (((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ A.pool lim st s1 ∗ stackAt sp' CryptoVerification.LibsignalTripleRatchet.Getters.dropSpeStackX ∗
          ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
          ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkVal) ∗
          ((sp' + 32#64) ↦₆₄ msgLen) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
          ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
          ((sp' + 56#64) ↦₆₄ ikLen) ∗ memRegion (sp' + 64#64) 4 ∗
          ((sp' + 68#64) ↦₃₂ kpkTag) ∗ ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
          CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗
          memRegion (sp' - BitVec.ofNat 64 (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100))
            (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100 - CryptoVerification.LibsignalTripleRatchet.Getters.dropSpeStackX)))
        (by apply entails_of_eq; sep_ac_rfl) ?_
      refine Entails.trans (sepConj_mono hw5 (sepConj_mono_left hhdr80)) (by apply entails_of_eq; sep_ac_rfl)) ?_
  refine pl_call_noPanic_pk keepsFrozenInv_codeRoLoaded
    ((⟨sp' + 312#64, [], .invalidProtobufEncoding⟩ : DropSpeGhost), st) hcallSpe
    (by subst hs1; simp_all [arm64_norm])
    (by subst hs1; simp_all [arm64_norm])
    (by subst hs1; tryFromPost_sp_align hsp)
    (by subst hs1; exact hcl1)
    (ret_pc := (blkPl_111).base + 1404#64) (by subst hs1; simp_all [arm64_norm])
    (T := speAt A.repAlloc [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool lim st s1 ∗
      stackAt s1.sp CryptoVerification.LibsignalTripleRatchet.Getters.dropSpeStackX)
    (φ := sp' + 312#64 = sp' + 312#64 ∧
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 ((blkPl_111).base + 1404#64))
    (by subst hs1; simp_all [dropSpeSpecX, arm64_norm])
    ⟨rfl, LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_blockPlacement_base_add 111 1404#64 (by decide) (by decide)⟩ rfl ?_
  clear hcallSpe
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [dropSpeSpecX]; simp only [sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun htr2 => ?_
  rw [← sepConj_assoc (memRegion (sp' + 312#64) 48) (∃∗ evs : List AllocEvent, _),
      sepConj_comm (memRegion (sp' + 312#64) 48) (∃∗ evs : List AllocEvent, _),
      sepConj_assoc, sepExists_sepConj_left]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun evs => ?_
  simp only [sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hfree => ?_
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, hx25_cs, hx26_cs, hx27_cs,
    hx28_cs, hx29_cs⟩
  refine pl_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2
    (CryptoVerification.E2E.Pqxdh.ResponderWire.SepWP.done hpc2 hrun2 fun hcl3 => ?_)
  refine ⟨⟨⟨by rw [hsp2, hsp1_eq], hsp2_align, hcl3,
      by subst hs1; simp [htr2, htr, arm64_norm]⟩,
    by subst hs1; simp [hx29_cs, h29, arm64_norm],
    by subst hs1; simp [hx28_cs, arm64_norm],
    by subst hs1; simp [hx27_cs, h27, arm64_norm],
    by subst hs1; simp [hx26_cs, arm64_norm],
    by subst hs1; simp [hx25_cs, arm64_norm],
    by subst hs1; simp [hx24_cs, arm64_norm],
    by subst hs1; simp [hx23_cs, arm64_norm],
    by subst hs1; simp [hx22_cs, h22, arm64_norm],
    by subst hs1; simp [hx21_cs, h21, arm64_norm],
    by subst hs1; simp [hx20_cs, h20, arm64_norm],
    by subst hs1; simp [hx19_cs, h19, arm64_norm]⟩, hbk_le, hbk_lt, evs, hfree, ?_⟩
  simp only [hstackSpe, hsp1_eq, arm64_norm]; apply entails_of_eq; sep_ac_rfl

theorem post_ik_some_to_590_noPanic_placed_wpW [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap x24 : BitVec 64} {vb : BitVec 8}
    (hst : PresenceErrTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap x24 vb s)
    (hpc : s.pc = (blkPl_111).base + 1404#64)
    (hrun : s.status = .Running) (hik_lt : ikCap.toNat < 2 ^ 63) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1424#64) s
      (memRegion (sp' + 312#64) 48 ∗ A.pool lim st s ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100))
      (fun sf Pf =>
        PresenceErrTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap x24 vb sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ memRegion (sp' + 312#64) 48 ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)))
      preKeyNoPanicQp := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  have hcallSpe := hC.dropSpeX
  have hik_eq := cap_add1_eq_of_lt hik_lt
  have hstackSpe := stackAt_sub_split sp' CryptoVerification.LibsignalTripleRatchet.Getters.dropSpeStackX (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)
  have hspe : speAt A.repAlloc [] (sp' + 312#64) .invalidProtobufEncoding =
      ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40 := by
    simp [speAt, speWord, BitVec.reduceAdd]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left (post_memRegion48_split8 (sp' + 312#64))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w312 =>
    pl_of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 5) ?_
  wp_steps_sync_pool (lsmpl.base 5)
  refine CryptoVerification.E2E.Pqxdh.ResponderWire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hcl1 => ?_
  refine pl_sepWPp_introState fun s1 hs1 => ?_
  rw [← hs1]
  have hsp1_eq : s1.sp = sp' := by subst hs1; tryFromPost_sp [hsp_eq]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (P' := (speAt A.repAlloc [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool lim st s1 ∗
      stackAt s1.sp CryptoVerification.LibsignalTripleRatchet.Getters.dropSpeStackX) ∗
      memRegion (sp' - BitVec.ofNat 64 (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100))
        (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100 - CryptoVerification.LibsignalTripleRatchet.Getters.dropSpeStackX))
    (by rw [hspe, hsp1_eq, hstackSpe]; apply entails_of_eq; sep_ac_rfl) ?_
  refine pl_call_noPanic_pk keepsFrozenInv_codeRoLoaded
    ((⟨sp' + 312#64, [], .invalidProtobufEncoding⟩ : DropSpeGhost), st) hcallSpe
    (by subst hs1; simp_all [arm64_norm])
    (by subst hs1; simp_all [arm64_norm])
    (by subst hs1; simpa [State.spAligned, arm64_norm] using hsp)
    (by subst hs1; exact hcl1)
    (ret_pc := (blkPl_111).base + 1424#64) (by subst hs1; simp_all [arm64_norm])
    (T := speAt A.repAlloc [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool lim st s1 ∗
      stackAt s1.sp CryptoVerification.LibsignalTripleRatchet.Getters.dropSpeStackX)
    (φ := sp' + 312#64 = sp' + 312#64 ∧
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 ((blkPl_111).base + 1424#64))
    (by subst hs1; simp_all [dropSpeSpecX, arm64_norm])
    ⟨rfl, LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_blockPlacement_base_add 111 1424#64 (by decide) (by decide)⟩ rfl ?_
  clear hcallSpe
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [dropSpeSpecX]; simp only [sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun htr2 => ?_
  rw [← sepConj_assoc (memRegion (sp' + 312#64) 48) (∃∗ evs : List AllocEvent, _),
      sepConj_comm (memRegion (sp' + 312#64) 48) (∃∗ evs : List AllocEvent, _),
      sepConj_assoc, sepExists_sepConj_left]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun evs => ?_
  simp only [sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hfree => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
  refine pl_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2
    (CryptoVerification.E2E.Pqxdh.ResponderWire.SepWP.done hpc2 hrun2 fun hcl3 => ?_)
  refine ⟨⟨⟨by rw [hsp2, hsp1_eq], hsp2_align, hcl3,
      by subst hs1; simp [htr2, htr, arm64_norm]⟩,
    by subst hs1; simp [hx29_2, hx29, arm64_norm],
    by subst hs1; simp [hx28_2, hx28, arm64_norm],
    by subst hs1; simp [hx27_2, hx27, arm64_norm],
    by subst hs1; simp [hx26_2, hx26, arm64_norm],
    by subst hs1; simp [hx25_2, hx25, arm64_norm],
    by subst hs1; simp [hx24_2, hx24, arm64_norm],
    by subst hs1; simp [hx23_2, hx23, arm64_norm],
    by subst hs1; simp [hx22_2, hx22, arm64_norm],
    by subst hs1; simp [hx21_2, hx21, arm64_norm],
    by subst hs1; simp [hx20_2, hx20, arm64_norm],
    by subst hs1; simp [hx19_2, hx19, arm64_norm]⟩, evs, hfree, ?_⟩
  simp only [hstackSpe, hsp1_eq, arm64_norm]; apply entails_of_eq; sep_ac_rfl

theorem post_msg_some_to_5a4_noPanic_placed_wpW [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap x24 : BitVec 64} {vb : BitVec 8}
    (hst : PresenceErrTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap x24 vb s)
    (hpc : s.pc = (blkPl_111).base + 1424#64)
    (hrun : s.status = .Running) (hmsg_lt : msgCap.toNat < 2 ^ 63) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1444#64) s
      (memRegion (sp' + 312#64) 48 ∗ A.pool lim st s ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100))
      (fun sf Pf =>
        PresenceErrTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap x24 vb sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ memRegion (sp' + 312#64) 48 ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)))
      preKeyNoPanicQp := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  have hcallSpe := hC.dropSpeX
  have hmsg_eq := cap_add1_eq_of_lt hmsg_lt
  have hstackSpe := stackAt_sub_split sp' CryptoVerification.LibsignalTripleRatchet.Getters.dropSpeStackX (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)
  have hspe : speAt A.repAlloc [] (sp' + 312#64) .invalidProtobufEncoding =
      ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40 := by
    simp [speAt, speWord, BitVec.reduceAdd]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left (post_memRegion48_split8 (sp' + 312#64))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w312 =>
    pl_of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 5) ?_
  wp_steps_sync_pool (lsmpl.base 5)
  refine CryptoVerification.E2E.Pqxdh.ResponderWire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hcl1 => ?_
  refine pl_sepWPp_introState fun s1 hs1 => ?_
  rw [← hs1]
  have hsp1_eq : s1.sp = sp' := by subst hs1; tryFromPost_sp [hsp_eq]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (P' := (speAt A.repAlloc [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool lim st s1 ∗
      stackAt s1.sp CryptoVerification.LibsignalTripleRatchet.Getters.dropSpeStackX) ∗
      memRegion (sp' - BitVec.ofNat 64 (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100))
        (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100 - CryptoVerification.LibsignalTripleRatchet.Getters.dropSpeStackX))
    (by rw [hspe, hsp1_eq, hstackSpe]; apply entails_of_eq; sep_ac_rfl) ?_
  refine pl_call_noPanic_pk keepsFrozenInv_codeRoLoaded
    ((⟨sp' + 312#64, [], .invalidProtobufEncoding⟩ : DropSpeGhost), st) hcallSpe
    (by subst hs1; simp_all [arm64_norm])
    (by subst hs1; simp_all [arm64_norm])
    (by subst hs1; simpa [State.spAligned, arm64_norm] using hsp)
    (by subst hs1; exact hcl1)
    (ret_pc := (blkPl_111).base + 1444#64) (by subst hs1; simp_all [arm64_norm])
    (T := speAt A.repAlloc [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool lim st s1 ∗
      stackAt s1.sp CryptoVerification.LibsignalTripleRatchet.Getters.dropSpeStackX)
    (φ := sp' + 312#64 = sp' + 312#64 ∧
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 ((blkPl_111).base + 1444#64))
    (by subst hs1; simp_all [dropSpeSpecX, arm64_norm])
    ⟨rfl, LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_blockPlacement_base_add 111 1444#64 (by decide) (by decide)⟩ rfl ?_
  clear hcallSpe
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [dropSpeSpecX]; simp only [sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun htr2 => ?_
  rw [← sepConj_assoc (memRegion (sp' + 312#64) 48) (∃∗ evs : List AllocEvent, _),
      sepConj_comm (memRegion (sp' + 312#64) 48) (∃∗ evs : List AllocEvent, _),
      sepConj_assoc, sepExists_sepConj_left]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun evs => ?_
  simp only [sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hfree => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
  refine pl_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2
    (CryptoVerification.E2E.Pqxdh.ResponderWire.SepWP.done hpc2 hrun2 fun hcl3 => ?_)
  refine ⟨⟨⟨by rw [hsp2, hsp1_eq], hsp2_align, hcl3,
      by subst hs1; simp [htr2, htr, arm64_norm]⟩,
    by subst hs1; simp [hx29_2, hx29, arm64_norm],
    by subst hs1; simp [hx28_2, hx28, arm64_norm],
    by subst hs1; simp [hx27_2, hx27, arm64_norm],
    by subst hs1; simp [hx26_2, hx26, arm64_norm],
    by subst hs1; simp [hx25_2, hx25, arm64_norm],
    by subst hs1; simp [hx24_2, hx24, arm64_norm],
    by subst hs1; simp [hx23_2, hx23, arm64_norm],
    by subst hs1; simp [hx22_2, hx22, arm64_norm],
    by subst hs1; simp [hx21_2, hx21, arm64_norm],
    by subst hs1; simp [hx20_2, hx20, arm64_norm],
    by subst hs1; simp [hx19_2, hx19, arm64_norm]⟩, evs, hfree, ?_⟩
  simp only [hstackSpe, hsp1_eq, arm64_norm]; apply entails_of_eq; sep_ac_rfl

theorem post_spk_some_to_5b4_noPanic_placed_wpW [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    (hst : PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (blkPl_111).base + 1444#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1460#64) s
      (memRegion (sp' + 312#64) 48 ∗ A.pool lim st s ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100))
      (fun sf Pf =>
        PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ memRegion (sp' + 312#64) 48 ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)))
      preKeyNoPanicQp := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  have hcallSpe := hC.dropSpeX
  have hstackSpe := stackAt_sub_split sp' CryptoVerification.LibsignalTripleRatchet.Getters.dropSpeStackX (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)
  have hspe : speAt A.repAlloc [] (sp' + 312#64) .invalidProtobufEncoding =
      ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40 := by
    simp [speAt, speWord, BitVec.reduceAdd]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left (post_memRegion48_split8 (sp' + 312#64))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w312 =>
    pl_of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 5) ?_
  wp_steps_sync_pool (lsmpl.base 5)
  refine CryptoVerification.E2E.Pqxdh.ResponderWire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hcl1 => ?_
  refine pl_sepWPp_introState fun s1 hs1 => ?_
  rw [← hs1]
  have hsp1_eq : s1.sp = sp' := by subst hs1; tryFromPost_sp [hsp_eq]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (P' := (speAt A.repAlloc [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool lim st s1 ∗
      stackAt s1.sp CryptoVerification.LibsignalTripleRatchet.Getters.dropSpeStackX) ∗
      memRegion (sp' - BitVec.ofNat 64 (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100))
        (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100 - CryptoVerification.LibsignalTripleRatchet.Getters.dropSpeStackX))
    (by rw [hspe, hsp1_eq, hstackSpe]; apply entails_of_eq; sep_ac_rfl) ?_
  refine pl_call_noPanic_pk keepsFrozenInv_codeRoLoaded
    ((⟨sp' + 312#64, [], .invalidProtobufEncoding⟩ : DropSpeGhost), st) hcallSpe
    (by subst hs1; simp_all [arm64_norm])
    (by subst hs1; simp_all [arm64_norm])
    (by subst hs1; simpa [State.spAligned, arm64_norm] using hsp)
    (by subst hs1; exact hcl1)
    (ret_pc := (blkPl_111).base + 1460#64) (by subst hs1; simp_all [arm64_norm])
    (T := speAt A.repAlloc [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool lim st s1 ∗
      stackAt s1.sp CryptoVerification.LibsignalTripleRatchet.Getters.dropSpeStackX)
    (φ := sp' + 312#64 = sp' + 312#64 ∧
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 ((blkPl_111).base + 1460#64))
    (by subst hs1; simp_all [dropSpeSpecX, arm64_norm])
    ⟨rfl, LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_blockPlacement_base_add 111 1460#64 (by decide) (by decide)⟩ rfl ?_
  clear hcallSpe
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [dropSpeSpecX]; simp only [sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun htr2 => ?_
  rw [← sepConj_assoc (memRegion (sp' + 312#64) 48) (∃∗ evs : List AllocEvent, _),
      sepConj_comm (memRegion (sp' + 312#64) 48) (∃∗ evs : List AllocEvent, _),
      sepConj_assoc, sepExists_sepConj_left]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun evs => ?_
  simp only [sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hfree => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
  refine pl_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2
    (CryptoVerification.E2E.Pqxdh.ResponderWire.SepWP.done hpc2 hrun2 fun hcl3 => ?_)
  refine ⟨⟨⟨by rw [hsp2, hsp1_eq], hsp2_align, hcl3,
      by subst hs1; simp [htr2, htr, arm64_norm]⟩,
    by subst hs1; simp [hx29_2, hx29, arm64_norm],
    by subst hs1; simp [hx28_2, hx28, arm64_norm],
    by subst hs1; simp [hx27_2, hx27, arm64_norm],
    by subst hs1; simp [hx26_2, hx26, arm64_norm],
    by subst hs1; simp [hx25_2, hx25, arm64_norm],
    by subst hs1; simp [hx24_2, hx24, arm64_norm],
    by subst hs1; simp [hx23_2, hx23, arm64_norm],
    by subst hs1; simp [hx22_2, hx22, arm64_norm],
    by subst hs1; simp [hx21_2, hx21, arm64_norm],
    by subst hs1; simp [hx20_2, hx20, arm64_norm],
    by subst hs1; simp [hx19_2, hx19, arm64_norm]⟩, evs, hfree, ?_⟩
  simp only [hstackSpe, hsp1_eq, arm64_norm]; apply entails_of_eq; sep_ac_rfl

theorem post_seg1_xok_to_5b4_noPanic_placed_wpW [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    {vb : BitVec 8} {regTag regVal opkTag opkVal spkId kpkTag kpkVal : BitVec 32}
    {kyberOpt : Option (List (BitVec 8))} {bk ik msg : List (BitVec 8)}
    (hst : PreKeyLoopExitStatePlaced s0 sp' sret len ptr0 vb s)
    (hpc : s.pc = (blkPl_111).base + 1120#64)
    (hrun : s.status = .Running) (hx24 : s.readReg64 .x24 = 0#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1460#64) s
      (memRegion (sp' + 16#64) 96 ∗ vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
        optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
        vecHeader (sp' + 336#64) bkCap bkPtr (BitVec.ofNat 64 bk.length) ∗
        CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗
        vecHeader (sp' + 360#64) ikCap ikPtr (BitVec.ofNat 64 ik.length) ∗
        CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc ikCap ikPtr ik ∗
        vecHeader (sp' + 384#64) msgCap msgPtr (BitVec.ofNat 64 msg.length) ∗
        CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc msgCap msgPtr msg ∗
        ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
        ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ spkId) ∗
        ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal) ∗
        A.pool lim st s ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100))
      (fun sf Pf =>
        PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb sf ∧
        bkCap.toNat < 2 ^ 63 ∧ ikCap.toNat < 2 ^ 63 ∧ msgCap.toNat < 2 ^ 63 ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ seg1SpillsAtW sp' bkCap bkPtr (BitVec.ofNat 64 bk.length) kyberLen
              ikPtr (BitVec.ofNat 64 ik.length) msgPtr (BitVec.ofNat 64 msg.length)
              regTag regVal opkTag opkVal spkId kpkTag kpkVal ∗
            memRegion (sp' + 312#64) 48 ∗ memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
            optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
            CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗
            CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc ikCap ikPtr ik ∗
            CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc msgCap msgPtr msg ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)))
      preKeyNoPanicQp := by
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono
        (vecU8Buf_cap_lt_len A.repAlloc ikCap ikPtr ik)
        (sepConj_mono_right (sepConj_mono_left
          (vecU8Buf_cap_lt_len A.repAlloc msgCap msgPtr msg)))))))))) ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (P' :=
      ⌜ik.length ≤ ikCap.toNat ∧ ikCap.toNat < 2 ^ 63 ∧ ikPtr ≠ 0⌝ ∗
      ⌜msg.length ≤ msgCap.toNat ∧ msgCap.toNat < 2 ^ 63 ∧ msgPtr ≠ 0⌝ ∗
      ((memRegion (sp' + 16#64) 96 ∗ vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
        optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
        vecHeader (sp' + 336#64) bkCap bkPtr (BitVec.ofNat 64 bk.length) ∗
        CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗
        vecHeader (sp' + 360#64) ikCap ikPtr (BitVec.ofNat 64 ik.length) ∗
        vecHeader (sp' + 384#64) msgCap msgPtr (BitVec.ofNat 64 msg.length) ∗
        ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
        ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ spkId) ∗
        ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal) ∗
        A.pool lim st s ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)) ∗
      (CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc ikCap ikPtr ik ∗ CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc msgCap msgPtr msg)))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun ⟨_, hik_lt, _⟩ => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun ⟨_, hmsg_lt, _⟩ => ?_
  let tailF := seg1SpillsAtW sp' bkCap bkPtr (BitVec.ofNat 64 bk.length) kyberLen
      ikPtr (BitVec.ofNat 64 ik.length) msgPtr (BitVec.ofNat 64 msg.length)
      regTag regVal opkTag opkVal spkId kpkTag kpkVal ∗
    memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
    optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
    CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗
    CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc ikCap ikPtr ik ∗
    CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc msgCap msgPtr msg
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.bind (Qm := fun s1 P1 =>
      PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s1 ∧
      bkCap.toNat < 2 ^ 63 ∧
      ∃ evs1 : List AllocEvent, FreeOnlyEvs evs1 ∧
        (P1 ⊢ (seg1SpillsAtW sp' bkCap bkPtr (BitVec.ofNat 64 bk.length) kyberLen
              ikPtr (BitVec.ofNat 64 ik.length) msgPtr (BitVec.ofNat 64 msg.length)
              regTag regVal opkTag opkVal spkId kpkTag kpkVal ∗
            memRegion (sp' + 312#64) 48 ∗ memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
            optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
            CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗
            A.pool lim (M.stepEvents evs1 st) s1 ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)) ∗
          (CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc ikCap ikPtr ik ∗ CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc msgCap msgPtr msg)))
    (w8b_frame_noPanic
      (post_bk_some_to_57c_noPanic_placed_wpW hC hst hpc hrun hx24)
      fun s1 P1 ⟨hst1, _, hbk_lt, evs1, hf1, hent1⟩ =>
        ⟨by simpa [PresenceOkStatePlaced, PresenceErrTailStatePlaced] using hst1, hbk_lt,
          evs1, hf1, sepConj_mono_left hent1⟩) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hst1, hbk_lt, evs1, hf1, hent1⟩
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (P' := (memRegion (sp' + 312#64) 48 ∗ A.pool lim (M.stepEvents evs1 st) s1 ∗
        stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)) ∗ tailF)
    (Entails.trans hent1 (by dsimp only [tailF]; apply entails_of_eq; sep_ac_rfl)) ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.bind (Qm := fun s2 P2 =>
      PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s2 ∧
      ∃ evs2 : List AllocEvent, FreeOnlyEvs evs2 ∧
        (P2 ⊢ (memRegion (sp' + 312#64) 48 ∗
            A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s2 ∗
            stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)) ∗ tailF))
    (w8b_frame_noPanic
      (post_ik_some_to_590_noPanic_placed_wpW hC hst1 hpc1 hrun1 hik_lt)
      fun s2 P2 ⟨hst2, evs2, hf2, hent2⟩ => ⟨hst2, evs2, hf2, sepConj_mono_left hent2⟩) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hst2, evs2, hf2, hent2⟩
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre hent2 ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.bind (Qm := fun s3 P3 =>
      PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s3 ∧
      ∃ evs3 : List AllocEvent, FreeOnlyEvs evs3 ∧
        (P3 ⊢ (memRegion (sp' + 312#64) 48 ∗
            A.pool lim (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st))) s3 ∗
            stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)) ∗ tailF))
    (w8b_frame_noPanic
      (post_msg_some_to_5a4_noPanic_placed_wpW hC hst2 hpc2 hrun2 hmsg_lt)
      fun s3 P3 ⟨hst3, evs3, hf3, hent3⟩ => ⟨hst3, evs3, hf3, sepConj_mono_left hent3⟩) ?_
  rintro s3 P3 hpc3 hrun3 ⟨hst3, evs3, hf3, hent3⟩
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre hent3 ?_
  refine w8b_frame_noPanic
    (post_spk_some_to_5b4_noPanic_placed_wpW hC hst3 hpc3 hrun3)
    fun sf Pf ⟨hst4, evs4, hf4, hent4⟩ =>
      ⟨hst4, hbk_lt, hik_lt, hmsg_lt, evs1 ++ evs2 ++ evs3 ++ evs4,
        ((hf1.append hf2).append hf3).append hf4, ?_⟩
  rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append]
  refine Entails.trans (sepConj_mono_left hent4) ?_
  dsimp only [tailF]; apply entails_of_eq; sep_ac_rfl

def PreKey5b4OkNoPanicWPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) : Prop :=
  ∀ (x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost) (st : M.σ) (s0 sf : State)
    (vb b1 : BitVec 8) (bs1 : List (BitVec 8))
    (m : ProtoPreKeySignalMessage) (bk ik msg : List (BitVec 8)) (spkId : BitVec 32)
    (bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberCap kyberPtr kyberLen : BitVec 64)
    (regTag regVal opkTag opkVal kpkTag kpkVal : BitVec 32),
    FitsEnv M lim st (PksmFrom5b4Env vb x.bytes bk ik msg m.kyberPreKeyId m.kyberCiphertext) →
    x.bytes = vb :: b1 :: bs1 → ¬ (vb >>> 4) < 3#8 → ¬ 4#8 < (vb >>> 4) →
    x.bytes.length < 2 ^ 32 →
    CryptoVerification.SignalSession.Cli.RunProofs.Pksm.decodeProto (b1 :: bs1) = some m →
    m.baseKey = some bk → m.identityKey = some ik → m.message = some msg →
    m.signedPreKeyId = some spkId →
    w8bOptU32Cells m.registrationId (regTag, regVal) →
    w8bOptU32Cells m.preKeyId (opkTag, opkVal) →
    w8bOptU32Cells m.kyberPreKeyId (kpkTag, kpkVal) →
    PresenceOkStatePlaced s0 (s0.sp - 608#64) x.ret (BitVec.ofNat 64 x.bytes.length) x.ptr
      kyberCap kyberPtr ikCap msgCap vb sf →
    bkCap.toNat < 2 ^ 63 → ikCap.toNat < 2 ^ 63 → msgCap.toNat < 2 ^ 63 →
    sf.pc = (blkPl_111).base + 1460#64 →
    sf.status = .Running →
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) sf
      (w8bXokPost (A.atState lim st sf) (s0.sp - 608#64) bkCap bkPtr kyberCap kyberPtr kyberLen
          ikCap ikPtr msgCap msgPtr regTag regVal opkTag opkVal spkId kpkTag kpkVal
          m.kyberCiphertext bk ik msg ∗
        w8bPostLoopFramePlaced s0 (s0.sp - 608#64) x.ret x.ptr x.bytes)
      (w8bRetPost A lim (PksmFrom5b4Env vb x.bytes bk ik msg m.kyberPreKeyId m.kyberCiphertext)
        x st s0)
      preKeyNoPanicQp

def PreKeyPresenceErrNoPanicWPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) : Prop :=
  ∀ (x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost) (st : M.σ) (s0 s : State)
    (vb b1 : BitVec 8) (bs1 : List (BitVec 8))
    (m : ProtoPreKeySignalMessage),
    FitsEnv M lim st (PksmPostEnv vb x.bytes m) →
    x.bytes = vb :: b1 :: bs1 → ¬ (vb >>> 4) < 3#8 → ¬ 4#8 < (vb >>> 4) →
    x.bytes.length < 2 ^ 32 →
    CryptoVerification.SignalSession.Cli.RunProofs.Pksm.decodeProto (b1 :: bs1) = some m →
    (m.baseKey = none ∨ m.identityKey = none ∨ m.message = none ∨ m.signedPreKeyId = none) →
    PreKeyLoopExitStatePlaced s0 (s0.sp - 608#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.ptr vb s →
    s.pc = (blkPl_111).base + 1120#64 →
    s.status = .Running →
    s.readReg64 .x24 = 0#64 →
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s
      (wirePreKeyOf A.repAlloc (s0.sp - 608#64 + 312#64) m ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 16 ∗
        memRegion (s0.sp - 608#64 + 440#64) 8 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        memRegion x.ret 248 ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗
        A.pool lim st s ∗ stackAt (s0.sp - 608#64) CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromSubStack)
      (w8bRetPost A lim (PksmPostEnv vb x.bytes m) x st s0)
      preKeyNoPanicQp

theorem preKeyPostLoopOkNoPanicW_placed_of_5b4 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : PksmCalleesPlaced M A lim H)
    (hPresErr : PreKeyPresenceErrNoPanicWPlaced M A lim H)
    (hOk : PreKey5b4OkNoPanicWPlaced M A lim H) :
    PreKeyPostLoopOkNoPanicWPlaced M A lim H := by
  intro x st s0 s vb b1 bs1 m hfit hcons hv3 hv4 hlen hdec hst hpc hrun hx24
  rcases hbkO : m.baseKey with _ | bk
  · exact hPresErr x st s0 s vb b1 bs1 m hfit hcons hv3 hv4 hlen hdec (Or.inl hbkO) hst hpc hrun hx24
  rcases hikO : m.identityKey with _ | ik
  · exact hPresErr x st s0 s vb b1 bs1 m hfit hcons hv3 hv4 hlen hdec (Or.inr (Or.inl hikO))
      hst hpc hrun hx24
  rcases hmsgO : m.message with _ | msg
  · exact hPresErr x st s0 s vb b1 bs1 m hfit hcons hv3 hv4 hlen hdec
      (Or.inr (Or.inr (Or.inl hmsgO))) hst hpc hrun hx24
  rcases hspkO : m.signedPreKeyId with _ | spkId
  · exact hPresErr x st s0 s vb b1 bs1 m hfit hcons hv3 hv4 hlen hdec
      (Or.inr (Or.inr (Or.inr hspkO))) hst hpc hrun hx24
  rw [w8b_memRegion296_split, stackAt_preKeyTryFromSubStack_skipField]
  unfold wirePreKeyOf
  rw [sepExists_sepConj_left]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun g => ?_
  rw [w8b_wirePreKeyAt_some_eq A.repAlloc g _ m hbkO hikO hmsgO hspkO]
  simp only [sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (w8b_optU32At_entails _ m.kyberPreKeyId))))))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun pKpk => ?_
  simp only [sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (w8b_optU32At_entails _ m.preKeyId)))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun pOpk => ?_
  simp only [sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (w8b_optU32At_entails _ m.registrationId))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun pReg => ?_
  simp only [sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (sepConj_mono_left (CryptoVerification.LibsignalTripleRatchet.Wire.optVecU8At_entails_header_buf A.repAlloc g.kyberCt _ m.kyberCiphertext)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun kc => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun kp =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun kl => ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (P' :=
      (memRegion (s0.sp - 608#64 + 16#64) 96 ∗
        vecHeader (s0.sp - 608#64 + 312#64) kc kp kl ∗
        optVecU8Buf A.repAlloc kc kp kl m.kyberCiphertext ∗
        vecHeader (s0.sp - 608#64 + 336#64) g.baseKey.cap g.baseKey.ptr
          (BitVec.ofNat 64 bk.length) ∗ CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc g.baseKey.cap g.baseKey.ptr bk ∗
        vecHeader (s0.sp - 608#64 + 360#64) g.identityKey.cap g.identityKey.ptr
          (BitVec.ofNat 64 ik.length) ∗ CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc g.identityKey.cap g.identityKey.ptr ik ∗
        vecHeader (s0.sp - 608#64 + 384#64) g.message.cap g.message.ptr
          (BitVec.ofNat 64 msg.length) ∗ CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc g.message.cap g.message.ptr msg ∗
        ((s0.sp - 608#64 + 408#64) ↦₃₂ pReg.1.1) ∗ ((s0.sp - 608#64 + 412#64) ↦₃₂ pReg.1.2) ∗
        ((s0.sp - 608#64 + 416#64) ↦₃₂ pOpk.1.1) ∗ ((s0.sp - 608#64 + 420#64) ↦₃₂ pOpk.1.2) ∗
        ((s0.sp - 608#64 + 424#64) ↦₃₂ 1#32) ∗ ((s0.sp - 608#64 + 428#64) ↦₃₂ spkId) ∗
        ((s0.sp - 608#64 + 432#64) ↦₃₂ pKpk.1.1) ∗ ((s0.sp - 608#64 + 436#64) ↦₃₂ pKpk.1.2) ∗
        A.pool lim st s ∗ stackAt (s0.sp - 608#64) (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)) ∗
      w8bPostLoopFramePlaced s0 (s0.sp - 608#64) x.ret x.ptr x.bytes)
    (by unfold w8bPostLoopFramePlaced; apply entails_of_eq; sep_ac_rfl) ?_
  refine w8b_bind_frame_noPanic
    (post_seg1_xok_to_5b4_noPanic_placed_wpW (kyberOpt := m.kyberCiphertext) (bk := bk) (ik := ik)
      (msg := msg) hC hst hpc hrun hx24) ?_
  rintro sm Pm hpcm hrunm ⟨hstm, hbkC, hikC, hmsgC, evs₁, hfree₁, hPm⟩
  have hfit5b4 := fitsEnv_pksmPost_step_freeOnly hbkO hikO hmsgO hspkO hfree₁ hfit
  refine CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.SepWPp.mono_post
    (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left hPm)
      (hOk x (M.stepEvents evs₁ st) s0 sm vb b1 bs1 m bk ik msg spkId g.baseKey.cap g.baseKey.ptr
        g.identityKey.cap g.identityKey.ptr g.message.cap g.message.ptr kc kp kl pReg.1.1 pReg.1.2
        pOpk.1.1 pOpk.1.2 pKpk.1.1 pKpk.1.2 hfit5b4 hcons hv3 hv4 hlen hdec hbkO hikO hmsgO hspkO
        pReg.2 pOpk.2 pKpk.2 hstm hbkC hikC hmsgC hpcm hrunm)) ?_
  intro sf Pf _ _ hq
  exact w8bRetPost_prepend (fun _ h2 => pksmPostEnv_prepend_some hbkO hikO hmsgO hspkO hfree₁ h2) hq

end PostLoop

section BaseKey

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoGames.LibsignalSession (PublicKey SignalProtocolError)
open CryptoGames.LibsignalSessionApi (ProtoPreKeySignalMessage)
open CryptoVerification (LibsignalHooks LibsignalPlacement blkPl_111 lsLogFilterAddr lsmpl)
open CryptoVerification.E2E.Pqxdh.ResponderWire (bv_add_neg_104 bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_16 bv_add_neg_160 bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191 bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40 bv_add_neg_48 bv_add_neg_512 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72 bv_add_neg_8 bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_sub_add_lit' bv_sub_sub_lit keepsFrozenInv_codeRoLoaded post_memRegion48_split33_15 preKeyPlacedProg)
open CryptoVerification.LibsignalTripleRatchet (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Wire (SepWPp deserializeFullPlacedSpec deserializeResult33At entails_of_eq optVecU8Buf slice_rest_entails_vecU8Buf vecU8BufRest vecU8Buf_entails_slice_rest)
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire (BaseKeyOkStatePlaced PresenceOkStatePlaced ecKeyParses ecKeyParses_of_deserialize_ok pkOf pkOf_bytes_of_ecKeyParses pkOf_of_deserialize_ok seg1SpillsAtW w8bOptU32Cells w8bPostLoopFramePlaced w8bRowKFrame w8bRowKPostPlaced w8bXokPost)
open Arm64 ProofLib.ProgramReflection
open ProofLib hiding SepWP SepWPp
open LibsignalBinary.Heap (AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget (PksmCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget (w8bRetPost PksmFrom5b4Env PksmFrom684Env pksmFrom5b4Env_of_ok_eq)

private abbrev bk_of_sepWP_frozen_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk
private abbrev bk_of_sepWP_end_pk :=
  @w8b_of_sepWP_end_noPanic_pk
private abbrev bk_call_noPanic_pk :=
  @w8b_call_noPanic_pk

private theorem bk_sepWPp_introState {prog : Program} {ret : BitVec 64} {s1 : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ s_mid, s_mid = s1 → SepWPp prog ret s_mid P Q Qp) :
    SepWPp prog ret s1 P Q Qp :=
  h s1 rfl

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512

theorem post_deser_bk_call_noPanic_placed_wpW [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr bkCap bkPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    (bk : List (BitVec 8))
    (hst : PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (blkPl_111).base + 1460#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1472#64) s
      (((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
        memRegion (sp' + 312#64) 48 ∗ CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗ lsLogOff ∗
        A.pool lim st s)
      (fun sf Pf =>
        PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb sf ∧
        (Pf ⊢ ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
          deserializeResult33At (sp' + 312#64) (CryptoGames.LibsignalSession.PublicKey.deserialize bk) ∗
          memRegion (sp' + 345#64) 15 ∗ CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗ lsLogOff ∗
          A.pool lim st sf))
      preKeyNoPanicQp := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  have hcallDeser := hC.deserializeFull
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (vecU8Buf_entails_slice_rest A.repAlloc bkCap bkPtr bk))))) ?_
  simp only [sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (P' :=
      ⌜bk.length ≤ bkCap.toNat ∧ bkCap.toNat < 2 ^ 63 ∧ bkPtr ≠ 0⌝ ∗
      (((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
        memRegion (sp' + 312#64) 48 ∗ (bkPtr ↦ₛ bk) ∗ vecU8BufRest A.repAlloc bkCap bkPtr bk ∗
        lsLogOff ∗ A.pool lim st s))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun ⟨hbk_le, hbk_lt, _⟩ => ?_
  have hbk_len_lt : bk.length < 2 ^ 63 := Nat.lt_of_le_of_lt hbk_le hbk_lt
  have hbk_toNat : (BitVec.ofNat 64 bk.length).toNat = bk.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine bk_of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 201) ?_
  wp_steps_sync_pool (lsmpl.base 201)
  refine CryptoVerification.E2E.Pqxdh.ResponderWire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hcl1 => ?_
  refine bk_sepWPp_introState fun s1 hs1 => ?_
  rw [← hs1]
  have h48_split := post_memRegion48_split33_15 sp'
  have hlog : lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (P' := ((bkPtr ↦ₛ bk) ∗ memRegion (sp' + 312#64) 33 ∗ (lsLogFilterAddr ↦₆₄ 0#64)) ∗
      (((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
        memRegion (sp' + 345#64) 15 ∗ vecU8BufRest A.repAlloc bkCap bkPtr bk ∗
        A.pool lim st s1))
    (by rw [h48_split, hlog]; apply entails_of_eq; sep_ac_rfl) ?_
  refine bk_call_noPanic_pk keepsFrozenInv_codeRoLoaded (bkPtr, bk, sp' + 312#64) hcallDeser
    (by subst hs1; simp_all [arm64_norm])
    (by subst hs1; simp_all [arm64_norm])
    (by subst hs1; simpa [State.spAligned, arm64_norm] using hsp)
    (by subst hs1; exact hcl1)
    (ret_pc := (blkPl_111).base + 1472#64) (by subst hs1; simp_all [arm64_norm])
    (T := (bkPtr ↦ₛ bk) ∗ memRegion (sp' + 312#64) 33 ∗ (lsLogFilterAddr ↦₆₄ 0#64))
    (φ := bkPtr = bkPtr ∧ (BitVec.ofNat 64 bk.length).toNat = bk.length ∧
      sp' + 312#64 = sp' + 312#64 ∧ bk.length < 2 ^ 63)
    (by subst hs1; simp_all [withVmPreserved, deserializeFullPlacedSpec, arm64_norm])
    ⟨rfl, hbk_toNat, rfl, hbk_len_lt⟩ rfl ?_
  clear hcallDeser
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [withVmPreserved, deserializeFullPlacedSpec]; simp only [sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hvm => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
  refine bk_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2
    (CryptoVerification.E2E.Pqxdh.ResponderWire.SepWP.done hpc2 hrun2 fun hcl3 => ?_)
  have hsp1_eq : s1.sp = sp' := by subst hs1; tryFromPost_sp [hsp_eq]
  refine ⟨⟨⟨by rw [hsp2, hsp1_eq], hsp2_align, hcl3,
      by subst hs1; simp [htr2, htr, arm64_norm]⟩,
    by subst hs1; simp [hx29_2, hx29, arm64_norm],
    by subst hs1; simp [hx28_2, hx28, arm64_norm],
    by subst hs1; simp [hx27_2, hx27, arm64_norm],
    by subst hs1; simp [hx26_2, hx26, arm64_norm],
    by subst hs1; simp [hx25_2, hx25, arm64_norm],
    by subst hs1; simp [hx24_2, hx24, arm64_norm],
    by subst hs1; simp [hx23_2, hx23, arm64_norm],
    by subst hs1; simp [hx22_2, hx22, arm64_norm],
    by subst hs1; simp [hx21_2, hx21, arm64_norm],
    by subst hs1; simp [hx20_2, hx20, arm64_norm],
    by subst hs1; simp [hx19_2, hx19, arm64_norm]⟩, ?_⟩
  have hrepack := slice_rest_entails_vecU8Buf A.repAlloc bkCap bkPtr bk
  rw [← hlog, ← A.pool_transport lim st s1 s2 hvm]
  refine Entails.trans (Q :=
      ((bkPtr ↦ₛ bk) ∗ vecU8BufRest A.repAlloc bkCap bkPtr bk) ∗
      (((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
        deserializeResult33At (sp' + 312#64) (CryptoGames.LibsignalSession.PublicKey.deserialize bk) ∗
        memRegion (sp' + 345#64) 15 ∗ lsLogOff ∗ A.pool lim st s2))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  exact Entails.trans (sepConj_mono_left hrepack) (by apply entails_of_eq; sep_ac_rfl)

theorem post_deser_bk_ok_to_684_noPanic_placed_wpW [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {pk : PublicKey}
    (hdeser : CryptoGames.LibsignalSession.PublicKey.deserialize bk = .ok pk)
    (hst : PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (blkPl_111).base + 1472#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1668#64) s
      (deserializeResult33At (sp' + 312#64) (CryptoGames.LibsignalSession.PublicKey.deserialize bk) ∗
        memRegion (sp' + 345#64) 15 ∗ A.pool lim st s)
      (fun sf Pf =>
        BaseKeyOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb bk pk sf ∧
        (Pf ⊢ ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
          memRegion (sp' + 345#64) 15 ∗ A.pool lim st sf))
      preKeyNoPanicQp := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  have hec : ecKeyParses bk = true := ecKeyParses_of_deserialize_ok hdeser
  have hpkOf : pkOf bk = pk := pkOf_of_deserialize_ok hdeser
  have hbytes : (pkOf bk).bytes.toList = (bk.take 33).drop 1 := pkOf_bytes_of_ecKeyParses hec
  have hpk_bytes : pk.bytes.toList = (bk.take 33).drop 1 := by rw [← hpkOf, hbytes]
  rw [hdeser]; dsimp only [deserializeResult33At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine bk_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps_sync_pool ((blkPl_111).base + 1668#64)
  refine CryptoVerification.E2E.Pqxdh.ResponderWire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hcl1 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
      by simp [htr, arm64_norm]⟩, hec, hpkOf, hbytes,
    by simp [hx29, arm64_norm], by simp [hx28, arm64_norm], by simp [hx27, arm64_norm],
    by simp [hx26, arm64_norm], by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
    by simp [hx23, arm64_norm], by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
    by simp [hx20, arm64_norm], by simp [hx19, arm64_norm]⟩, ?_⟩
  rw [hpk_bytes]; apply entails_of_eq; sep_ac_rfl

theorem post_deser_bk_ok_full_to_684_noPanic_placed_wpW [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr bkCap bkPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {pk : PublicKey}
    (hdeser : CryptoGames.LibsignalSession.PublicKey.deserialize bk = .ok pk)
    (hst : PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (blkPl_111).base + 1460#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1668#64) s
      (((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
        memRegion (sp' + 312#64) 48 ∗ CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗ lsLogOff ∗
        A.pool lim st s)
      (fun sf Pf =>
        BaseKeyOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb bk pk sf ∧
        (Pf ⊢ ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
          ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
          memRegion (sp' + 345#64) 15 ∗ CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗ lsLogOff ∗
          A.pool lim st sf))
      preKeyNoPanicQp := by
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.bind (post_deser_bk_call_noPanic_placed_wpW hC bk hst hpc hrun) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hst1, hent1⟩
  let restF := ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
    CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗ lsLogOff
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (P' := (deserializeResult33At (sp' + 312#64) (CryptoGames.LibsignalSession.PublicKey.deserialize bk) ∗
      memRegion (sp' + 345#64) 15 ∗ A.pool lim st s1) ∗ restF)
    (Entails.trans hent1 (by dsimp only [restF]; apply entails_of_eq; sep_ac_rfl)) ?_
  refine w8b_frame_noPanic
    (post_deser_bk_ok_to_684_noPanic_placed_wpW hdeser hst1 hpc1 hrun1)
    fun sf Pf ⟨hbst, hent2⟩ => ⟨hbst, ?_⟩
  refine Entails.trans (sepConj_mono_left hent2) ?_
  dsimp only [restF]; apply entails_of_eq; sep_ac_rfl

def PreKey684OkNoPanicWPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) : Prop :=
  ∀ (x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost) (st : M.σ) (s0 sf : State)
    (vb b1 : BitVec 8) (bs1 : List (BitVec 8))
    (m : ProtoPreKeySignalMessage) (bk ik msg : List (BitVec 8)) (spkId : BitVec 32)
    (pk : PublicKey)
    (bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberCap kyberPtr kyberLen : BitVec 64)
    (regTag regVal opkTag opkVal kpkTag kpkVal : BitVec 32),
    FitsEnv M lim st (PksmFrom684Env vb x.bytes ik msg m.kyberPreKeyId m.kyberCiphertext) →
    x.bytes = vb :: b1 :: bs1 → ¬ (vb >>> 4) < 3#8 → ¬ 4#8 < (vb >>> 4) →
    x.bytes.length < 2 ^ 32 →
    CryptoVerification.SignalSession.Cli.RunProofs.Pksm.decodeProto (b1 :: bs1) = some m →
    m.baseKey = some bk → m.identityKey = some ik → m.message = some msg →
    m.signedPreKeyId = some spkId →
    w8bOptU32Cells m.registrationId (regTag, regVal) →
    w8bOptU32Cells m.preKeyId (opkTag, opkVal) →
    w8bOptU32Cells m.kyberPreKeyId (kpkTag, kpkVal) →
    CryptoGames.LibsignalSession.PublicKey.deserialize bk = .ok pk →
    BaseKeyOkStatePlaced s0 (s0.sp - 608#64) x.ret (BitVec.ofNat 64 x.bytes.length) x.ptr
      kyberCap kyberPtr ikCap msgCap vb bk pk sf →
    bkCap.toNat < 2 ^ 63 → ikCap.toNat < 2 ^ 63 → msgCap.toNat < 2 ^ 63 →
    sf.pc = (blkPl_111).base + 1668#64 →
    sf.status = .Running →
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) sf
      (w8bRowKPostPlaced (A.atState lim st sf) (s0.sp - 608#64) bkCap bkPtr bk ∗
        w8bRowKFrame (A.atState lim st sf) s0 (s0.sp - 608#64) x.ret x.ptr bkCap kyberCap kyberPtr
          kyberLen ikCap ikPtr msgCap msgPtr regTag regVal opkTag opkVal spkId kpkTag kpkVal
          m.kyberCiphertext ik msg x.bytes)
      (w8bRetPost A lim (PksmFrom684Env vb x.bytes ik msg m.kyberPreKeyId m.kyberCiphertext)
        x st s0)
      preKeyNoPanicQp

def PreKeyBaseKeyErrNoPanicWPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) : Prop :=
  ∀ (x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost) (st : M.σ) (s0 sf : State)
    (vb b1 : BitVec 8) (bs1 : List (BitVec 8))
    (m : ProtoPreKeySignalMessage) (bk ik msg : List (BitVec 8)) (spkId : BitVec 32)
    (e : SignalProtocolError)
    (bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberCap kyberPtr kyberLen : BitVec 64)
    (regTag regVal opkTag opkVal kpkTag kpkVal : BitVec 32),
    FitsEnv M lim st (PksmFrom5b4Env vb x.bytes bk ik msg m.kyberPreKeyId m.kyberCiphertext) →
    x.bytes = vb :: b1 :: bs1 → ¬ (vb >>> 4) < 3#8 → ¬ 4#8 < (vb >>> 4) →
    x.bytes.length < 2 ^ 32 →
    CryptoVerification.SignalSession.Cli.RunProofs.Pksm.decodeProto (b1 :: bs1) = some m →
    m.baseKey = some bk → m.identityKey = some ik → m.message = some msg →
    m.signedPreKeyId = some spkId →
    w8bOptU32Cells m.registrationId (regTag, regVal) →
    w8bOptU32Cells m.preKeyId (opkTag, opkVal) →
    w8bOptU32Cells m.kyberPreKeyId (kpkTag, kpkVal) →
    CryptoGames.LibsignalSession.PublicKey.deserialize bk = .error e →
    PresenceOkStatePlaced s0 (s0.sp - 608#64) x.ret (BitVec.ofNat 64 x.bytes.length) x.ptr
      kyberCap kyberPtr ikCap msgCap vb sf →
    bkCap.toNat < 2 ^ 63 → ikCap.toNat < 2 ^ 63 → msgCap.toNat < 2 ^ 63 →
    sf.pc = (blkPl_111).base + 1460#64 →
    sf.status = .Running →
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) sf
      (w8bXokPost (A.atState lim st sf) (s0.sp - 608#64) bkCap bkPtr kyberCap kyberPtr kyberLen
          ikCap ikPtr msgCap msgPtr regTag regVal opkTag opkVal spkId kpkTag kpkVal
          m.kyberCiphertext bk ik msg ∗
        w8bPostLoopFramePlaced s0 (s0.sp - 608#64) x.ret x.ptr x.bytes)
      (w8bRetPost A lim (PksmFrom5b4Env vb x.bytes bk ik msg m.kyberPreKeyId m.kyberCiphertext)
        x st s0)
      preKeyNoPanicQp

theorem preKey5b4OkNoPanicW_placed_of_684 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    (hErr : PreKeyBaseKeyErrNoPanicWPlaced M A lim H)
    (hOk : PreKey684OkNoPanicWPlaced M A lim H) :
    PreKey5b4OkNoPanicWPlaced M A lim H := by
  intro x st s0 sf vb b1 bs1 m bk ik msg spkId bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberCap
    kyberPtr kyberLen regTag regVal opkTag opkVal kpkTag kpkVal hfit hcons hv3 hv4 hlen hdec hbkO
    hikO hmsgO hspkO hreg hopk hkpk hst hbkC hikC hmsgC hpc hrun
  rcases hd : CryptoGames.LibsignalSession.PublicKey.deserialize bk with e | pk
  · exact hErr x st s0 sf vb b1 bs1 m bk ik msg spkId e bkCap bkPtr ikCap ikPtr msgCap msgPtr
      kyberCap kyberPtr kyberLen regTag regVal opkTag opkVal kpkTag kpkVal hfit hcons hv3 hv4 hlen
      hdec hbkO hikO hmsgO hspkO hreg hopk hkpk hd hst hbkC hikC hmsgC hpc hrun
  have henv_eq := pksmFrom5b4Env_of_ok_eq (vb := vb) (xBytes := x.bytes) (ik := ik) (msg := msg)
    (kpkOpt := m.kyberPreKeyId) (kyberOpt := m.kyberCiphertext) hd
  rw [henv_eq] at hfit ⊢
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (P' :=
      (((s0.sp - 608#64 + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗
        ((s0.sp - 608#64 + 80#64) ↦₆₄ bkPtr) ∗
        memRegion (s0.sp - 608#64 + 312#64) 48 ∗ CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗
        lsLogOff ∗ A.pool lim st sf) ∗
      w8bRowKFrame A.repAlloc s0 (s0.sp - 608#64) x.ret x.ptr bkCap kyberCap kyberPtr kyberLen
        ikCap ikPtr msgCap msgPtr regTag regVal opkTag opkVal spkId kpkTag kpkVal
        m.kyberCiphertext ik msg x.bytes)
    (by
      unfold w8bXokPost w8bPostLoopFramePlaced w8bRowKFrame seg1SpillsAtW
      simp only [LibsignalBinary.Heap.RustCliAllocBudget.atState, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
        CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf, optVecU8Buf, emp_sepConj]
      apply entails_of_eq; sep_ac_rfl) ?_
  refine w8b_bind_frame_noPanic (post_deser_bk_ok_full_to_684_noPanic_placed_wpW hC hd hst hpc hrun) ?_
  rintro sm Pm hpcm hrunm ⟨hbst, hPm⟩
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (Entails.trans (sepConj_mono_left hPm) ?_)
    (hOk x st s0 sm vb b1 bs1 m bk ik msg spkId pk bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberCap
      kyberPtr kyberLen regTag regVal opkTag opkVal kpkTag kpkVal hfit hcons hv3 hv4 hlen hdec hbkO
      hikO hmsgO hspkO hreg hopk hkpk hd hbst hbkC hikC hmsgC hpcm hrunm)
  unfold w8bRowKPostPlaced w8bRowKFrame
  simp only [LibsignalBinary.Heap.RustCliAllocBudget.atState, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
    CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf, optVecU8Buf, emp_sepConj]
  apply entails_of_eq; sep_ac_rfl

end BaseKey

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bNoPanicAuxA
