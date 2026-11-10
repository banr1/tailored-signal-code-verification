/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.Epilogue
public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.Defs
public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.RecordCodecs.Deps
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.ErrTails
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.ErrTailsBudget
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `SignedPreKeyRecordStructure::decode` Convergence and Epilogue

`RustCliAllocBudget`-threaded relocatable convergence and `Vec<u8>` cleanup proofs (`+656` to
return) on Block `562`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.EpilogueBudget

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification
open CryptoVerification.RecordCodecs.Placed
open LibsignalBinary.Heap
open LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification.RecordCodecsBinary (DecodeGhost sepWPp_of_sepWP_lscro signedDecodeResultAt signedDecodeStack)
open CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers (SpkCfg SpkGhost SpkSavedRegs spkCalleeSavedAt spkCfgLegacy spkConvergeMem spkErr88_intro spkMemRegion88_err_unpack spkMemRegion88_unpack spkOff_converge spkOff_freePrivRet spkOff_freePub spkOff_freePubRet spkOff_freeSigRet spkOff_retOk spkOk88_intro spkStack_unsplit spkStruct88_pack spkStructAt spkStructOf spk_vecU8Buf_zero_elim)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget (OptByteFreeEnv SignedHooksPlaced SpkDecodeEnv SpkEpilogueFreeEnv SpkLoopEnv)
open LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.DefsBudget (SpkConvergeStatePlaced noPanicQp sepWPp_end_noPanic_lscro spk_call_noPanic_lscro spk_dealloc_placed_ok)
open LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.ErrTailsBudget (sepWPp_mono_post)
attribute [local arm64_norm] BitVec.toNat_zero

set_option maxRecDepth 2000000
attribute [local irreducible] Program.fetch Program.externAt?

private theorem signedDecodeResultAt_eq_repAlloc (B : RustAlloc) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (h : B.live = A.live) (ret : BitVec 64)
    (out : Option SignedPreKeyRecordStructure) :
    signedDecodeResultAt B ret out = signedDecodeResultAt A.repAlloc ret out := by
  cases B; dsimp only at h; subst h; cases out <;> rfl

private theorem signedDecodeResultAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (ret : BitVec 64)
    (out : Option SignedPreKeyRecordStructure) :
    signedDecodeResultAt (A.atState lim st s) ret out = signedDecodeResultAt A.repAlloc ret out := rfl

private theorem spkSub224_offs (sp : BitVec 64) :
    (sp - 224#64 + 16#64 = sp - 208#64) ∧
    (sp - 224#64 + 24#64 = sp - 200#64) ∧
    (sp - 224#64 + 32#64 = sp - 192#64) ∧
    (sp - 224#64 + 40#64 = sp - 184#64) ∧
    (sp - 224#64 + 48#64 = sp - 176#64) ∧
    (sp - 224#64 + 56#64 = sp - 168#64) ∧
    (sp - 224#64 + 64#64 = sp - 160#64) ∧
    (sp - 224#64 + 72#64 = sp - 152#64) ∧
    (sp - 224#64 + 80#64 = sp - 144#64) ∧
    (sp - 224#64 + 88#64 = sp - 136#64) ∧
    (sp - 224#64 + 96#64 = sp - 128#64) ∧
    (sp - 224#64 + 104#64 = sp - 120#64) ∧
    (sp - 224#64 + 112#64 = sp - 112#64) := by
  refine ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
    by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

abbrev spkEpilogueTail (A : RustAlloc) (s0 : State) (x : DecodeGhost)
    (out : Option SignedPreKeyRecordStructure) : SepProp :=
  signedDecodeResultAt A x.ret out ∗
    memRegion (s0.sp - 224#64) 16 ∗
    memRegion (s0.sp - 224#64 + 16#64) 88 ∗
    ((s0.sp - 224#64 + 104#64) ↦₆₄ (s0.sp - 224#64)) ∗
    memRegion (s0.sp - 224#64 + 112#64) 48 ∗
    spkCalleeSavedAt (s0.sp - 224#64) s0 ∗
    (x.bytesA ↦ₛ x.bytes) ∗ A.pool ∗
    stackAt (s0.sp - 224#64) (CryptoVerification.SpqrV1.Varint.skipField3Stack 100)

abbrev spkRetPostPlaced {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (E : List AllocEvent → Prop)
    (s0 : State) (x : DecodeGhost)
    (out : Option SignedPreKeyRecordStructure) : State → SepProp → Prop :=
  fun sf Pf =>
    sf.sp = s0.sp ∧
      (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
      (Pf ⊢ ⌜sf.trace = s0.trace⌝ ∗
        (∃∗ evs : List AllocEvent, ⌜E evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
        signedDecodeResultAt A.repAlloc x.ret out ∗
        (x.bytesA ↦ₛ x.bytes) ∗ stackAt s0.sp signedDecodeStack)

theorem spkRetPostPlaced_prepend {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs₁ : List AllocEvent}
    {E₂ E : List AllocEvent → Prop}
    (hstep : ∀ evs₂, E₂ evs₂ → E (evs₁ ++ evs₂))
    (s0 : State) (x : DecodeGhost) (out : Option SignedPreKeyRecordStructure)
    (sf : State) (Pf : SepProp)
    (hq : spkRetPostPlaced A lim (M.stepEvents evs₁ st) E₂ s0 x out sf Pf) :
    spkRetPostPlaced A lim st E s0 x out sf Pf := by
  rcases hq with ⟨hsp, hcs, hent⟩
  refine ⟨hsp, hcs, Entails.trans hent (sepConj_mono_right (sepConj_mono_left ?_))⟩
  refine Entails.sepExists_elim fun evs₂ => Entails.pure_left fun he2 => ?_
  refine Entails.trans ?_
    (Entails.sepExists_intro (P := fun evs => ⌜E evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf)
      (evs₁ ++ evs₂))
  rw [M.stepEvents_append]
  exact Entails.pure_right (hstep evs₂ he2) (Entails.refl _)

private def spkDestWords88 (ret r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : BitVec 64) : SepProp :=
  (ret ↦₆₄ r0) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r2) ∗
    ((ret + 24#64) ↦₆₄ r3) ∗ ((ret + 32#64) ↦₆₄ r4) ∗ ((ret + 40#64) ↦₆₄ r5) ∗
    ((ret + 48#64) ↦₆₄ r6) ∗ ((ret + 56#64) ↦₆₄ r7) ∗ ((ret + 64#64) ↦₆₄ r8) ∗
    ((ret + 72#64) ↦₆₄ r9) ∗ ((ret + 80#64) ↦₆₄ r10)

private def spkRawWords88 (spBase : BitVec 64) (g : SpkGhost)
    (m : SignedPreKeyRecordStructure) (pad32 : BitVec 32) : SepProp :=
  ((spBase + 16#64) ↦₆₄ g.pub.cap) ∗ ((spBase + 24#64) ↦₆₄ g.pub.ptr) ∗
    ((spBase + 32#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
    ((spBase + 40#64) ↦₆₄ g.priv.cap) ∗ ((spBase + 48#64) ↦₆₄ g.priv.ptr) ∗
    ((spBase + 56#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
    ((spBase + 64#64) ↦₆₄ g.sig.cap) ∗ ((spBase + 72#64) ↦₆₄ g.sig.ptr) ∗
    ((spBase + 80#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
    ((spBase + 88#64) ↦₆₄ m.timestamp) ∗ ((spBase + 96#64) ↦₆₄ (pad32 ++ m.id))

private theorem spkRawWords88_pack (spBase : BitVec 64) (g : SpkGhost)
    (m : SignedPreKeyRecordStructure) (pad32 : BitVec 32) :
    spkRawWords88 spBase g m pad32 ⊢ memRegion (spBase + 16#64) 88 := by
  have hp96 : ((spBase + 96#64) ↦₃₂ m.id) ∗ ((spBase + 100#64) ↦₃₂ pad32) =
      ((spBase + 96#64) ↦₆₄ (pad32 ++ m.id)) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair (spBase + 96#64) m.id pad32
  unfold spkRawWords88
  rw [← hp96]
  simpa [vecHeader, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
    spkStruct88_pack spBase g.pub.cap g.pub.ptr (BitVec.ofNat 64 m.publicKey.length)
      g.priv.cap g.priv.ptr (BitVec.ofNat 64 m.privateKey.length)
      g.sig.cap g.sig.ptr (BitVec.ofNat 64 m.signature.length)
      m.timestamp m.id pad32

theorem retErr_736_placed_wp [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {x : DecodeGhost} {s0 s : State}
    {out : Option SignedPreKeyRecordStructure}
    (hst : SpkConvergeStatePlaced s0 (s0.sp - 224#64) x.ret s)
    (hpc : s.pc = (blkPl_562).base + spkOff_freeSigRet)
    (hrun : s.status = .Running) :
    Wire.SepWPp (lsProg_562 H) (s0.readReg64 .x30) s
      (spkEpilogueTail (A.atState lim st s) s0 x out)
      (spkRetPostPlaced A lim st (fun evs => evs = []) s0 x out) (noPanicQp s0) := by
  rcases hst with ⟨hsp_eq, _hsp, hcrl, htr, _hx24, _hx19, hsaved⟩
  unfold spkEpilogueTail spkCalleeSavedAt
  dsimp only [RustCliAllocBudget.atState]
  simp only [sepConj_assoc]
  refine sepWPp_end_noPanic_lscro hcrl ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro _
  refine ⟨by simp [arm64_norm], fun hv => ?_, ?_⟩
  · refine ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simpa [arm64_norm] using hsaved.x25, by simpa [arm64_norm] using hsaved.x26,
      by simpa [arm64_norm] using hsaved.x27, by simpa [arm64_norm] using hsaved.x28,
      by simp [arm64_norm], hv⟩
  · rw [pure_true_emp (by simp [htr, arm64_norm]), emp_sepConj]
    have hstk := spkStack_unsplit spkCfgLegacy s0.sp s0
    dsimp only [spkCfgLegacy, SpkCfg.subStack] at hstk
    unfold spkCalleeSavedAt at hstk
    refine Entails.trans ?_
      (sepConj_mono
        (Entails.sepExists_right [] (Entails.pure_right rfl (Entails.refl _)))
        (sepConj_mono_right (sepConj_mono_right hstk)))
    dsimp only [AllocCostModel.stepEvents, List.foldl]
    rw [signedDecodeResultAt_eq_repAlloc _ A rfl]
    apply entails_of_eq
    simp only [RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
      RustCliAllocBudget.pool_writeReg, RustCliAllocBudget.pool_setPC,
      RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_advancePC,
      hsp_eq, arm64_norm]
    ac_rfl

theorem retOk_800_placed_wp [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {x : DecodeGhost} {s0 s : State}
    {out : Option SignedPreKeyRecordStructure}
    (hst : SpkConvergeStatePlaced s0 (s0.sp - 224#64) x.ret s)
    (hpc : s.pc = (blkPl_562).base + spkOff_retOk)
    (hrun : s.status = .Running) :
    Wire.SepWPp (lsProg_562 H) (s0.readReg64 .x30) s
      (spkEpilogueTail (A.atState lim st s) s0 x out)
      (spkRetPostPlaced A lim st (fun evs => evs = []) s0 x out) (noPanicQp s0) := by
  rcases hst with ⟨hsp_eq, _hsp, hcrl, htr, _hx24, _hx19, hsaved⟩
  unfold spkEpilogueTail spkCalleeSavedAt
  dsimp only [RustCliAllocBudget.atState]
  simp only [sepConj_assoc]
  refine sepWPp_end_noPanic_lscro hcrl ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro _
  refine ⟨by simp [arm64_norm], fun hv => ?_, ?_⟩
  · refine ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simpa [arm64_norm] using hsaved.x25, by simpa [arm64_norm] using hsaved.x26,
      by simpa [arm64_norm] using hsaved.x27, by simpa [arm64_norm] using hsaved.x28,
      by simp [arm64_norm], hv⟩
  · rw [pure_true_emp (by simp [htr, arm64_norm]), emp_sepConj]
    have hstk := spkStack_unsplit spkCfgLegacy s0.sp s0
    dsimp only [spkCfgLegacy, SpkCfg.subStack] at hstk
    unfold spkCalleeSavedAt at hstk
    refine Entails.trans ?_
      (sepConj_mono
        (Entails.sepExists_right [] (Entails.pure_right rfl (Entails.refl _)))
        (sepConj_mono_right (sepConj_mono_right hstk)))
    dsimp only [AllocCostModel.stepEvents, List.foldl]
    rw [signedDecodeResultAt_eq_repAlloc _ A rfl]
    apply entails_of_eq
    simp only [RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
      RustCliAllocBudget.pool_writeReg, RustCliAllocBudget.pool_setPC,
      RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_advancePC,
      hsp_eq, arm64_norm]
    ac_rfl

theorem freeSig_716_placed_wp [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hH : SignedHooksPlaced M A lim H)
    {x : DecodeGhost} {s0 s : State}
    {sigCap sigPtr : BitVec 64} {sigBs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure}
    (hst : SpkConvergeStatePlaced s0 (s0.sp - 224#64) x.ret s)
    (hpc : s.pc = (blkPl_562).base + spkOff_freePrivRet)
    (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = sigCap) (hx21 : s.readReg64 .x21 = sigPtr) :
    Wire.SepWPp (lsProg_562 H) (s0.readReg64 .x30) s
      (vecU8Buf A.repAlloc sigCap sigPtr sigBs ∗ spkEpilogueTail (A.atState lim st s) s0 x out)
      (spkRetPostPlaced A lim st OptByteFreeEnv s0 x out) (noPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcrl, htr, hx24, hx19, hsaved⟩
  by_cases hcap : sigCap = 0#64
  · subst hcap
    refine Wire.SepWPp.mono_pre (sepConj_mono_left (spk_vecU8Buf_zero_elim A.repAlloc sigPtr sigBs)) ?_
    rw [emp_sepConj]
    have h20 : s.readReg64 (Reg.gpr 20#5) = 0#64 := hx20
    refine sepWPp_mono_post
      (spkRetPostPlaced_prepend A lim st (evs₁ := []) (E₂ := fun evs => evs = [])
        (fun _ h => by subst h; exact Or.inl rfl) s0 x out) ?_
    dsimp only [AllocCostModel.stepEvents, List.foldl]
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_freeSigRet) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcrl1
    refine Wire.SepWPp.mono_pre ?_
      (retErr_736_placed_wp (A := A) (lim := lim) (st := st) (x := x) (s0 := s0) (out := out)
        ⟨by simp [hsp_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
         hcrl1, by simp [htr, arm64_norm], by simp [hx24, arm64_norm], by simp [hx19, arm64_norm],
         ⟨by simpa [arm64_norm] using hsaved.x25, by simpa [arm64_norm] using hsaved.x26,
          by simpa [arm64_norm] using hsaved.x27, by simpa [arm64_norm] using hsaved.x28⟩⟩
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]))
    unfold spkEpilogueTail; simp only [signedDecodeResultAt_atState]; dsimp only [RustCliAllocBudget.atState]
    apply entails_of_eq
    simp only [RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_setPC, arm64_norm]
  · refine Wire.SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_dealloc A.repAlloc sigCap sigPtr sigBs hcap)) ?_
    unfold spkEpilogueTail; simp only [signedDecodeResultAt_atState]; dsimp only [RustCliAllocBudget.atState]; simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hcall := spk_dealloc_placed_ok hH
    have hstack := stackAt_sub_split (s0.sp - 224#64) allocHookStack (CryptoVerification.SpqrV1.Varint.skipField3Stack 100)
    have h20 : s.readReg64 (Reg.gpr 20#5) = sigCap := hx20
    have h21 : s.readReg64 (Reg.gpr 21#5) = sigPtr := hx21
    have hbeq : (sigCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    refine sepWPp_of_sepWP_lscro hcrl (mid := lsρ lsRustDeallocSym) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [lsρ, lsRustDeallocSym, arm64_norm])
      (by simp [hrun, arm64_norm]) ?_
    intro hcrl1
    refine spk_call_noPanic_lscro (sigPtr, sigCap.toNat, 1, st) hcall
      (by simp [lsρ, lsRustDeallocSym, arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
      (ret_pc := (blkPl_562).base + spkOff_freeSigRet) (by simp [arm64_norm])
      (T := A.pool lim st s ∗ A.repAlloc.live sigPtr sigCap.toNat 1 ∗ memRegion sigPtr sigCap.toNat ∗
        stackAt (s0.sp - 224#64) allocHookStack)
      (φ := True)
      (by simp (config := { decide := true }) [rustCliDeallocBudgetSpec, RustCliAllocBudget.repAlloc,
        RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_setPC, hsp_eq, h20, h21, hbeq,
        arm64_norm, wp_norm]) trivial
      (by rw [hstack]; sep_focus) ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
    dsimp only [rustCliDeallocBudgetSpec]; rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun ⟨hpres, _⟩ => ?_
    have htr2 : s2.trace = s.trace := by simpa [arm64_norm] using hpres.2.1
    have hsp2_eq : s2.sp = s0.sp - 224#64 := by simpa [hsp_eq, arm64_norm] using hsp2
    have hx19_2 : s2.readReg64 .x19 = x.ret := by simpa [hx19, arm64_norm] using hcs2.1
    have hx24_2 : s2.readReg64 .x24 = s0.sp - 224#64 + 16#64 :=
      by simpa [hx24, arm64_norm] using hcs2.2.2.2.2.2.1
    have hsaved2 : SpkSavedRegs s0 s2 :=
      ⟨by simpa [hsaved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
       by simpa [hsaved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
    refine sepWPp_mono_post
      (spkRetPostPlaced_prepend A lim st (evs₁ := rustDeallocEvents sigCap.toNat 1)
        (E₂ := fun evs => evs = [])
        (fun _ h => by subst h; rw [List.append_nil]; exact Or.inr ⟨sigCap.toNat, hpos, by omega, rfl⟩)
        s0 x out) ?_
    refine Wire.SepWPp.mono_pre ?_
      (retErr_736_placed_wp (A := A) (lim := lim)
        (st := M.stepEvents (rustDeallocEvents sigCap.toNat 1) st)
        (x := x) (s0 := s0) (s := s2) (out := out)
        ⟨hsp2_eq, hsp2_align, hcrl2, htr2.trans htr, hx24_2, hx19_2, hsaved2⟩
        hpc2 hrun2)
    unfold spkEpilogueTail; simp only [signedDecodeResultAt_atState]; dsimp only [RustCliAllocBudget.atState]
    have hb1 : s0.sp - 224#64 + 16#64 = s0.sp - 208#64 := by bv_omega
    have hb2 : s0.sp - 224#64 + 104#64 = s0.sp - 120#64 := by bv_omega
    have hb3 : s0.sp - 224#64 + 112#64 = s0.sp - 112#64 := by bv_omega
    have hb4 : s0.sp - 224#64 - BitVec.ofNat 64 (CryptoVerification.SpqrV1.Varint.skipField3Stack 100) = s0.sp - 18240#64 := by
      change s0.sp - 224#64 - 18016#64 = s0.sp - 18240#64; bv_omega
    apply entails_of_eq; rw [hstack, hb1, hb2, hb3, hb4]; simp only [hsp_eq, hsp2_eq, arm64_norm]; ac_rfl

theorem freePriv_696_placed_wp [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hH : SignedHooksPlaced M A lim H)
    {x : DecodeGhost} {s0 s : State}
    {privCap privPtr sigCap sigPtr : BitVec 64} {privBs sigBs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure}
    (hst : SpkConvergeStatePlaced s0 (s0.sp - 224#64) x.ret s)
    (hpc : s.pc = (blkPl_562).base + spkOff_freePubRet)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = privCap) (hx23 : s.readReg64 .x23 = privPtr)
    (hx20 : s.readReg64 .x20 = sigCap) (hx21 : s.readReg64 .x21 = sigPtr) :
    Wire.SepWPp (lsProg_562 H) (s0.readReg64 .x30) s
      (vecU8Buf A.repAlloc privCap privPtr privBs ∗ vecU8Buf A.repAlloc sigCap sigPtr sigBs ∗
        spkEpilogueTail (A.atState lim st s) s0 x out)
      (spkRetPostPlaced A lim st
        (fun evs => ∃ e2 e3, OptByteFreeEnv e2 ∧ OptByteFreeEnv e3 ∧ evs = e2 ++ e3) s0 x out)
      (noPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcrl, htr, hx24, hx19, hsaved⟩
  by_cases hcap : privCap = 0#64
  · subst hcap
    refine Wire.SepWPp.mono_pre (sepConj_mono_left (spk_vecU8Buf_zero_elim A.repAlloc privPtr privBs)) ?_
    rw [emp_sepConj]
    have h22 : s.readReg64 (Reg.gpr 22#5) = 0#64 := hx22
    refine sepWPp_mono_post
      (spkRetPostPlaced_prepend A lim st (evs₁ := []) (E₂ := OptByteFreeEnv)
        (fun e3 h3 => ⟨[], e3, Or.inl rfl, h3, rfl⟩) s0 x out) ?_
    dsimp only [AllocCostModel.stepEvents, List.foldl]
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_freePrivRet) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcrl1
    refine Wire.SepWPp.mono_pre ?_
      (freeSig_716_placed_wp (st := st) hH (x := x) (s0 := s0)
        (sigCap := sigCap) (sigPtr := sigPtr) (sigBs := sigBs) (out := out)
        ⟨by simp [hsp_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
         hcrl1, by simp [htr, arm64_norm], by simp [hx24, arm64_norm], by simp [hx19, arm64_norm],
         ⟨by simpa [arm64_norm] using hsaved.x25, by simpa [arm64_norm] using hsaved.x26,
          by simpa [arm64_norm] using hsaved.x27, by simpa [arm64_norm] using hsaved.x28⟩⟩
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [hx20, arm64_norm]) (by simp [hx21, arm64_norm]))
    unfold spkEpilogueTail; simp only [signedDecodeResultAt_atState]; dsimp only [RustCliAllocBudget.atState]
    apply entails_of_eq
    simp only [RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_setPC, arm64_norm]
  · refine Wire.SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_dealloc A.repAlloc privCap privPtr privBs hcap)) ?_
    unfold spkEpilogueTail; simp only [signedDecodeResultAt_atState]; dsimp only [RustCliAllocBudget.atState]; simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hcall := spk_dealloc_placed_ok hH
    have hstack := stackAt_sub_split (s0.sp - 224#64) allocHookStack (CryptoVerification.SpqrV1.Varint.skipField3Stack 100)
    have h22 : s.readReg64 (Reg.gpr 22#5) = privCap := hx22
    have h23 : s.readReg64 (Reg.gpr 23#5) = privPtr := hx23
    have hbeq : (privCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    refine sepWPp_of_sepWP_lscro hcrl (mid := lsρ lsRustDeallocSym) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [lsρ, lsRustDeallocSym, arm64_norm])
      (by simp [hrun, arm64_norm]) ?_
    intro hcrl1
    refine spk_call_noPanic_lscro (privPtr, privCap.toNat, 1, st) hcall
      (by simp [lsρ, lsRustDeallocSym, arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
      (ret_pc := (blkPl_562).base + spkOff_freePrivRet) (by simp [arm64_norm])
      (T := A.pool lim st s ∗ A.repAlloc.live privPtr privCap.toNat 1 ∗ memRegion privPtr privCap.toNat ∗
        stackAt (s0.sp - 224#64) allocHookStack)
      (φ := True)
      (by simp (config := { decide := true }) [rustCliDeallocBudgetSpec, RustCliAllocBudget.repAlloc,
        RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_setPC, hsp_eq, h22, h23, hbeq,
        arm64_norm, wp_norm]) trivial
      (by rw [hstack]; sep_focus) ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
    dsimp only [rustCliDeallocBudgetSpec]; rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun ⟨hpres, _⟩ => ?_
    have htr2 : s2.trace = s.trace := by simpa [arm64_norm] using hpres.2.1
    have hsp2_eq : s2.sp = s0.sp - 224#64 := by simpa [hsp_eq, arm64_norm] using hsp2
    have hx19_2 : s2.readReg64 .x19 = x.ret := by simpa [hx19, arm64_norm] using hcs2.1
    have hx20_2 : s2.readReg64 .x20 = sigCap := by simpa [hx20, hbeq, arm64_norm] using hcs2.2.1
    have hx21_2 : s2.readReg64 .x21 = sigPtr := by simpa [hx21, hbeq, arm64_norm] using hcs2.2.2.1
    have hx24_2 : s2.readReg64 .x24 = s0.sp - 224#64 + 16#64 :=
      by simpa [hx24, arm64_norm] using hcs2.2.2.2.2.2.1
    have hsaved2 : SpkSavedRegs s0 s2 :=
      ⟨by simpa [hsaved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
       by simpa [hsaved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
    refine sepWPp_mono_post
      (spkRetPostPlaced_prepend A lim st (evs₁ := rustDeallocEvents privCap.toNat 1)
        (E₂ := OptByteFreeEnv)
        (fun e3 h3 => ⟨_, e3, Or.inr ⟨privCap.toNat, hpos, by omega, rfl⟩, h3, rfl⟩)
        s0 x out) ?_
    refine Wire.SepWPp.mono_pre ?_
      (freeSig_716_placed_wp (st := M.stepEvents (rustDeallocEvents privCap.toNat 1) st)
        hH (x := x) (s0 := s0) (s := s2) (sigCap := sigCap) (sigPtr := sigPtr) (sigBs := sigBs)
        (out := out)
        ⟨hsp2_eq, hsp2_align, hcrl2, htr2.trans htr, hx24_2, hx19_2, hsaved2⟩
        hpc2 hrun2 hx20_2 hx21_2)
    unfold spkEpilogueTail; simp only [signedDecodeResultAt_atState]; dsimp only [RustCliAllocBudget.atState]
    have hb1 : s0.sp - 224#64 + 16#64 = s0.sp - 208#64 := by bv_omega
    have hb2 : s0.sp - 224#64 + 104#64 = s0.sp - 120#64 := by bv_omega
    have hb3 : s0.sp - 224#64 + 112#64 = s0.sp - 112#64 := by bv_omega
    have hb4 : s0.sp - 224#64 - BitVec.ofNat 64 (CryptoVerification.SpqrV1.Varint.skipField3Stack 100) = s0.sp - 18240#64 := by
      change s0.sp - 224#64 - 18016#64 = s0.sp - 18240#64; bv_omega
    apply entails_of_eq; rw [hstack, hb1, hb2, hb3, hb4]; simp only [hsp_eq, hsp2_eq, arm64_norm]; ac_rfl

theorem freePub_680_placed_wp [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hH : SignedHooksPlaced M A lim H)
    {x : DecodeGhost} {s0 s : State}
    {pubCap pubPtr privCap privPtr sigCap sigPtr : BitVec 64}
    {pubBs privBs sigBs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure}
    (hst : SpkConvergeStatePlaced s0 (s0.sp - 224#64) x.ret s)
    (hpc : s.pc = (blkPl_562).base + spkOff_freePub)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = pubCap) (hx0 : s.readReg64 .x0 = pubPtr)
    (hx22 : s.readReg64 .x22 = privCap) (hx23 : s.readReg64 .x23 = privPtr)
    (hx20 : s.readReg64 .x20 = sigCap) (hx21 : s.readReg64 .x21 = sigPtr) :
    Wire.SepWPp (lsProg_562 H) (s0.readReg64 .x30) s
      (vecU8Buf A.repAlloc pubCap pubPtr pubBs ∗ vecU8Buf A.repAlloc privCap privPtr privBs ∗
        vecU8Buf A.repAlloc sigCap sigPtr sigBs ∗ spkEpilogueTail (A.atState lim st s) s0 x out)
      (spkRetPostPlaced A lim st SpkEpilogueFreeEnv s0 x out) (noPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcrl, htr, hx24, hx19, hsaved⟩
  by_cases hcap : pubCap = 0#64
  · subst hcap
    refine Wire.SepWPp.mono_pre (sepConj_mono_left (spk_vecU8Buf_zero_elim A.repAlloc pubPtr pubBs)) ?_
    rw [emp_sepConj]
    have h8 : s.readReg64 (Reg.gpr 8#5) = 0#64 := hx8
    refine sepWPp_mono_post
      (spkRetPostPlaced_prepend A lim st (evs₁ := [])
        (E₂ := fun evs => ∃ e2 e3, OptByteFreeEnv e2 ∧ OptByteFreeEnv e3 ∧ evs = e2 ++ e3)
        (fun _ ⟨e2, e3, h2, h3, he⟩ => ⟨[], e2, e3, Or.inl rfl, h2, h3, by simpa using he⟩)
        s0 x out) ?_
    dsimp only [AllocCostModel.stepEvents, List.foldl]
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_freePubRet) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcrl1
    refine Wire.SepWPp.mono_pre ?_
      (freePriv_696_placed_wp (st := st) hH (x := x) (s0 := s0)
        (privCap := privCap) (privPtr := privPtr) (sigCap := sigCap) (sigPtr := sigPtr)
        (privBs := privBs) (sigBs := sigBs) (out := out)
        ⟨by simp [hsp_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
         hcrl1, by simp [htr, arm64_norm], by simp [hx24, arm64_norm], by simp [hx19, arm64_norm],
         ⟨by simpa [arm64_norm] using hsaved.x25, by simpa [arm64_norm] using hsaved.x26,
          by simpa [arm64_norm] using hsaved.x27, by simpa [arm64_norm] using hsaved.x28⟩⟩
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [hx22, arm64_norm]) (by simp [hx23, arm64_norm])
        (by simp [hx20, arm64_norm]) (by simp [hx21, arm64_norm]))
    unfold spkEpilogueTail; simp only [signedDecodeResultAt_atState]; dsimp only [RustCliAllocBudget.atState]
    apply entails_of_eq
    simp only [RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_setPC, arm64_norm]
  · refine Wire.SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_dealloc A.repAlloc pubCap pubPtr pubBs hcap)) ?_
    unfold spkEpilogueTail; simp only [signedDecodeResultAt_atState]; dsimp only [RustCliAllocBudget.atState]; simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hcall := spk_dealloc_placed_ok hH
    have hstack := stackAt_sub_split (s0.sp - 224#64) allocHookStack (CryptoVerification.SpqrV1.Varint.skipField3Stack 100)
    have h8 : s.readReg64 (Reg.gpr 8#5) = pubCap := hx8
    have h0 : s.readReg64 (Reg.gpr 0#5) = pubPtr := hx0
    have hbeq : (pubCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    refine sepWPp_of_sepWP_lscro hcrl (mid := lsρ lsRustDeallocSym) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [lsρ, lsRustDeallocSym, arm64_norm])
      (by simp [hrun, arm64_norm]) ?_
    intro hcrl1
    refine spk_call_noPanic_lscro (pubPtr, pubCap.toNat, 1, st) hcall
      (by simp [lsρ, lsRustDeallocSym, arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
      (ret_pc := (blkPl_562).base + spkOff_freePubRet) (by simp [arm64_norm])
      (T := A.pool lim st s ∗ A.repAlloc.live pubPtr pubCap.toNat 1 ∗ memRegion pubPtr pubCap.toNat ∗
        stackAt (s0.sp - 224#64) allocHookStack)
      (φ := True)
      (by simp (config := { decide := true }) [rustCliDeallocBudgetSpec, RustCliAllocBudget.repAlloc,
        RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_setPC, hsp_eq, h8, h0, hbeq,
        arm64_norm, wp_norm]) trivial
      (by rw [hstack]; sep_focus) ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
    dsimp only [rustCliDeallocBudgetSpec]; rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun ⟨hpres, _⟩ => ?_
    have htr2 : s2.trace = s.trace := by simpa [arm64_norm] using hpres.2.1
    have hsp2_eq : s2.sp = s0.sp - 224#64 := by simpa [hsp_eq, arm64_norm] using hsp2
    have hx19_2 : s2.readReg64 .x19 = x.ret := by simpa [hx19, arm64_norm] using hcs2.1
    have hx20_2 : s2.readReg64 .x20 = sigCap := by simpa [hx20, hbeq, arm64_norm] using hcs2.2.1
    have hx21_2 : s2.readReg64 .x21 = sigPtr := by simpa [hx21, hbeq, arm64_norm] using hcs2.2.2.1
    have hx22_2 : s2.readReg64 .x22 = privCap := by simpa [hx22, hbeq, arm64_norm] using hcs2.2.2.2.1
    have hx23_2 : s2.readReg64 .x23 = privPtr := by simpa [hx23, hbeq, arm64_norm] using hcs2.2.2.2.2.1
    have hx24_2 : s2.readReg64 .x24 = s0.sp - 224#64 + 16#64 :=
      by simpa [hx24, arm64_norm] using hcs2.2.2.2.2.2.1
    have hsaved2 : SpkSavedRegs s0 s2 :=
      ⟨by simpa [hsaved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
       by simpa [hsaved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
    refine sepWPp_mono_post
      (spkRetPostPlaced_prepend A lim st (evs₁ := rustDeallocEvents pubCap.toNat 1)
        (E₂ := fun evs => ∃ e2 e3, OptByteFreeEnv e2 ∧ OptByteFreeEnv e3 ∧ evs = e2 ++ e3)
        (fun _ ⟨e2, e3, h2, h3, he⟩ =>
          ⟨_, e2, e3, Or.inr ⟨pubCap.toNat, hpos, by omega, rfl⟩, h2, h3,
           by rw [he, List.append_assoc]⟩)
        s0 x out) ?_
    refine Wire.SepWPp.mono_pre ?_
      (freePriv_696_placed_wp (st := M.stepEvents (rustDeallocEvents pubCap.toNat 1) st)
        hH (x := x) (s0 := s0) (s := s2)
        (privCap := privCap) (privPtr := privPtr) (sigCap := sigCap) (sigPtr := sigPtr)
        (privBs := privBs) (sigBs := sigBs) (out := out)
        ⟨hsp2_eq, hsp2_align, hcrl2, htr2.trans htr, hx24_2, hx19_2, hsaved2⟩
        hpc2 hrun2 hx22_2 hx23_2 hx20_2 hx21_2)
    unfold spkEpilogueTail; simp only [signedDecodeResultAt_atState]; dsimp only [RustCliAllocBudget.atState]
    have hb1 : s0.sp - 224#64 + 16#64 = s0.sp - 208#64 := by bv_omega
    have hb2 : s0.sp - 224#64 + 104#64 = s0.sp - 120#64 := by bv_omega
    have hb3 : s0.sp - 224#64 + 112#64 = s0.sp - 112#64 := by bv_omega
    have hb4 : s0.sp - 224#64 - BitVec.ofNat 64 (CryptoVerification.SpqrV1.Varint.skipField3Stack 100) = s0.sp - 18240#64 := by
      change s0.sp - 224#64 - 18016#64 = s0.sp - 18240#64; bv_omega
    apply entails_of_eq; rw [hstack, hb1, hb2, hb3, hb4]; simp only [hsp_eq, hsp2_eq, arm64_norm]; ac_rfl

theorem converge_656_to_ret_placed_wp [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {evsL : List AllocEvent}
    {H : LibsignalHooks} (hH : SignedHooksPlaced M A lim H)
    {x : DecodeGhost} {s0 s : State}
    {out : Option SignedPreKeyRecordStructure}
    (hevsL : SpkLoopEnv (2 * x.bytes.length + 3) x.bytes.length evsL)
    (hst : SpkConvergeStatePlaced s0 (s0.sp - 224#64) x.ret s)
    (hpc : s.pc = (blkPl_562).base + spkOff_converge)
    (hrun : s.status = .Running) :
    Wire.SepWPp (lsProg_562 H) (s0.readReg64 .x30) s
      (spkConvergeMem (A.atState lim (M.stepEvents evsL st) s)
        (s0.sp - 224#64) x.ret x.bytesA x.bytes out (s.readReg64 .x1) ∗
        spkCalleeSavedAt (s0.sp - 224#64) s0)
      (spkRetPostPlaced A lim st (SpkDecodeEnv x.bytes.length) s0 x out) (noPanicQp s0) := by
  let sp' := s0.sp - 224#64
  rcases hst with ⟨hsp_eq, hsp, hcrl, htr, hx24, hx19, hsaved⟩
  cases out with
  | some m =>
    unfold spkConvergeMem spkStructOf
    dsimp only [RustCliAllocBudget.atState]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun g => Wire.SepWPp.pure_pre fun hx1_zero => ?_
    unfold spkStructAt
    rw [vecU8At_eq_header_buf, vecU8At_eq_header_buf, vecU8At_eq_header_buf]
    simp only [sepConj_assoc]
    refine Wire.SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono (memRegion_four_entails (sp' + 100#64))
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (spkMemRegion88_unpack x.ret)))))))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun r0 => Wire.SepWPp.exists_pre fun r1 =>
      Wire.SepWPp.exists_pre fun r2 => Wire.SepWPp.exists_pre fun r3 =>
      Wire.SepWPp.exists_pre fun r4 => Wire.SepWPp.exists_pre fun r5 =>
      Wire.SepWPp.exists_pre fun r6 => Wire.SepWPp.exists_pre fun r7 =>
      Wire.SepWPp.exists_pre fun r8 => Wire.SepWPp.exists_pre fun r9 =>
      Wire.SepWPp.exists_pre fun r10 => Wire.SepWPp.exists_pre fun pad32 => ?_
    have hp96 : ((s0.sp - 224#64 + 96#64) ↦₃₂ m.id) ∗ ((s0.sp - 224#64 + 100#64) ↦₃₂ pad32) =
        ((s0.sp - 224#64 + 96#64) ↦₆₄ (pad32 ++ m.id)) := by
      simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair (s0.sp - 224#64 + 96#64) m.id pad32
    dsimp only [sp'] at hpc ⊢
    refine Wire.SepWPp.mono_pre
      (P' := spkRawWords88 (s0.sp - 224#64) g m pad32 ∗
        vecU8Buf A.repAlloc g.pub.cap g.pub.ptr m.publicKey ∗ vecU8Buf A.repAlloc g.priv.cap g.priv.ptr m.privateKey ∗
        vecU8Buf A.repAlloc g.sig.cap g.sig.ptr m.signature ∗
        memRegion (s0.sp - 224#64) 16 ∗ ((s0.sp - 224#64 + 104#64) ↦₆₄ (s0.sp - 224#64)) ∗
        memRegion (s0.sp - 224#64 + 112#64) 48 ∗
        spkDestWords88 x.ret r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ∗
        (x.bytesA ↦ₛ x.bytes) ∗ A.pool lim (M.stepEvents evsL st) s ∗
        stackAt (s0.sp - 224#64) (CryptoVerification.SpqrV1.Varint.skipField3Stack 100) ∗
        spkCalleeSavedAt (s0.sp - 224#64) s0)
      (by
        dsimp only [vecHeader, spkRawWords88, spkDestWords88]
        have hb_eq1 : vecU8Buf { pool := A.pool lim (M.stepEvents evsL st) s, live := A.live }
            g.pub.cap g.pub.ptr m.publicKey = vecU8Buf A.repAlloc g.pub.cap g.pub.ptr m.publicKey := rfl
        have hb_eq2 : vecU8Buf { pool := A.pool lim (M.stepEvents evsL st) s, live := A.live }
            g.priv.cap g.priv.ptr m.privateKey = vecU8Buf A.repAlloc g.priv.cap g.priv.ptr m.privateKey := rfl
        have hb_eq3 : vecU8Buf { pool := A.pool lim (M.stepEvents evsL st) s, live := A.live }
            g.sig.cap g.sig.ptr m.signature = vecU8Buf A.repAlloc g.sig.cap g.sig.ptr m.signature := rfl
        rw [hb_eq1, hb_eq2, hb_eq3, ← sepConj_assoc ((s0.sp - 224#64 + 96#64) ↦₃₂ m.id), hp96]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; apply entails_of_eq; ac_rfl) ?_
    unfold spkRawWords88 spkDestWords88; simp only [sepConj_assoc]
    have h1 : s.readReg64 (Reg.gpr 1#5) = 0#64 := hx1_zero
    have h19 : s.readReg64 (Reg.gpr 19#5) = x.ret := hx19
    have h24 : s.readReg64 (Reg.gpr 24#5) = s0.sp - 224#64 + 16#64 := hx24
    refine sepWPp_mono_post
      (spkRetPostPlaced_prepend A lim st (evs₁ := evsL) (E₂ := fun evs => evs = [])
        (fun _ h => by subst h; rw [List.append_nil]; exact Or.inl hevsL) s0 x (some m)) ?_
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_retOk) ?_
    wp_steps_sync_pool ((blkPl_562).base + spkOff_retOk)
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcrl1
    refine Wire.SepWPp.mono_pre ?_
      (retOk_800_placed_wp (A := A) (lim := lim) (st := M.stepEvents evsL st)
        (x := x) (s0 := s0) (out := some m)
        ⟨by simp [hsp_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
         hcrl1, by simp [htr, arm64_norm], by simp [h24, arm64_norm], by simp [h19, arm64_norm],
         ⟨by simpa [arm64_norm] using hsaved.x25, by simpa [arm64_norm] using hsaved.x26,
          by simpa [arm64_norm] using hsaved.x27, by simpa [arm64_norm] using hsaved.x28⟩⟩
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]))
    unfold spkEpilogueTail; simp only [signedDecodeResultAt_atState]; dsimp only [RustCliAllocBudget.atState]
    have h88 := spkRawWords88_pack (s0.sp - 224#64) g m pad32
    unfold spkRawWords88 at h88
    have hres := spkOk88_intro A.repAlloc g x.ret m pad32 rfl
    refine Entails.trans ?_
      (sepConj_mono hres (sepConj_mono_right (sepConj_mono_left h88)))
    apply entails_of_eq
    simp only [spkSub224_offs s0.sp, hsp_eq, h19, h24, arm64_norm]; ac_rfl
  | none =>
    unfold spkConvergeMem
    dsimp only [RustCliAllocBudget.atState]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun mErr => Wire.SepWPp.pure_pre fun hx1_nz => ?_
    unfold spkStructOf
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun g => ?_
    unfold spkStructAt
    rw [vecU8At_eq_header_buf, vecU8At_eq_header_buf, vecU8At_eq_header_buf]
    simp only [sepConj_assoc]
    refine Wire.SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono (memRegion_four_entails (sp' + 100#64))
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (spkMemRegion88_err_unpack x.ret))))))))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun r0 => Wire.SepWPp.exists_pre fun r1 =>
      Wire.SepWPp.exists_pre fun pad32 => ?_
    have hp96 : ((s0.sp - 224#64 + 96#64) ↦₃₂ mErr.id) ∗ ((s0.sp - 224#64 + 100#64) ↦₃₂ pad32) =
        ((s0.sp - 224#64 + 96#64) ↦₆₄ (pad32 ++ mErr.id)) := by
      simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair (s0.sp - 224#64 + 96#64) mErr.id pad32
    dsimp only [sp'] at hpc ⊢
    refine Wire.SepWPp.mono_pre
      (P' := spkRawWords88 (s0.sp - 224#64) g mErr pad32 ∗
        vecU8Buf A.repAlloc g.pub.cap g.pub.ptr mErr.publicKey ∗ vecU8Buf A.repAlloc g.priv.cap g.priv.ptr mErr.privateKey ∗
        vecU8Buf A.repAlloc g.sig.cap g.sig.ptr mErr.signature ∗ decodeErrorAt A.repAlloc (s.readReg64 .x1) ∗
        memRegion (s0.sp - 224#64) 16 ∗ ((s0.sp - 224#64 + 104#64) ↦₆₄ (s0.sp - 224#64)) ∗
        memRegion (s0.sp - 224#64 + 112#64) 48 ∗
        (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ memRegion (x.ret + 16#64) 72 ∗
        (x.bytesA ↦ₛ x.bytes) ∗ A.pool lim (M.stepEvents evsL st) s ∗
        stackAt (s0.sp - 224#64) (CryptoVerification.SpqrV1.Varint.skipField3Stack 100) ∗
        spkCalleeSavedAt (s0.sp - 224#64) s0)
      (by
        dsimp only [vecHeader, spkRawWords88]
        have hb_eq1 : vecU8Buf { pool := A.pool lim (M.stepEvents evsL st) s, live := A.live }
            g.pub.cap g.pub.ptr mErr.publicKey = vecU8Buf A.repAlloc g.pub.cap g.pub.ptr mErr.publicKey := rfl
        have hb_eq2 : vecU8Buf { pool := A.pool lim (M.stepEvents evsL st) s, live := A.live }
            g.priv.cap g.priv.ptr mErr.privateKey = vecU8Buf A.repAlloc g.priv.cap g.priv.ptr mErr.privateKey := rfl
        have hb_eq3 : vecU8Buf { pool := A.pool lim (M.stepEvents evsL st) s, live := A.live }
            g.sig.cap g.sig.ptr mErr.signature = vecU8Buf A.repAlloc g.sig.cap g.sig.ptr mErr.signature := rfl
        have hd_eq : decodeErrorAt { pool := A.pool lim (M.stepEvents evsL st) s, live := A.live }
            (s.readReg64 .x1) = decodeErrorAt A.repAlloc (s.readReg64 .x1) := rfl
        rw [hb_eq1, hb_eq2, hb_eq3, hd_eq, ← sepConj_assoc ((s0.sp - 224#64 + 96#64) ↦₃₂ mErr.id), hp96]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; apply entails_of_eq; ac_rfl) ?_
    unfold spkRawWords88
    let err := s.readReg64 .x1
    have h1 : s.readReg64 (Reg.gpr 1#5) = err := rfl
    have h19 : s.readReg64 (Reg.gpr 19#5) = x.ret := hx19
    have hbeq : (err == 0#64) = false := beq_eq_false_iff_ne.mpr hx1_nz
    refine sepWPp_mono_post
      (spkRetPostPlaced_prepend A lim st (evs₁ := evsL) (E₂ := SpkEpilogueFreeEnv)
        (fun evsF hF => Or.inr ⟨evsL, evsF, hevsL, hF, rfl⟩) s0 x none) ?_
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_freePub) ?_
    wp_steps_sync_pool ((blkPl_562).base + spkOff_freePub)
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcrl1
    refine Wire.SepWPp.mono_pre ?_
      (freePub_680_placed_wp (st := M.stepEvents evsL st) hH (x := x) (s0 := s0)
        (pubCap := g.pub.cap) (pubPtr := g.pub.ptr) (privCap := g.priv.cap) (privPtr := g.priv.ptr)
        (sigCap := g.sig.cap) (sigPtr := g.sig.ptr)
        (pubBs := mErr.publicKey) (privBs := mErr.privateKey) (sigBs := mErr.signature) (out := none)
        ⟨by simp [hsp_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
         hcrl1, by simp [htr, arm64_norm], by simp [hx24, arm64_norm], by simp [h19, arm64_norm],
         ⟨by simpa [arm64_norm] using hsaved.x25, by simpa [arm64_norm] using hsaved.x26,
          by simpa [arm64_norm] using hsaved.x27, by simpa [arm64_norm] using hsaved.x28⟩⟩
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]))
    unfold spkEpilogueTail; simp only [signedDecodeResultAt_atState]; dsimp only [RustCliAllocBudget.atState]
    have h88 := spkRawWords88_pack (s0.sp - 224#64) g mErr pad32
    unfold spkRawWords88 at h88
    have hres := spkErr88_intro A.repAlloc x.ret err (out := none) rfl
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hres (sepConj_mono_right (sepConj_mono_left h88))))))
    apply entails_of_eq; dsimp only [errTag, err]
    simp only [spkSub224_offs s0.sp, hsp_eq, h19, arm64_norm]; ac_rfl

end LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.EpilogueBudget
