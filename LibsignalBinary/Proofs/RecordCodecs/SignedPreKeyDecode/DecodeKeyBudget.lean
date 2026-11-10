/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.DecodeKey
public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.Defs
public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.DefsBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.RecordCodecs.Deps
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.BytesAndSkip
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.BytesAndSkipBudget
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.ErrTails
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.ErrTailsBudget
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `SignedPreKeyRecordStructure::decode` Key Varint Decode

`RustCliAllocBudget`-threaded relocatable key-varint CPS proofs (`+104 .. +140` and error stubs
`+328 .. +368`) on Block `562`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.DecodeKeyBudget

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
open CryptoVerification.RecordCodecsBinary (sepWPp_of_sepWP_lscro)
open CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers
  (SpkCfg SpkLoopRegs spkCfgLegacy spkCfg_split_varint spkCfg_subStack_le
   spkConvergeMem_none_intro spkErr16_pack40 spkMemRegion48_unpack16 spkOff_converge
   spkOff_dispatch spkOff_fromCommon spkOff_key spkOff_keyRet spkPointsTo112_memRegion40_entails_48
   spkStructOf)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
  (DecodeVarint2Env SignedHooksPlaced SignedPortDepsPlaced SpkCaps SpkErrTailEnv
   SpkLoopBoundedEnv decodeVarint2BudgetSpec decodeVarint2Events fitsEnv_spkLoop_errTail)
open LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.BytesAndSkipBudget (spkLoopRegs_of_calleeSaved)
open LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.DefsBudget
  (noPanicQp sepWPp_call_budget_lscro sepWPp_end_noPanic_lscro spkAfterVarintCapsMem
   spkAfterVarintCapsMemAt spkConvergePostPlaced spkLoopCapsMem spkLoopCapsMemAt
   spkStructLoopCapsOf spkStructLoopCapsOf_entails_of spk_decodeVarint6_placed_ok)
open LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.ErrTailsBudget (fromCommon_372_placed_wp)
attribute [local arm64_norm] BitVec.toNat_zero

/-! ### Local Helpers -/

private theorem decodeKey_none_pack (cfg : SpkCfg) (A : RustAlloc) (sp' x19 ptr err : BitVec 64)
    (caps : SpkCaps) (bs : List (BitVec 8)) (m : SignedPreKeyRecordStructure) :
    ((sp' + 104#64) ↦₆₄ sp') ∗ A.pool ∗
      stackAt sp' cfg.varintStk ∗
      decodeErrorAtStackLen A err 0 ∗
      memRegion sp' 16 ∗ (ptr ↦ₛ bs) ∗
      memRegion (sp' + 112#64) 48 ∗
      spkStructLoopCapsOf A sp' bs.length caps m ∗
      memRegion x19 88 ∗
      memRegion (sp' - BitVec.ofNat 64 cfg.subStack)
        (cfg.subStack - cfg.varintStk) ⊢
      spkStructOf A sp' m ∗
        decodeErrorAtStackLen A err 0 ∗
        memRegion sp' 16 ∗
        ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion (sp' + 112#64) 48 ∗
        memRegion x19 88 ∗
        (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' cfg.subStack := by
  have hstack := stackAt_sub_split sp' cfg.varintStk cfg.subStack
    (spkCfg_split_varint cfg) (spkCfg_subStack_le cfg)
  have hp :
      ((sp' + 104#64) ↦₆₄ sp') ∗ A.pool ∗
        stackAt sp' cfg.varintStk ∗
        decodeErrorAtStackLen A err 0 ∗
        memRegion sp' 16 ∗ (ptr ↦ₛ bs) ∗
        memRegion (sp' + 112#64) 48 ∗
        spkStructLoopCapsOf A sp' bs.length caps m ∗
        memRegion x19 88 ∗
        memRegion (sp' - BitVec.ofNat 64 cfg.subStack)
          (cfg.subStack - cfg.varintStk) =
      spkStructLoopCapsOf A sp' bs.length caps m ∗
        decodeErrorAtStackLen A err 0 ∗
        memRegion sp' 16 ∗
        ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion (sp' + 112#64) 48 ∗
        memRegion x19 88 ∗
        (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' cfg.subStack := by
    rw [hstack]; ac_rfl
  rw [hp]
  exact sepConj_mono_left (spkStructLoopCapsOf_entails_of A sp' bs.length caps m)

private theorem decodeKey_err_pack (cfg : SpkCfg) (A : RustAlloc) (sp' x19 ptr : BitVec 64)
    (caps : SpkCaps) (bs rest : List (BitVec 8)) (m : SignedPreKeyRecordStructure)
    (e0 v120 : BitVec 64) :
    ((sp' + 104#64) ↦₆₄ sp') ∗ A.pool ∗
      stackAt sp' cfg.varintStk ∗
      sliceCursorAfter sp' ptr bs rest ∗
      ((sp' + 112#64) ↦₆₄ e0) ∗ ((sp' + 120#64) ↦₆₄ v120) ∗
      memRegion (sp' + 128#64) 32 ∗
      spkStructLoopCapsOf A sp' bs.length caps m ∗
      memRegion x19 88 ∗
      memRegion (sp' - BitVec.ofNat 64 cfg.subStack)
        (cfg.subStack - cfg.varintStk) ⊢
      ((sp' + 112#64) ↦₆₄ e0) ∗ memRegion (sp' + 120#64) 40 ∗
        spkStructOf A sp' m ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗
        stackAt sp' cfg.subStack := by
  have hstack := stackAt_sub_split sp' cfg.varintStk cfg.subStack
    (spkCfg_split_varint cfg) (spkCfg_subStack_le cfg)
  have hp :
      ((sp' + 104#64) ↦₆₄ sp') ∗ A.pool ∗
        stackAt sp' cfg.varintStk ∗
        sliceCursorAfter sp' ptr bs rest ∗
        ((sp' + 112#64) ↦₆₄ e0) ∗ ((sp' + 120#64) ↦₆₄ v120) ∗
        memRegion (sp' + 128#64) 32 ∗
        spkStructLoopCapsOf A sp' bs.length caps m ∗
        memRegion x19 88 ∗
        memRegion (sp' - BitVec.ofNat 64 cfg.subStack)
          (cfg.subStack - cfg.varintStk) =
      (((sp' + 120#64) ↦₆₄ v120) ∗ memRegion (sp' + 128#64) 32) ∗
        spkStructLoopCapsOf A sp' bs.length caps m ∗
        sliceCursorAfter sp' ptr bs rest ∗
        (((sp' + 112#64) ↦₆₄ e0) ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
          memRegion x19 88 ∗ A.pool ∗
          stackAt sp' cfg.subStack) := by
    rw [hstack]; ac_rfl
  rw [hp]
  refine Entails.trans
    (sepConj_mono (spkErr16_pack40 sp' v120)
      (sepConj_mono (spkStructLoopCapsOf_entails_of A sp' bs.length caps m)
        (sepConj_mono_left (sliceCursorAfter_entails_memRegion sp' ptr bs rest)))) ?_
  apply entails_of_eq; ac_rfl

private theorem decodeKey_ok_pack (cfg : SpkCfg) (A : RustAlloc) (sp' x19 ptr : BitVec 64)
    (caps : SpkCaps) (bs rest : List (BitVec 8)) (m : SignedPreKeyRecordStructure)
    (e0 e1 : BitVec 64) :
    ((sp' + 104#64) ↦₆₄ sp') ∗ A.pool ∗
      stackAt sp' cfg.varintStk ∗
      sliceCursorAfter sp' ptr bs rest ∗
      ((sp' + 112#64) ↦₆₄ e0) ∗ ((sp' + 120#64) ↦₆₄ e1) ∗
      memRegion (sp' + 128#64) 32 ∗
      spkStructLoopCapsOf A sp' bs.length caps m ∗
      memRegion x19 88 ∗
      memRegion (sp' - BitVec.ofNat 64 cfg.subStack)
        (cfg.subStack - cfg.varintStk) ⊢
      spkAfterVarintCapsMemAt cfg.subStack A sp' x19 ptr caps bs rest bs.length m := by
  unfold spkAfterVarintCapsMemAt
  have hstack := stackAt_sub_split sp' cfg.varintStk cfg.subStack
    (spkCfg_split_varint cfg) (spkCfg_subStack_le cfg)
  have h48 := Entails.trans (sepConj_mono_right (spkErr16_pack40 sp' e1))
    (spkPointsTo112_memRegion40_entails_48 sp' e0)
  have hp :
      ((sp' + 104#64) ↦₆₄ sp') ∗ A.pool ∗
        stackAt sp' cfg.varintStk ∗
        sliceCursorAfter sp' ptr bs rest ∗
        ((sp' + 112#64) ↦₆₄ e0) ∗ ((sp' + 120#64) ↦₆₄ e1) ∗
        memRegion (sp' + 128#64) 32 ∗
        spkStructLoopCapsOf A sp' bs.length caps m ∗
        memRegion x19 88 ∗
        memRegion (sp' - BitVec.ofNat 64 cfg.subStack)
          (cfg.subStack - cfg.varintStk) =
      (((sp' + 112#64) ↦₆₄ e0) ∗ ((sp' + 120#64) ↦₆₄ e1) ∗ memRegion (sp' + 128#64) 32) ∗
        sliceCursorAfter sp' ptr bs rest ∗
        ((sp' + 104#64) ↦₆₄ sp') ∗
        spkStructLoopCapsOf A sp' bs.length caps m ∗
        memRegion x19 88 ∗ A.pool ∗
        stackAt sp' cfg.subStack := by
    rw [hstack]; ac_rfl
  rw [hp]
  refine Entails.trans (sepConj_mono_left h48) ?_
  apply entails_of_eq; ac_rfl

/-! ### Budget-threaded proofs -/

attribute [local irreducible] Program.fetch Program.externAt?

theorem decodeKey_104_placed_cps [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SpkCaps}
    {H : LibsignalHooks} (hH : SignedHooksPlaced M A lim H) (d : SignedPortDepsPlaced M A lim H)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : SignedPreKeyRecordStructure}
    {out : Option SignedPreKeyRecordStructure}
    (hlen : bs.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_562).base + spkOff_key) (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hFit : FitsEnv M lim st (SpkLoopBoundedEnv rem caps))
    (hok : ∀ (tag : ℕ) (wt : WireType) (rest : List (BitVec 8)) (s3 : State),
      decodeKey bs = some ((tag, wt), rest) →
      s3.pc = (blkPl_562).base + spkOff_dispatch → s3.status = .Running →
      SpkLoopRegs s0 sp' x19 s3 →
      s3.readReg64 .x0 = BitVec.ofNat 64 wt.toNat →
      s3.readReg64 .x1 = BitVec.ofNat 64 tag →
      s3.spAligned = true → LibsignalCodeRoLoaded lsmpl s3.mem →
      s3.trace = s0.trace →
      Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s3
        (spkAfterVarintCapsMem (A.atState lim st s3) sp' x19 ptr caps bs rest bs.length m)
        (spkConvergePostPlaced A lim st rem caps s0 sp' x19 ptr bs out) (noPanicQp s0))
    (hnone : decodeKey bs = none → out = none) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s
      (spkLoopCapsMem (A.atState lim st s) sp' x19 ptr caps bs m)
      (spkConvergePostPlaced A lim st rem caps s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  unfold spkLoopCapsMem spkLoopCapsMemAt
  have hcall := spk_decodeVarint6_placed_ok d
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have hstack := stackAt_sub_split sp' CryptoVerification.SpqrV1.Varint.decodeVarint2Stack
    (CryptoVerification.SpqrV1.Varint.skipField3Stack 100)
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 559) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 => ?_
  refine sepWPp_call_budget_lscro (⟨sp' + 104#64, sp', ptr, bs⟩, st) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (ret_pc := (blkPl_562).base + spkOff_keyRet) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 104#64) ↦₆₄ sp') ∗ sliceCursorAt sp' ptr bs ∗
      A.pool lim st s ∗ stackAt sp' CryptoVerification.SpqrV1.Varint.decodeVarint2Stack)
    (φ := sp' + 104#64 = sp' + 104#64 ∧ bs.length < 2 ^ 63 ∧ FitsEnv M lim st (DecodeVarint2Env bs))
    (by simp [decodeVarint2BudgetSpec, RustCliAllocBudget.pool_writeReg64,
      RustCliAllocBudget.pool_setPC, hsp_eq, h29, arm64_norm])
    ⟨rfl, hlen, fitsEnv_spkLoop_errTail (fun _ => SpkErrTailEnv.of_decodeVarint2) hFit⟩
    (by
      have hloop_eq : spkStructLoopCapsOf (A.atState lim st s) sp' bs.length caps m =
          spkStructLoopCapsOf A.repAlloc sp' bs.length caps m := rfl
      rw [hloop_eq]
      dsimp only [RustCliAllocBudget.atState]
      rw [hstack]; sep_focus)
    fun s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2 => ?_
  have hregs2 : SpkLoopRegs s0 sp' x19 s2 := spkLoopRegs_of_calleeSaved hsp2 hcs2
    ⟨by simp [hsp_eq, arm64_norm], by simp [h29, arm64_norm],
     by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
     ⟨by simpa [arm64_norm] using hregs.saved.x25, by simpa [arm64_norm] using hregs.saved.x26,
      by simpa [arm64_norm] using hregs.saved.x27, by simpa [arm64_norm] using hregs.saved.x28⟩⟩
  have hsp2_eq : s2.sp = sp' := hregs2.sp
  have hx29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs2.x29
  dsimp only [decodeVarint2BudgetSpec]
  cases hdv : decodeVarint bs with
  | none =>
    have hdk : decodeKey bs = none := by unfold decodeKey; rw [hdv]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun evs => ?_
    refine Wire.SepWPp.pure_pre fun hx0_1 => Wire.SepWPp.pure_pre fun htr2 => ?_
    rw [sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hevs => ?_
    simp only [sepConj_pure_left_comm, sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun hx1_nz => ?_
    have hw0_1 : s2.readReg64 (Reg.gpr 0#5) = 1#64 := hx0_1
    refine sepWPp_end_noPanic_lscro hcrl2 ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcrl3 => ?_
    refine ⟨⟨by simpa [arm64_norm] using hregs2.sp,
      by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
      hcrl3, by simp [htr2, htr, arm64_norm],
      by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
      ⟨by simpa [arm64_norm] using hregs2.saved.x25, by simpa [arm64_norm] using hregs2.saved.x26,
       by simpa [arm64_norm] using hregs2.saved.x27, by simpa [arm64_norm] using hregs2.saved.x28⟩⟩,
      evs, .done (SpkErrTailEnv.of_decodeVarint2 hevs), ?_⟩
    have hp1 := decodeKey_none_pack spkCfgLegacy (A.atState lim (M.stepEvents evs st) s2)
      sp' x19 ptr (s2.readReg64 (Reg.gpr 1#5)) caps bs m
    have hp2 := spkConvergeMem_none_intro spkCfgLegacy.subStack
      (A.atState lim (M.stepEvents evs st) s2) sp' x19 ptr (s2.readReg64 (Reg.gpr 1#5)) 0 m bs
      (hnone hdk) hx1_nz
    dsimp only [RustCliAllocBudget.atState] at hp1 hp2 ⊢
    simp only [RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_setPC,
      hsp_eq, hsp2_eq, arm64_norm]
    exact Entails.trans hp1 hp2
  | some kv =>
    rcases kv with ⟨key, rest⟩
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun evs => ?_
    refine Wire.SepWPp.pure_pre fun ⟨hx0_0, hx1_key⟩ => Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_pure_left_comm, sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun hevs => ?_
    have hevs0 : evs = [] := by rw [hevs]; simp [decodeVarint2Events, hdv]
    subst hevs0
    dsimp only [AllocCostModel.stepEvents, List.foldl]
    have hw0_0 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    have hw1_k : s2.readReg64 (Reg.gpr 1#5) = key := hx1_key
    refine Wire.SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (spkMemRegion48_unpack16 sp')))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun e0 => Wire.SepWPp.exists_pre fun e1 => ?_
    by_cases hkey32 : 2 ^ 32 ≤ key.toNat
    · have hdk : decodeKey bs = none := by
        unfold decodeKey; rw [hdv]; simp [show ¬ key.toNat < 4294967296 by omega]
      have hbeq : ((key >>> 32) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr (bne_iff_ne.mp (key_lsr32_ne_zero_of_ge key hkey32))
      refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_562).base + spkOff_fromCommon) ?_
      wp_steps_sync_pool ((blkPl_562).base + spkOff_fromCommon)
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcrl3 => ?_
      refine Wire.SepWPp.mono_pre ?_
        (fromCommon_372_placed_wp (st := st) (rem := rem) (caps := caps) hH
          (s0 := s0) (sp' := sp') (x19 := x19) (ptr := ptr)
          (kind := BitVec.ofNat 64 (2 ^ 63 + 4)) (e0 := e0)
          (mErr := m) (bs := bs) (out := out) (hnone hdk)
          (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
           by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
           ⟨by simpa [arm64_norm] using hregs2.saved.x25, by simpa [arm64_norm] using hregs2.saved.x26,
            by simpa [arm64_norm] using hregs2.saved.x27, by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
          (by simp [arm64_norm]) (by simp [KindNoHeap])
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hcrl3 (by simp [htr2, htr, arm64_norm]) hFit)
      refine Entails.trans ?_
        (decodeKey_err_pack spkCfgLegacy (A.atState lim st _) sp' x19 ptr caps bs rest m e0 key)
      dsimp only [RustCliAllocBudget.atState, spkCfgLegacy, SpkCfg.subStack]
      simp only [hsp_eq, hsp2_eq, hx29_2, arm64_norm]
      apply entails_of_eq; ac_rfl
    · have hkey_lt : key.toNat < 2 ^ 32 := Nat.lt_of_not_ge hkey32
      have hlsr := key_lsr32_eq_zero_of_lt key hkey_lt
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hdk : decodeKey bs = none := by
          unfold decodeKey; rw [hdv]; simp [show key.toNat < 4294967296 by omega, hwt]
        have hge6 : 6 ≤ key.toNat % 8 := by
          have h := (WireType.ofNat?_eq_none_iff (key.toNat % 8) (Nat.mod_lt _ (by decide))).mp hwt; omega
        have hcs_cond := key_and7_ule6_of_ge key hge6
        refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_562).base + spkOff_fromCommon) ?_
        wp_steps_sync_pool ((blkPl_562).base + spkOff_fromCommon)
        refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcrl3 => ?_
        refine Wire.SepWPp.mono_pre ?_
          (fromCommon_372_placed_wp (st := st) (rem := rem) (caps := caps) hH
            (s0 := s0) (sp' := sp') (x19 := x19) (ptr := ptr)
            (kind := BitVec.ofNat 64 (2 ^ 63 + 3)) (e0 := e0)
            (mErr := m) (bs := bs) (out := out) (hnone hdk)
            (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
            ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
             by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
             ⟨by simpa [arm64_norm] using hregs2.saved.x25, by simpa [arm64_norm] using hregs2.saved.x26,
              by simpa [arm64_norm] using hregs2.saved.x27, by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
            (by simp [arm64_norm]) (by simp [KindNoHeap])
            (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
            hcrl3 (by simp [htr2, htr, arm64_norm]) hFit)
        refine Entails.trans ?_
          (decodeKey_err_pack spkCfgLegacy (A.atState lim st _) sp' x19 ptr caps bs rest m e0 (key &&& 7#64))
        dsimp only [RustCliAllocBudget.atState, spkCfgLegacy, SpkCfg.subStack]
        simp only [hsp_eq, hsp2_eq, hx29_2, arm64_norm]
        apply entails_of_eq; ac_rfl
      | some wt =>
        have hcs_cond := key_and7_ule6_of_lt key (WireType.lt_six_of_ofNat?_eq_some hwt)
        by_cases htag0 : key.toNat / 8 < 1
        · have hdk : decodeKey bs = none := by
            unfold decodeKey; rw [hdv]
            simp [show key.toNat < 4294967296 by omega, hwt, show key.toNat < 8 by omega]
          have htz := key_tag32_eq_zero_of_lt1 key hkey_lt htag0
          refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_562).base + spkOff_fromCommon) ?_
          wp_steps_sync_pool ((blkPl_562).base + spkOff_fromCommon)
          refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcrl3 => ?_
          refine Wire.SepWPp.mono_pre ?_
            (fromCommon_372_placed_wp (st := st) (rem := rem) (caps := caps) hH
              (s0 := s0) (sp' := sp') (x19 := x19) (ptr := ptr)
              (kind := BitVec.ofNat 64 (2 ^ 63 + 5)) (e0 := e0)
              (mErr := m) (bs := bs) (out := out) (hnone hdk)
              (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
              ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
               by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
               ⟨by simpa [arm64_norm] using hregs2.saved.x25, by simpa [arm64_norm] using hregs2.saved.x26,
                by simpa [arm64_norm] using hregs2.saved.x27, by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
              (by simp [arm64_norm]) (by simp [KindNoHeap])
              (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
              hcrl3 (by simp [htr2, htr, arm64_norm]) hFit)
          refine Entails.trans ?_
            (decodeKey_err_pack spkCfgLegacy (A.atState lim st _) sp' x19 ptr caps bs rest m e0 e1)
          dsimp only [RustCliAllocBudget.atState, spkCfgLegacy, SpkCfg.subStack]
          simp only [hsp_eq, hsp2_eq, hx29_2, arm64_norm]
          apply entails_of_eq; ac_rfl
        · have hdk : decodeKey bs = some ((key.toNat / 8, wt), rest) := by
            unfold decodeKey; rw [hdv]
            simp [show key.toNat < 4294967296 by omega, hwt, show ¬ key.toNat < 8 by omega]
          have htnz' : (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 key) >>> 3)) == 0#64) = false := by
            simpa [arm64_norm] using key_tag32_ne_zero_of_ge1 key hkey_lt htag0
          refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_562).base + spkOff_dispatch) ?_
          wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcrl3 => ?_
          have htag_eq : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 key) >>> 3)) =
              BitVec.ofNat 64 (key.toNat / 8) := by
            simpa [arm64_norm] using key_tag32_zeroExtend64_eq key hkey_lt
          have hwt_eq := key_and7_eq_wt key hwt
          refine Wire.SepWPp.mono_pre ?_
            (hok (key.toNat / 8) wt rest _ hdk
              (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
              ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
               by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
               ⟨by simpa [arm64_norm] using hregs2.saved.x25, by simpa [arm64_norm] using hregs2.saved.x26,
                by simpa [arm64_norm] using hregs2.saved.x27, by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
              (by simp [hwt_eq, arm64_norm]) (by simpa [arm64_norm] using htag_eq)
              (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
              hcrl3 (by simp [htr2, htr, arm64_norm]))
          have hp := decodeKey_ok_pack spkCfgLegacy (A.atState lim st s2) sp' x19 ptr caps bs rest m e0 e1
          dsimp only [RustCliAllocBudget.atState] at hp ⊢
          simp only [RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_setPC,
            hsp_eq, hsp2_eq, arm64_norm]
          exact hp

end LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.DecodeKeyBudget
