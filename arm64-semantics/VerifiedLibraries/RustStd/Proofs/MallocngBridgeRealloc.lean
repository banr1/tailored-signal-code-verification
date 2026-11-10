/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.BV
public import VerifiedLibraries.Mallocng.Spec
public import VerifiedLibraries.Mallocng.Proofs.BridgeHelpers
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocHelpers
public import VerifiedLibraries.Mallocng.Proofs.RdlAllocProof
public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Proofs.MallocngInst
public import VerifiedLibraries.RustStd.Proofs.MallocngBridgeCommon

/-!
# Placed `__rustc::__rdl_realloc` Bridge Proof

Verifies the 43-instruction `__rustc::__rdl_realloc` shim (`rdlReallocInstrs`) and its
1-instruction `b` thunk against `rustStdReallocSpec` over `mallocngRustCliAllocWithOf`
(`rdlRealloc_placed_withExtra_ok`, `rdlRealloc_thunk_withExtra_ok`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.CType ProofLib.SepLogic ProofLib.StdStartup
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## Spatial and Pure Helpers -/

private theorem memRegion8_entails_pointsTo64 (a : BitVec 64) :
    memRegion a 8 ⊢ ∃∗ w : BitVec 64, a ↦₆₄ w := by
  refine Entails.trans (memRegion_entails_exists_pointsToBytes 8 a (by decide)) ?_
  refine Entails.sepExists_elim fun bs => Entails.pure_left fun hlen => ?_
  have htake : (bs.drop 0).take 8 = bs := by
    simp [List.take_of_length_le (by omega : bs.length ≤ 8)]
  have heq := pointsToBytes_take8_eq_pointsTo64 a bs 0 (by omega)
  rw [htake] at heq
  rw [heq]
  exact Entails.sepExists_right _ (Entails.refl _)

private theorem repack_hookFrame_64 (sp w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    (((sp - 64#64) ↦₆₄ w0) ∗ ((sp - 56#64) ↦₆₄ w1) ∗
     ((sp - 48#64) ↦₆₄ w2) ∗ ((sp - 40#64) ↦₆₄ w3) ∗
     ((sp - 32#64) ↦₆₄ w4) ∗ ((sp - 24#64) ↦₆₄ w5) ∗
     ((sp - 16#64) ↦₆₄ w6) ∗ ((sp - 8#64) ↦₆₄ w7)) ∗
    (stackFrameAt (sp - 64#64) mallocngStackBytes ∗
     stackFrameAt (sp - 64#64 - 1024#64) 3008) ⊢
      Rust.hookFrame sp := by
  rw [hookFrame_eq_stack64_1024 sp]
  exact sepConj_mono_left (pack_stack64 sp w0 w1 w2 w3 w4 w5 w6 w7)

private theorem repack_stack64_to_1024 (sp w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    (((sp - 64#64) ↦₆₄ w0) ∗ ((sp - 56#64) ↦₆₄ w1) ∗
     ((sp - 48#64) ↦₆₄ w2) ∗ ((sp - 40#64) ↦₆₄ w3) ∗
     ((sp - 32#64) ↦₆₄ w4) ∗ ((sp - 24#64) ↦₆₄ w5) ∗
     ((sp - 16#64) ↦₆₄ w6) ∗ ((sp - 8#64) ↦₆₄ w7)) ∗
    (stackFrameAt (sp - 64#64) mallocngStackBytes ∗
     stackFrameAt (sp - 64#64 - 1024#64) 3008) ⊢
      stackFrameAt sp mallocngStackBytes ∗ stackFrameAt (sp - 1024#64) 3072 := by
  rw [← hookFrame_eq_stack1024 sp]
  exact repack_hookFrame_64 sp w0 w1 w2 w3 w4 w5 w6 w7

private theorem allocMemcpy_prep_entails (p q : BitVec 64) (bs : List (BitVec 8))
    (oldLen newLen copyLen : Nat)
    (h1 : bs.length ≤ copyLen) (h2 : copyLen ≤ oldLen) (h3 : copyLen ≤ newLen)
    (h4 : oldLen ≤ 2 ^ 64) (h5 : newLen ≤ 2 ^ 64) :
    ((p ↦ₛ bs) ∗ memRegion (p + BitVec.ofNat 64 bs.length) (oldLen - bs.length) ∗
     memRegion q newLen) ⊢
    ∃∗ midBs : List (BitVec 8),
      ⌜(bs ++ midBs).length = copyLen⌝ ∗
      (memRegion q (bs ++ midBs).length ∗ (p ↦ₛ (bs ++ midBs))) ∗
      (memRegion (p + BitVec.ofNat 64 copyLen) (oldLen - copyLen) ∗
       memRegion (q + BitVec.ofNat 64 copyLen) (newLen - copyLen)) := by
  refine Entails.trans (copyPrep_entails p q bs oldLen newLen copyLen h1 h2 h3 h4 h5) ?_
  refine Entails.sepExists_elim fun dstBs => Entails.sepExists_elim fun midBs => ?_
  refine Entails.sepExists_right midBs ?_
  refine Entails.pure_left fun ⟨hdst, hmid⟩ => ?_
  refine Entails.pure_right hmid ?_
  have hqReg : (q ↦ₛ dstBs) ⊢ memRegion q (bs ++ midBs).length := by
    rw [hmid, ← hdst]
    exact (IsBlock.pointsToBytes q dstBs).entails_memRegion
  refine Entails.trans (sepConj_mono_left hqReg) ?_
  exact Entails.of_eq (by ac_rfl)

/-! ## Epilogue (`+0x98..+0xa8`) -/

private theorem rdlRealloc_epilogue {P : Program}
    {reallocAddr cReallocAddr posixMemalignAddr memcpyAddr freeAddr : BitVec 64}
    (hCode : hasInstrs P reallocAddr
      (rdlReallocInstrs reallocAddr cReallocAddr posixMemalignAddr memcpyAddr freeAddr))
    (s0 s : State) (w0 w1 : BitVec 64) (Q : SepProp)
    (post : State → SepProp → Prop) (oom : State → SepProp)
    (hsp_align : s0.spAligned = true)
    (hpc : s.pc = reallocAddr + 0x98#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 64#64)
    (hx23 : s.readReg64 .x23 = s0.readReg64 .x23)
    (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hcs_v : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hpost : ∀ sf : State,
      sf.readReg64 .x0 = s.readReg64 .x0 →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      AllocCallPreserved s sf →
      PoolPreserved s sf →
      post sf (Rust.hookFrame s0.sp ∗ Q)) :
    SepWP P (s0.readReg64 Reg.lr) s
      ((((s0.sp - 64#64) ↦₆₄ w0) ∗ ((s0.sp - 56#64) ↦₆₄ w1) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
       (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
        stackFrameAt (s0.sp - 64#64 - 1024#64) 3008) ∗ Q)
      post oom := by
  have hsp_s : decide (s.sp &&& 15#64 = 0#64) = true := by
    rw [hsp]; exact spAligned_sub64 hsp_align
  have hf38 := fetch_instr_at 38 (off := 0x98#64) hCode
  have hf39 := fetch_instr_at 39 (off := 0x9c#64) hCode
  have hf40 := fetch_instr_at 40 (off := 0xa0#64) hCode
  have hf41 := fetch_instr_at 41 (off := 0xa4#64) hCode
  have hf42 := fetch_instr_at 42 (off := 0xa8#64) hCode
  wp_step; wp_step; wp_step; wp_step; wp_step
  rw [← sepConj_assoc]
  refine SepWP.weaken_pre (sepConj_mono_left (repack_hookFrame_64 s0.sp w0 w1 _ _ _ _ _ _)) ?_
  refine SepWP.done (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) ?_
  refine hpost _ (by simp [arm64_norm]) (by simp [arm64_norm]) ?_ ?_ ?_
  · unfold CalleeSavedPreserved
    simp [arm64_norm, hx23, hx24, hx25, hx26, hx27, hx28, hcs_v]
  · unfold AllocCallPreserved
    simp [arm64_norm]
  · unfold PoolPreserved
    simp [arm64_norm]

/-! ## Fast Path A (`+0x2c..+0x40`) -/

private theorem pathA_ok_rearr (B1 B2 B3 Ppost Pstk1 extra Pstk2 : SepProp) :
    B1 ∗ B2 ∗ B3 ∗ Ppost ∗ Pstk1 ∗ extra ∗ Pstk2 =
      (Ppost ∗ extra) ∗ (Pstk1 ∗ Pstk2) ∗ (B1 ∗ B2 ∗ B3) := by ac_rfl

private theorem pathA_fail_rearr (B1 B2 B3 Ppure Ppost Pstk1 extra Pstk2 : SepProp) :
    B1 ∗ B2 ∗ B3 ∗ Ppure ∗ Ppost ∗ Pstk1 ∗ extra ∗ Pstk2 =
      Ppure ∗ (Ppost ∗ extra) ∗ (Pstk1 ∗ Pstk2) ∗ (B1 ∗ B2 ∗ B3) := by ac_rfl

private theorem rdlRealloc_pathA {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (extra : SepProp) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {cAddrs : MallocngCEntryAddrs}
    {reallocAddr memcpyAddr : BitVec 64}
    (hCode : hasInstrs P reallocAddr
      (rdlReallocInstrs reallocAddr cAddrs.realloc cAddrs.posixMemalign memcpyAddr cAddrs.free))
    (hC : MallocngProgCContractsWith J extra P mAddrs cAddrs)
    (p alignBv newBv : BitVec 64) (old align new lb lk : Nat) (bs : List (BitVec 8))
    (b : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (sv0 sv1 : BitVec 64) (R : SepProp) (s0 s : State)
    (hsp_align : s0.spAligned = true)
    (hAlignNat : alignBv.toNat = align) (hNewNat : newBv.toNat = new)
    (hLayoutNew : RustLayoutOk new align) (hLayoutOld : RustLayoutOk old align)
    (hpMod : p.toNat % align = 0)
    (hPow2 : IsPow2Align alignBv) (hAl16 : align ≤ 16)
    (hpNe : p ≠ 0#64) (hp16 : 16 ∣ p.toNat) (hp48 : p.toNat + old ≤ 2 ^ 48)
    (hbsOld : bs.length ≤ old) (hbsNew : bs.length ≤ new)
    (hpc : s.pc = reallocAddr + 0x2c#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 64#64)
    (hx0 : s.readReg64 .x0 = p) (hx19 : s.readReg64 .x19 = newBv)
    (hx23 : s.readReg64 .x23 = s0.readReg64 .x23) (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25) (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hcs_v : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hPres : AllocCallPreserved s0 s) (hBrk : s.brk = s0.brk) :
    let allocInst := mallocngRustCliAllocWithOf J hIf extra γ mAddrs
    let spec := rustStdReallocSpec allocInst
    let x := (p, old, align, new, bs, lb, lk)
    SepWP P (s0.readReg64 Reg.lr) s
      (MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 ∗ extra ∗
       J.Block γ p old ∗ (p ↦ₛ bs) ∗
       memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
       ((((s0.sp - 64#64) ↦₆₄ sv0) ∗ ((s0.sp - 56#64) ↦₆₄ sv1) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
        (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
         stackFrameAt (s0.sp - 64#64 - 1024#64) 3008)))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => spec.onOom x s0 sf) := by
  intro allocInst spec x
  have hsp_s : decide (s.sp &&& 15#64 = 0#64) = true := by
    rw [hsp]; exact spAligned_sub64 hsp_align
  have hf11 := fetch_instr_at 11 (off := 0x2c#64) hCode; have hf12 := fetch_instr_at 12 (off := 0x30#64) hCode
  have hf13 := fetch_instr_at 13 (off := 0x34#64) hCode; have hf14 := fetch_instr_at 14 (off := 0x38#64) hCode
  have hf15 := fetch_instr_at 15 (off := 0x3c#64) hCode; have hf16 := fetch_instr_at 16 (off := 0x40#64) hCode
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  have hTake : bs.take new = bs := List.take_of_length_le hbsNew
  have hPreShape :
      (MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 ∗ extra ∗
       J.Block γ p old ∗ (p ↦ₛ bs) ∗
       memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
       ((((s0.sp - 64#64) ↦₆₄ sv0) ∗ ((s0.sp - 56#64) ↦₆₄ sv1) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
        (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
         stackFrameAt (s0.sp - 64#64 - 1024#64) 3008))) ⊢
      (MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 ∗ extra ∗
       J.Block γ p old ∗ (p ↦ₛ bs) ∗
       memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
       stackFrameAt s0.sp mallocngStackBytes) ∗
      stackFrameAt (s0.sp - 1024#64) 3072 := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right
        (repack_stack64_to_1024 s0.sp sv0 sv1 _ _ _ _ _ _)))))) ?_
    exact Entails.of_eq (by
      generalize MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 = Penv
      generalize stackFrameAt s0.sp mallocngStackBytes = Pstk1
      generalize stackFrameAt (s0.sp - 1024#64) 3072 = Pstk2
      ac_rfl)
  refine SepWP.weaken_pre hPreShape ?_
  refine SepWP.call_subroutine_frame (hC.realloc_ok γ)
    (x := (p, newBv, s0.sp, some (old, bs), s0.tpidrEl0, s0.brkStart, b, ivs0))
    (F := stackFrameAt (s0.sp - 1024#64) 3072)
    (ret_pc := s0.readReg64 Reg.lr)
    (by simp [arm64_norm]; bv_omega)
    (by simp [arm64_norm, hrun])
    (by simpa [State.spAligned, arm64_norm] using hsp_align)
    (by simp [arm64_norm])
    ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    ?_ ?_
  · intro R' hsat
    dsimp only [withExtra, ToBaseSpec.toSpec, mallocngReallocSpec, CondOwn, OptOwn, MallocngInitBlock]
    have hEnvEq : ∀ sPre : State,
        sPre.tpidrEl0 = s0.tpidrEl0 → sPre.brkStart = s0.brkStart → sPre.brk = s0.brk →
        MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 sPre =
        MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 := by
      intro sPre h1 h2 h3; unfold MallocngEnv; rw [h1, h2, h3]
    rw [hEnvEq _ (by simp [arm64_norm, hPres.2.2.2.1]) (by simp [arm64_norm, hPres.2.2.2.2.1])
      (by simp [arm64_norm, hBrk])]
    rw [sepConj_assoc] at hsat
    refine Satisfies.mono (sepConj_mono_left ?_) hsat
    have hp64 : p.toNat + old < 2 ^ 64 := Nat.lt_of_le_of_lt hp48 (by decide)
    refine Entails.trans ?_ (sepConj_mono_left (Entails.pure_right
      ⟨by simp [arm64_norm, hx0], by simp [arm64_norm], by simp [arm64_norm],
       ⟨hpNe, hpNe, hp16, hp64, hbsOld⟩, trivial⟩ (Entails.refl _)))
    exact Entails.of_eq (by
      generalize MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 = Penv
      generalize stackFrameAt s0.sp mallocngStackBytes = Pstk1
      ac_rfl)
  · intro sf hpc_f hrun_f hsp_f hcs_f
    have hsp_sf : sf.sp = s0.sp := by simpa [arm64_norm] using hsp_f
    have hcs_s0 : CalleeSavedPreserved s0 sf := by
      refine CalleeSavedPreserved.trans ?_ hcs_f
      unfold CalleeSavedPreserved
      simp [arm64_norm, hx23, hx24, hx25, hx26, hx27, hx28, hcs_v]
    refine SepWP.done hpc_f hrun_f ⟨fun hsat => ?_, hsp_sf, hcs_s0⟩
    dsimp only [withExtra, ToBaseSpec.toSpec, mallocngReallocSpec] at hsat
    dsimp only [spec, x, rustStdReallocSpec]
    rw [hNewNat] at hsat
    by_cases hMax : new ≤ MallocngMaxAllocSize
    · have hOkT : decide (new ≤ MallocngMaxAllocSize) = true := decide_eq_true hMax
      rw [hOkT] at hsat
      dsimp only [CondOwn, OptOwn, MallocngInitBlock] at hsat
      simp only [↓reduceIte, Option.map_some, Option.getD_some, hTake, emp_sepConj] at hsat
      apply (fun e => Satisfies.mono e hsat)
      refine sepConj_mono_left ?_
      simp only [sepConj_assoc]
      refine Entails.pure_left fun ⟨_, ⟨hretNe, _, h16Ret, _, _⟩, hAcc⟩ => ?_
      have hPresSf : AllocCallPreserved s0 sf := by
        refine allocCallPreserved_trans hPres ?_
        refine allocCallPreserved_of_fields_eq (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp [arm64_norm])
          (allocCallPreserved_of_mallocngProcPreserved hAcc.1)
      have hAlBv16 : alignBv.toNat ≤ 16 := by rwa [hAlignNat]
      have hMod : (sf.readReg64 .x0).toNat % align = 0 := by
        rw [← hAlignNat]
        exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (isPow2Align_dvd_16 hPow2 hAlBv16) h16Ret)
      have hretNe0 : sf.readReg64 .x0 ≠ 0 := hretNe
      simp only [hretNe0, ↓reduceIte]
      refine Entails.pure_right hPresSf ?_
      rw [pathA_ok_rearr, ← hookFrame_eq_stack1024 s0.sp]
      refine Entails.trans (sepConj_mono_left (postEnv_withExtra_entails_errno_pool hIf extra γ
        mAddrs _ ivs0 (lb + allocInst.cost new align - allocInst.cost old align) lk s0 _ sf)) ?_
      have hLive : J.Block γ (sf.readReg64 .x0) new ⊢ allocInst.live (sf.readReg64 .x0) new align :=
        Entails.pure_right ⟨hMod, hLayoutNew⟩ (Entails.refl _)
      refine Entails.trans (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (Entails.pure_right hMod hLive)))) ?_
      exact Entails.of_eq (by
        generalize StdErrnoCell s0.tpidrEl0 = Perrno
        generalize allocInst.pool (lb + allocInst.cost new align - allocInst.cost old align) lk sf = Ppool
        generalize Rust.hookFrame s0.sp = Phook
        generalize allocInst.live (sf.readReg64 .x0) new align = Plive
        ac_rfl)
    · have hOkF : decide (new ≤ MallocngMaxAllocSize) = false := decide_eq_false hMax
      rw [hOkF] at hsat
      dsimp only [CondOwn, OptOwn, MallocngInitBlock] at hsat
      simp only [Bool.false_eq_true, ↓reduceIte, mallocngReallocBudget] at hsat
      apply (fun e => Satisfies.mono e hsat)
      refine sepConj_mono_left ?_
      simp only [sepConj_assoc]
      refine Entails.pure_left fun ⟨_, _, hAcc⟩ => ?_
      have hPresSf : AllocCallPreserved s0 sf := by
        refine allocCallPreserved_trans hPres ?_
        refine allocCallPreserved_of_fields_eq (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp [arm64_norm])
          (allocCallPreserved_of_mallocngProcPreserved hAcc.1)
      have hNull : NullAllowed new align := by
        unfold MallocngMaxAllocSize at hMax
        unfold NullAllowed
        omega
      rw [pathA_fail_rearr, ← hookFrame_eq_stack1024 s0.sp]
      refine Entails.pure_left fun hret0 => ?_
      have hret0' : sf.readReg64 .x0 = 0 := hret0
      simp only [hret0', ↓reduceIte]
      refine Entails.pure_right hPresSf ?_
      refine Entails.trans (sepConj_mono_left (postEnv_withExtra_entails_errno_pool hIf extra γ
        mAddrs b ivs0 lb lk s0 _ sf)) ?_
      have hLiveOld : J.Block γ p old ⊢ allocInst.live p old align :=
        Entails.pure_right ⟨hpMod, hLayoutOld⟩ (Entails.refl _)
      refine Entails.trans (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (Entails.pure_right hNull hLiveOld)))) ?_
      exact Entails.of_eq (by
        generalize StdErrnoCell s0.tpidrEl0 = Perrno
        generalize allocInst.pool lb lk sf = Ppool
        generalize Rust.hookFrame s0.sp = Phook
        generalize allocInst.live p old align = Plive
        ac_rfl)
  · intro R' sf _ hsat
    dsimp only [withExtra, ToBaseSpec.toSpec, mallocngReallocSpec] at hsat
    dsimp only [spec, x, rustStdReallocSpec]
    have hsat' := satisfies_drop_mid hsat
    rw [satisfies_pure_sepConj] at hsat' ⊢
    obtain ⟨hoom, hR'⟩ := hsat'
    obtain ⟨hfs_f, htr_f, hsig_f⟩ := oomCond_imp_preserved hoom
    simp only [arm64_norm] at hfs_f htr_f hsig_f
    exact ⟨⟨hfs_f.trans hPres.1, htr_f.trans hPres.2.1, hsig_f.trans hPres.2.2.1⟩, hR'⟩

/-! ## Slow Path B Failure (`+0x64..+0x6c`) -/

private theorem rdlRealloc_pathB_fail {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (extra : SepProp) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs}
    {reallocAddr cReallocAddr posixMemalignAddr memcpyAddr freeAddr : BitVec 64}
    (hCode : hasInstrs P reallocAddr
      (rdlReallocInstrs reallocAddr cReallocAddr posixMemalignAddr memcpyAddr freeAddr))
    (p alignBv newBv : BitVec 64) (old align new lb lk : Nat) (bs : List (BitVec 8))
    (sv0 : BitVec 64) (R : SepProp) (s0 s2 : State)
    (hsp_align : s0.spAligned = true)
    (hAlignNat : alignBv.toNat = align) (hNewNat : newBv.toNat = new)
    (hLayoutOld : RustLayoutOk old align) (hpMod : p.toNat % align = 0)
    (hNotFit : ¬ MallocngLayoutFit newBv alignBv)
    (hpc2 : s2.pc = reallocAddr + 0x64#64) (hrun2 : s2.status = .Running) (hsp2 : s2.sp = s0.sp - 64#64)
    (hRet32 : s2.readReg32 .x0 = 12#32)
    (hx23 : s2.readReg64 .x23 = s0.readReg64 .x23) (hx24 : s2.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s2.readReg64 .x25 = s0.readReg64 .x25) (hx26 : s2.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s2.readReg64 .x27 = s0.readReg64 .x27) (hx28 : s2.readReg64 .x28 = s0.readReg64 .x28)
    (hcs_v : calleeSavedVRegs s2 = calleeSavedVRegs s0) (hPres2 : AllocCallPreserved s0 s2) :
    let allocInst := mallocngRustCliAllocWithOf J hIf extra γ mAddrs
    let spec := rustStdReallocSpec allocInst
    let x := (p, old, align, new, bs, lb, lk)
    SepWP P (s0.readReg64 Reg.lr) s2
      (memRegion (s0.sp - 56#64) 8 ∗
       StdErrnoCell s0.tpidrEl0 ∗ allocInst.pool lb lk s2 ∗
       J.Block γ p old ∗ (p ↦ₛ bs) ∗
       memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
       (((s0.sp - 64#64) ↦₆₄ sv0) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
       (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
        stackFrameAt (s0.sp - 64#64 - 1024#64) 3008))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => spec.onOom x s0 sf) := by
  intro allocInst spec x
  refine SepWP.weaken_pre (sepConj_mono_left (memRegion8_entails_pointsTo64 (s0.sp - 56#64))) ?_
  conv => arg 4; rw [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro w1
  refine SepWP.weaken_pre (P' :=
      ((((s0.sp - 64#64) ↦₆₄ sv0) ∗ ((s0.sp - 56#64) ↦₆₄ w1) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
       (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
        stackFrameAt (s0.sp - 64#64 - 1024#64) 3008) ∗
       (StdErrnoCell s0.tpidrEl0 ∗ allocInst.pool lb lk s2 ∗
        J.Block γ p old ∗ (p ↦ₛ bs) ∗
        memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length))))
    (Entails.of_eq (by
      generalize StdErrnoCell s0.tpidrEl0 = Perrno
      generalize allocInst.pool lb lk s2 = Ppool
      generalize stackFrameAt (s0.sp - 64#64) mallocngStackBytes = Pstk1
      generalize stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 = Pstk2
      ac_rfl)) ?_
  have hf25 := fetch_instr_at 25 (off := 0x64#64) hCode
  have hf26 := fetch_instr_at 26 (off := 0x68#64) hCode
  have hf27 := fetch_instr_at 27 (off := 0x6c#64) hCode
  wp_step; wp_step; wp_step
  wp_if hc
  · apply rdlRealloc_epilogue hCode s0 _ sv0 w1 _ _ _ hsp_align
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun2]) (by simp [arm64_norm, hsp2])
      (by simp [arm64_norm, hx23]) (by simp [arm64_norm, hx24]) (by simp [arm64_norm, hx25])
      (by simp [arm64_norm, hx26]) (by simp [arm64_norm, hx27]) (by simp [arm64_norm, hx28])
      (by simp [arm64_norm, hcs_v])
    intro sf hx0f hspf hcsf hPresEp hPoolEp
    simp only [arm64_norm] at hx0f
    refine ⟨fun hsat => ?_, hspf, hcsf⟩
    dsimp only [spec, x, rustStdReallocSpec]
    have hx0f0 : sf.readReg64 .x0 = 0 := hx0f
    simp only [hx0f0, ↓reduceIte]
    have hPresSf : AllocCallPreserved s0 sf := by
      refine allocCallPreserved_trans hPres2 ?_
      exact allocCallPreserved_of_fields_eq (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) hPresEp
    have hPool2f : PoolPreserved s2 sf := by
      rcases hPoolEp with ⟨hbs_ep, hbrk_ep, htp_ep⟩
      simp only [arm64_norm] at hbs_ep hbrk_ep htp_ep
      exact ⟨hbs_ep, hbrk_ep, htp_ep⟩
    have hPoolEq : allocInst.pool lb lk s2 = allocInst.pool lb lk sf :=
      (allocInst.pool_transport lb lk s2 sf hPool2f).symm
    have hNull : NullAllowed new align := by
      have hgt := not_layoutFit_imp_gt_2pow62 hNotFit
      rw [hNewNat, hAlignNat] at hgt
      exact hgt
    have hLiveOld : J.Block γ p old ⊢ allocInst.live p old align :=
      Entails.pure_right ⟨hpMod, hLayoutOld⟩ (Entails.refl _)
    apply (fun e => Satisfies.mono e hsat)
    refine sepConj_mono_left ?_
    rw [hPoolEq]
    refine Entails.pure_right hPresSf ?_
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (Entails.pure_right hNull hLiveOld))))) ?_
    exact Entails.of_eq (by
      generalize StdErrnoCell s0.tpidrEl0 = Perrno
      generalize allocInst.pool lb lk sf = Ppool
      generalize Rust.hookFrame s0.sp = Phook
      generalize allocInst.live p old align = Plive
      ac_rfl)
  · dsimp only [State.readReg32, Reg.x0] at hRet32
    rw [hRet32] at hc
    exact absurd hc (by decide)

/-! ## Slow Path B Free (`+0x8c..+0x94`) -/

private theorem pathB_free_post_rearr (Ppure Ppost Pstk1 extra Pframe : SepProp) :
    ((Ppure ∗ (Ppost ∗ Pstk1)) ∗ extra) ∗ Pframe =
      Ppure ∗ ((Ppost ∗ extra) ∗ Pstk1 ∗ Pframe) := by ac_rfl

private theorem rdlRealloc_pathB_free {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (extra : SepProp) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {cAddrs : MallocngCEntryAddrs}
    {reallocAddr memcpyAddr : BitVec 64}
    (hCode : hasInstrs P reallocAddr
      (rdlReallocInstrs reallocAddr cAddrs.realloc cAddrs.posixMemalign memcpyAddr cAddrs.free))
    (hC : MallocngProgCContractsWith J extra P mAddrs cAddrs)
    (p q : BitVec 64) (old align new lb lk : Nat) (bs : List (BitVec 8))
    (b1 : MallocngBudget) (ivs1 : List (BitVec 64 × Nat))
    (sv0 : BitVec 64) (R : SepProp) (s0 s3 : State)
    (hsp_align : s0.spAligned = true)
    (hLayoutNew : RustLayoutOk new align)
    (hpNe : p ≠ 0#64) (hp16 : 16 ∣ p.toNat) (hp48 : p.toNat + old ≤ 2 ^ 48)
    (hqNe : q ≠ 0#64) (hqMod : q.toNat % align = 0)
    (hpc3 : s3.pc = reallocAddr + 0x8c#64) (hrun3 : s3.status = .Running) (hsp3 : s3.sp = s0.sp - 64#64)
    (hx21_3 : s3.readReg64 .x21 = q) (hx22_3 : s3.readReg64 .x22 = p)
    (hx23_3 : s3.readReg64 .x23 = s0.readReg64 .x23) (hx24_3 : s3.readReg64 .x24 = s0.readReg64 .x24)
    (hx25_3 : s3.readReg64 .x25 = s0.readReg64 .x25) (hx26_3 : s3.readReg64 .x26 = s0.readReg64 .x26)
    (hx27_3 : s3.readReg64 .x27 = s0.readReg64 .x27) (hx28_3 : s3.readReg64 .x28 = s0.readReg64 .x28)
    (hcs_v3 : calleeSavedVRegs s3 = calleeSavedVRegs s0) (hPres3 : AllocCallPreserved s0 s3) :
    let allocInst := mallocngRustCliAllocWithOf J hIf extra γ mAddrs
    let spec := rustStdReallocSpec allocInst
    let x := (p, old, align, new, bs, lb, lk)
    SepWP P (s0.readReg64 Reg.lr) s3
      ((MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b1 ivs1 s3 ∗
        stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
        J.Block γ p old ∗ memRegion p old ∗ extra) ∗
       (J.Block γ q new ∗ (q ↦ₛ bs) ∗
        memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length) ∗
        stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 ∗
        (((s0.sp - 64#64) ↦₆₄ sv0) ∗ ((s0.sp - 56#64) ↦₆₄ q) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => spec.onOom x s0 sf) := by
  intro allocInst spec x
  have hsp_s3 : decide (s3.sp &&& 15#64 = 0#64) = true := by
    rw [hsp3]; exact spAligned_sub64 hsp_align
  have hf35 := fetch_instr_at 35 (off := 0x8c#64) hCode
  have hf36 := fetch_instr_at 36 (off := 0x90#64) hCode; have hf37 := fetch_instr_at 37 (off := 0x94#64) hCode
  wp_step; wp_step
  refine SepWP.call_subroutine_frame (hC.free_ok γ)
    (x := (p, s0.sp - 64#64, old, s0.tpidrEl0, s0.brkStart, b1, ivs1))
    (F := J.Block γ q new ∗ (q ↦ₛ bs) ∗ memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length) ∗
      stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 ∗
      (((s0.sp - 64#64) ↦₆₄ sv0) ∗ ((s0.sp - 56#64) ↦₆₄ q) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (ret_pc := reallocAddr + 0x94#64)
    (by simp [arm64_norm]; bv_omega) (by simp [arm64_norm, hrun3])
    (by simpa [State.spAligned, arm64_norm] using hsp_s3) (by simp [arm64_norm]) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
    (fun _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
  · intro R' hsat
    dsimp only [withExtra, ToBaseSpec.toSpec, mallocngFreeSpec, MallocngFreeableBlock]
    simp only [hpNe, ↓reduceIte]
    have hEnvEq : ∀ sPre : State,
        sPre.tpidrEl0 = s3.tpidrEl0 → sPre.brkStart = s3.brkStart → sPre.brk = s3.brk →
        MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b1 ivs1 sPre =
        MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b1 ivs1 s3 := by
      intro sPre h1 h2 h3; unfold MallocngEnv; rw [h1, h2, h3]
    rw [hEnvEq _ (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])]; rw [sepConj_assoc] at hsat
    refine Satisfies.mono (sepConj_mono_left ?_) hsat
    have hp64 : p.toNat + old < 2 ^ 64 := Nat.lt_of_le_of_lt hp48 (by decide)
    refine Entails.trans ?_ (sepConj_mono_left (Entails.pure_right
      ⟨by simp [arm64_norm], by simp [arm64_norm, hsp3], hp16, hp64⟩ (Entails.refl _)))
    exact Entails.of_eq (by
      generalize MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b1 ivs1 s3 = Penv
      generalize stackFrameAt (s0.sp - 64#64) mallocngStackBytes = Pstk1; ac_rfl)
  · intro s4 hpc4 hrun4 hsp4 hcs4
    simp only [CalleeSavedPreserved, arm64_norm] at hsp4 hcs4
    have hsp4' : s4.sp = s0.sp - 64#64 := hsp4.trans hsp3
    obtain ⟨_, _, hx21_4, _, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, _, hcs_v4⟩ := hcs4
    replace hx21_4 := hx21_4.trans hx21_3; replace hx23_4 := hx23_4.trans hx23_3
    replace hx24_4 := hx24_4.trans hx24_3; replace hx25_4 := hx25_4.trans hx25_3
    replace hx26_4 := hx26_4.trans hx26_3; replace hx27_4 := hx27_4.trans hx27_3
    replace hx28_4 := hx28_4.trans hx28_3; replace hcs_v4 := hcs_v4.trans hcs_v3
    dsimp only [withExtra, ToBaseSpec.toSpec, mallocngFreeSpec]
    conv => arg 4; simp only [emp_sepConj, sepConj_emp]; rw [pathB_free_post_rearr]
    apply SepWP.pure_elim; intro hAcc34; try simp only [true_and] at hAcc34
    have hPres4 : AllocCallPreserved s0 s4 :=
      allocCallPreserved_trans hPres3 (allocCallPreserved_of_fields_eq
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (allocCallPreserved_of_mallocngProcPreserved hAcc34.1))
    refine SepWP.weaken_pre (sepConj_mono_left
      (postEnv_withExtra_entails_errno_pool hIf extra γ mAddrs _ ivs1
        (lb + allocInst.cost new align - allocInst.cost old align) lk s0 _ s4)) ?_
    refine SepWP.weaken_pre (P' :=
        ((((s0.sp - 64#64) ↦₆₄ sv0) ∗ ((s0.sp - 56#64) ↦₆₄ q) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
         (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
          stackFrameAt (s0.sp - 64#64 - 1024#64) 3008) ∗
         (StdErrnoCell s0.tpidrEl0 ∗
          allocInst.pool (lb + allocInst.cost new align - allocInst.cost old align) lk s4 ∗
          J.Block γ q new ∗ (q ↦ₛ bs) ∗ memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length))))
      (Entails.of_eq (by
        generalize StdErrnoCell s0.tpidrEl0 = Perrno
        generalize allocInst.pool (lb + allocInst.cost new align - allocInst.cost old align) lk s4 = Ppool
        generalize stackFrameAt (s0.sp - 64#64) mallocngStackBytes = Pstk1
        generalize stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 = Pstk2; ac_rfl)) ?_
    wp_step
    apply rdlRealloc_epilogue hCode s0 _ sv0 q _ _ _ hsp_align
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun4]) (by simp [arm64_norm, hsp4'])
      (by simp [arm64_norm, hx23_4]) (by simp [arm64_norm, hx24_4]) (by simp [arm64_norm, hx25_4])
      (by simp [arm64_norm, hx26_4]) (by simp [arm64_norm, hx27_4]) (by simp [arm64_norm, hx28_4])
      (by simp [arm64_norm, hcs_v4])
    intro sf hx0f hspf hcsf hPresEp hPoolEp
    simp only [arm64_norm] at hx0f; try rw [hx21_4] at hx0f
    refine ⟨fun hsat => ?_, hspf, hcsf⟩
    dsimp only [spec, x, rustStdReallocSpec]
    have hqNe0 : q ≠ 0 := hqNe; rw [hx0f]; simp only [hqNe0, ↓reduceIte]
    have hPresSf : AllocCallPreserved s0 sf :=
      allocCallPreserved_trans hPres4 (allocCallPreserved_of_fields_eq
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) hPresEp)
    have hPool4f : PoolPreserved s4 sf := by
      rcases hPoolEp with ⟨hbs_ep, hbrk_ep, htp_ep⟩
      simp only [arm64_norm] at hbs_ep hbrk_ep htp_ep; exact ⟨hbs_ep, hbrk_ep, htp_ep⟩
    have hPoolEq :
        allocInst.pool (lb + allocInst.cost new align - allocInst.cost old align) lk s4 =
        allocInst.pool (lb + allocInst.cost new align - allocInst.cost old align) lk sf :=
      (allocInst.pool_transport _ lk s4 sf hPool4f).symm
    have hLiveNew : J.Block γ q new ⊢ allocInst.live q new align :=
      Entails.pure_right ⟨hqMod, hLayoutNew⟩ (Entails.refl _)
    apply (fun e => Satisfies.mono e hsat); refine sepConj_mono_left ?_
    rw [hPoolEq]; refine Entails.pure_right hPresSf ?_
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (Entails.pure_right hqMod hLiveNew))))) ?_
    exact Entails.of_eq (by
      generalize StdErrnoCell s0.tpidrEl0 = Perrno
      generalize allocInst.pool (lb + allocInst.cost new align - allocInst.cost old align) lk sf = Ppool
      generalize Rust.hookFrame s0.sp = Phook; generalize allocInst.live q new align = Plive; ac_rfl)

/-! ## Slow Path B Copy (`+0x64..+0x88`) -/

private theorem rdlRealloc_pathB_copy {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (extra : SepProp) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {cAddrs : MallocngCEntryAddrs}
    {reallocAddr memcpyAddr : BitVec 64}
    (hCode : hasInstrs P reallocAddr
      (rdlReallocInstrs reallocAddr cAddrs.realloc cAddrs.posixMemalign memcpyAddr cAddrs.free))
    (hC : MallocngProgCContractsWith J extra P mAddrs cAddrs)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpySpec)
    (p q oldBv newBv : BitVec 64) (old align new lb lk : Nat) (bs : List (BitVec 8))
    (b1 : MallocngBudget) (ivs1 : List (BitVec 64 × Nat))
    (sv0 : BitVec 64) (R : SepProp) (s0 s2 : State)
    (hsp_align : s0.spAligned = true)
    (hOldNat : oldBv.toNat = old) (hNewNat : newBv.toNat = new)
    (hLayoutNew : RustLayoutOk new align)
    (hpNe : p ≠ 0#64) (hp16 : 16 ∣ p.toNat) (hp48 : p.toNat + old ≤ 2 ^ 48)
    (hqNe : q ≠ 0#64) (hqMod : q.toNat % align = 0)
    (hbsOld : bs.length ≤ old) (hbsNew : bs.length ≤ new)
    (hpc2 : s2.pc = reallocAddr + 0x64#64) (hrun2 : s2.status = .Running) (hsp2 : s2.sp = s0.sp - 64#64)
    (hRet32 : s2.readReg32 .x0 = 0#32)
    (hx19_2 : s2.readReg64 .x19 = newBv) (hx20_2 : s2.readReg64 .x20 = oldBv) (hx22_2 : s2.readReg64 .x22 = p)
    (hx23_2 : s2.readReg64 .x23 = s0.readReg64 .x23) (hx24_2 : s2.readReg64 .x24 = s0.readReg64 .x24)
    (hx25_2 : s2.readReg64 .x25 = s0.readReg64 .x25) (hx26_2 : s2.readReg64 .x26 = s0.readReg64 .x26)
    (hx27_2 : s2.readReg64 .x27 = s0.readReg64 .x27) (hx28_2 : s2.readReg64 .x28 = s0.readReg64 .x28)
    (hcs_v2 : calleeSavedVRegs s2 = calleeSavedVRegs s0) (hPres2 : AllocCallPreserved s0 s2) :
    let allocInst := mallocngRustCliAllocWithOf J hIf extra γ mAddrs
    let spec := rustStdReallocSpec allocInst
    let x := (p, old, align, new, bs, lb, lk)
    SepWP P (s0.readReg64 Reg.lr) s2
      (MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b1 ivs1 s2 ∗ extra ∗
       J.Block γ q new ∗ memRegion q new ∗
       J.Block γ p old ∗ (p ↦ₛ bs) ∗
       memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
       ((((s0.sp - 64#64) ↦₆₄ sv0) ∗ ((s0.sp - 56#64) ↦₆₄ q) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
        (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
         stackFrameAt (s0.sp - 64#64 - 1024#64) 3008)))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => spec.onOom x s0 sf) := by
  intro allocInst spec x
  have hsp_s2 : decide (s2.sp &&& 15#64 = 0#64) = true := by
    rw [hsp2]; exact spAligned_sub64 hsp_align
  have hSlot2 : s2.sp + 8#64 = s0.sp - 56#64 := by rw [hsp2]; bv_omega
  conv => arg 4; rw [← hSlot2]
  have hf25 := fetch_instr_at 25 (off := 0x64#64) hCode; have hf26 := fetch_instr_at 26 (off := 0x68#64) hCode
  have hf27 := fetch_instr_at 27 (off := 0x6c#64) hCode; have hf28 := fetch_instr_at 28 (off := 0x70#64) hCode
  have hf29 := fetch_instr_at 29 (off := 0x74#64) hCode; have hf30 := fetch_instr_at 30 (off := 0x78#64) hCode
  have hf31 := fetch_instr_at 31 (off := 0x7c#64) hCode; have hf32 := fetch_instr_at 32 (off := 0x80#64) hCode
  have hf33 := fetch_instr_at 33 (off := 0x84#64) hCode; have hf34 := fetch_instr_at 34 (off := 0x88#64) hCode
  wp_step; wp_step; wp_step
  wp_if hc
  · dsimp only [State.readReg32, Reg.x0] at hRet32
    rw [hRet32] at hc
    exact absurd hc (by decide)
  · wp_step; wp_step
    wp_if hq0
    · exact absurd hq0 hqNe
    · conv => arg 4; rw [hSlot2]
      wp_step; wp_step; wp_step; wp_step; wp_step
      let copyBv : BitVec 64 := if newBv.ult oldBv = true then newBv else oldBv
      have hOldLt64 : old < 2 ^ 64 := hOldNat ▸ oldBv.isLt
      have hNewLt64 : new < 2 ^ 64 := hNewNat ▸ newBv.isLt
      have hCopyBounds : bs.length ≤ copyBv.toNat ∧ copyBv.toNat ≤ old ∧ copyBv.toNat ≤ new := by
        dsimp only [copyBv]
        by_cases hcc : newBv.ult oldBv = true
        · have hlt : new < old := by
            rw [← hNewNat, ← hOldNat]; simpa [BitVec.ult] using hcc
          simp only [hcc, ↓reduceIte, hNewNat]; omega
        · have hnlt : ¬ (new < old) := by
            rw [← hNewNat, ← hOldNat]; simpa [BitVec.ult] using hcc
          simp only [hcc, Bool.false_eq_true, ↓reduceIte, hOldNat]; omega
      obtain ⟨hCopy1, hCopy2, hCopy3⟩ := hCopyBounds
      let Pstk64 : SepProp :=
        (((s0.sp - 64#64) ↦₆₄ sv0) ∗ ((s0.sp - 56#64) ↦₆₄ q) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      have hPrep :
          (MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b1 ivs1 s2 ∗ extra ∗
           J.Block γ q new ∗ memRegion q new ∗
           J.Block γ p old ∗ (p ↦ₛ bs) ∗
           memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
           (Pstk64 ∗ (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
            stackFrameAt (s0.sp - 64#64 - 1024#64) 3008))) ⊢
          ∃∗ midBs : List (BitVec 8),
            ⌜(bs ++ midBs).length = copyBv.toNat⌝ ∗
            (memRegion q (bs ++ midBs).length ∗ (p ↦ₛ (bs ++ midBs))) ∗
            (MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b1 ivs1 s2 ∗ extra ∗
             J.Block γ q new ∗ J.Block γ p old ∗
             memRegion (p + BitVec.ofNat 64 copyBv.toNat) (old - copyBv.toNat) ∗
             memRegion (q + BitVec.ofNat 64 copyBv.toNat) (new - copyBv.toNat) ∗
             (Pstk64 ∗ (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
              stackFrameAt (s0.sp - 64#64 - 1024#64) 3008))) := by
        have hRe1 :
            (MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b1 ivs1 s2 ∗ extra ∗
             J.Block γ q new ∗ memRegion q new ∗
             J.Block γ p old ∗ (p ↦ₛ bs) ∗
             memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
             (Pstk64 ∗ (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
              stackFrameAt (s0.sp - 64#64 - 1024#64) 3008))) =
            (((p ↦ₛ bs) ∗ memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
              memRegion q new) ∗
             (MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b1 ivs1 s2 ∗ extra ∗
              J.Block γ q new ∗ J.Block γ p old ∗
              (Pstk64 ∗ (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
               stackFrameAt (s0.sp - 64#64 - 1024#64) 3008)))) := by
          generalize MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b1 ivs1 s2 = Penv
          generalize (Pstk64 ∗ (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
            stackFrameAt (s0.sp - 64#64 - 1024#64) 3008)) = Pstk
          ac_rfl
        rw [hRe1]
        refine Entails.trans (sepConj_mono_left
          (allocMemcpy_prep_entails p q bs old new copyBv.toNat hCopy1 hCopy2 hCopy3
            (Nat.le_of_lt hOldLt64) (Nat.le_of_lt hNewLt64))) ?_
        simp only [sepExists_sepConj_left]
        refine Entails.sepExists_mono fun midBs => Entails.of_eq (by
          generalize MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b1 ivs1 s2 = Penv
          generalize (Pstk64 ∗ (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
            stackFrameAt (s0.sp - 64#64 - 1024#64) 3008)) = Pstk
          ac_rfl)
      refine SepWP.weaken_pre hPrep ?_
      apply SepWP.exists_elim; intro midBs; apply SepWP.pure_elim; intro hsrcLen
      refine SepWP.call_subroutine_frame hMemcpy (x := (q, p, bs ++ midBs))
        (F := MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b1 ivs1 s2 ∗ extra ∗
          J.Block γ q new ∗ J.Block γ p old ∗
          memRegion (p + BitVec.ofNat 64 copyBv.toNat) (old - copyBv.toNat) ∗
          memRegion (q + BitVec.ofNat 64 copyBv.toNat) (new - copyBv.toNat) ∗
          (Pstk64 ∗ (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
           stackFrameAt (s0.sp - 64#64 - 1024#64) 3008)))
        (ret_pc := reallocAddr + 0x8c#64)
        (by simp [arm64_norm]; bv_omega) (by simp [arm64_norm, hrun2])
        (by simpa [State.spAligned, arm64_norm] using hsp_s2) (by simp [arm64_norm]) ?_
        (fun _ _ _ hp => not_satisfies_false_sepConj hp)
        (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
        (fun _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
      · intro R' hsat
        dsimp only [allocMemcpySpec]; rw [sepConj_assoc] at hsat
        refine Satisfies.mono (sepConj_mono_left ?_) hsat
        have hbvEq : BitVec.ofNat 64 (bs ++ midBs).length = copyBv := by rw [hsrcLen]; simp
        exact Entails.pure_right ⟨by simp [arm64_norm], by simp [arm64_norm],
          by rw [hbvEq]; simp [arm64_norm, copyBv],
          by rw [hsrcLen]; exact copyBv.isLt⟩ (Entails.refl _)
      · intro s3 hpc3 hrun3 hsp3 hcs3
        simp only [CalleeSavedPreserved, arm64_norm] at hsp3 hcs3
        have hsp3' : s3.sp = s0.sp - 64#64 := hsp3.trans hsp2
        obtain ⟨_, _, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, _, hcs_v3⟩ := hcs3
        replace hx22_3 := hx22_3.trans hx22_2; replace hx23_3 := hx23_3.trans hx23_2
        replace hx24_3 := hx24_3.trans hx24_2; replace hx25_3 := hx25_3.trans hx25_2
        replace hx26_3 := hx26_3.trans hx26_2; replace hx27_3 := hx27_3.trans hx27_2
        replace hx28_3 := hx28_3.trans hx28_2; replace hcs_v3 := hcs_v3.trans hcs_v2
        dsimp only [allocMemcpySpec]; rw [sepConj_assoc]
        apply SepWP.pure_elim; rintro ⟨_, hPresMc, hBrkMc⟩
        have hPres3 : AllocCallPreserved s0 s3 :=
          allocCallPreserved_trans hPres2 (allocCallPreserved_of_fields_eq
            (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
            (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
            (by simp [arm64_norm]) hPresMc)
        have hEnvEq3 : MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b1 ivs1 s2 =
            MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b1 ivs1 s3 := by
          have htp3 : s3.tpidrEl0 = s2.tpidrEl0 := by simpa [arm64_norm] using hPresMc.2.2.2.1
          have hbs3 : s3.brkStart = s2.brkStart := by simpa [arm64_norm] using hPresMc.2.2.2.2.1
          have hbrk3 : s3.brk = s2.brk := by simpa [arm64_norm] using hBrkMc
          unfold MallocngEnv; rw [htp3, hbs3, hbrk3]
        have hFin :
            (((q ↦ₛ (bs ++ midBs)) ∗ (p ↦ₛ (bs ++ midBs))) ∗
             (MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b1 ivs1 s2 ∗ extra ∗
              J.Block γ q new ∗ J.Block γ p old ∗
              memRegion (p + BitVec.ofNat 64 copyBv.toNat) (old - copyBv.toNat) ∗
              memRegion (q + BitVec.ofNat 64 copyBv.toNat) (new - copyBv.toNat) ∗
              (Pstk64 ∗ (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
               stackFrameAt (s0.sp - 64#64 - 1024#64) 3008)))) ⊢
            ((MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b1 ivs1 s3 ∗
              stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗ J.Block γ p old ∗ memRegion p old ∗ extra) ∗
             (J.Block γ q new ∗ (q ↦ₛ bs) ∗ memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length) ∗
              stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 ∗ Pstk64)) := by
          rw [hEnvEq3]
          have hRe2 :
              (((q ↦ₛ (bs ++ midBs)) ∗ (p ↦ₛ (bs ++ midBs))) ∗
               (MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b1 ivs1 s3 ∗ extra ∗
                J.Block γ q new ∗ J.Block γ p old ∗
                memRegion (p + BitVec.ofNat 64 copyBv.toNat) (old - copyBv.toNat) ∗
                memRegion (q + BitVec.ofNat 64 copyBv.toNat) (new - copyBv.toNat) ∗
                (Pstk64 ∗ (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
                 stackFrameAt (s0.sp - 64#64 - 1024#64) 3008)))) =
              (((q ↦ₛ (bs ++ midBs)) ∗ (p ↦ₛ (bs ++ midBs)) ∗
                memRegion (p + BitVec.ofNat 64 copyBv.toNat) (old - copyBv.toNat) ∗
                memRegion (q + BitVec.ofNat 64 copyBv.toNat) (new - copyBv.toNat)) ∗
               (MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b1 ivs1 s3 ∗ extra ∗
                J.Block γ q new ∗ J.Block γ p old ∗ stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
                stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 ∗ Pstk64)) := by
            generalize MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b1 ivs1 s3 = Penv
            generalize stackFrameAt (s0.sp - 64#64) mallocngStackBytes = Pstk1
            generalize stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 = Pstk2; ac_rfl
          rw [hRe2]
          refine Entails.trans (sepConj_mono_left
            (copyFinish_entails p q bs midBs old new copyBv.toNat hsrcLen hCopy2 hCopy3
              (Nat.le_of_lt hOldLt64) (Nat.le_of_lt hNewLt64))) ?_
          exact Entails.of_eq (by
            generalize MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b1 ivs1 s3 = Penv
            generalize stackFrameAt (s0.sp - 64#64) mallocngStackBytes = Pstk1
            generalize stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 = Pstk2; ac_rfl)
        refine SepWP.weaken_pre hFin ?_
        exact rdlRealloc_pathB_free hIf extra γ hCode hC p q old align new lb lk bs b1 ivs1 sv0 R
          s0 s3 hsp_align hLayoutNew hpNe hp16 hp48 hqNe hqMod hpc3 hrun3 hsp3' hx21_3 hx22_3
          hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hcs_v3 hPres3

/-! ## Slow Path B `posix_memalign` (`+0x44..+0x60`) -/

private theorem pathB_posix_post_rearr (Ppure Pslot Ppost Pstk1 extra Pframe : SepProp) :
    ((Ppure ∗ (Pslot ∗ (Ppost ∗ Pstk1))) ∗ extra) ∗ Pframe =
      Ppure ∗ (Pslot ∗ (Ppost ∗ extra) ∗ Pstk1 ∗ Pframe) := by ac_rfl

private theorem rdlRealloc_pathB_posix {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (extra : SepProp) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {cAddrs : MallocngCEntryAddrs}
    {reallocAddr memcpyAddr : BitVec 64}
    (hCode : hasInstrs P reallocAddr
      (rdlReallocInstrs reallocAddr cAddrs.realloc cAddrs.posixMemalign memcpyAddr cAddrs.free))
    (hC : MallocngProgCContractsWith J extra P mAddrs cAddrs)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpySpec)
    (p oldBv alignBv newBv : BitVec 64) (old align new lb lk : Nat) (bs : List (BitVec 8))
    (b : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (sv0 sv1 : BitVec 64) (R : SepProp) (s0 s1 : State)
    (hsp_align : s0.spAligned = true)
    (hOldNat : oldBv.toNat = old) (hAlignNat : alignBv.toNat = align) (hNewNat : newBv.toNat = new)
    (hLayoutNew : RustLayoutOk new align) (hLayoutOld : RustLayoutOk old align)
    (hpMod : p.toNat % align = 0)
    (hPow2 : IsPow2Align alignBv) (hAlMax : alignBv.toNat ≤ MaxAlignedAllocAlign)
    (hpNe : p ≠ 0#64) (hp16 : 16 ∣ p.toNat) (hp48 : p.toNat + old ≤ 2 ^ 48)
    (hbsOld : bs.length ≤ old) (hbsNew : bs.length ≤ new)
    (hpc1 : s1.pc = reallocAddr + 0x44#64) (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 64#64)
    (hx0_1 : s1.readReg64 .x0 = p) (hx2_1 : s1.readReg64 .x2 = alignBv)
    (hx19_1 : s1.readReg64 .x19 = newBv) (hx20_1 : s1.readReg64 .x20 = oldBv)
    (hx23_1 : s1.readReg64 .x23 = s0.readReg64 .x23) (hx24_1 : s1.readReg64 .x24 = s0.readReg64 .x24)
    (hx25_1 : s1.readReg64 .x25 = s0.readReg64 .x25) (hx26_1 : s1.readReg64 .x26 = s0.readReg64 .x26)
    (hx27_1 : s1.readReg64 .x27 = s0.readReg64 .x27) (hx28_1 : s1.readReg64 .x28 = s0.readReg64 .x28)
    (hcs_v1 : calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (hPres1 : AllocCallPreserved s0 s1) (hBrk1 : s1.brk = s0.brk) :
    let allocInst := mallocngRustCliAllocWithOf J hIf extra γ mAddrs
    let spec := rustStdReallocSpec allocInst
    let x := (p, old, align, new, bs, lb, lk)
    SepWP P (s0.readReg64 Reg.lr) s1
      (MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 ∗ extra ∗
       J.Block γ p old ∗ (p ↦ₛ bs) ∗
       memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
       ((((s0.sp - 64#64) ↦₆₄ sv0) ∗ ((s0.sp - 56#64) ↦₆₄ sv1) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
        (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
         stackFrameAt (s0.sp - 64#64 - 1024#64) 3008)))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => spec.onOom x s0 sf) := by
  intro allocInst spec x
  have hsp_s1 : decide (s1.sp &&& 15#64 = 0#64) = true := by
    rw [hsp1]; exact spAligned_sub64 hsp_align
  let effAlign : BitVec 64 := if (8#64).ult alignBv = true then alignBv else 8#64
  have hEffDisj : (effAlign = alignBv ∧ 8 < alignBv.toNat) ∨
      (effAlign = 8#64 ∧ alignBv.toNat ≤ 8) := by
    dsimp only [effAlign]
    by_cases hhi : (8#64).ult alignBv = true
    · exact Or.inl ⟨by simp [hhi], by simpa [BitVec.ult] using hhi⟩
    · exact Or.inr ⟨by simp [hhi], by
        have hn : ¬ (8 < alignBv.toNat) := by simpa [BitVec.ult] using hhi
        omega⟩
  obtain ⟨hEffMax, hMax16, _hEffSz, hPosixOk, hPosixRet⟩ :=
    rdlRealloc_effAlign_props (new := newBv) hPow2 hAlMax hEffDisj
  have hf17 := fetch_instr_at 17 (off := 0x44#64) hCode; have hf18 := fetch_instr_at 18 (off := 0x48#64) hCode
  have hf19 := fetch_instr_at 19 (off := 0x4c#64) hCode; have hf20 := fetch_instr_at 20 (off := 0x50#64) hCode
  have hf21 := fetch_instr_at 21 (off := 0x54#64) hCode; have hf22 := fetch_instr_at 22 (off := 0x58#64) hCode
  have hf23 := fetch_instr_at 23 (off := 0x5c#64) hCode; have hf24 := fetch_instr_at 24 (off := 0x60#64) hCode
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  have hSlot1 : s1.sp + 8#64 = s0.sp - 56#64 := by rw [hsp1]; bv_omega
  conv => arg 4; rw [← hSlot1]
  wp_step
  conv => arg 4; rw [hSlot1]
  wp_step
  let F_saved : SepProp :=
    ((s0.sp - 64#64) ↦₆₄ sv0) ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
  have hPreP :
      (MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 ∗ extra ∗
       J.Block γ p old ∗ (p ↦ₛ bs) ∗
       memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
       ((((s0.sp - 64#64) ↦₆₄ sv0) ∗ ((s0.sp - 56#64) ↦₆₄ 0#64) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
        (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
         stackFrameAt (s0.sp - 64#64 - 1024#64) 3008))) ⊢
      (memRegion (s0.sp - 56#64) 8 ∗
       MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 ∗
       stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗ extra) ∗
      (J.Block γ p old ∗ (p ↦ₛ bs) ∗
       memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
       F_saved ∗ stackFrameAt (s0.sp - 64#64 - 1024#64) 3008) := by
    dsimp only [F_saved]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right
        (sepConj_mono_left (pointsTo64_entails_memRegion (s0.sp - 56#64) 0#64))))))))) ?_
    exact Entails.of_eq (by
      generalize MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 = Penv
      generalize stackFrameAt (s0.sp - 64#64) mallocngStackBytes = Pstk1
      generalize stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 = Pstk2
      ac_rfl)
  refine SepWP.weaken_pre hPreP ?_
  refine SepWP.call_subroutine_frame (hC.posixMemalign_ok γ)
    (x := (s0.sp - 56#64, effAlign, newBv, s0.sp - 64#64, s0.tpidrEl0, s0.brkStart, b, ivs0))
    (F := J.Block γ p old ∗ (p ↦ₛ bs) ∗ memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
      F_saved ∗ stackFrameAt (s0.sp - 64#64 - 1024#64) 3008)
    (ret_pc := reallocAddr + 0x64#64)
    (by simp [arm64_norm]; bv_omega) (by simp [arm64_norm, hrun1])
    (by simpa [State.spAligned, arm64_norm] using hsp_s1) (by simp [arm64_norm]) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_ ?_
  · intro R' hsat
    dsimp only [withExtra, ToBaseSpec.toSpec, mallocngPosixMemalignSpec]
    have hEnvEq : ∀ sPre : State,
        sPre.tpidrEl0 = s0.tpidrEl0 → sPre.brkStart = s0.brkStart → sPre.brk = s0.brk →
        MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 sPre =
        MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 := by
      intro sPre h1 h2 h3; unfold MallocngEnv; rw [h1, h2, h3]
    rw [hEnvEq _ (by simp [arm64_norm, hPres1.2.2.2.1]) (by simp [arm64_norm, hPres1.2.2.2.2.1])
      (by simp [arm64_norm, hBrk1])]
    rw [sepConj_assoc] at hsat
    refine Satisfies.mono (sepConj_mono_left ?_) hsat
    refine Entails.trans ?_ (sepConj_mono_left (Entails.pure_right
      ⟨by simp [arm64_norm], by simp [arm64_norm, effAlign],
       by simp [arm64_norm], by simp [arm64_norm, hsp1], trivial, trivial, trivial, hEffMax⟩
      (Entails.refl _)))
    exact Entails.of_eq (by
      generalize MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 = Penv
      generalize stackFrameAt (s0.sp - 64#64) mallocngStackBytes = Pstk1; ac_rfl)
  · intro s2 hpc2 hrun2 hsp2 hcs2
    simp only [CalleeSavedPreserved, arm64_norm] at hsp2 hcs2
    have hsp2' : s2.sp = s0.sp - 64#64 := hsp2.trans hsp1
    obtain ⟨hx19_2, hx20_2, _, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _, hcs_v2⟩ := hcs2
    replace hx19_2 := hx19_2.trans hx19_1; replace hx20_2 := hx20_2.trans hx20_1
    replace hx23_2 := hx23_2.trans hx23_1; replace hx24_2 := hx24_2.trans hx24_1
    replace hx25_2 := hx25_2.trans hx25_1; replace hx26_2 := hx26_2.trans hx26_1
    replace hx27_2 := hx27_2.trans hx27_1; replace hx28_2 := hx28_2.trans hx28_1
    replace hcs_v2 := hcs_v2.trans hcs_v1
    dsimp only [withExtra, ToBaseSpec.toSpec, mallocngPosixMemalignSpec]
    rw [hPosixOk, hPosixRet]
    conv => arg 4; rw [pathB_posix_post_rearr]
    apply SepWP.pure_elim; rintro ⟨_, hRet32, hAcc12⟩
    have hPres2 : AllocCallPreserved s0 s2 :=
      allocCallPreserved_trans hPres1 (allocCallPreserved_of_fields_eq
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (allocCallPreserved_of_mallocngProcPreserved hAcc12.1))
    by_cases hFit : MallocngLayoutFit newBv alignBv
    · rw [decide_eq_true hFit]; simp only [hFit, ↓reduceIte] at hRet32 ⊢
      dsimp only [OptOutPtr, outPtrPost, MallocngBlock]
      conv => arg 4; rw [sepExists_sepConj_left]
      apply SepWP.exists_elim; intro q
      conv => arg 4; rw [sepConj_assoc]
      apply SepWP.pure_elim; rintro ⟨hqNe, hqAlignEff, _⟩
      rw [hMax16] at hqAlignEff
      have hqMod : q.toNat % align = 0 := by
        rw [← hAlignNat]
        exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (isPow2Align_dvd_max16 hPow2) hqAlignEff)
      unfold MallocngPostEnv
      conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro ivs1
      conv => arg 4; rw [sepConj_comm (((s0.sp - 56#64) ↦₆₄ q) ∗ _) _]; simp only [sepConj_assoc]
      apply SepWP.pure_elim; intro _hNoOrph; rw [hNewNat]
      refine SepWP.weaken_pre (Entails.of_eq ?_)
        (rdlRealloc_pathB_copy hIf extra γ hCode hC hMemcpy p q oldBv newBv old align new lb lk bs
          (mallocngAlignedBudget true effAlign.toNat new b) ivs1 sv0 R s0 s2 hsp_align
          hOldNat hNewNat hLayoutNew hpNe hp16 hp48 hqNe hqMod hbsOld hbsNew
          hpc2 hrun2 hsp2' hRet32 hx19_2 hx20_2 hx22_2
          hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hcs_v2 hPres2)
      dsimp only [F_saved]
      generalize MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart _ ivs1 s2 = Penv
      generalize stackFrameAt (s0.sp - 64#64) mallocngStackBytes = Pstk1
      generalize stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 = Pstk2; ac_rfl
    · rw [decide_eq_false hFit]; simp only [hFit, Bool.false_eq_true, ↓reduceIte] at hRet32 ⊢
      dsimp only [OptOutPtr]
      refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left
        (postEnv_withExtra_entails_errno_pool hIf extra γ mAddrs _ ivs0 lb lk s0 _ s2))) ?_
      refine SepWP.weaken_pre (Entails.of_eq ?_)
        (rdlRealloc_pathB_fail hIf extra γ hCode p alignBv newBv old align new lb lk bs sv0 R s0 s2
          hsp_align hAlignNat hNewNat hLayoutOld hpMod hFit hpc2 hrun2 hsp2' hRet32
          hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hcs_v2 hPres2)
      dsimp only [F_saved]
      generalize StdErrnoCell s0.tpidrEl0 = Perrno; generalize allocInst.pool lb lk s2 = Ppool
      generalize stackFrameAt (s0.sp - 64#64) mallocngStackBytes = Pstk1
      generalize stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 = Pstk2; ac_rfl
  · intro R' sf _ hsat
    dsimp only [withExtra, ToBaseSpec.toSpec, mallocngPosixMemalignSpec] at hsat
    dsimp only [spec, x, rustStdReallocSpec]
    have hsat' := satisfies_drop_mid hsat
    rw [satisfies_pure_sepConj] at hsat' ⊢
    obtain ⟨hoom, hR'⟩ := hsat'
    obtain ⟨hfs_f, htr_f, hsig_f⟩ := oomCond_imp_preserved hoom
    simp only [arm64_norm] at hfs_f htr_f hsig_f
    exact ⟨⟨hfs_f.trans hPres1.1, htr_f.trans hPres1.2.1, hsig_f.trans hPres1.2.2.1⟩, hR'⟩

/-! ## Placed `__rdl_realloc` and Thunk Contracts -/

private theorem unpack_stack64 (sp : BitVec 64) :
    stackFrameAt sp 64 ⊢
      ∃∗ sv0 : BitVec 64, ∃∗ sv1 : BitVec 64, ∃∗ sv2 : BitVec 64, ∃∗ sv3 : BitVec 64,
      ∃∗ sv4 : BitVec 64, ∃∗ sv5 : BitVec 64, ∃∗ sv6 : BitVec 64, ∃∗ sv7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ sv0) ∗ ((sp - 56#64) ↦₆₄ sv1) ∗ ((sp - 48#64) ↦₆₄ sv2) ∗
        ((sp - 40#64) ↦₆₄ sv3) ∗ ((sp - 32#64) ↦₆₄ sv4) ∗ ((sp - 24#64) ↦₆₄ sv5) ∗
        ((sp - 16#64) ↦₆₄ sv6) ∗ ((sp - 8#64) ↦₆₄ sv7) := by
  dsimp only [reduceStackFrameAt]; exact Entails.refl _

private theorem prologue_pre_entails {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (extra : SepProp) (γ : GhostName) (mAddrs : MallocngAddrs)
    (p : BitVec 64) (old align lb lk : Nat) (bs : List (BitVec 8)) (s0 : State) :
    let allocInst := mallocngRustCliAllocWithOf J hIf extra γ mAddrs
    (allocInst.pool lb lk s0 ∗ allocInst.live p old align ∗ (p ↦ₛ bs) ∗
     memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ StdErrnoCell s0.tpidrEl0 ∗
     Rust.hookFrame s0.sp) ⊢
    ∃∗ b : MallocngBudget, ∃∗ ivs0 : List (BitVec 64 × Nat),
      ∃∗ sv0 : BitVec 64, ∃∗ sv1 : BitVec 64, ∃∗ sv2 : BitVec 64, ∃∗ sv3 : BitVec 64,
      ∃∗ sv4 : BitVec 64, ∃∗ sv5 : BitVec 64, ∃∗ sv6 : BitVec 64, ∃∗ sv7 : BitVec 64,
      ⌜p.toNat % align = 0 ∧ RustLayoutOk old align ∧
        p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + old ≤ 2 ^ 48⌝ ∗
      (MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 ∗ extra ∗
       J.Block γ p old ∗ (p ↦ₛ bs) ∗ memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
       ((((s0.sp - 64#64) ↦₆₄ sv0) ∗ ((s0.sp - 56#64) ↦₆₄ sv1) ∗
         ((s0.sp - 48#64) ↦₆₄ sv2) ∗ ((s0.sp - 40#64) ↦₆₄ sv3) ∗
         ((s0.sp - 32#64) ↦₆₄ sv4) ∗ ((s0.sp - 24#64) ↦₆₄ sv5) ∗
         ((s0.sp - 16#64) ↦₆₄ sv6) ∗ ((s0.sp - 8#64) ↦₆₄ sv7)) ∗
        (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
         stackFrameAt (s0.sp - 64#64 - 1024#64) 3008))) := by
  intro allocInst
  have hRe :
      (allocInst.pool lb lk s0 ∗ allocInst.live p old align ∗ (p ↦ₛ bs) ∗
       memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ StdErrnoCell s0.tpidrEl0 ∗
       Rust.hookFrame s0.sp) =
      ((allocInst.pool lb lk s0 ∗ StdErrnoCell s0.tpidrEl0) ∗
       Rust.hookFrame s0.sp ∗ allocInst.live p old align ∗
       ((p ↦ₛ bs) ∗ memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length))) := by
    generalize allocInst.pool lb lk s0 = Ppool; generalize allocInst.live p old align = Plive
    generalize StdErrnoCell s0.tpidrEl0 = Perrno; generalize Rust.hookFrame s0.sp = Phook
    ac_rfl
  rw [hRe, mallocngRustCliPoolWithOf_sep_stdErrnoCell_eq hIf extra γ mAddrs lb lk s0,
      hookFrame_eq_stack64_1024 s0.sp]
  dsimp only [allocInst, mallocngRustCliAllocWithOf, mallocngRustCliLiveOf]
  rw [sepExists_sepConj_left, sepExists_sepConj_left]
  refine Entails.sepExists_mono fun b => ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_left]
  refine Entails.sepExists_mono fun ivs0 => ?_
  have hEnv : J.MallocngHeap γ mAddrs s0.tpidrEl0 s0.brkStart s0.brk b ivs0 ⊢
      MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 :=
    Entails.pure_right ⟨rfl, rfl⟩ (Entails.refl _)
  refine Entails.trans (sepConj_mono_left (sepConj_mono_left hEnv)) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_right (hIf.block_nonnull γ p old))))) ?_
  refine Entails.trans (Entails.of_eq (Q :=
      stackFrameAt s0.sp 64 ∗
      (⌜p.toNat % align = 0 ∧ RustLayoutOk old align⌝ ∗
       ⌜p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + old ≤ 2 ^ 48 ∧ old ≤ MallocngMaxAllocSize⌝ ∗
       (MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 ∗ extra ∗
        J.Block γ p old ∗ (p ↦ₛ bs) ∗ memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
        (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
         stackFrameAt (s0.sp - 64#64 - 1024#64) 3008)))) (by
    generalize MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 = Penv
    generalize stackFrameAt s0.sp 64 = Pstk0
    generalize stackFrameAt (s0.sp - 64#64) mallocngStackBytes = Pstk1
    generalize stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 = Pstk2
    ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left (unpack_stack64 s0.sp)) ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun sv0 => ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun sv1 => ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun sv2 => ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun sv3 => ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun sv4 => ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun sv5 => ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun sv6 => ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun sv7 => ?_
  refine Entails.trans (Entails.of_eq (Q :=
      ⌜p.toNat % align = 0 ∧ RustLayoutOk old align⌝ ∗
      ⌜p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + old ≤ 2 ^ 48 ∧ old ≤ MallocngMaxAllocSize⌝ ∗
      (MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 ∗ extra ∗
       J.Block γ p old ∗ (p ↦ₛ bs) ∗ memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
       ((((s0.sp - 64#64) ↦₆₄ sv0) ∗ ((s0.sp - 56#64) ↦₆₄ sv1) ∗
         ((s0.sp - 48#64) ↦₆₄ sv2) ∗ ((s0.sp - 40#64) ↦₆₄ sv3) ∗
         ((s0.sp - 32#64) ↦₆₄ sv4) ∗ ((s0.sp - 24#64) ↦₆₄ sv5) ∗
         ((s0.sp - 16#64) ↦₆₄ sv6) ∗ ((s0.sp - 8#64) ↦₆₄ sv7)) ∗
        (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
         stackFrameAt (s0.sp - 64#64 - 1024#64) 3008)))) (by
    generalize MallocngEnv J γ mAddrs s0.tpidrEl0 s0.brkStart b ivs0 s0 = Penv
    generalize stackFrameAt (s0.sp - 64#64) mallocngStackBytes = Pstk1
    generalize stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 = Pstk2
    ac_rfl)) ?_
  refine Entails.pure_left fun ⟨hpMod, hLayOld⟩ => ?_
  refine Entails.pure_left fun ⟨hpNe, hp16, hp48, _⟩ => ?_
  exact Entails.pure_right ⟨hpMod, hLayOld, hpNe, hp16, hp48⟩ (Entails.refl _)

theorem rdlRealloc_placed_withExtra_ok {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (extra : SepProp) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {cAddrs : MallocngCEntryAddrs}
    (reallocAddr memcpyAddr : BitVec 64)
    (hCode : hasInstrs P reallocAddr
      (rdlReallocInstrs reallocAddr cAddrs.realloc cAddrs.posixMemalign memcpyAddr cAddrs.free))
    (hC : MallocngProgCContractsWith J extra P mAddrs cAddrs)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpySpec) :
    subroutine_ok P reallocAddr
      (rustStdReallocSpec (mallocngRustCliAllocWithOf J hIf extra γ mAddrs)) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨p, old, align, new, bs, lb, lk⟩ R s0 hpc hrun hpre hsp_align
  refine ⟨_, hpre, ?_⟩
  dsimp only [rustStdReallocSpec]
  apply SepWP.pure_elim
  let oldBv := s0.readReg64 .x1; let alignBv := s0.readReg64 .x2; let newBv := s0.readReg64 .x3
  rintro ⟨hx0, hOldNat, hAlignNat, hNewNat, hLayoutNew, hbsOld, hbsNew, _⟩
  have hAlignBv : alignBv.toNat = align := hAlignNat
  have ⟨_, ⟨k, hk⟩, _, hAlLe⟩ := hLayoutNew
  have hPow2 : IsPow2Align alignBv := isPow2Align_of_toNat_pow2 (hAlignBv.trans hk)
  have hAlMax : alignBv.toNat ≤ MaxAlignedAllocAlign := by unfold MaxAlignedAllocAlign; omega
  refine SepWP.weaken_pre (prologue_pre_entails hIf extra γ mAddrs p old align lb lk bs s0) ?_
  apply SepWP.exists_elim; intro b; apply SepWP.exists_elim; intro ivs0
  apply SepWP.exists_elim; intro sv0; apply SepWP.exists_elim; intro sv1
  apply SepWP.exists_elim; intro sv2; apply SepWP.exists_elim; intro sv3
  apply SepWP.exists_elim; intro sv4; apply SepWP.exists_elim; intro sv5
  apply SepWP.exists_elim; intro sv6; apply SepWP.exists_elim; intro sv7
  apply SepWP.pure_elim; rintro ⟨hpMod, hLayoutOld, hpNe, hp16, hp48⟩
  have hsp_sub : decide ((s0.sp - 64#64) &&& 15#64 = 0#64) = true := spAligned_sub64 hsp_align
  have hf0 := fetch_instr_at0 hCode
  have hf1 := fetch_instr_at 1 (off := 0x04#64) hCode; have hf2 := fetch_instr_at 2 (off := 0x08#64) hCode
  have hf3 := fetch_instr_at 3 (off := 0x0c#64) hCode; have hf4 := fetch_instr_at 4 (off := 0x10#64) hCode
  have hf5 := fetch_instr_at 5 (off := 0x14#64) hCode; have hf6 := fetch_instr_at 6 (off := 0x18#64) hCode
  have hf7 := fetch_instr_at 7 (off := 0x1c#64) hCode; have hf8 := fetch_instr_at 8 (off := 0x20#64) hCode
  have hf9 := fetch_instr_at 9 (off := 0x24#64) hCode; have hf10 := fetch_instr_at 10 (off := 0x28#64) hCode
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_if hgt16
  · exact rdlRealloc_pathB_posix hIf extra γ hCode hC hMemcpy p oldBv alignBv newBv old align new
      lb lk bs b ivs0 sv0 sv1 R s0 _ hsp_align hOldNat hAlignBv hNewNat hLayoutNew hLayoutOld
      hpMod hPow2 hAlMax hpNe hp16 hp48 hbsOld hbsNew
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm])
      (by simp [arm64_norm, hx0]) (by simp [arm64_norm, alignBv])
      (by simp [arm64_norm, newBv]) (by simp [arm64_norm, oldBv])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by unfold AllocCallPreserved; simp [arm64_norm]) (by simp [arm64_norm])
  · have hAl16 : align ≤ 16 := by
      have hn : ¬ (16 < alignBv.toNat) := by simpa [BitVec.ult] using hgt16
      omega
    wp_step; wp_step
    wp_if hgtNew
    · exact rdlRealloc_pathB_posix hIf extra γ hCode hC hMemcpy p oldBv alignBv newBv old align new
        lb lk bs b ivs0 sv0 sv1 R s0 _ hsp_align hOldNat hAlignBv hNewNat hLayoutNew hLayoutOld
        hpMod hPow2 hAlMax hpNe hp16 hp48 hbsOld hbsNew
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm])
        (by simp [arm64_norm, hx0]) (by simp [arm64_norm, alignBv])
        (by simp [arm64_norm, newBv]) (by simp [arm64_norm, oldBv])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by unfold AllocCallPreserved; simp [arm64_norm]) (by simp [arm64_norm])
    · exact rdlRealloc_pathA hIf extra γ hCode hC p alignBv newBv old align new lb lk bs b ivs0
        sv0 sv1 R s0 _ hsp_align hAlignBv hNewNat hLayoutNew hLayoutOld hpMod hPow2 hAl16
        hpNe hp16 hp48 hbsOld hbsNew
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm])
        (by simp [arm64_norm, hx0]) (by simp [arm64_norm, newBv])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by unfold AllocCallPreserved; simp [arm64_norm]) (by simp [arm64_norm])

theorem rdlRealloc_thunk_withExtra_ok {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (extra : SepProp) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {cAddrs : MallocngCEntryAddrs}
    (thunkAddr reallocAddr memcpyAddr : BitVec 64)
    (hThunk : hasInstrs P thunkAddr [ .b (reallocAddr - thunkAddr) ])
    (hCode : hasInstrs P reallocAddr
      (rdlReallocInstrs reallocAddr cAddrs.realloc cAddrs.posixMemalign memcpyAddr cAddrs.free))
    (hC : MallocngProgCContractsWith J extra P mAddrs cAddrs)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpySpec) :
    subroutine_ok P thunkAddr
      (rustStdReallocSpec (mallocngRustCliAllocWithOf J hIf extra γ mAddrs)) :=
  subroutine_ok_of_b_thunk (fetch_instr_at0 hThunk)
    (hok := rdlRealloc_placed_withExtra_ok hIf extra γ reallocAddr memcpyAddr hCode hC hMemcpy)

end VerifiedLibraries.RustStd
