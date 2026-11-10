/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec.CoreMemrchr
public import VerifiedLibraries.RustStd.Proofs.ExecSeg
public import VerifiedLibraries.RustStd.Proofs.CoreIo
public import VerifiedLibraries.RustStd.Proofs.Wave1.CoreMemrchrLemmas
public import ProofLib.GenPlacedFetches
public meta import ProofLib.ProgramReflection

/-!
# Placement-Generic Proof of `core::slice::memchr::memrchr`

Proves `coreMemrchr_ok`: the `aarch64-unknown-linux-musl` implementation of
`core::slice::memchr::memrchr` (`coreMultiLib` block `2`) satisfies `coreMemrchrSpec` at every
valid `MultiPlacement`.
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches ProofLib.StdStartup

/-! ## Placed Fetch Generation -/

class CoreMemrchrPl where
  mpl : MultiPlacement
  placeable : coreMultiLib.Placeable mpl

def cmLib2 : PlacedLib := coreMultiLib.blockLib 2
def cmPl2 [CoreMemrchrPl] : Placement := coreMultiLib.blockPlacement CoreMemrchrPl.mpl 2
theorem cmPlaceable2 [CoreMemrchrPl] : cmLib2.Placeable cmPl2 :=
  coreMultiLib.placeable_blockLib (by decide) CoreMemrchrPl.placeable
def cmPC2 [CoreMemrchrPl] : Program := cmLib2.program cmPl2

def cmProg2 : Program := { code := cmLib2.text.code, symbols := cmLib2.text.symbols }
def cmTree2 : WordTree := word_tree_of% cmProg2
theorem cm2_code_eq : cmLib2.text.code = cmTree2.toBytes := by rfl_kernel
theorem cm2_tree_size : cmTree2.checkSize? = some 74 := by rfl_kernel

gen_placed_fetches cmPC2 cmLib2 cmTree2 cm2_code_eq cm2_tree_size
  via_placement cmPl2 cmPlaceable2 [0x0 → 0x104]

theorem cmNoSvc0_2 : checkBlockNoSvc0 (coreMultiLib.blockLib 2).text = true := by
  decide

section
arm64_proof_prelude

/-! ## Pure Segment Exit Invariant and Helper Bridges -/

private def CmSavedGprs (s0 s1 : State) : Prop :=
  s1.readReg64 .x19 = s0.readReg64 .x19 ∧ s1.readReg64 .x20 = s0.readReg64 .x20 ∧
  s1.readReg64 .x21 = s0.readReg64 .x21 ∧ s1.readReg64 .x22 = s0.readReg64 .x22 ∧
  s1.readReg64 .x23 = s0.readReg64 .x23 ∧ s1.readReg64 .x24 = s0.readReg64 .x24 ∧
  s1.readReg64 .x25 = s0.readReg64 .x25 ∧ s1.readReg64 .x26 = s0.readReg64 .x26 ∧
  s1.readReg64 .x27 = s0.readReg64 .x27 ∧ s1.readReg64 .x28 = s0.readReg64 .x28

private theorem CmSavedGprs.refl (s : State) : CmSavedGprs s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem CmSavedGprs.trans {s0 s1 s2 : State}
    (a : CmSavedGprs s0 s1) (b : CmSavedGprs s1 s2) : CmSavedGprs s0 s2 :=
  ⟨b.1.trans a.1, b.2.1.trans a.2.1, b.2.2.1.trans a.2.2.1, b.2.2.2.1.trans a.2.2.2.1,
   b.2.2.2.2.1.trans a.2.2.2.2.1, b.2.2.2.2.2.1.trans a.2.2.2.2.2.1,
   b.2.2.2.2.2.2.1.trans a.2.2.2.2.2.2.1, b.2.2.2.2.2.2.2.1.trans a.2.2.2.2.2.2.2.1,
   b.2.2.2.2.2.2.2.2.1.trans a.2.2.2.2.2.2.2.2.1, b.2.2.2.2.2.2.2.2.2.trans a.2.2.2.2.2.2.2.2.2⟩

private structure CmBodyPreserved (s_entry s : State) (sp0 : BitVec 64) : Prop where
  running : s.status = .Running
  sp_eq : s.sp = sp0 - 16#64
  sp_al : s.spAligned = true
  gprs : CmSavedGprs s_entry s
  vregs : calleeSavedVRegs s = calleeSavedVRegs s_entry

private structure CmExitState (s_entry sf : State) (sp0 fp0 lr0 : BitVec 64)
    (c : BitVec 8) (bs : List (BitVec 8)) : Prop where
  pc_eq : sf.pc = lr0
  running : sf.status = .Running
  sp_eq : sf.sp = sp0
  fp_eq : sf.readReg64 .fp = fp0
  lr_eq : sf.readReg64 .lr = lr0
  gprs : CmSavedGprs s_entry sf
  vregs : calleeSavedVRegs sf = calleeSavedVRegs s_entry
  ret_ok : RustAbi.optionU64.holds sf ((lastIndexOf c bs).map (BitVec.ofNat 64))

private abbrev cmFrame (p sp0 fp0 lr0 : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  (p ↦ₛ bs) ∗ ((sp0 - 16#64) ↦₆₄ fp0) ∗ ((sp0 - 8#64) ↦₆₄ lr0)

private theorem stackFrameAt16_eq_pair (sp0 : BitVec 64) :
    stackFrameAt sp0 16 =
      ∃∗ st0, ∃∗ st1, ((sp0 - 16#64) ↦₆₄ st0) ∗ ((sp0 - 8#64) ↦₆₄ st1) := by
  rw [← stackAt_eq_stackFrameAt sp0 16, stackAt_eq_cells sp0 2]
  dsimp only [cells]
  simp only [Nat.reduceMul, sepConj_emp, sepExists_sepConj_right, bv_lin_norm]

private theorem byte_cmp32_of_eq {x y : BitVec 8} (h : x = y) :
    (BitVec.setWidth 32 x == BitVec.setWidth 32 y) = true ∧
    (BitVec.setWidth 32 x != BitVec.setWidth 32 y) = false := by
  subst h; simp

private theorem byte_cmp32_of_ne {x y : BitVec 8} (h : x ≠ y) :
    (BitVec.setWidth 32 x == BitVec.setWidth 32 y) = false ∧
    (BitVec.setWidth 32 x != BitVec.setWidth 32 y) = true := by
  have hne32 : BitVec.setWidth 32 x ≠ BitVec.setWidth 32 y := by
    intro heq
    apply h
    have h8 := congrArg (BitVec.setWidth 8) heq
    simpa using h8
  exact ⟨beq_false_of_ne hne32, bne_iff_ne.mpr hne32⟩

/-! ## Reverse Prefix Byte Scan -/

private theorem cmLoop3 [CoreMemrchrPl] {s_entry : State}
    {sp0 fp0 lr0 p : BitVec 64} {c : BitVec 8} {bs : List (BitVec 8)}
    {post : State → SepProp → Prop}
    (hn : bs.length < 2 ^ 64)
    (hpost : ∀ sf : State, CmExitState s_entry sf sp0 fp0 lr0 c bs →
      post sf (cmFrame p sp0 fp0 lr0 bs)) :
    ∀ (cur : Nat) (s : State),
      cur ≤ bs.length →
      s.pc = cmPl2.base + 216#64 →
      CmBodyPreserved s_entry s sp0 →
      s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 cur →
      s.readReg64 (.gpr 10#5) = p - 1#64 →
      s.readReg64 .x0 = 1#64 →
      s.readReg64 (.gpr 9#5) = c.zeroExtend 64 →
      NoMatchFrom c bs cur →
      SepWP (cmPC2.rebase cmPl2.base (fun _ => none)) lr0 s (cmFrame p sp0 fp0 lr0 bs) post
  | 0, s, _hcur, hpc, hpres, hx8, _hx10, _hx0, _hx9, hnomatch => by
    have hnone : lastIndexOf c bs = none := memrchrLastIdx_eq_none hnomatch
    have hrun := hpres.running
    have hsp := hpres.sp_eq
    have hsp_al := hpres.sp_al
    have hsp0_al : (sp0 &&& 15#64 == 0#64) = true := by
      have h1 : (sp0 - 16#64) &&& 15#64 = 0#64 := by simpa [State.spAligned, hsp] using hsp_al
      exact beq_iff_eq.mpr (by simpa [arm64_norm] using h1)
    wp_conv_pre => rw [cmFrame]
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact hpost _ ⟨rfl, by simpa [arm64_norm] using hrun,
      by simp [arm64_norm],
      by simp [arm64_norm],
      by simp [arm64_norm],
      CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
      (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs,
      by simp [hnone, RustAbi.optionU64, arm64_norm]⟩
  | idx + 1, s, hcur, hpc, hpres, hx8, hx10, hx0, hx9, hnomatch => by
    have hidx : idx < bs.length := by omega
    have hne0 : BitVec.ofNat 64 (idx + 1) ≠ 0#64 := by bv_omega
    have hbeq0 : (BitVec.ofNat 64 (idx + 1) == 0#64) = false := beq_false_of_ne hne0
    obtain ⟨hptr, hsub1⟩ := memrchr_loop3_ptr_eq p idx
    have hrun := hpres.running
    have hsp := hpres.sp_eq
    have hsp_al := hpres.sp_al
    by_cases hbc : bs.getD idx 0#8 = c
    ·
      have hsome : lastIndexOf c bs = some idx := memrchrLastIdx_eq_some_of_hit hidx hbc hnomatch
      obtain ⟨hcmp_eq, hcmp_ne⟩ := byte_cmp32_of_eq hbc
      have hsp0_al : (sp0 &&& 15#64 == 0#64) = true := by
        have h1 : (sp0 - 16#64) &&& 15#64 = 0#64 := by simpa [State.spAligned, hsp] using hsp_al
        exact beq_iff_eq.mpr (by simpa [arm64_norm] using h1)
      wp_conv_pre => rw [cmFrame, pointsToBytes_focus8 p bs idx hidx, ← hptr, sepConj_assoc]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      conv => arg 2; rw [hptr, ← sepConj_assoc, ← pointsToBytes_focus8 p bs idx hidx]
      exact hpost _ ⟨rfl, by simpa [arm64_norm] using hrun,
        by simp [arm64_norm],
        by simp [arm64_norm],
        by simp [arm64_norm],
        CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
        (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs,
        by simp [hsome, RustAbi.optionU64, arm64_norm, hx0]⟩
    ·
      have hnomatch' : NoMatchFrom c bs idx := noMatchFrom_step_one hidx hbc hnomatch
      obtain ⟨hcmp_eq, hcmp_ne⟩ := byte_cmp32_of_ne hbc
      apply rustSepWP_cut (mid := cmPl2.base + 216#64)
      wp_conv_pre => rw [cmFrame, pointsToBytes_focus8 p bs idx hidx, ← hptr, sepConj_assoc]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [hptr, ← sepConj_assoc, ← pointsToBytes_focus8 p bs idx hidx]
      exact cmLoop3 hn hpost idx _ (by omega) rfl
        ⟨by simpa [arm64_norm] using hrun, by simpa [arm64_norm] using hsp,
         by simpa [arm64_norm] using hsp_al,
         CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
         (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs⟩
        (by simp [arm64_norm])
        (by simp [arm64_norm, hx10])
        (by simp [arm64_norm, hx0])
        (by simp [arm64_norm, hx9])
        hnomatch'

/-! ## Post-SWAR Bounds Check and 16-Byte GPR SWAR Scan -/

private theorem cmAfterLoop2 [CoreMemrchrPl] {s_entry s : State}
    {sp0 fp0 lr0 p : BitVec 64} {c : BitVec 8} {bs : List (BitVec 8)} {cur : Nat}
    {post : State → SepProp → Prop}
    (hn : bs.length < 2 ^ 64)
    (hpost : ∀ sf : State, CmExitState s_entry sf sp0 fp0 lr0 c bs →
      post sf (cmFrame p sp0 fp0 lr0 bs))
    (hcur : cur ≤ bs.length)
    (hpc : s.pc = cmPl2.base + 200#64)
    (hpres : CmBodyPreserved s_entry s sp0)
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 cur)
    (hx1 : s.readReg64 .x1 = p)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hx9 : s.readReg64 (.gpr 9#5) = c.zeroExtend 64)
    (hnomatch : NoMatchFrom c bs cur) :
    SepWP (cmPC2.rebase cmPl2.base (fun _ => none)) lr0 s (cmFrame p sp0 fp0 lr0 bs) post := by
  obtain ⟨hhi_false, hule_true⟩ := memrchr_prefix_check_false hcur hn
  have hrun := hpres.running
  have hsp := hpres.sp_eq
  have hsp_al := hpres.sp_al
  apply rustSepWP_cut (mid := cmPl2.base + 216#64)
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
  exact cmLoop3 hn hpost cur _ hcur rfl
    ⟨by simpa [arm64_norm] using hrun, by simpa [arm64_norm] using hsp,
     by simpa [arm64_norm] using hsp_al,
     CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
     (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs⟩
    (by simp [arm64_norm, hx8])
    (by simp [arm64_norm])
    (by simp [arm64_norm])
    (by simp [arm64_norm, hx9])
    hnomatch

private theorem cmLoop2 [CoreMemrchrPl] {s_entry : State}
    {sp0 fp0 lr0 p : BitVec 64} {c : BitVec 8} {bs : List (BitVec 8)} {lo : Nat}
    {post : State → SepProp → Prop}
    (hn : bs.length < 2 ^ 64)
    (hpost : ∀ sf : State, CmExitState s_entry sf sp0 fp0 lr0 c bs →
      post sf (cmFrame p sp0 fp0 lr0 bs)) :
    ∀ (q : Nat) (s : State),
      lo + 16 * q ≤ bs.length →
      s.pc = cmPl2.base + 140#64 →
      CmBodyPreserved s_entry s sp0 →
      s.readReg64 .x0 = BitVec.ofNat 64 (lo + 16 * q) →
      s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 lo →
      s.readReg64 .x1 = p →
      s.readReg64 .x2 = BitVec.ofNat 64 bs.length →
      s.readReg64 (.gpr 9#5) = c.zeroExtend 64 →
      s.readReg64 (.gpr 11#5) = memrchrRepeatByte64 c →
      s.readReg64 (.gpr 12#5) = 72340172838076672#64 →
      s.readReg64 (.gpr 13#5) = 9259542123273814144#64 →
      NoMatchFrom c bs (lo + 16 * q) →
      SepWP (cmPC2.rebase cmPl2.base (fun _ => none)) lr0 s (cmFrame p sp0 fp0 lr0 bs) post
  | 0, s, hcur, hpc, hpres, hx0, hx10, hx1, hx2, hx9, _hx11, _hx12, _hx13, hnomatch => by
    simp only [Nat.mul_zero, Nat.add_zero] at hcur hx0 hnomatch
    have hrun := hpres.running
    have hsp := hpres.sp_eq
    have hsp_al := hpres.sp_al
    apply rustSepWP_cut (mid := cmPl2.base + 200#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact cmAfterLoop2 hn hpost hcur rfl
      ⟨by simpa [arm64_norm] using hrun, by simpa [arm64_norm] using hsp,
       by simpa [arm64_norm] using hsp_al,
       CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
       (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs⟩
      (by simp [arm64_norm])
      (by simp [arm64_norm, hx1])
      (by simp [arm64_norm, hx2])
      (by simp [arm64_norm, hx9])
      hnomatch
  | q' + 1, s, hcur, hpc, hpres, hx0, hx10, hx1, hx2, hx9, hx11, hx12, hx13, hnomatch => by
    let cur := lo + 16 * (q' + 1)
    have h16 : 16 ≤ cur := by dsimp [cur]; omega
    have hcur_lt : cur < 2 ^ 64 := by dsimp [cur] at *; omega
    have hcur_sub16 : cur - 16 = lo + 16 * q' := by dsimp [cur]; omega
    have hls_false : (BitVec.ofNat 64 cur).ule (BitVec.ofNat 64 lo) = false := by
      simp [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcur_lt,
        Nat.mod_eq_of_lt (show lo < 2 ^ 64 by dsimp [cur] at *; omega)]
      dsimp [cur]; omega
    have hgt_true : (BitVec.ofNat 64 lo).ult (BitVec.ofNat 64 cur) = true := by
      simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcur_lt,
        Nat.mod_eq_of_lt (show lo < 2 ^ 64 by dsimp [cur] at *; omega)]
      dsimp [cur]; omega
    obtain ⟨hptr16, hsub16⟩ := memrchr_loop2_ptr_eq p h16 hcur_lt
    obtain ⟨w0, w1, hchunk, hfocus⟩ := pointsToBytes_focus16_words p bs h16 hcur
    have hrun := hpres.running
    have hsp := hpres.sp_eq
    have hsp_al := hpres.sp_al
    let rep := memrchrRepeatByte64 c
    let u0 := w0 ^^^ rep
    let u1 := w1 ^^^ rep
    let swarFlags :=
      9259542123273814144#64 &&&
        ~~~(((72340172838076672#64 - u0) ||| u0) &&& ((72340172838076672#64 - u1) ||| u1))
    by_cases hswar : swarFlags = 0#64
    ·
      have hswar_beq : (swarFlags == 0#64) = true := beq_iff_eq.mpr hswar
      obtain ⟨hw0, hw1⟩ := (memrchrSwarBics_eq_zero_iff w0 w1 c).mp hswar
      have hnomatch' : NoMatchFrom c bs (lo + 16 * q') := by
        rw [← hcur_sub16]
        exact noMatchFrom_step_chunk16 h16 hcur hchunk hw0 hw1 hnomatch
      apply rustSepWP_cut (mid := cmPl2.base + 140#64)
      wp_conv_pre => rw [cmFrame, hfocus, ← hptr16, sepConj_assoc]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [← sepConj_assoc, hptr16, ← hfocus]
      exact cmLoop2 hn hpost q' _ (by omega) rfl
        ⟨by simpa [arm64_norm] using hrun, by simpa [arm64_norm] using hsp,
         by simpa [arm64_norm] using hsp_al,
         CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
         (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs⟩
        (by simp [arm64_norm, hsub16, hcur_sub16, cur])
        (by simp [arm64_norm, hx10])
        (by simp [arm64_norm, hx1])
        (by simp [arm64_norm, hx2])
        (by simp [arm64_norm, hx9])
        (by simp [arm64_norm, hx11])
        (by simp [arm64_norm, hx12])
        (by simp [arm64_norm, hx13])
        hnomatch'
    ·
      have hswar_beq : (swarFlags == 0#64) = false := beq_false_of_ne hswar
      apply rustSepWP_cut (mid := cmPl2.base + 200#64)
      wp_conv_pre => rw [cmFrame, hfocus, ← hptr16, sepConj_assoc]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [← sepConj_assoc, hptr16, ← hfocus]
      exact cmAfterLoop2 hn hpost hcur rfl
        ⟨by simpa [arm64_norm] using hrun, by simpa [arm64_norm] using hsp,
         by simpa [arm64_norm] using hsp_al,
         CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
         (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs⟩
        (by simp [arm64_norm])
        (by simp [arm64_norm, hx1])
        (by simp [arm64_norm, hx2])
        (by simp [arm64_norm, hx9])
        hnomatch

/-! ## Reverse Unaligned Suffix Scan -/

private theorem cmLoop1 [CoreMemrchrPl] {s_entry : State}
    {sp0 fp0 lr0 p : BitVec 64} {c : BitVec 8} {bs : List (BitVec 8)} {lo mid q : Nat}
    {post : State → SepProp → Prop}
    (hn : bs.length < 2 ^ 64)
    (hmid_eq : mid = lo + 16 * q)
    (hmid_le : mid ≤ bs.length)
    (hpost : ∀ sf : State, CmExitState s_entry sf sp0 fp0 lr0 c bs →
      post sf (cmFrame p sp0 fp0 lr0 bs)) :
    ∀ (rem k : Nat) (s : State),
      rem + k = bs.length - mid →
      s.pc = cmPl2.base + 80#64 →
      CmBodyPreserved s_entry s sp0 →
      s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (bs.length - mid) →
      s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 k →
      s.readReg64 (.gpr 12#5) = (p + BitVec.ofNat 64 bs.length - 1#64) - BitVec.ofNat 64 k →
      s.readReg64 (.gpr 9#5) = c.zeroExtend 64 →
      s.readReg64 .x0 = BitVec.ofNat 64 mid →
      s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 lo →
      s.readReg64 .x1 = p →
      s.readReg64 .x2 = BitVec.ofNat 64 bs.length →
      NoMatchFrom c bs (bs.length - k) →
      SepWP (cmPC2.rebase cmPl2.base (fun _ => none)) lr0 s (cmFrame p sp0 fp0 lr0 bs) post
  | 0, k, s, hrem, hpc, hpres, hx8, hx11, _hx12, hx9, hx0, hx10, hx1, hx2, hnomatch => by
    have hk_eq : k = bs.length - mid := by omega
    subst hk_eq
    have hsub_mid : bs.length - (bs.length - mid) = mid := by omega
    rw [hsub_mid] at hnomatch
    have hrun := hpres.running
    have hsp := hpres.sp_eq
    have hsp_al := hpres.sp_al
    apply rustSepWP_cut (mid := cmPl2.base + 140#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact cmLoop2 hn hpost q _ (hmid_eq ▸ hmid_le) rfl
      ⟨by simpa [arm64_norm] using hrun, by simpa [arm64_norm] using hsp,
       by simpa [arm64_norm] using hsp_al,
       CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
       (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs⟩
      (by simp [arm64_norm, hx0, hmid_eq])
      (by simp [arm64_norm, hx10])
      (by simp [arm64_norm, hx1])
      (by simp [arm64_norm, hx2])
      (by simp [arm64_norm, hx9])
      (by simp [arm64_norm, memrchrRepeatByte64])
      (by simp [arm64_norm])
      (by simp [arm64_norm])
      (hmid_eq ▸ hnomatch)
  | rem' + 1, k, s, hrem, hpc, hpres, hx8, hx11, hx12, hx9, hx0, hx10, hx1, hx2, hnomatch => by
    have hk_lt_sub : k < bs.length - mid := by omega
    have hk_lt_n : k < bs.length := by omega
    let idx := bs.length - 1 - k
    have hidx : idx < bs.length := by dsimp [idx]; omega
    have hne_k : BitVec.ofNat 64 (bs.length - mid) ≠ BitVec.ofNat 64 k := by bv_omega
    have hbeq_k : (BitVec.ofNat 64 (bs.length - mid) == BitVec.ofNat 64 k) = false :=
      beq_false_of_ne hne_k
    have hptr := memrchr_loop1_ptr_eq p hk_lt_n hn
    have hhit_idx := memrchr_loop1_hit_idx hk_lt_n hn
    rw [BitVec.ofNat_add] at hhit_idx
    have hrun := hpres.running
    have hsp := hpres.sp_eq
    have hsp_al := hpres.sp_al
    by_cases hbc : bs.getD idx 0#8 = c
    ·
      have habove_idx : NoMatchFrom c bs (idx + 1) := by
        have heq : idx + 1 = bs.length - k := by dsimp [idx]; omega
        exact heq ▸ hnomatch
      have hsome : lastIndexOf c bs = some idx := memrchrLastIdx_eq_some_of_hit hidx hbc habove_idx
      obtain ⟨hcmp_eq, hcmp_ne⟩ := byte_cmp32_of_eq hbc
      rw [hptr] at hx12
      wp_conv_pre => rw [cmFrame, pointsToBytes_focus8 p bs idx hidx, sepConj_assoc]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      conv => arg 2; rw [← sepConj_assoc, ← pointsToBytes_focus8 p bs idx hidx]
      exact hpost _ ⟨rfl, by simpa [arm64_norm] using hrun,
        by simp [arm64_norm],
        by simp [arm64_norm],
        by simp [arm64_norm],
        CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
        (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs,
        by simp [hsome, RustAbi.optionU64, arm64_norm, idx]⟩
    ·
      have hnomatch' : NoMatchFrom c bs (bs.length - (k + 1)) :=
        noMatchFrom_step_one_sub hk_lt_n hbc hnomatch
      obtain ⟨hcmp_eq, hcmp_ne⟩ := byte_cmp32_of_ne hbc
      rw [hptr] at hx12
      apply rustSepWP_cut (mid := cmPl2.base + 80#64)
      wp_conv_pre => rw [cmFrame, pointsToBytes_focus8 p bs idx hidx, sepConj_assoc]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [← sepConj_assoc, ← pointsToBytes_focus8 p bs idx hidx]
      exact cmLoop1 hn hmid_eq hmid_le hpost rem' (k + 1) _ (by omega) rfl
        ⟨by simpa [arm64_norm] using hrun, by simpa [arm64_norm] using hsp,
         by simpa [arm64_norm] using hsp_al,
         CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
         (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs⟩
        (by simp [arm64_norm, hx8])
        (by simp [arm64_norm, BitVec.ofNat_add])
        (by simp only [arm64_norm]; rw [← hptr, BitVec.ofNat_add]; bv_lin)
        (by simp [arm64_norm, hx9])
        (by simp [arm64_norm, hx0])
        (by simp [arm64_norm, hx10])
        (by simp [arm64_norm, hx1])
        (by simp [arm64_norm, hx2])
        hnomatch'

/-! ## Prologue Join and `coreMemrchr_ok` -/

private theorem cmFromJoin3c [CoreMemrchrPl] {s_entry s : State}
    {sp0 fp0 lr0 p : BitVec 64} {c : BitVec 8} {bs : List (BitVec 8)} {lo mid q : Nat}
    {post : State → SepProp → Prop}
    (hn : bs.length < 2 ^ 64)
    (hmid_eq : mid = lo + 16 * q)
    (hmid_le : mid ≤ bs.length)
    (hpost : ∀ sf : State, CmExitState s_entry sf sp0 fp0 lr0 c bs →
      post sf (cmFrame p sp0 fp0 lr0 bs))
    (hpc : s.pc = cmPl2.base + 60#64)
    (hpres : CmBodyPreserved s_entry s sp0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 mid)
    (hx10 : s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 lo)
    (hx1 : s.readReg64 .x1 = p)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hx8_low : BitVec.zeroExtend 64 (BitVec.setWidth 32 (s.readReg64 (.gpr 8#5)) &&& 255#32) = c.zeroExtend 64) :
    SepWP (cmPC2.rebase cmPl2.base (fun _ => none)) lr0 s (cmFrame p sp0 fp0 lr0 bs) post := by
  have hsub_n_mid : BitVec.ofNat 64 bs.length - BitVec.ofNat 64 mid =
      BitVec.ofNat 64 (bs.length - mid) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have hadd_p : BitVec.ofNat 64 bs.length + p - 1#64 =
      (p + BitVec.ofNat 64 bs.length - 1#64) - BitVec.ofNat 64 0 := by
    bv_lin
  have hrun := hpres.running
  have hsp := hpres.sp_eq
  have hsp_al := hpres.sp_al
  apply rustSepWP_cut (mid := cmPl2.base + 80#64)
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
  exact cmLoop1 hn hmid_eq hmid_le hpost (bs.length - mid) 0 _ (by omega) rfl
    ⟨by simpa [arm64_norm] using hrun, by simpa [arm64_norm] using hsp,
     by simpa [arm64_norm] using hsp_al,
     CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
     (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs⟩
    (by simp only [arm64_norm]; rw [← hmid_eq]; exact hsub_n_mid)
    (by simp [arm64_norm])
    (by simp [arm64_norm, hadd_p])
    (by simp [arm64_norm, hx8_low])
    (by simp [arm64_norm, hx0])
    (by simp [arm64_norm, hx10])
    (by simp [arm64_norm, hx1])
    (by simp [arm64_norm, hx2])
    (by simpa using noMatchFrom_self c bs)

private theorem cmBlock2_ok [CoreMemrchrPl] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P (coreMultiLib.fnAddr CoreMemrchrPl.mpl coreMemrchrSym)
      (coreMultiLib.withCodeLoaded CoreMemrchrPl.mpl coreMemrchrSpec) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨c, p, bs, sp_arg⟩ R s0 hpc hrun hpre hsp
  rw [fnAddr_eq_base CoreMemrchrPl.placeable 2 coreMemrchrSym (by decide) (by decide)] at hpc
  dsimp only [MultiPlacedLib.withCodeLoaded, coreMemrchrSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜coreMultiLib.CodeLoaded CoreMemrchrPl.mpl s0.mem⌝,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hc_reg, hp_reg, hlen_reg, hsp_arg, hn⟩, hpre⟩
  subst hsp_arg
  rw [stackFrameAt16_eq_pair s0.sp] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨st0, st1, hpre⟩
  refine ⟨_, hpre, ?_⟩
  apply sepWP_seg_rebase_pure hext 2 (by decide) cmNoSvc0_2 hcl (mid := s0.readReg64 .lr)
  intro s1' hcpu1
  change SepWP (cmPC2.rebase cmPl2.base (fun _ => none)) (s0.readReg64 .lr) s1' _ _
  have hpc1 : s1'.pc = cmPl2.base := hcpu1.pc_eq.trans hpc
  have hrun1 : s1'.status = .Running := hcpu1.status_eq.trans hrun
  have hsp1_al : s1'.spAligned = true := hcpu1.spAligned.trans hsp
  have hsp1 : s1'.sp = s0.sp := hcpu1.sp_eq
  have hx1_1 : s1'.readReg64 .x1 = p := (hcpu1.readReg64 .x1).trans hp_reg
  have hx2_1 : s1'.readReg64 .x2 = BitVec.ofNat 64 bs.length := (hcpu1.readReg64 .x2).trans hlen_reg
  have hc_low : (s1'.readReg64 .x0).setWidth 8 = c := by
    have hx0_32 : s1'.readReg32 .x0 = s0.readReg32 .x0 := hcpu1.readReg32 .x0
    have hsw : (s1'.readReg64 .x0).setWidth 8 = (s1'.readReg32 .x0).truncate 8 := by
      simp [State.readReg32, State.readReg64]
    rw [hsw, hx0_32, hc_reg]
  let fp0 := s1'.readReg64 .fp
  let lr0 := s1'.readReg64 .lr
  have hlr0_eq : lr0 = s0.readReg64 .lr := hcpu1.readReg64 .lr
  rw [← hlr0_eq]
  have hpost : ∀ sf' : State, CmExitState s1' sf' s0.sp fp0 lr0 c bs →
      ∀ sm : State, SameCpuState sm sf' → coreMultiLib.CodeLoaded CoreMemrchrPl.mpl sm.mem →
        ProofLib.NonSyscallPreserved s0 sm →
        SepWP P lr0 sm (cmFrame p s0.sp fp0 lr0 bs)
          (fun sf Q =>
            (∀ hm_f : sf.mem ⊨ Q ∗ R,
              sf.mem ⊨ (coreMultiLib.withCodeLoaded CoreMemrchrPl.mpl coreMemrchrSpec).post
                (c, p, bs, s0.sp) s0 sf ∗ R) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf => (coreMultiLib.withCodeLoaded CoreMemrchrPl.mpl coreMemrchrSpec).onOom
            (c, p, bs, s0.sp) s0 sf) := by
    intro sf' hexit sm hcpu_out _hcl_out hnsp
    have hpc_sm : sm.pc = lr0 := hcpu_out.pc_eq.trans hexit.pc_eq
    have hrun_sm : sm.status = .Running := hcpu_out.status_eq.trans hexit.running
    have hsp_sm : sm.sp = s0.sp := hcpu_out.sp_eq.trans hexit.sp_eq
    have hcs_sm : CalleeSavedPreserved s0 sm := by
      refine SameCpuState.calleeSavedPreserved hcpu1 hcpu_out ?_
      rw [CalleeSavedPreserved.iff_regs]
      exact ⟨hexit.gprs.1, hexit.gprs.2.1, hexit.gprs.2.2.1, hexit.gprs.2.2.2.1,
        hexit.gprs.2.2.2.2.1, hexit.gprs.2.2.2.2.2.1, hexit.gprs.2.2.2.2.2.2.1,
        hexit.gprs.2.2.2.2.2.2.2.1, hexit.gprs.2.2.2.2.2.2.2.2.1,
        hexit.gprs.2.2.2.2.2.2.2.2.2, hexit.fp_eq, hexit.vregs⟩
    have hret_sm : RustAbi.optionU64.holds sm ((lastIndexOf c bs).map (BitVec.ofNat 64)) := by
      have hret := hexit.ret_ok
      cases hopt : (lastIndexOf c bs).map (BitVec.ofNat 64) with
      | none =>
        rw [hopt] at hret
        exact (hcpu_out.readReg64 .x0).trans hret
      | some v =>
        rw [hopt] at hret
        exact ⟨(hcpu_out.readReg64 .x0).trans hret.1,
               (hcpu_out.readReg64 .x1).trans hret.2⟩
    refine SepWP.done hpc_sm hrun_sm ⟨fun hm_f => ?_, hsp_sm, hcs_sm⟩
    refine Satisfies.mono ?_ hm_f
    apply sepConj_mono_left
    dsimp only [MultiPlacedLib.withCodeLoaded, coreMemrchrSpec, cmFrame]
    rw [stackFrameAt16_eq_pair s0.sp]
    simp only [sepExists_sepConj_right]
    refine Entails.sepExists_right fp0 <| Entails.sepExists_right lr0 ?_
    rw [pure_sepConj_of_true ⟨hnsp.1, hnsp.2.2.2.2.2.2, hret_sm⟩]
    sep_entail
  let head := (memrchrHeadBV p).toNat
  have hhead_lt8 : head < 8 := memrchrHeadBV_lt8 p
  have hhead_bv : memrchrHeadBV p = BitVec.ofNat 64 head := memrchrHeadBV_eq_ofNat p
  wp_conv_pre => rw [← hsp1]
  by_cases hlt : bs.length < head
  ·
    have hult_true : (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 head) = true := by
      simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
        Nat.mod_eq_of_lt (show head < 2 ^ 64 by omega)]
      omega
    apply rustSepWP_cut (mid := cmPl2.base + 60#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun1) ?_
    wp_conv_pre => rw [hsp1]
    exact cmFromJoin3c (s_entry := s1') (lo := bs.length) (mid := bs.length) (q := 0)
      hn (by omega) (by omega) hpost rfl
      ⟨by simpa [arm64_norm] using hrun1, by simp [arm64_norm],
       by simpa [arm64_norm] using hsp,
       by simp [CmSavedGprs, arm64_norm],
       by simp [calleeSavedVRegs, arm64_norm]⟩
      (by simp [arm64_norm])
      (by simp [arm64_norm])
      (by simp [arm64_norm, hx1_1])
      (by simp [arm64_norm, hx2_1])
      (by simpa [arm64_norm, hc_low] using lowByte_mov_and_ff (s1'.readReg64 .x0))
  ·
    have hge : head ≤ bs.length := by omega
    have hult_false : (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 head) = false := by
      simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
        Nat.mod_eq_of_lt (show head < 2 ^ 64 by omega)]
      omega
    have hand15 :
        BitVec.zeroExtend 64 ((BitVec.ofNat 64 bs.length).setWidth 32 - (BitVec.ofNat 64 head).setWidth 32) &&& 15#64 =
          BitVec.ofNat 64 ((bs.length - head) % 16) := by
      rw [sub32_zext64_and15_eq, ofNat_sub_and15_eq_mod16 hge hn]
    obtain ⟨_htl_le, htl_ult_false, hmid_bv, hmid_eq, hmid_le⟩ := memrchr_split_of_ge hge hn
    apply rustSepWP_cut (mid := cmPl2.base + 60#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun1) ?_
    wp_conv_pre => rw [hsp1]
    exact cmFromJoin3c (s_entry := s1') (lo := head) (mid := bs.length - (bs.length - head) % 16)
      (q := (bs.length - head) / 16) hn hmid_eq hmid_le hpost rfl
      ⟨by simpa [arm64_norm] using hrun1, by simp [arm64_norm],
       by simpa [arm64_norm] using hsp,
       by simp [CmSavedGprs, arm64_norm],
       by simp [calleeSavedVRegs, arm64_norm]⟩
      (by simp [arm64_norm, ← hmid_eq])
      (by simp [arm64_norm])
      (by simp [arm64_norm, hx1_1])
      (by simp [arm64_norm, hx2_1])
      (by simpa [arm64_norm, hc_low] using lowByte_mov_and_ff (s1'.readReg64 .x0))

/-- Placement-generic correctness of `core::slice::memchr::memrchr` (`coreMultiLib` block `2`)
    against `coreMemrchrSpec`. -/
theorem coreMemrchr_ok {mpl : MultiPlacement}
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreMemrchrSym)
      (coreMultiLib.withCodeLoaded mpl coreMemrchrSpec) := by
  letI : CoreMemrchrPl := ⟨mpl, hpl⟩
  exact cmBlock2_ok hext

end

end VerifiedLibraries.RustStd
