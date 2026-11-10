/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.PutStr.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-- Miss exit at `+244`: check capacity (`cmp x23, x8; b.eq +320`), call `grow_one` if full,
    then append `(x.name, x.bytes)` at `+256..+292` and return through `+296..+316`. -/
theorem step_miss {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {growStk stk : Nat}
    (hGrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneDirName)
      (growOneDirSpec A img growStk))
    (x : DirPutStrGhost) (R : SepProp) (s0 s : State)
    (cap ptr namePtr bCap bPtr : BitVec 64)
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hstk_max : stk ≤ 2 ^ 64)
    (hlen32 : x.dir.changed.length < 2 ^ 32)
    (hmiss : ∀ e ∈ x.dir.changed, e.1 ≠ x.name)
    (hinv : ImgCallInv img s)
    (hpc : s.pc = atOff ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName) 244)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 80#64)
    (htr : s.trace = s0.trace)
    (hhigh : PresHigh s0 s)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.name.length)
    (hx20 : s.readReg64 .x20 = x.bytesV)
    (hx21 : s.readReg64 .x21 = namePtr)
    (hx22 : s.readReg64 .x22 = x.self)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 x.dir.changed.length)
    (hx24 : s.readReg64 .x24 = ptr) :
    let cal := max growStk extHookStack
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s
      ((x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
        vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        nameBuf A namePtr x.name ∗
        (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Heap A bCap bPtr x.bytes ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
        stackAt (s0.sp - 80#64) cal ∗
        savedSlots s0 ∗
        A.pool)
      (DirPutStrPost A img x s0 stk R)
      (DirPutStrPanic A img x s0 stk R) := by
  intro cal
  have hgrow := growOne_ok_at_dirPutStr hGrow
  have hfn : libsignalSessionCode.fnOff dirPutStrName =
      num% (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") := dirPutStr_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode dirPutStrBin
    img.base (Rust.withPanics ext) hfn
    (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") 244 92
  dsimp only [tripleRatchetProgAtExt, atOff] at hpc hgrow ⊢
  clear hGrow hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr dirPutStrName = fnBase
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  have hpush : ∀ (s1 : State) (cap1 ptr1 : BitVec 64),
      x.dir.changed.length < cap1.toNat →
      s1.pc = atOff fnBase 256 →
      s1.status = .Running →
      s1.spAligned = true →
      s1.sp = s0.sp - 80#64 →
      s1.trace = s0.trace →
      PresHigh s0 s1 →
      s1.readReg64 .x19 = BitVec.ofNat 64 x.name.length →
      s1.readReg64 .x20 = x.bytesV →
      s1.readReg64 .x21 = namePtr →
      s1.readReg64 .x22 = x.self →
      s1.readReg64 .x23 = BitVec.ofNat 64 x.dir.changed.length →
      s1.readReg64 .x24 = ptr1 →
      SepWPp prog (s0.readReg64 Reg.lr) s1
        ((x.self ↦₆₄ cap1) ∗ ((x.self + 8#64) ↦₆₄ ptr1) ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
          vecBuf A 48 8 (dirEntryAt A) cap1 ptr1 x.dir.changed ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          nameBuf A namePtr x.name ∗
          (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Heap A bCap bPtr x.bytes ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
          stackAt (s0.sp - 80#64) cal ∗
          savedSlots s0 ∗
          A.pool)
        (DirPutStrPost A img x s0 stk R)
        (DirPutStrPanic A img x s0 stk R) := by
    intro s1 cap1 ptr1 hlt1 hpc1 hrun1 hspa1 hsp1 htr1 hhigh1
      hr19 hr20 hr21 hr22 hr23 hr24
    dsimp only [DirPutStrPost, DirPutStrPanic, dirPutStrSpec, Spec.inImage, atOff] at hpc1 ⊢
    rcases hhigh1 with ⟨hr27, hr28, hvregs1⟩
    apply sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (vecBuf_dirEntry_expose_slot A cap1 ptr1 x.dir.changed hlt1)))))
    dsimp only
    rw [show ∀ (A1 A2 A3 P0 B1 B2 B3 E6 Z : SepProp),
          A1 ∗ A2 ∗ A3 ∗ (P0 ∗ B1 ∗ B2 ∗ B3 ∗ E6) ∗ Z =
            P0 ∗ E6 ∗ A1 ∗ A2 ∗ A3 ∗ B1 ∗ B2 ∗ B3 ∗ Z from
          fun _ _ _ _ _ _ _ _ _ => by ac_rfl]
    refine sepWPp_pure_left fun ⟨hle1, hbound1, hptr1, hcap1_ne⟩ => ?_
    set slot := ptr1 + BitVec.ofNat 64 (x.dir.changed.length * 48)
    refine sepWPp_exists_left fun u0 => ?_
    simp only [sepConj_assoc]
    refine sepWPp_exists_left fun u1 => ?_
    refine sepWPp_exists_left fun u2 => ?_
    refine sepWPp_exists_left fun u3 => ?_
    refine sepWPp_exists_left fun u4 => ?_
    refine sepWPp_exists_left fun u5 => ?_
    apply SepWPp.of_sepWP_ret
    have hslot_eq : ptr1 + BitVec.ofNat 64 x.dir.changed.length * 48#64 = slot :=
      madd_slot_eq ptr1 x.dir.changed.length
    have hlen1_eq : BitVec.ofNat 64 x.dir.changed.length + 1#64 =
        BitVec.ofNat 64 (x.dir.changed.length + 1) := by
      rw [← BitVec.ofNat_add]
    wp_steps
    apply SepWP.fold (savedSlots_merge s0 (cal := cal) hstk hstk_max) (by sep_frame)
    apply SepWP.fold
      (pointsTo64_three_entails_memRegion24 x.bytesV bCap bPtr (BitVec.ofNat 64 x.bytes.length))
      (by sep_frame)
    apply SepWP.fold
      (vecOf_dirEntry_push_assemble A x.self cap1 ptr1 namePtr bCap bPtr
        x.dir.changed x.name x.bytes hle1 hbound1 hptr1 hcap1_ne)
      (by sep_frame)
    have hput : (x.dir.put x.name x.bytes).changed = x.dir.changed ++ [(x.name, x.bytes)] :=
      setOrPush_eq_append_singleton_of_forall_ne x.name x.bytes x.dir.changed hmiss
    have hdir :
        vecOf A 48 8 (dirEntryAt A) x.self (x.dir.changed ++ [(x.name, x.bytes)]) ∗
          strRefAt (x.self + 0x18#64) x.dir.path ⊢
          dirAt A x.self (x.dir.put x.name x.bytes) := by
      unfold dirAt
      rw [hput]
      exact Entails.refl _
    apply SepWP.fold hdir (by sep_frame)
    wp_done
  have hpull_len :
      vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed =
        ⌜x.dir.changed.length ≤ cap.toNat⌝ ∗
          vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed := by
    apply Entails.antisymm
    · unfold vecBuf
      refine Entails.pure_left fun h => ?_
      exact Entails.pure_right h.1 (Entails.pure_right h (Entails.refl _))
    · exact Entails.pure_left fun _ => Entails.refl _
  rw [hpull_len]
  rw [show ∀ (A1 A2 A3 P0 B Z : SepProp),
        A1 ∗ A2 ∗ A3 ∗ (P0 ∗ B) ∗ Z = P0 ∗ A1 ∗ A2 ∗ A3 ∗ B ∗ Z from
        fun _ _ _ _ _ _ => by ac_rfl]
  refine sepWPp_pure_left fun hle_cap => ?_
  by_cases heq_bv : BitVec.ofNat 64 x.dir.changed.length = cap
  · -- Full capacity (`len = cap`): call `grow_one`
    have hcap_eq : x.dir.changed.length = cap.toNat := by
      have ht := congrArg BitVec.toNat heq_bv
      rwa [ofNat_toNat_of_lt (by omega)] at ht
    have hcap32 : cap.toNat < 2 ^ 32 := by omega
    have hbeq_eq : (BitVec.ofNat 64 x.dir.changed.length == cap) = true :=
      beq_iff_eq.mpr heq_bv
    apply sepWPp_cut (mid := atOff fnBase
      (ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>"
        "<alloc::raw_vec::RawVec<(alloc::string::String, alloc::vec::Vec<u8>)>>::grow_one")) hinv
    dsimp only [atOff]
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s1 hs1 hinv_s1
    have hsp_s1 : s1.sp = s0.sp - 80#64 := by
      rw [hs1]; simp only [wp_norm, arm64_norm]; exact hsp
    have htr_s1 : s1.trace = s0.trace := by
      rw [hs1]; simp only [wp_norm, arm64_norm]; exact htr
    rw [← hsp_s1, stackAt_split_sub s1.sp (Nat.le_max_left growStk extHookStack) (by omega)]
    have hvec_in :
        (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
          vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed =
          vecAt A 48 8 (dirEntryAt A) x.self cap ptr x.dir.changed := by
      unfold vecAt vecHeader
      ac_rfl
    apply call_inImage_wpp hgrow ⟨x.self, cap, ptr, x.dir.changed⟩
      (ret_pc := atOff fnBase 328)
      (F := strRefAt (x.self + 0x18#64) x.dir.path ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        nameBuf A namePtr x.name ∗
        (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Heap A bCap bPtr x.bytes ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
        memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - growStk) ∗
        savedSlots s0)
      (hinv := hinv_s1)
      (hpc := by rw [hs1]; simp only [wp_norm, arm64_norm])
      (hrun := by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hrun)
      (hsp_align := by
        have hsp_eq : s1.sp = s.sp := by rw [hs1]; simp only [wp_norm, arm64_norm]
        simpa only [State.spAligned, hsp_eq] using hsp_align)
      (hlr := by rw [hs1]; dsimp [atOff]; simp only [wp_norm, arm64_norm])
      (hspec := rfl)
      (hφ := ⟨by rw [hs1]; simp only [wp_norm, arm64_norm], hcap32⟩)
      (hP := by
        rw [← hvec_in]
        ac_rfl)
      (hpan := fun _ => panic_callee_wpp (s := s1) htr_s1)
      (hexit := fun _ _ => rfl)
      (hoom := fun _ => rfl)
    intro sm hpcm hrunm hspm hcsm hinvm
    have hsp_sm : sm.sp = s0.sp - 80#64 := hspm.trans hsp_s1
    have hsp_align_sm : sm.spAligned = true := by
      have hsp_eq : sm.sp = s.sp := hspm.trans (by rw [hs1]; simp only [wp_norm, arm64_norm])
      simpa only [State.spAligned, hsp_eq] using hsp_align
    have hhigh_s1 : PresHigh s0 s1 :=
      ⟨by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.1,
       by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.2.1,
       by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.2.2⟩
    have hhigh_sm : PresHigh s0 sm := hhigh_s1.of_callee hcsm
    have hx19_sm : sm.readReg64 .x19 = BitVec.ofNat 64 x.name.length :=
      hcsm.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx19)
    have hx20_sm : sm.readReg64 .x20 = x.bytesV :=
      hcsm.2.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx20)
    have hx21_sm : sm.readReg64 .x21 = namePtr :=
      hcsm.2.2.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx21)
    have hx22_sm : sm.readReg64 .x22 = x.self :=
      hcsm.2.2.2.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx22)
    have hx23_sm : sm.readReg64 .x23 = BitVec.ofNat 64 x.dir.changed.length :=
      hcsm.2.2.2.2.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx23)
    dsimp only [growOneDirBaseSpec]
    simp only [sepConj_assoc]
    refine sepWPp_pure_left fun htr_sm0 => ?_
    have htr_sm : sm.trace = s0.trace := htr_sm0.trans htr_s1
    refine sepWPp_exists_left fun ptr' => ?_
    set newCap := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
    have hlt_new : x.dir.changed.length < newCap.toNat :=
      growOne_cap_gt hcap_eq hlen32
    unfold vecAt vecHeader
    simp only [sepConj_assoc]
    apply sepWPp_cut (mid := atOff fnBase 256) hinvm
    dsimp only [atOff] at hpcm ⊢
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s2 hs2 _hinv_s2
    have hstack_back :
        memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - growStk) ∗
          stackAt s1.sp growStk =
          stackAt (s0.sp - 80#64) cal := by
      rw [← stackAt_split_sub s1.sp (Nat.le_max_left growStk extHookStack) (by omega), hsp_s1]
    have hrearr :
        (x.self ↦₆₄ newCap) ∗ ((x.self + 8#64) ↦₆₄ ptr') ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
          vecBuf A 48 8 (dirEntryAt A) newCap ptr' x.dir.changed ∗
          stackAt s1.sp growStk ∗ A.pool ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          nameBuf A namePtr x.name ∗
          (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Heap A bCap bPtr x.bytes ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
          memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - growStk) ∗
          savedSlots s0 =
        (x.self ↦₆₄ newCap) ∗ ((x.self + 8#64) ↦₆₄ ptr') ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
          vecBuf A 48 8 (dirEntryAt A) newCap ptr' x.dir.changed ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          nameBuf A namePtr x.name ∗
          (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Heap A bCap bPtr x.bytes ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
          (memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - growStk) ∗
            stackAt s1.sp growStk) ∗
          savedSlots s0 ∗
          A.pool := by
      ac_rfl
    rw [hrearr, hstack_back]
    exact hpush s2 newCap ptr' hlt_new
      (by rw [hs2]; dsimp [atOff]; simp only [wp_norm, arm64_norm])
      (by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hrunm)
      (by
        have hsp_eq : s2.sp = sm.sp := by rw [hs2]; simp only [wp_norm, arm64_norm]
        simpa only [State.spAligned, hsp_eq] using hsp_align_sm)
      (by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hsp_sm)
      (by rw [hs2]; simp only [wp_norm, arm64_norm]; exact htr_sm)
      ⟨by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hhigh_sm.1,
       by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hhigh_sm.2.1,
       by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hhigh_sm.2.2⟩
      (by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hx19_sm)
      (by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hx20_sm)
      (by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hx21_sm)
      (by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hx22_sm)
      (by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hx23_sm)
      (by rw [hs2]; simp only [wp_norm, arm64_norm])
  · -- Spare capacity (`len < cap`)
    have hlt_cap : x.dir.changed.length < cap.toNat := by
      by_contra hge
      have heq_nat : cap.toNat = x.dir.changed.length := by omega
      exact heq_bv (ofNat_eq_of_toNat_eq heq_nat).symm
    have hbeq_ne : (BitVec.ofNat 64 x.dir.changed.length == cap) = false :=
      beq_false_of_ne heq_bv
    apply sepWPp_cut (mid := atOff fnBase 256) hinv
    dsimp only [atOff]
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s1 hs1 _hinv_s1
    exact hpush s1 cap ptr hlt_cap
      (by rw [hs1]; simp only [wp_norm, arm64_norm])
      (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hrun)
      (by
        have hsp_eq : s1.sp = s.sp := by rw [hs1]; simp only [wp_norm, arm64_norm]
        simpa only [State.spAligned, hsp_eq] using hsp_align)
      (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hsp)
      (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact htr)
      ⟨by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.1,
       by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.2.1,
       by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.2.2⟩
      (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx19)
      (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx20)
      (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx21)
      (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx22)
      (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx23)
      (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx24)

end CryptoVerification.SignalSession.Cli.PutStr.Helpers
