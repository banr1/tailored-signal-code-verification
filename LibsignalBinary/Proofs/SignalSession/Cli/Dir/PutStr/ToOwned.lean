/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.Hit
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.Miss
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.PutStr.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

private theorem entails_eq' {P Q : SepProp} (h : P = Q) : P ⊢ Q :=
  h ▸ Entails.refl P

private theorem satisfies_eq' {m : Memory} {P Q : SepProp} (h : P = Q) (hm : m ⊨ P) : m ⊨ Q :=
  h ▸ hm

private theorem bv_sub_eq_add_neg64' (a b : BitVec 64) : a - b = a + (-b) :=
  BitVec.sub_eq_add_neg a b

private theorem sp_slot_norm (sp : BitVec 64) :
    sp + (-80#64 + 8#64) = sp + (-72#64) ∧
    sp + (-80#64 + 16#64) = sp + (-64#64) ∧
    sp + (-80#64 + 24#64) = sp + (-56#64) ∧
    sp + (-80#64 + 32#64) = sp + (-48#64) ∧
    sp + (-80#64 + 40#64) = sp + (-40#64) ∧
    sp + (-80#64 + 48#64) = sp + (-32#64) ∧
    sp + (-80#64 + 56#64) = sp + (-24#64) ∧
    sp + (-80#64 + 64#64) = sp + (-16#64) ∧
    sp + (-80#64 + 72#64) = sp + (-8#64) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem pull_alloc_pure_right (P1 P2 R : SepProp) (φ : Prop) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ R = ⌜φ⌝ ∗ P1 ∗ P2 ∗ R := by
  ac_rfl

private theorem shim_pre_eq (s : State) :
    session2ShimSpecX.pre () s = ⌜True⌝ ∗ stackAt s.sp extHookStack := by
  apply Entails.antisymm
  · dsimp only [session2ShimSpecX, withStack, sessionShimSpec]
    exact Entails.pure_right trivial (Entails.refl _)
  · dsimp only [session2ShimSpecX, withStack, sessionShimSpec]
    exact Entails.pure_left fun _ => Entails.refl _

/-- Shared loop preheader `+104..+116` when `x.dir.changed = e0 :: rest0`:
    computes `x25 = ptr + 32#64` and `x26 = BitVec.ofNat 64 (x.dir.changed.length * 48)`,
    branches to `+132`, and enters `step_loop` with `pre = []`, `suf = e0 :: rest0`. -/
private theorem step_preheader {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {growStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (hGrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneDirName)
      (growOneDirSpec A img growStk))
    (x : DirPutStrGhost) (R : SepProp) (s0 s : State)
    (e0 : List (BitVec 8) × List (BitVec 8))
    (rest0 : List (List (BitVec 8) × List (BitVec 8)))
    (cap ptr namePtr bCap bPtr : BitVec 64)
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hstk_max : stk ≤ 2 ^ 64)
    (hname32 : x.name.length < 2 ^ 32)
    (hlen32 : x.dir.changed.length < 2 ^ 32)
    (hchanged : x.dir.changed = e0 :: rest0)
    (hsp_align0 : s0.spAligned = true)
    (hinv : ImgCallInv img s)
    (hpc : s.pc = atOff ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName) 104)
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
  have hfn : libsignalSessionCode.fnOff dirPutStrName =
      num% (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") := dirPutStr_fnOff
  let fnBase := (tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName
  code_fetches_range CryptoVerification.libsignalSessionCode dirPutStrBin
    img.base (Rust.withPanics ext) hfn
    (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") 104 16
  apply sepWPp_cut_rebase (mid := atOff fnBase 132) hinv
  dsimp +zetaDelta only [fnBase, tripleRatchetProgAtExt, atOff] at hpc
  dsimp +zetaDelta only [fnBase, atOff]
  set fnBase' := (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr dirPutStrName
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch]
  examples_hide_fetches
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro s1 P1 hinv_s1 ⟨hs1, hP1⟩
  · subst hP1
    have hx25_init :
        ptr + 32#64 =
          ptr + BitVec.ofNat 64 (([] : List (List (BitVec 8) × List (BitVec 8))).length * 48) + 32#64 := by
      change ptr + 32#64 = ptr + 0#64 + 32#64
      bv_omega
    have hx26_init :
        ((BitVec.ofNat 64 (e0 :: rest0).length + (BitVec.ofNat 64 (e0 :: rest0).length) <<< 1) <<< 4) =
          BitVec.ofNat 64 ((e0 :: rest0).length * 48) :=
      preheader_mul48 _
    let _ := hx23
    let _ := hx24
    let _ := hx25_init
    let _ := hx26_init
    apply sepWPp_eq_pre
    · exact step_loop hC hBcmp hGrow x R s0 cap ptr namePtr bCap bPtr
        hstk hstk_max hname32 hlen32 hsp_align0 (e0 :: rest0) [] s1
        (List.cons_ne_nil _ _)
        (by simpa only [List.nil_append] using hchanged)
        (fun _ hm => (List.not_mem_nil hm).elim)
        hinv_s1
        (by rw [hs1]; try dsimp +zetaDelta only [fnBase, atOff, tripleRatchetProgAtExt]; try simp only [wp_norm, arm64_norm])
        (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hrun)
        (by
          have hsp_eq : s1.sp = s.sp := by rw [hs1]; try simp only [wp_norm, arm64_norm]
          simpa only [State.spAligned, hsp_eq] using hsp_align)
        (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hsp)
        (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact htr)
        ⟨by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hhigh.1,
         by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hhigh.2.1,
         by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hhigh.2.2⟩
        (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx19)
        (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx20)
        (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx21)
        (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx22)
        (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx23)
        (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx24)
        (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx25_init)
        (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx26_init)
    · try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
      try simp only [sp_slot_norm]
      try rw [emp_sepConj]
      try rw [sepConj_emp]
      try simp only [wp_norm, arm64_norm]
      try rw [Nat.mul_comm 48]
      try ac_rfl

/-- Full proof of `<signal_session::stores::Dir>::put::<&str>`:
    prologue (`+0..+36`), `name.to_owned()` (`+92..+100` for `name = []`; `+40..+88` plus cold OOM
    panic block `+336..+344` for `name ≠ []`), loop dispatch (`step_preheader` / `step_loop`),
    and hit/miss exits (`step_hit` / `step_miss`). -/
theorem dirPutStr_ok_main_roX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {growStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hRO : SpqrV1.Alloc.MemcpyROOkExtX img ext)
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (hGrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneDirName)
      (growOneDirSpec A img growStk))
    (hstk : 0x50 + max growStk extHookStack ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName)
      (dirPutStrSpec A img stk) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp_align0
  have hpre_full := hpre
  dsimp only [dirPutStrSpec, Spec.inImage] at hpre_full
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_full
  rcases hpre_full with ⟨hinv0, hpre_inner⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_inner
  rcases hpre_inner with ⟨⟨hx0, hx1, hx2_nat, hx3, hname32, hlen32⟩, hmem_spatial⟩
  have hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 x.name.length :=
    ofNat_eq_of_toNat_eq hx2_nat
  have hstk_max : stk ≤ 2 ^ 64 := by
    have hm1 : s0.mem ⊨ vecU8 A x.bytesV x.bytes ∗ stackAt s0.sp stk ∗
        (dirAt A x.self x.dir ∗ SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          A.pool ∗ R) :=
      satisfies_eq' (by ac_rfl) hmem_spatial
    unfold vecU8 at hm1
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1
    rcases hm1 with ⟨bc, bp, hmb⟩
    rw [vecU8At_eq_header_heap] at hmb
    unfold stackAt at hmb
    have hmb' : s0.mem ⊨ (x.bytesV ↦₆₄ bc) ∗ memRegion (s0.sp - BitVec.ofNat 64 stk) stk ∗
        (((x.bytesV + 8#64) ↦₆₄ bp) ∗ ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Heap A bc bp x.bytes ∗
          (dirAt A x.self x.dir ∗ SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
            A.pool ∗ R)) :=
      satisfies_eq' (by ac_rfl) hmb
    exact memRegion_le_two_pow_64_of_pointsTo64 hmb'
  let cal := max growStk extHookStack
  unfold dirAt vecOf vecAt vecHeader at hmem_spatial
  unfold vecU8 at hmem_spatial
  rw [stackAt_dirPutStr_split s0.sp (cal := cal) hstk hstk_max] at hmem_spatial
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem_spatial
  rcases hmem_spatial with ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, bCap, bPtr, cap, ptr, hm_init⟩
  rw [vecU8At_eq_header_heap] at hm_init
  have hm_ord : s0.mem ⊨
      ((x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
        vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Heap A bCap bPtr x.bytes ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
        stackAt (s0.sp - 80#64) cal ∗
        (((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
          ((s0.sp - 64#64) ↦₆₄ v2) ∗ ((s0.sp - 56#64) ↦₆₄ v3) ∗
          ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
          ((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
          ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9)) ∗
        A.pool) ∗ R :=
    satisfies_eq' (by ac_rfl) hm_init
  refine ⟨_, R, hm_ord, ?_⟩
  clear hpre hm_init hm_ord
  have hshim := shim_ok_at_dirPutStr hC
  have halloc := alloc_ok_at_dirPutStr hC
  have hmemcpy := memcpy_bytesAt_inImage_ok_at_roX img A ext hC hRO x.nameRo
  have hfn : libsignalSessionCode.fnOff dirPutStrName =
      num% (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") := dirPutStr_fnOff
  let fnBase := (tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName
  by_cases hnil : x.name = []
  · -- Empty slice (`x.name = []`)
    have hx2_zero : s0.readReg64 .x2 = 0#64 := by
      rw [hx2, hnil]; rfl
    have hname_fold :
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ⊢
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗ nameBuf A 1#64 x.name := by
      rw [hnil]
      exact Entails.trans (entails_eq' (sepConj_emp _).symm) (sepConj_mono_right (nameBuf_of_nil A))
    cases hdir_cases : x.dir.changed with
    | nil =>
      code_fetches_range CryptoVerification.libsignalSessionCode dirPutStrBin
        img.base (Rust.withPanics ext) hfn
        (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") 0 40
      code_fetches_range CryptoVerification.libsignalSessionCode dirPutStrBin
        img.base (Rust.withPanics ext) hfn
        (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") 92 12
      apply sepWPp_cut_rebase (mid := atOff fnBase 244) hinv0
      dsimp +zetaDelta only [fnBase, tripleRatchetProgAtExt, atOff] at hpc
      dsimp +zetaDelta only [fnBase, atOff]
      set fnBase' := (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr dirPutStrName
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)) = prog
        reverting [Program.fetch]
      examples_hide_fetches
      wp_steps
      apply SepWP.fold hname_fold (by sep_frame)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro s1 P1 hinv_s1 ⟨hs1, hP1⟩
      · subst hP1
        let _ := hC
        let _ := hBcmp
        let _ := hshim
        let _ := halloc
        let _ := hmemcpy
        let _ := hx1
        let _ := hx2
        let _ := hx2_zero
        let _ := hname32
        rw [← hdir_cases]
        apply sepWPp_eq_pre
        · exact step_miss hGrow x R s0 s1 cap ptr 1#64 bCap bPtr
            hstk hstk_max hlen32
            (by rw [hdir_cases]; intro _ hm; exact (List.not_mem_nil hm).elim)
            hinv_s1
            (by rw [hs1]; try dsimp +zetaDelta only [fnBase, atOff, tripleRatchetProgAtExt]; try simp only [wp_norm, arm64_norm])
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hrun)
            (spAligned_of_sub80 hsp_align0 (by rw [hs1]; try simp only [wp_norm, arm64_norm]))
            (by rw [hs1]; try simp only [wp_norm, arm64_norm])
            (by rw [hs1]; try simp only [wp_norm, arm64_norm])
            ⟨by rw [hs1]; try simp only [wp_norm, arm64_norm],
             by rw [hs1]; try simp only [wp_norm, arm64_norm],
             by dsimp only [calleeSavedVRegs]; rw [hs1]; try simp only [wp_norm, arm64_norm]⟩
            (by rw [hs1]; simp only [wp_norm, arm64_norm]; rw [hnil]; rfl)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx3)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm])
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx0)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try rw [hdir_cases]; try rfl)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm])
        · try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
          repeat rw [bv_sub_eq_add_neg64']
          try simp only [sp_slot_norm]
          try rw [emp_sepConj]
          try rw [sepConj_emp]
          try simp only [wp_norm, arm64_norm]
          try rw [Nat.mul_comm 48]
          try ac_rfl
    | cons e0 rest0 =>
      have hlen_pos : 0 < (e0 :: rest0).length := by simp
      have hlen_nz : (BitVec.ofNat 64 (e0 :: rest0).length == 0#64) = false :=
        beq_ofNat_zero_eq_false hlen_pos (by rw [← hdir_cases]; omega)
      code_fetches_range CryptoVerification.libsignalSessionCode dirPutStrBin
        img.base (Rust.withPanics ext) hfn
        (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") 0 40
      code_fetches_range CryptoVerification.libsignalSessionCode dirPutStrBin
        img.base (Rust.withPanics ext) hfn
        (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") 92 12
      apply sepWPp_cut_rebase (mid := atOff fnBase 104) hinv0
      dsimp +zetaDelta only [fnBase, tripleRatchetProgAtExt, atOff] at hpc
      dsimp +zetaDelta only [fnBase, atOff]
      set fnBase' := (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr dirPutStrName
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)) = prog
        reverting [Program.fetch]
      examples_hide_fetches
      wp_steps
      apply SepWP.fold hname_fold (by sep_frame)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro s1 P1 hinv_s1 ⟨hs1, hP1⟩
      · subst hP1
        let _ := hshim
        let _ := halloc
        let _ := hmemcpy
        let _ := hx1
        let _ := hx2
        let _ := hx2_zero
        let _ := hlen_nz
        rw [← hdir_cases]
        apply sepWPp_eq_pre
        · exact step_preheader hC hBcmp hGrow x R s0 s1 e0 rest0 cap ptr 1#64 bCap bPtr
            hstk hstk_max hname32 hlen32 hdir_cases hsp_align0 hinv_s1
            (by rw [hs1]; try dsimp +zetaDelta only [fnBase, atOff, tripleRatchetProgAtExt]; try simp only [wp_norm, arm64_norm])
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hrun)
            (spAligned_of_sub80 hsp_align0 (by rw [hs1]; try simp only [wp_norm, arm64_norm]))
            (by rw [hs1]; try simp only [wp_norm, arm64_norm])
            (by rw [hs1]; try simp only [wp_norm, arm64_norm])
            ⟨by rw [hs1]; try simp only [wp_norm, arm64_norm],
             by rw [hs1]; try simp only [wp_norm, arm64_norm],
             by dsimp only [calleeSavedVRegs]; rw [hs1]; try simp only [wp_norm, arm64_norm]⟩
            (by rw [hs1]; simp only [wp_norm, arm64_norm]; rw [hnil]; rfl)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx3)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm])
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx0)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try rw [hdir_cases]; try rfl)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm])
        · try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
          repeat rw [bv_sub_eq_add_neg64']
          try simp only [sp_slot_norm]
          try rw [emp_sepConj]
          try rw [sepConj_emp]
          try simp only [wp_norm, arm64_norm]
          try rw [Nat.mul_comm 48]
          try ac_rfl
  · -- Non-empty slice (`x.name ≠ []`)
    have hname_pos : 0 < x.name.length := List.length_pos_of_ne_nil hnil
    have hx2_nz : (BitVec.ofNat 64 x.name.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hname_pos (by omega)
    have hname_toNat : (BitVec.ofNat 64 x.name.length).toNat = x.name.length :=
      ofNat_toNat_of_lt (by omega)
    have hlay_name : LayoutOk x.name.length 1 :=
      layoutOk_u8_of_lt hname_pos (by omega)
    code_fetches_range CryptoVerification.libsignalSessionCode dirPutStrBin
      img.base (Rust.withPanics ext) hfn
      (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") 0 48
    apply sepWPp_cut_rebase (mid := atOff fnBase
      (ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>"
        "__rustc::__rust_no_alloc_shim_is_unstable_v2")) hinv0
    dsimp +zetaDelta only [fnBase, tripleRatchetProgAtExt, atOff] at hpc
    dsimp +zetaDelta only [fnBase, atOff]
    set fnBase' := (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr dirPutStrName
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog
      reverting [Program.fetch]
    examples_hide_fetches
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s1 P1 hinv_s1 ⟨hs1, hP1⟩
    · subst hP1
      let _ := hx2_nz
      have hsp_s1 : s1.sp = s0.sp - 80#64 := by
        rw [hs1]; try simp only [wp_norm, arm64_norm]
      have hspa_s1 : s1.spAligned = true :=
        spAligned_of_sub80 hsp_align0 hsp_s1
      have htr_s1 : s1.trace = s0.trace := by
        rw [hs1]; try simp only [wp_norm, arm64_norm]
      rw [stackAt_split_sp hsp_s1 (Nat.le_max_right growStk extHookStack) (by omega)]
      apply call_inImage_wpp hshim ()
        (ret_pc := atOff fnBase 48)
        (F := (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
          vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Heap A bCap bPtr x.bytes ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
          memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
          savedSlots s0 ∗
          A.pool)
        (hinv := hinv_s1)
        (hpc := by rw [hs1]; try dsimp +zetaDelta only [fnBase, atOff, tripleRatchetProgAtExt]; try simp only [wp_norm, arm64_norm])
        (hrun := by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hrun)
        (hsp_align := hspa_s1)
        (hlr := by rw [hs1]; try dsimp +zetaDelta only [fnBase, atOff, tripleRatchetProgAtExt]; try simp only [wp_norm, arm64_norm])
        (hspec := shim_pre_eq s1)
        (hφ := trivial)
        (hP := by
          try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
          repeat rw [bv_sub_eq_add_neg64']
          try simp only [sp_slot_norm]
          try rw [emp_sepConj]
          try rw [sepConj_emp]
          try simp only [wp_norm, arm64_norm]
          try rw [Nat.mul_comm 48]
          try ac_rfl)
        (hpan := fun _ => panic_false_wpp)
        (hexit := fun _ _ => rfl)
        (hoom := fun _ => rfl)
      intro s2 hpcs2 hruns2 hsps2 hcss2 hinvs2
      dsimp only [session2ShimSpecX, withStack, sessionShimSpec]
      try simp only [sepConj_assoc]
      refine sepWPp_pure_left fun htr_s20 => ?_
      have hsp_s2 : s2.sp = s0.sp - 80#64 := hsps2.trans hsp_s1
      have hspa_s2 : s2.spAligned = true := by
        simpa only [State.spAligned, hsps2] using hspa_s1
      have htr_s2 : s2.trace = s0.trace := htr_s20.trans htr_s1
      have hhigh_s2 : PresHigh s0 s2 :=
        (PresHigh.of_callee
          ⟨by rw [hs1]; try simp only [wp_norm, arm64_norm],
           by rw [hs1]; try simp only [wp_norm, arm64_norm],
           by dsimp only [calleeSavedVRegs]; rw [hs1]; try simp only [wp_norm, arm64_norm]⟩
          hcss2)
      have hx19_s2 : s2.readReg64 .x19 = BitVec.ofNat 64 x.name.length :=
        hcss2.1.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx2)
      have hx20_s2 : s2.readReg64 .x20 = x.bytesV :=
        hcss2.2.1.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx3)
      have hx22_s2 : s2.readReg64 .x22 = x.self :=
        hcss2.2.2.2.1.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx0)
      have hx23_s2 : s2.readReg64 .x23 = x.nameA :=
        hcss2.2.2.2.2.1.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx1)
      let _ := hsp_s2
      let _ := hspa_s2
      code_fetches_range CryptoVerification.libsignalSessionCode dirPutStrBin
        img.base (Rust.withPanics ext) hfn
        (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") 48 12
      apply sepWPp_cut_rebase (mid := atOff fnBase
        (ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>" "__rustc::__rust_alloc")) hinvs2
      dsimp +zetaDelta only [fnBase, tripleRatchetProgAtExt, atOff] at hpcs2
      dsimp +zetaDelta only [fnBase, atOff]
      set fnBase' := (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr dirPutStrName
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)) = prog
        reverting [Program.fetch]
      examples_hide_fetches
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro s3 P3 hinv_s3 ⟨hs3, hP3⟩
      · subst hP3
        have hsp_s3 : s3.sp = s1.sp := by
          rw [hs3]; try simp only [wp_norm, arm64_norm]; try exact hsps2
        have hspa_s3 : s3.spAligned = true := by
          simpa only [State.spAligned, hsp_s3] using hspa_s1
        have htr_s3 : s3.trace = s0.trace := by
          rw [hs3]; try simp only [wp_norm, arm64_norm]; try exact htr_s2
        rw [← hsp_s3]
        apply call_inImage_wpp halloc (x.name.length, 1)
          (ret_pc := atOff fnBase 60)
          (F := (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
            ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
            vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
            strRefAt (x.self + 0x18#64) x.dir.path ∗
            SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
            (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
            ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Heap A bCap bPtr x.bytes ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
            memRegion (s3.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
            savedSlots s0)
          (hinv := hinv_s3)
          (hpc := by rw [hs3]; try dsimp +zetaDelta only [fnBase, atOff, tripleRatchetProgAtExt]; try simp only [wp_norm, arm64_norm])
          (hrun := by rw [hs3]; try simp only [wp_norm, arm64_norm]; try exact hruns2)
          (hsp_align := hspa_s3)
          (hlr := by rw [hs3]; try dsimp +zetaDelta only [fnBase, atOff, tripleRatchetProgAtExt]; try simp only [wp_norm, arm64_norm])
          (hspec := rfl)
          (hφ := ⟨by rw [hs3]; simp only [wp_norm, arm64_norm]; exact hname_toNat,
                  by rw [hs3]; try simp only [wp_norm, arm64_norm],
                  hlay_name⟩)
          (hP := by
            try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
            repeat rw [bv_sub_eq_add_neg64']
            try simp only [sp_slot_norm]
            try rw [emp_sepConj]
            try rw [sepConj_emp]
            try simp only [wp_norm, arm64_norm]
            try rw [Nat.mul_comm 48]
            try ac_rfl)
          (hpan := fun _ => panic_false_wpp)
          (hexit := fun _ _ => rfl)
          (hoom := fun _ => rfl)
        intro s4 hpcs4 hruns4 hsps4 hcss4 hinvs4
        dsimp only [rustAllocSpecWithStack]
        have hsp_s4 : s4.sp = s1.sp := hsps4.trans hsp_s3
        have hspa_s4 : s4.spAligned = true := by
          simpa only [State.spAligned, hsp_s4] using hspa_s1
        have hhigh_s4 : PresHigh s0 s4 :=
          (PresHigh.of_callee
            ⟨by rw [hs3]; try simp only [wp_norm, arm64_norm]; try exact hhigh_s2.1,
             by rw [hs3]; try simp only [wp_norm, arm64_norm]; try exact hhigh_s2.2.1,
             by rw [hs3]; try simp only [wp_norm, arm64_norm]; try exact hhigh_s2.2.2⟩
            hcss4)
        have hx19_s4 : s4.readReg64 .x19 = BitVec.ofNat 64 x.name.length :=
          hcss4.1.trans (by rw [hs3]; try simp only [wp_norm, arm64_norm]; try exact hx19_s2)
        have hx20_s4 : s4.readReg64 .x20 = x.bytesV :=
          hcss4.2.1.trans (by rw [hs3]; try simp only [wp_norm, arm64_norm]; try exact hx20_s2)
        have hx22_s4 : s4.readReg64 .x22 = x.self :=
          hcss4.2.2.2.1.trans (by rw [hs3]; try simp only [wp_norm, arm64_norm]; try exact hx22_s2)
        have hx23_s4 : s4.readReg64 .x23 = x.nameA :=
          hcss4.2.2.2.2.1.trans (by rw [hs3]; try simp only [wp_norm, arm64_norm]; try exact hx23_s2)
        by_cases hoom : s4.readReg64 .x0 = 0
        · -- Allocation failure (`x0 = 0`)
          have hoom_beq_z : (s4.readReg64 .x0 == 0#64) = true := beq_iff_eq.mpr hoom
          simp only [hoom, ↓reduceIte]
          try simp only [sepConj_assoc]
          rw [pull_alloc_pure_right]
          refine sepWPp_pure_left fun htrace_oom => ?_
          code_fetches_range CryptoVerification.libsignalSessionCode dirPutStrBin
            img.base (Rust.withPanics ext) hfn
            (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") 60 4
          code_fetches_range CryptoVerification.libsignalSessionCode dirPutStrBin
            img.base (Rust.withPanics ext) hfn
            (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") 336 12
          apply sepWPp_cut_rebase (mid := atOff fnBase
            (ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>"
              "alloc::raw_vec::handle_error")) hinvs4
          dsimp +zetaDelta only [fnBase, tripleRatchetProgAtExt, atOff] at hpcs4
          dsimp +zetaDelta only [fnBase, atOff]
          set fnBase' := (libsignalSessionCode.rebase img.base
            (Rust.withPanics ext)).fnAddr dirPutStrName
          generalize_entry (libsignalSessionCode.rebase img.base
            (Rust.withPanics ext)) = prog
            reverting [Program.fetch]
          examples_hide_fetches
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          intro s5 P5 _hinv_s5 ⟨hs5, hP5⟩
          · subst hP5
            let _ := hBcmp
            let _ := hGrow
            let _ := hmemcpy
            let _ := hsp_s4
            let _ := hspa_s4
            let _ := hhigh_s4
            let _ := hx19_s4
            let _ := hx20_s4
            let _ := hx22_s4
            let _ := hx23_s4
            let _ := hoom_beq_z
            let _ := hlen32
            refine SepWPp.panic
              (by rw [hs5]; simp only [wp_norm, arm64_norm]; exact hruns4)
              (by
                have hpc5 : s5.pc = (tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName +
                    BitVec.ofNat 64 (ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>"
                      "alloc::raw_vec::handle_error") := by
                  rw [hs5]; try dsimp +zetaDelta only [fnBase, atOff, tripleRatchetProgAtExt]; try simp only [wp_norm, arm64_norm]
                rw [hpc5]
                exact panic_at_dirPutStr_handle_error img.base ext)
              fun hm_pan => ?_
            exact allowPanic_panicked
              (allocFailedIn_panicked (allocFailedIn_of_append (by
                rw [hs5]
                try simp only [wp_norm, arm64_norm]
                rw [htrace_oom, htr_s3])))
              hm_pan
        · -- Allocation success (`x0 ≠ 0`): copy `x.name` via `memcpy`
          have hoom_raw : (s4.readReg64 .x0 == 0#64) = false := beq_false_of_ne hoom
          let allocPtr := s4.readReg64 .x0
          simp only [hoom, ↓reduceIte]
          try simp only [sepConj_assoc]
          rw [pull_alloc_pure_right]
          refine sepWPp_pure_left fun ⟨_halign_ptr, htr_s43⟩ => ?_
          have htr_s4 : s4.trace = s0.trace := htr_s43.trans htr_s3
          code_fetches_range CryptoVerification.libsignalSessionCode dirPutStrBin
            img.base (Rust.withPanics ext) hfn
            (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") 60 20
          apply sepWPp_cut_rebase (mid := atOff fnBase
            (ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>" "memcpy")) hinvs4
          dsimp +zetaDelta only [fnBase, tripleRatchetProgAtExt, atOff] at hpcs4
          dsimp +zetaDelta only [fnBase, atOff]
          set fnBase' := (libsignalSessionCode.rebase img.base
            (Rust.withPanics ext)).fnAddr dirPutStrName
          generalize_entry (libsignalSessionCode.rebase img.base
            (Rust.withPanics ext)) = prog
            reverting [Program.fetch]
          examples_hide_fetches
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          intro s5 P5 hinv_s5 ⟨hs5, hP5⟩
          · subst hP5
            let _ := hoom_raw
            let _ := hsp_s4
            let _ := hspa_s4
            have hsp_s5 : s5.sp = s3.sp := by
              rw [hs5]; try simp only [wp_norm, arm64_norm]; try exact hsps4
            have hspa_s5 : s5.spAligned = true := by
              simpa only [State.spAligned, hsp_s5] using hspa_s3
            have htr_s5 : s5.trace = s0.trace := by
              rw [hs5]; try simp only [wp_norm, arm64_norm]; try exact htr_s4
            rw [← hsp_s5]
            apply call_inImage_wpp hmemcpy (allocPtr, x.nameA, x.name)
              (ret_pc := atOff fnBase 80)
              (F := A.pool ∗
                A.live allocPtr x.name.length 1 ∗
                (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
                ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
                vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
                strRefAt (x.self + 0x18#64) x.dir.path ∗
                (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
                ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
                vecU8Heap A bCap bPtr x.bytes ∗
                memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
                memRegion (s5.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
                savedSlots s0)
              (hinv := hinv_s5)
              (hpc := by rw [hs5]; try dsimp +zetaDelta only [fnBase, atOff, tripleRatchetProgAtExt]; try simp only [wp_norm, arm64_norm])
              (hrun := by rw [hs5]; try simp only [wp_norm, arm64_norm]; try exact hruns4)
              (hsp_align := hspa_s5)
              (hlr := by rw [hs5]; try dsimp +zetaDelta only [fnBase, atOff, tripleRatchetProgAtExt]; try simp only [wp_norm, arm64_norm])
              (hspec := sepConj_assoc _ _ _)
              (hφ := ⟨by rw [hs5]; try simp +zetaDelta only [wp_norm, arm64_norm],
                      by rw [hs5]; try simp only [wp_norm, arm64_norm]; try exact hx23_s4,
                      by rw [hs5]; simp only [wp_norm, arm64_norm]; exact hname_toNat,
                      by omega⟩)
              (hP := by
                try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt, allocPtr]
                repeat rw [bv_sub_eq_add_neg64']
                try simp only [sp_slot_norm]
                try rw [emp_sepConj]
                try rw [sepConj_emp]
                try simp only [wp_norm, arm64_norm]
                try rw [Nat.mul_comm 48]
                try ac_rfl)
              (hpan := fun _ => panic_false_wpp)
              (hexit := fun _ _ => rfl)
              (hoom := fun _ => rfl)
            intro s6 hpcs6 hruns6 hsps6 hcss6 hinvs6
            dsimp only [withStack, SpqrV1.Alloc.sessionMemcpyBytesAtSpec]
            try simp only [sepConj_assoc]
            refine sepWPp_pure_left fun ⟨_hx0_mc, htr_s65⟩ => ?_
            have hsp_s6 : s6.sp = s0.sp - 80#64 :=
              hsps6.trans (hsp_s5.trans (hsp_s3.trans hsp_s1))
            have hspa_s6 : s6.spAligned = true := by
              simpa only [State.spAligned, hsps6] using hspa_s5
            have htr_s6 : s6.trace = s0.trace := htr_s65.trans htr_s5
            have hhigh_s6 : PresHigh s0 s6 :=
              (PresHigh.of_callee
                ⟨by rw [hs5]; try simp only [wp_norm, arm64_norm]; try exact hhigh_s4.1,
                 by rw [hs5]; try simp only [wp_norm, arm64_norm]; try exact hhigh_s4.2.1,
                 by rw [hs5]; try simp only [wp_norm, arm64_norm]; try exact hhigh_s4.2.2⟩
                hcss6)
            have hx19_s6 : s6.readReg64 .x19 = BitVec.ofNat 64 x.name.length :=
              hcss6.1.trans (by rw [hs5]; try simp only [wp_norm, arm64_norm]; try exact hx19_s4)
            have hx20_s6 : s6.readReg64 .x20 = x.bytesV :=
              hcss6.2.1.trans (by rw [hs5]; try simp only [wp_norm, arm64_norm]; try exact hx20_s4)
            have hx21_s6 : s6.readReg64 .x21 = allocPtr :=
              hcss6.2.2.1.trans (by rw [hs5]; try simp +zetaDelta only [wp_norm, arm64_norm])
            have hx22_s6 : s6.readReg64 .x22 = x.self :=
              hcss6.2.2.2.1.trans (by rw [hs5]; try simp only [wp_norm, arm64_norm]; try exact hx22_s4)
            have hstk_merge6 :
                memRegion (s5.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
                  stackAt s5.sp extHookStack =
                  stackAt (s0.sp - 80#64) cal := by
              rw [← stackAt_split_sub s5.sp
                (Nat.le_max_right growStk extHookStack) (by omega), hsp_s5, hsp_s3, hsp_s1]
            have hpost_mc_ent :
                (allocPtr ↦ₛ x.name) ∗
                  SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                  stackAt s5.sp extHookStack ∗
                  A.pool ∗
                  A.live allocPtr x.name.length 1 ∗
                  (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
                  ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
                  vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
                  strRefAt (x.self + 0x18#64) x.dir.path ∗
                  (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
                  ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
                  vecU8Heap A bCap bPtr x.bytes ∗
                  memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
                  memRegion (s5.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
                  savedSlots s0 ⊢
                (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
                  ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
                  vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
                  strRefAt (x.self + 0x18#64) x.dir.path ∗
                  SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                  nameBuf A allocPtr x.name ∗
                  (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
                  ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
                  vecU8Heap A bCap bPtr x.bytes ∗
                  memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
                  stackAt (s0.sp - 80#64) cal ∗
                  savedSlots s0 ∗
                  A.pool := by
              rw [show ∀ (BS NB Stk5 Pool Live S0 S1 S2 VB Path B0 B1 B2 BH M0 MC Sav : SepProp),
                    BS ∗ NB ∗ Stk5 ∗ Pool ∗ Live ∗ S0 ∗ S1 ∗ S2 ∗ VB ∗ Path ∗
                      B0 ∗ B1 ∗ B2 ∗ BH ∗ M0 ∗ MC ∗ Sav =
                    (Live ∗ BS) ∗
                      (S0 ∗ S1 ∗ S2 ∗ VB ∗ Path ∗ NB ∗ B0 ∗ B1 ∗ B2 ∗ BH ∗
                        M0 ∗ (MC ∗ Stk5) ∗ Sav ∗ Pool) by intros; ac_rfl]
              rw [hstk_merge6]
              exact Entails.trans
                (sepConj_mono_left (nameBuf_of_nonempty A allocPtr x.name hnil hoom (by omega)))
                (entails_eq' (by ac_rfl))
            apply sepWPp_weaken_pre hpost_mc_ent
            cases hdir_cases : x.dir.changed with
            | nil =>
              code_fetches_range CryptoVerification.libsignalSessionCode dirPutStrBin
                img.base (Rust.withPanics ext) hfn
                (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") 80 12
              apply sepWPp_cut_rebase (mid := atOff fnBase 244) hinvs6
              dsimp +zetaDelta only [fnBase, tripleRatchetProgAtExt, atOff] at hpcs6
              dsimp +zetaDelta only [fnBase, atOff]
              set fnBase' := (libsignalSessionCode.rebase img.base
                (Rust.withPanics ext)).fnAddr dirPutStrName
              generalize_entry (libsignalSessionCode.rebase img.base
                (Rust.withPanics ext)) = prog
                reverting [Program.fetch]
              examples_hide_fetches
              wp_steps
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              intro s7 P7 hinv_s7 ⟨hs7, hP7⟩
              · subst hP7
                let _ := hBcmp
                let _ := hC
                rw [← hdir_cases]
                apply sepWPp_eq_pre
                · exact step_miss hGrow x R s0 s7 cap ptr allocPtr bCap bPtr
                    hstk hstk_max hlen32
                    (by rw [hdir_cases]; intro _ hm; exact (List.not_mem_nil hm).elim)
                    hinv_s7
                    (by rw [hs7]; try dsimp +zetaDelta only [fnBase, atOff, tripleRatchetProgAtExt]; try simp only [wp_norm, arm64_norm])
                    (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hruns6)
                    (by
                      have hsp_eq : s7.sp = s6.sp := by rw [hs7]; try simp only [wp_norm, arm64_norm]
                      simpa only [State.spAligned, hsp_eq] using hspa_s6)
                    (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hsp_s6)
                    (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact htr_s6)
                    ⟨by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hhigh_s6.1,
                     by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hhigh_s6.2.1,
                     by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hhigh_s6.2.2⟩
                    (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hx19_s6)
                    (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hx20_s6)
                    (by rw [hs7]; try simp +zetaDelta only [wp_norm, arm64_norm]; try exact hx21_s6)
                    (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hx22_s6)
                    (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try rw [hdir_cases]; try rfl)
                    (by rw [hs7]; try simp only [wp_norm, arm64_norm])
                · try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
                  try simp only [sp_slot_norm]
                  try rw [emp_sepConj]
                  try rw [sepConj_emp]
                  try simp only [wp_norm, arm64_norm]
                  try rw [Nat.mul_comm 48]
                  try ac_rfl
            | cons e0 rest0 =>
              have hlen_pos : 0 < (e0 :: rest0).length := by simp
              have hlen_nz : (BitVec.ofNat 64 (e0 :: rest0).length == 0#64) = false :=
                beq_ofNat_zero_eq_false hlen_pos (by rw [← hdir_cases]; omega)
              code_fetches_range CryptoVerification.libsignalSessionCode dirPutStrBin
                img.base (Rust.withPanics ext) hfn
                (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") 80 12
              apply sepWPp_cut_rebase (mid := atOff fnBase 104) hinvs6
              dsimp +zetaDelta only [fnBase, tripleRatchetProgAtExt, atOff] at hpcs6
              dsimp +zetaDelta only [fnBase, atOff]
              set fnBase' := (libsignalSessionCode.rebase img.base
                (Rust.withPanics ext)).fnAddr dirPutStrName
              generalize_entry (libsignalSessionCode.rebase img.base
                (Rust.withPanics ext)) = prog
                reverting [Program.fetch]
              examples_hide_fetches
              wp_steps
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              intro s7 P7 hinv_s7 ⟨hs7, hP7⟩
              · subst hP7
                let _ := hlen_nz
                rw [← hdir_cases]
                apply sepWPp_eq_pre
                · exact step_preheader hC hBcmp hGrow x R s0 s7 e0 rest0 cap ptr allocPtr bCap bPtr
                    hstk hstk_max hname32 hlen32 hdir_cases hsp_align0 hinv_s7
                    (by rw [hs7]; try dsimp +zetaDelta only [fnBase, atOff, tripleRatchetProgAtExt]; try simp only [wp_norm, arm64_norm])
                    (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hruns6)
                    (by
                      have hsp_eq : s7.sp = s6.sp := by rw [hs7]; try simp only [wp_norm, arm64_norm]
                      simpa only [State.spAligned, hsp_eq] using hspa_s6)
                    (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hsp_s6)
                    (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact htr_s6)
                    ⟨by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hhigh_s6.1,
                     by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hhigh_s6.2.1,
                     by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hhigh_s6.2.2⟩
                    (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hx19_s6)
                    (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hx20_s6)
                    (by rw [hs7]; try simp +zetaDelta only [wp_norm, arm64_norm]; try exact hx21_s6)
                    (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hx22_s6)
                    (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try rw [hdir_cases]; try rfl)
                    (by rw [hs7]; try simp only [wp_norm, arm64_norm])
                · try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
                  try simp only [sp_slot_norm]
                  try rw [emp_sepConj]
                  try rw [sepConj_emp]
                  try simp only [wp_norm, arm64_norm]
                  try rw [Nat.mul_comm 48]
                  try ac_rfl

theorem dirPutStr_ok_main {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {growStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (hGrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneDirName)
      (growOneDirSpec A img growStk))
    (hstk : 0x50 + max growStk extHookStack ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName)
      (dirPutStrSpec A img stk) :=
  dirPutStr_ok_main_roX hC (SpqrV1.Alloc.memcpyROOkExtX_of_hookSat hRO) hBcmp hGrow hstk

theorem dirPutStr_ok_main_withStack {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {growStk stk roStk : Nat}
    (hC : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName (SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack roStk))
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (hGrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneDirName)
      (growOneDirSpec A img growStk))
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hro : roStk ≤ extHookStack := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName)
      (dirPutStrSpec A img stk) :=
  dirPutStr_ok_main_roX hC (memcpyROOkExtX_of_withStack hro hRO) hBcmp hGrow hstk

end CryptoVerification.SignalSession.Cli.PutStr.Helpers
