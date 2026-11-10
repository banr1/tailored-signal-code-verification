/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.Pure
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.PutStr.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-- Opaque equality wrapper so `wp_steps` and `wp_norm_lhs` keep `curBase` atomic. -/
structure CurEq (c b : BitVec 64) : Prop where
  out : c = b

theorem stackAt_split_sp {sp s_sp : BitVec 64} {sub n : Nat}
    (hsp : s_sp = sp) (hle : sub ≤ n) (hmax : n ≤ 2 ^ 64) :
    stackAt sp n = memRegion (s_sp - BitVec.ofNat 64 n) (n - sub) ∗ stackAt s_sp sub := by
  subst hsp
  exact stackAt_split_sub s_sp hle hmax

theorem sepWPp_eq_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P' Q Qp)
    (hP : P = P') :
    SepWPp prog ret s P Q Qp :=
  hP ▸ h

/-- Shared post-drop tail of the hit branch starting at `+188`:
    copies the 24-byte `bytes` header `[x20..x20+16]` into `[dst..dst+16]` (`dst = curBase + 24#64`),
    then either jumps to `+296..+316` (`ret`, if `x.name = []`) or restores the frame and
    tail-calls `__rust_dealloc(namePtr, x.name.length, 1)` at `+240` (`x.name ≠ []`). -/
private theorem step_hit_copy_and_exit {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {growStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (x : DirPutStrGhost) (R : SepProp) (s0 s : State)
    (pre rest : List (List (BitVec 8) × List (BitVec 8)))
    (cap ptr curBase namePtr bCap bPtr d0 d1 d2 : BitVec 64)
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hstk_max : stk ≤ 2 ^ 64)
    (hname32 : x.name.length < 2 ^ 32)
    (hput_eq : (x.dir.put x.name x.bytes).changed = pre ++ (x.name, x.bytes) :: rest)
    (hcur : curBase = ptr + BitVec.ofNat 64 (pre.length * 48))
    (hle : (pre ++ (x.name, x.bytes) :: rest).length ≤ cap.toNat)
    (hbound : cap.toNat * 48 < 2 ^ 63)
    (hptr : ptr ≠ 0)
    (hcap : cap ≠ 0)
    (hsp_align0 : s0.spAligned = true)
    (hinv : ImgCallInv img s)
    (hpc : s.pc = atOff ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName) 188)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64)
    (htr : s.trace = s0.trace)
    (hhigh : PresHigh s0 s)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.name.length)
    (hx20 : s.readReg64 .x20 = x.bytesV)
    (hx21 : s.readReg64 .x21 = namePtr)
    (hx22 : s.readReg64 .x22 = curBase + 24#64) :
    let cal := max growStk extHookStack
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s
      ((x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (pre ++ (x.name, x.bytes) :: rest).length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        vecU8 A curBase x.name ∗
        ((curBase + 24#64) ↦₆₄ d0) ∗ ((curBase + 32#64) ↦₆₄ d1) ∗
        ((curBase + 40#64) ↦₆₄ d2) ∗
        arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 ((pre ++ (x.name, x.bytes) :: rest).length * 48))
          ((cap.toNat - (pre ++ (x.name, x.bytes) :: rest).length) * 48) ∗
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
  have hdealloc := dealloc_ok_at_dirPutStr hC
  have hfn : libsignalSessionCode.fnOff dirPutStrName =
      num% (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") := dirPutStr_fnOff
  have hdir_ent :
      vecOf A 48 8 (dirEntryAt A) x.self (pre ++ (x.name, x.bytes) :: rest) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ⊢
        dirAt A x.self (x.dir.put x.name x.bytes) := by
    unfold dirAt
    rw [hput_eq]
    exact Entails.refl _
  have hhit_ent :
      (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (pre ++ (x.name, x.bytes) :: rest).length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        vecU8 A curBase x.name ∗
        (((curBase + 24#64) ↦₆₄ bCap) ∗ ((curBase + 32#64) ↦₆₄ bPtr) ∗
          ((curBase + 40#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗ vecU8Heap A bCap bPtr x.bytes) ∗
        arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 ((pre ++ (x.name, x.bytes) :: rest).length * 48))
          ((cap.toNat - (pre ++ (x.name, x.bytes) :: rest).length) * 48) ⊢
        vecOf A 48 8 (dirEntryAt A) x.self (pre ++ (x.name, x.bytes) :: rest) :=
    vecOf_dirEntry_hit_assemble A x.self cap ptr curBase bCap bPtr
      pre rest x.name x.bytes hcur hle hbound hptr hcap
  clear hcur
  by_cases hnil : x.name = []
  · -- `x.name = []`: shared epilogue
    have hx19_z : s.readReg64 .x19 = 0#64 := by
      rw [hx19, hnil]; rfl
    have hdrop_name : nameBuf A namePtr x.name ⊢ emp := by
      rw [hnil]; exact nameBuf_drop_nil A namePtr
    code_fetches_range CryptoVerification.libsignalSessionCode dirPutStrBin
      img.base (Rust.withPanics ext) hfn
      (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") 188 20
    code_fetches_range CryptoVerification.libsignalSessionCode dirPutStrBin
      img.base (Rust.withPanics ext) hfn
      (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") 296 24
    dsimp only [DirPutStrPost, DirPutStrPanic, dirPutStrSpec, Spec.inImage,
      tripleRatchetProgAtExt, atOff, savedSlots] at hpc ⊢
    clear hC hdealloc hfn
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr dirPutStrName = fnBase
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog
      reverting [Program.fetch, Program.externAt?, subroutine_ok]
    examples_hide_fetches
    rcases hhigh with ⟨hx27, hx28, hvregs⟩
    apply SepWPp.of_sepWP_ret
    wp_steps
    apply SepWP.fold hdrop_name (by sep_frame)
    apply SepWP.fold (savedSlots_merge s0 (cal := cal) hstk hstk_max) (by sep_frame)
    apply SepWP.fold
      (pointsTo64_three_entails_memRegion24 x.bytesV bCap bPtr (BitVec.ofNat 64 x.bytes.length))
      (by sep_frame)
    apply SepWP.fold hhit_ent (by sep_frame)
    apply SepWP.fold hdir_ent (by sep_frame)
    wp_done
  · -- `x.name ≠ []`: tail-call `__rust_dealloc`
    have hpos : 0 < x.name.length := List.length_pos_of_ne_nil hnil
    have hx19_nz : (BitVec.ofNat 64 x.name.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hpos (by omega)
    have hx19_toNat : (BitVec.ofNat 64 x.name.length).toNat = x.name.length :=
      ofNat_toNat_of_lt (by omega)
    code_fetches_range CryptoVerification.libsignalSessionCode dirPutStrBin
      img.base (Rust.withPanics ext) hfn
      (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") 188 56
    dsimp only [tripleRatchetProgAtExt, atOff, savedSlots] at hpc hdealloc ⊢
    clear hC hfn
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr dirPutStrName = fnBase
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog
      reverting [Program.fetch, Program.externAt?, subroutine_ok]
    examples_hide_fetches
    apply sepWPp_cut (mid := atOff fnBase
      (ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>" "__rustc::__rust_dealloc")) hinv
    dsimp only [atOff]
    wp_steps
    apply SepWP.fold (savedSlots_merge s0 (cal := cal) hstk hstk_max) (by sep_frame)
    apply SepWP.fold
      (pointsTo64_three_entails_memRegion24 x.bytesV bCap bPtr (BitVec.ofNat 64 x.bytes.length))
      (by sep_frame)
    apply SepWP.fold hhit_ent (by sep_frame)
    apply SepWP.fold hdir_ent (by sep_frame)
    apply SepWP.fold (nameBuf_for_dealloc A namePtr x.name hnil) (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s1 hs1 hinv_s1
    rw [show ∀ (P0 L1 M1 D1 N1 B24 S1 Pool : SepProp),
          (P0 ∗ L1 ∗ M1) ∗ D1 ∗ N1 ∗ B24 ∗ S1 ∗ Pool =
            P0 ∗ (Pool ∗ L1 ∗ M1 ∗ D1 ∗ N1 ∗ B24 ∗ S1) from
          fun _ _ _ _ _ _ _ _ => by ac_rfl]
    refine sepWPp_pure_left fun ⟨_hnp_ne0, hlay_name⟩ => ?_
    have hsp_s1 : s1.sp = s0.sp := by
      rw [hs1]; simp only [wp_norm, arm64_norm]
    have hsp_align_s1 : s1.spAligned = true := by
      simpa only [State.spAligned, hsp_s1] using hsp_align0
    have htr_s1 : s1.trace = s0.trace := by
      rw [hs1]; simp only [wp_norm, arm64_norm]; exact htr
    have hcs_s1 : CalleeSavedPreserved s0 s1 := by
      refine calleeSavedPreserved_of_restored
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        ⟨by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.1,
         by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.2.1,
         by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.2.2⟩
    rw [← hsp_s1, stackAt_split_sub s1.sp (show extHookStack ≤ stk by omega) hstk_max]
    apply tailcall_inImage_frame hdealloc (namePtr, x.name.length, 1)
      (F := dirAt A x.self (x.dir.put x.name x.bytes) ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.bytesV 24 ∗
        memRegion (s1.sp - BitVec.ofNat 64 stk) (stk - extHookStack))
      (hinv := hinv_s1)
      (hpc := by rw [hs1]; simp only [wp_norm, arm64_norm])
      (hrun := by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hrun)
      (hsp := hsp_align_s1)
      (hlr := by rw [hs1]; simp only [wp_norm, arm64_norm])
      (hspec := rfl)
      (hφ := ⟨by rw [hs1]; simp only [wp_norm, arm64_norm],
              by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx19_toNat,
              by rw [hs1]; simp only [wp_norm, arm64_norm],
              hlay_name⟩)
      (hP := by ac_rfl)
      (hpan := fun _ => rfl)
      (hexit := fun _ _ => rfl)
      (hoom := fun _ => rfl)
    intro sf _hpcf _hrunf hspf hcsf
    refine ⟨?_, hspf.trans hsp_s1, hcs_s1.trans hcsf⟩
    intro hm
    dsimp only [rustDeallocExternSpecWithStack] at hm
    dsimp only [dirPutStrSpec, Spec.inImage]
    have hstk_re :
        memRegion (s1.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗
          stackAt s1.sp extHookStack =
          stackAt s0.sp stk := by
      rw [← stackAt_split_sub s1.sp (show extHookStack ≤ stk by omega) hstk_max, hsp_s1]
    rw [show ((⌜sf.trace = s1.trace⌝ ∗ A.pool ∗ stackAt s1.sp extHookStack) ∗
          (dirAt A x.self (x.dir.put x.name x.bytes) ∗
            SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
            memRegion x.bytesV 24 ∗
            memRegion (s1.sp - BitVec.ofNat 64 stk) (stk - extHookStack))) ∗ R =
        ⌜sf.trace = s1.trace⌝ ∗
          (dirAt A x.self (x.dir.put x.name x.bytes) ∗
            SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
            memRegion x.bytesV 24 ∗
            (memRegion (s1.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗
              stackAt s1.sp extHookStack) ∗
            A.pool ∗ R) by ac_rfl] at hm
    rw [satisfies_pure_sepConj, hstk_re] at hm
    rcases hm with ⟨htr_sf1, hmem_sf⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr_sf1.trans htr_s1, ?_⟩
    ac_nf at hmem_sf ⊢

/-- Hit branch entry at `+164`: drop old `Vec<u8>` value (`oldCap = 0` or `__rust_dealloc`),
    then delegate to `step_hit_copy_and_exit` at `+188`. -/
theorem step_hit {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {growStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (x : DirPutStrGhost) (R : SepProp) (s0 s : State)
    (pre rest : List (List (BitVec 8) × List (BitVec 8)))
    (oldBs : List (BitVec 8))
    (cap ptr curBase namePtr bCap bPtr oldCap oldPtr : BitVec 64)
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hstk_max : stk ≤ 2 ^ 64)
    (hname32 : x.name.length < 2 ^ 32)
    (hput_eq : (x.dir.put x.name x.bytes).changed = pre ++ (x.name, x.bytes) :: rest)
    (hcur : curBase = ptr + BitVec.ofNat 64 (pre.length * 48))
    (hle : (pre ++ (x.name, x.bytes) :: rest).length ≤ cap.toNat)
    (hbound : cap.toNat * 48 < 2 ^ 63)
    (hptr : ptr ≠ 0)
    (hcap : cap ≠ 0)
    (hsp_align0 : s0.spAligned = true)
    (hinv : ImgCallInv img s)
    (hpc : s.pc = atOff ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName) 164)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 80#64)
    (htr : s.trace = s0.trace)
    (hhigh : PresHigh s0 s)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.name.length)
    (hx20 : s.readReg64 .x20 = x.bytesV)
    (hx21 : s.readReg64 .x21 = namePtr)
    (hx25 : s.readReg64 .x25 = curBase + 32#64) :
    let cal := max growStk extHookStack
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s
      ((x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (pre ++ (x.name, x.bytes) :: rest).length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        vecU8 A curBase x.name ∗
        ((curBase + 24#64) ↦₆₄ oldCap) ∗ ((curBase + 32#64) ↦₆₄ oldPtr) ∗
        ((curBase + 40#64) ↦₆₄ BitVec.ofNat 64 oldBs.length) ∗
        vecU8Heap A oldCap oldPtr oldBs ∗
        arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 ((pre ++ (x.name, x.bytes) :: rest).length * 48))
          ((cap.toNat - (pre ++ (x.name, x.bytes) :: rest).length) * 48) ∗
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
  have hcur' : CurEq curBase (ptr + BitVec.ofNat 64 (pre.length * 48)) := ⟨hcur⟩
  clear hcur
  have hdealloc := dealloc_ok_at_dirPutStr hC
  have hfn : libsignalSessionCode.fnOff dirPutStrName =
      num% (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") := dirPutStr_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode dirPutStrBin
    img.base (Rust.withPanics ext) hfn
    (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") 164 24
  set fnBase := (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirPutStrName
  by_cases hold0 : oldCap = 0#64
  · -- `oldCap = 0`
    subst hold0
    apply sepWPp_cut_rebase (mid := atOff fnBase 188) hinv
    dsimp only [atOff] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog
      reverting [Program.fetch]
    examples_hide_fetches
    wp_steps
    apply SepWP.fold (vecU8Heap_drop_zero A oldPtr oldBs) (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s1 P1 hinv_s1 ⟨hs1, hP1⟩
    · subst hP1
      apply sepWPp_eq_pre
      · exact step_hit_copy_and_exit hC x R s0 s1 pre rest cap ptr curBase namePtr bCap bPtr
          0#64 oldPtr (BitVec.ofNat 64 oldBs.length)
          hstk hstk_max hname32 hput_eq hcur'.out hle hbound hptr hcap hsp_align0 hinv_s1
          (by rw [hs1]; try dsimp +zetaDelta only [atOff, tripleRatchetProgAtExt]; simp only [wp_norm, arm64_norm])
          (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hrun)
          (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hsp)
          (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact htr)
          ⟨by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hhigh.1,
           by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hhigh.2.1,
           by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hhigh.2.2⟩
          (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hx19)
          (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hx20)
          (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hx21)
          (by rw [hs1]; simp only [wp_norm, arm64_norm])
      · try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
        try rw [emp_sepConj]
        try rw [sepConj_emp]
        try simp only [wp_norm, arm64_norm]
        try rw [Nat.mul_comm 48]
        try ac_rfl
  · -- `oldCap ≠ 0`: deallocate `oldPtr`
    have hold_beq : (oldCap == 0#64) = false := beq_false_of_ne hold0
    apply sepWPp_cut_rebase (mid := atOff fnBase
      (ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>" "__rustc::__rust_dealloc")) hinv
    dsimp only [atOff] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog
      reverting [Program.fetch]
    examples_hide_fetches
    wp_steps
    apply SepWP.fold (vecU8Heap_for_dealloc A oldCap oldPtr oldBs hold0) (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s1 P1 hinv_s1 ⟨hs1, hP1⟩
    · subst hP1
      rw [show ∀ (P0 L0 M0 Z : SepProp),
            (P0 ∗ L0 ∗ M0) ∗ Z = P0 ∗ L0 ∗ M0 ∗ Z from
            fun _ _ _ _ => by ac_rfl]
      refine sepWPp_pure_left fun ⟨_holdp_ne0, hlay_old⟩ => ?_
      have hsp_s1 : s1.sp = s0.sp - 80#64 := by
        rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hsp
      have htr_s1 : s1.trace = s0.trace := by
        rw [hs1]; simp only [wp_norm, arm64_norm]; try exact htr
      rw [stackAt_split_sp hsp_s1 (Nat.le_max_right growStk extHookStack) (by omega)]
      apply call_inImage_wpp hdealloc (oldPtr, oldCap.toNat, 1)
        (ret_pc := atOff fnBase 188)
        (F := (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (pre ++ (x.name, x.bytes) :: rest).length) ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A) 48 ptr pre ∗
          vecU8 A curBase x.name ∗
          ((curBase + 24#64) ↦₆₄ oldCap) ∗ ((curBase + 32#64) ↦₆₄ oldPtr) ∗
          ((curBase + 40#64) ↦₆₄ BitVec.ofNat 64 oldBs.length) ∗
          arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
          memRegion (ptr + BitVec.ofNat 64 ((pre ++ (x.name, x.bytes) :: rest).length * 48))
            ((cap.toNat - (pre ++ (x.name, x.bytes) :: rest).length) * 48) ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          nameBuf A namePtr x.name ∗
          (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Heap A bCap bPtr x.bytes ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
          memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
          savedSlots s0)
        (hinv := hinv_s1)
        (hpc := by rw [hs1]; try dsimp +zetaDelta only [atOff, tripleRatchetProgAtExt]; simp only [wp_norm, arm64_norm])
        (hrun := by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hrun)
        (hsp_align := by
          have hsp_eq : s1.sp = s.sp := by rw [hs1]; simp only [wp_norm, arm64_norm]
          simpa only [State.spAligned, hsp_eq] using hsp_align)
        (hlr := by rw [hs1]; try dsimp +zetaDelta only [atOff, tripleRatchetProgAtExt]; simp only [wp_norm, arm64_norm])
        (hspec := rfl)
        (hφ := ⟨by rw [hs1]; simp only [wp_norm, arm64_norm],
                by rw [hs1]; simp only [wp_norm, arm64_norm],
                by rw [hs1]; simp only [wp_norm, arm64_norm],
                hlay_old⟩)
        (hP := by
          try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
          try rw [emp_sepConj]
          try rw [sepConj_emp]
          try simp only [wp_norm, arm64_norm]
          try rw [Nat.mul_comm 48]
          try ac_rfl)
        (hpan := fun _ => panic_false_wpp)
        (hexit := fun _ _ => rfl)
        (hoom := fun _ => rfl)
      intro sm hpcm hrunm hspm hcsm hinvm
      dsimp only [rustDeallocExternSpecWithStack]
      try simp only [sepConj_assoc]
      refine sepWPp_pure_left fun htr_sm0 => ?_
      have hstk_back :
          memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
            stackAt s1.sp extHookStack =
            stackAt (s0.sp - 80#64) cal := by
        rw [← stackAt_split_sub s1.sp (Nat.le_max_right growStk extHookStack) (by omega), hsp_s1]
      rw [show ∀ (Pool StkE A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 : SepProp),
            Pool ∗ StkE ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗
              A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 =
            A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗
              A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ (A20 ∗ StkE) ∗ A21 ∗ Pool from
            fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by ac_rfl]
      rw [hstk_back]
      have hhigh_s1 : PresHigh s0 s1 :=
        ⟨by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hhigh.1,
         by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hhigh.2.1,
         by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hhigh.2.2⟩
      exact step_hit_copy_and_exit hC x R s0 sm pre rest cap ptr curBase namePtr bCap bPtr
        oldCap oldPtr (BitVec.ofNat 64 oldBs.length)
        hstk hstk_max hname32 hput_eq hcur'.out hle hbound hptr hcap hsp_align0 hinvm
        hpcm hrunm
        (hspm.trans hsp_s1)
        (htr_sm0.trans htr_s1)
        (hhigh_s1.of_callee hcsm)
        (hcsm.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hx19))
        (hcsm.2.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hx20))
        (hcsm.2.2.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hx21))
        (hcsm.2.2.2.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]))

end CryptoVerification.SignalSession.Cli.PutStr.Helpers
