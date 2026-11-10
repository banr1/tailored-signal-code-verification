/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.HitAndLoop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.Miss
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# Verification of `<signal_session::stores::Dir>::put::<alloc::string::String>`

Verifies `Dir::put::<String>` (`0x60`-byte frame) against `dirPutSpec A img stk`:
scans `Dir.changed` via `bcmp` (`DirGhost.setOrPush`), replacing the first matching entry's value
buffer and tail-deallocating the moved `name` on hit, or growing `Dir.changed` via `grow_one` when
full and appending `(name, bytes)` on miss.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Put

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.SignalSession.Cli.Put.Helpers

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem mul_48_bv (n : BitVec 64) :
    ((n + (n <<< 1)) <<< 4) = 48#64 * n := by
  bv_bits

/-- `Dir::put::<String>` satisfies `dirPutSpec A img stk` at any 4 KiB-aligned image base, given allocator/`bcmp` contracts and `grow_one`. -/
theorem dirPut_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {growStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (hGrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneDirName)
      (growOneDirSpec A img growStk))
    (hstk : 0x60 + max growStk extHookStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName)
      (dirPutSpec A img stk) := by
  let _ := hb
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc0 hrun0 hpre hsp0
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa only [State.spAligned, beq_iff_eq] using hsp0
  change s0.mem ⊨
    (⌜ImgCallInv img s0⌝ ∗
      (⌜s0.readReg64 .x0 = x.self ∧ s0.readReg64 .x1 = x.nameV ∧
          s0.readReg64 .x2 = x.bytesV ∧ x.dir.changed.length < 2 ^ 32⌝ ∗
        dirAt A x.self x.dir ∗ vecU8 A x.nameV x.name ∗ vecU8 A x.bytesV x.bytes ∗
        stackAt s0.sp stk ∗ A.pool)) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, ⟨hx0, hx1, hx2, hlen_lt32⟩, hmem⟩
  rw [show dirAt A x.self x.dir =
        (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
          RustHeap.vecAt A 48 8 (dirEntryAt A) x.self cap ptr x.dir.changed) ∗
          strRefAt (x.self + 0x18#64) x.dir.path from rfl,
      show vecU8 A x.nameV x.name =
        (∃∗ nameCap : BitVec 64, ∃∗ namePtr : BitVec 64,
          vecU8At A x.nameV nameCap namePtr x.name) from rfl] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc] at hmem
  rw [satisfies_sepExists] at hmem; obtain ⟨nameCap, hmem⟩ := hmem
  rw [satisfies_sepExists] at hmem; obtain ⟨namePtr, hmem⟩ := hmem
  rw [satisfies_sepExists] at hmem; obtain ⟨cap, hmem⟩ := hmem
  rw [satisfies_sepExists] at hmem; obtain ⟨ptr, hmem⟩ := hmem
  have hstk_le : stk ≤ 2 ^ 64 := by
    have hcell : s0.mem ⊨ (x.self ↦₆₄ cap) ∗ (stackAt s0.sp stk ∗
        (((x.self + 8#64) ↦₆₄ ptr) ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
          vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          vecU8At A x.nameV nameCap namePtr x.name ∗
          vecU8 A x.bytesV x.bytes ∗ A.pool ∗ R)) := by
      unfold RustHeap.vecAt vecHeader at hmem
      convert hmem using 1; ac_rfl
    exact Nat.le_of_lt (stk_lt_two_pow_64 (by omega) hcell)
  have h96 : 0x60 ≤ stk := by omega
  have hgrow_stk : growStk ≤ stk - 96 := by omega
  have hhook96 : extHookStack ≤ stk - 96 := by omega
  have hbcmp := subroutine_ok_withPutCS s0 (bcmp_ok_at (b := img.base) hBcmp)
  have hdealloc := subroutine_ok_withPutCS_x img s0 hinv0 (dealloc_ok_at hC)
  have hgrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName +
        BitVec.ofNat 64 (ls_rel% dirPutName growOneDirName))
      (withPutCS s0 (growOneDirRawSpec A growStk)) :=
    subroutine_ok_withPutCS_x img s0 hinv0 (grow_ok_at hGrow)
  rw [stackAt_put_frame h96 hstk_le s0.sp,
      vecU8At_eq_header_rest' A x.nameV nameCap namePtr x.name] at hmem
  simp only [← sepConj_assoc] at hmem
  refine ⟨_, R, hmem, ?_⟩
  have hbcmp0 := putCalleeOk_mk img ext (ls_rel% dirPutName cliBcmpName) hbcmp
  have hdealloc0 := putCalleeOk_mk img ext (ls_rel% dirPutName deallocName) hdealloc
  have hgrow0 := putCalleeOk_mk img ext (ls_rel% dirPutName growOneDirName) hgrow
  clear hbcmp hdealloc hgrow hGrow hC hBcmp
  code_fetches_range libsignalSessionCode dirPutBin img.base (Rust.withPanics ext)
    (ls_lemma% fnOff dirPutName) (ls_off% dirPutName) 0 68
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr dirPutName = entry
  examples_hide_fetches
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun v0 => ?_
  refine SepWPp.exists_elim fun v1 => ?_
  refine SepWPp.exists_elim fun v2 => ?_
  refine SepWPp.exists_elim fun v3 => ?_
  refine SepWPp.exists_elim fun v4 => ?_
  refine SepWPp.exists_elim fun v5 => ?_
  refine SepWPp.exists_elim fun v6 => ?_
  refine SepWPp.exists_elim fun v7 => ?_
  refine SepWPp.exists_elim fun v8 => ?_
  refine SepWPp.exists_elim fun v9 => ?_
  refine SepWPp.exists_elim fun v10 => ?_
  refine SepWPp.exists_elim fun v11 => ?_
  unfold RustHeap.vecAt vecHeader
  refine SepWPp.weaken_pre
    (Entails.of_eq (show _ =
      ⌜x.name.length ≤ nameCap.toNat ∧ nameCap.toNat < 2 ^ 63 ∧ namePtr ≠ 0⌝ ∗
      (((s0.sp - 96#64) ↦₆₄ v0) ∗ ((s0.sp - 88#64) ↦₆₄ v1) ∗
        ((s0.sp - 80#64) ↦₆₄ v2) ∗ ((s0.sp - 72#64) ↦₆₄ v3) ∗
        ((s0.sp - 64#64) ↦₆₄ v4) ∗ ((s0.sp - 56#64) ↦₆₄ v5) ∗
        ((s0.sp - 48#64) ↦₆₄ v6) ∗ ((s0.sp - 40#64) ↦₆₄ v7) ∗
        ((s0.sp - 32#64) ↦₆₄ v8) ∗ ((s0.sp - 24#64) ↦₆₄ v9) ∗
        ((s0.sp - 16#64) ↦₆₄ v10) ∗ ((s0.sp - 8#64) ↦₆₄ v11) ∗
        stackAt (s0.sp - 96#64) (stk - 96) ∗
        (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
        vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        (x.nameV ↦₆₄ nameCap) ∗ ((x.nameV + 8#64) ↦₆₄ namePtr) ∗
        ((x.nameV + 16#64) ↦₆₄ BitVec.ofNat 64 x.name.length) ∗
        vecU8Rest A nameCap namePtr x.name ∗
        vecU8 A x.bytesV x.bytes ∗ A.pool) by ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨hna_le, hna_lt, hna_ptr⟩ => ?_
  have hsp_align96 : (s0.sp - 96#64) &&& 15#64 = 0#64 := sp_sub_96_aligned halign
  cases hchanged : x.dir.changed with
  | nil =>
    -- Empty `Dir.changed` (`len = 0`): jump to `step_miss` (`+196`)
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (196))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_p
    refine SepWPp.weaken_pre ?_
      (step_miss (img := img) (A := A) (ext := ext) (growStk := growStk) (stk := stk)
        (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr) (R := R)
        (putCalleeOk_get hgrow0) h96 hgrow_stk hstk_le
        (by rw [hchanged]; intro _ h; exact nomatch h)
        hlen_lt32 hna_le hna_lt hna_ptr
        (pc_of_entry hentry 196#64 (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        halign
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by rw [hchanged]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        ((PutCalleeSaved.refl s0).step (by simp only [arm64_norm]) hinv_p)
        rfl)
    have hname_mem :
        (x.nameV ↦₆₄ nameCap) ∗ ((x.nameV + 8#64) ↦₆₄ namePtr) ∗
          ((x.nameV + 16#64) ↦₆₄ BitVec.ofNat 64 x.name.length) ⊢
        memRegion x.nameV 24 :=
      vecHeader_entails_memRegion x.nameV nameCap namePtr (BitVec.ofNat 64 x.name.length)
    unfold putSavedCells RustHeap.vecAt vecHeader
    rw [hchanged]
    refine Entails.trans (Entails.of_eq (show _ =
      (((x.nameV ↦₆₄ nameCap) ∗ ((x.nameV + 8#64) ↦₆₄ namePtr) ∗
        ((x.nameV + 16#64) ↦₆₄ BitVec.ofNat 64 x.name.length)) ∗
        (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
          ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
          ((s0.sp - 72#64) ↦₆₄ v3) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
          stackAt (s0.sp - 96#64) (stk - 96) ∗
          (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 ([] : List _).length) ∗
          vecBuf A 48 8 (dirEntryAt A) cap ptr [] ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          vecU8Rest A nameCap namePtr x.name ∗
          vecU8 A x.bytesV x.bytes ∗ A.pool)) by ac_rfl))
      (Entails.trans (sepConj_mono_left hname_mem) (Entails.of_eq (by ac_rfl)))
  | cons hd rest =>
    -- Non-empty `Dir.changed`: enter `step_loop` (`+80`)
    have hlen_cons_lt32 : (hd :: rest).length < 2 ^ 32 := by rw [← hchanged]; exact hlen_lt32
    have hlen_ne0 : BitVec.ofNat 64 (hd :: rest).length ≠ 0#64 := by
      intro h0
      have h := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_zero,
          List.length_cons] at h
      omega
    refine SepWPp.weaken_pre
      (Entails.trans (Entails.of_eq (show _ =
        vecBuf A 48 8 (dirEntryAt A) cap ptr (hd :: rest) ∗
          (((s0.sp - 96#64) ↦₆₄ v0) ∗ ((s0.sp - 88#64) ↦₆₄ v1) ∗
            ((s0.sp - 80#64) ↦₆₄ v2) ∗ ((s0.sp - 72#64) ↦₆₄ v3) ∗
            ((s0.sp - 64#64) ↦₆₄ v4) ∗ ((s0.sp - 56#64) ↦₆₄ v5) ∗
            ((s0.sp - 48#64) ↦₆₄ v6) ∗ ((s0.sp - 40#64) ↦₆₄ v7) ∗
            ((s0.sp - 32#64) ↦₆₄ v8) ∗ ((s0.sp - 24#64) ↦₆₄ v9) ∗
            ((s0.sp - 16#64) ↦₆₄ v10) ∗ ((s0.sp - 8#64) ↦₆₄ v11) ∗
            stackAt (s0.sp - 96#64) (stk - 96) ∗
            (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
            ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: rest).length) ∗
            strRefAt (x.self + 0x18#64) x.dir.path ∗
            (x.nameV ↦₆₄ nameCap) ∗ ((x.nameV + 8#64) ↦₆₄ namePtr) ∗
            ((x.nameV + 16#64) ↦₆₄ BitVec.ofNat 64 x.name.length) ∗
            vecU8Rest A nameCap namePtr x.name ∗
            vecU8 A x.bytesV x.bytes ∗ A.pool) by ac_rfl))
        (sepConj_mono_left (vecBuf_expose_arrayAt A 48 8 (dirEntryAt A) cap ptr (hd :: rest)))) ?_
    refine SepWPp.weaken_pre
      (Entails.of_eq (show _ =
        ⌜(hd :: rest).length ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧
          (hd :: rest).length * 48 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (((s0.sp - 96#64) ↦₆₄ v0) ∗ ((s0.sp - 88#64) ↦₆₄ v1) ∗
          ((s0.sp - 80#64) ↦₆₄ v2) ∗ ((s0.sp - 72#64) ↦₆₄ v3) ∗
          ((s0.sp - 64#64) ↦₆₄ v4) ∗ ((s0.sp - 56#64) ↦₆₄ v5) ∗
          ((s0.sp - 48#64) ↦₆₄ v6) ∗ ((s0.sp - 40#64) ↦₆₄ v7) ∗
          ((s0.sp - 32#64) ↦₆₄ v8) ∗ ((s0.sp - 24#64) ↦₆₄ v9) ∗
          ((s0.sp - 16#64) ↦₆₄ v10) ∗ ((s0.sp - 8#64) ↦₆₄ v11) ∗
          stackAt (s0.sp - 96#64) (stk - 96) ∗
          (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: rest).length) ∗
          arrayAt (dirEntryAt A) 48 ptr (hd :: rest) ∗
          (if cap = 0 then emp
           else A.live ptr (cap.toNat * 48) 8 ∗
             memRegion (ptr + BitVec.ofNat 64 ((hd :: rest).length * 48))
               ((cap.toNat - (hd :: rest).length) * 48)) ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          (x.nameV ↦₆₄ nameCap) ∗ ((x.nameV + 8#64) ↦₆₄ namePtr) ∗
          ((x.nameV + 16#64) ↦₆₄ BitVec.ofNat 64 x.name.length) ∗
          vecU8Rest A nameCap namePtr x.name ∗
          vecU8 A x.bytesV x.bytes ∗ A.pool) by ac_rfl)) ?_
    refine SepWPp.pure_elim fun ⟨hlen_le, hcap48_lt, _, hptr_ne⟩ => ?_
    have hcap0 : cap ≠ 0 := by
      intro h0
      rw [h0] at hlen_le
      change (hd :: rest).length ≤ 0 at hlen_le
      rw [List.length_cons] at hlen_le
      omega
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (80))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    intro hinv_p
    have hx27_eq :
        ((BitVec.ofNat 64 (hd :: rest).length +
            (BitVec.ofNat 64 (hd :: rest).length <<< 1)) <<< 4) =
          BitVec.ofNat 64 (48 * (hd :: rest).length) := by
      rw [mul_48_bv, show (48#64 : BitVec 64) = BitVec.ofNat 64 48 from rfl, ← BitVec.ofNat_mul]
    refine SepWPp.weaken_pre ?_
      (step_loop (img := img) (A := A) (ext := ext) (growStk := growStk) (stk := stk)
        (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr) (R := R)
        (putCalleeOk_get hbcmp0) (putCalleeOk_get hdealloc0)
        (putCalleeOk_get hgrow0)
        h96 hhook96 hgrow_stk hstk_le hlen_lt32
        (by rw [hchanged]; exact hlen_le) hcap48_lt hptr_ne hna_le hna_lt hna_ptr halign
        rest [] hd _ _
        (by rw [hchanged, List.nil_append])
        (fun _ h => nomatch h)
        (pc_of_entry hentry 80#64 (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by rw [hchanged]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp [arm64_norm])
        (by simp only [arm64_norm]; exact hx27_eq)
        ((PutCalleeSaved.refl s0).step (by simp only [arm64_norm]) hinv_p)
        rfl)
    have hname_mem :
        (x.nameV ↦₆₄ nameCap) ∗ ((x.nameV + 8#64) ↦₆₄ namePtr) ∗
          ((x.nameV + 16#64) ↦₆₄ BitVec.ofNat 64 x.name.length) ⊢
        memRegion x.nameV 24 :=
      vecHeader_entails_memRegion x.nameV nameCap namePtr (BitVec.ofNat 64 x.name.length)
    simp only [hcap0, ↓reduceIte, arrayAt_cons, arrayAt_nil, emp_sepConj]
    unfold putSavedCells vecHeader
    rw [hchanged]
    have h0ptr : ptr + BitVec.ofNat 64 (([] : List (List (BitVec 8) × List (BitVec 8))).length * 48) = ptr := by
      simp
    rw [h0ptr]
    refine Entails.trans (Entails.of_eq (show _ =
      (((x.nameV ↦₆₄ nameCap) ∗ ((x.nameV + 8#64) ↦₆₄ namePtr) ∗
        ((x.nameV + 16#64) ↦₆₄ BitVec.ofNat 64 x.name.length)) ∗
        (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
          ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
          ((s0.sp - 72#64) ↦₆₄ v3) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
          stackAt (s0.sp - 96#64) (stk - 96) ∗
          (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: rest).length) ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          dirEntryAt A hd ptr ∗
          arrayAt (dirEntryAt A) 48 (ptr + BitVec.ofNat 64 48) rest ∗
          memRegion (ptr + BitVec.ofNat 64 ((hd :: rest).length * 48))
            ((cap.toNat - (hd :: rest).length) * 48) ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          vecU8Rest A nameCap namePtr x.name ∗
          vecU8 A x.bytesV x.bytes ∗ A.pool)) by ac_rfl))
      (Entails.trans (sepConj_mono_left hname_mem) (Entails.of_eq (by ac_rfl)))

end CryptoVerification.SignalSession.Cli.Put
