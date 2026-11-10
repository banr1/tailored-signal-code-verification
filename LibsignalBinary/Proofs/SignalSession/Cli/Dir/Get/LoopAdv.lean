/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.Hit
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.Decode
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# Loop Advance Step (`+68`..`+80` / `+164`) for `<signal_session::stores::Dir>::get`
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Get.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SpqrV1.Alloc

ls_attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
ls_attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem cstk_le_pow64 {cstk stk : Nat} (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64) :
    cstk ≤ 2 ^ 64 :=
  Nat.le_trans (Nat.le_add_left cstk 112) (Nat.le_trans hstk hfull)

theorem lt_pow63_of_lt_pow32 {n : Nat} (h : n < 2 ^ 32) : n < 2 ^ 63 :=
  Nat.lt_trans h (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 32 < 63))

theorem lt_pow64_of_lt_pow32 {n : Nat} (h : n < 2 ^ 32) : n < 2 ^ 64 :=
  Nat.lt_trans h (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 32 < 64))

theorem lt_pow64_of_lt_pow63 {n : Nat} (h : n < 2 ^ 63) : n < 2 ^ 64 :=
  Nat.lt_trans h (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 63 < 64))

theorem ofNat64_toNat_of_lt32 {n : Nat} (h : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_pow64_of_lt_pow32 h)]

theorem ofNat64_toNat_of_lt63 {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_pow64_of_lt_pow63 h)]

private theorem sub48_cons_len
    {hd : List (BitVec 8) × List (BitVec 8)}
    {rest : List (List (BitVec 8) × List (BitVec 8))} :
    BitVec.ofNat 64 (48 * (hd :: rest).length) - 48#64 =
      BitVec.ofNat 64 (48 * rest.length) := by
  have hbeq : BitVec.ofNat 64 (48 * (hd :: rest).length) =
      BitVec.ofNat 64 (48 * rest.length) + 48#64 := by
    rw [List.length_cons, Nat.mul_add_one, ← BitVec.ofNat_add]
  rw [hbeq]
  bv_bits

private theorem ofNat48_beq_48_false
    {hd nxt : List (BitVec 8) × List (BitVec 8)}
    {tail : List (List (BitVec 8) × List (BitVec 8))}
    (hlt : 48 * (hd :: nxt :: tail).length < 2 ^ 63) :
    (BitVec.ofNat 64 (48 * (hd :: nxt :: tail).length) == 48#64) = false := by
  have hlt64 : 48 * (hd :: nxt :: tail).length < 2 ^ 64 := lt_pow64_of_lt_pow63 hlt
  clear hlt
  apply beq_false_of_ne
  intro h
  have ht : (BitVec.ofNat 64 (48 * (hd :: nxt :: tail).length)).toNat = (48#64).toNat :=
    congrArg BitVec.toNat h
  have h48_nat : (48#64).toNat = 48 := rfl
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64, h48_nat] at ht
  clear hlt64 h48_nat h
  simp only [List.length_cons] at ht
  omega

/-- Advance helper from `+68` (`SUBS X24, X24, #48; ADD X23, X23, #48; B.EQ +88`) when `hdName ≠ x.name`:
    jumps to `hmiss` at `+164` when `rest = []`, or hands control to `ih` at `+80` when `rest ≠ []`. -/
theorem step_loop_advance
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {cstk stk : Nat}
    {x : DirGetGhost} {s0 sm : State}
    {changedCap changedPtr : BitVec 64}
    {pre rest : List (List (BitVec 8) × List (BitVec 8))}
    {hdName hdBytes : List (BitVec 8)}
    {Extra R : SepProp}
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hcap_ok : x.dir.changed.length ≤ changedCap.toNat ∧
      changedCap.toNat * 48 < 2 ^ 63 ∧ changedPtr ≠ 0)
    (hchanged : x.dir.changed = pre ++ (hdName, hdBytes) :: rest)
    (hne : ∀ e ∈ pre, e.1 ≠ x.name)
    (hhd_ne : hdName ≠ x.name)
    (hmiss : ∀ sm : State,
      sm.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName + 164#64 →
      sm.status = .Running →
      sm.spAligned = true →
      sm.sp = s0.sp - 112#64 →
      HighCalleeSaved s0 sm →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.fs.files = s0.fs.files →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = x.ret →
      sm.readReg64 .x20 = BitVec.ofNat 64 x.name.length →
      sm.readReg64 .x21 = x.self →
      sm.readReg64 .x22 = x.nameA →
      (∀ e ∈ x.dir.changed, e.1 ≠ x.name) →
      SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
        (s0.readReg64 .lr) sm
        ((dirAt A x.self x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          memRegion x.ret 48 ∗
          stackAt (s0.sp - 112#64) cstk ∗
          memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
          savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗ Extra)
        (dirGetPostQ rd pathOk A img stk x s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
        (dirGetPanicQp rd pathOk A img stk x s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R))
    (ih : ∀ (pre' : List (List (BitVec 8) × List (BitVec 8))) (sn : State),
      rest ≠ [] →
      x.dir.changed = pre' ++ rest →
      (∀ e ∈ pre', e.1 ≠ x.name) →
      img.FrozenLoaded sn →
      sn.symtab = img.symtab →
      sn.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName + 80#64 →
      sn.status = .Running →
      sn.spAligned = true →
      sn.sp = s0.sp - 112#64 →
      HighCalleeSaved s0 sn →
      sn.fs.files = s0.fs.files →
      sn.trace = s0.trace →
      sn.readReg64 .x19 = x.ret →
      sn.readReg64 .x20 = BitVec.ofNat 64 x.name.length →
      sn.readReg64 .x21 = x.self →
      sn.readReg64 .x22 = x.nameA →
      sn.readReg64 .x23 = changedPtr + BitVec.ofNat 64 (48 * pre'.length) + 40#64 →
      sn.readReg64 .x24 = BitVec.ofNat 64 (48 * rest.length) →
      SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
        (s0.readReg64 .lr) sn
        (((vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
          RustHeap.arrayAt (dirEntryAt A) 48 changedPtr pre' ∗
          RustHeap.arrayAt (dirEntryAt A) 48
            (changedPtr + BitVec.ofNat 64 (48 * pre'.length)) rest ∗
          (if changedCap = 0 then emp
           else A.live changedPtr (changedCap.toNat * 48) 8 ∗
             memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
               ((changedCap.toNat - x.dir.changed.length) * 48)) ∗
          strRefAt (x.self + 24#64) x.dir.path) ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          memRegion x.ret 48 ∗
          stackAt (s0.sp - 112#64) cstk ∗
          memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
          savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗ Extra)
        (dirGetPostQ rd pathOk A img stk x s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
        (dirGetPanicQp rd pathOk A img stk x s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R))
    (hfz_m : img.FrozenLoaded sm)
    (hsym_m : sm.symtab = img.symtab)
    (hpc_m : sm.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName + 68#64)
    (hrun_m : sm.status = .Running)
    (hsp_al_m : sm.spAligned = true)
    (hsp_m : sm.sp = s0.sp - 112#64)
    (hhcs_m : HighCalleeSaved s0 sm)
    (hfs_m : sm.fs.files = s0.fs.files)
    (htr_m : sm.trace = s0.trace)
    (hx19_m : sm.readReg64 .x19 = x.ret)
    (hx20_m : sm.readReg64 .x20 = BitVec.ofNat 64 x.name.length)
    (hx21_m : sm.readReg64 .x21 = x.self)
    (hx22_m : sm.readReg64 .x22 = x.nameA)
    (hx23_m : sm.readReg64 .x23 = changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64)
    (hx24_m : sm.readReg64 .x24 = BitVec.ofNat 64 (48 * ((hdName, hdBytes) :: rest).length)) :
    SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      (s0.readReg64 .lr) sm
      (((vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
        RustHeap.arrayAt (dirEntryAt A) 48 changedPtr pre ∗
        vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length)) hdName ∗
        vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) hdBytes ∗
        RustHeap.arrayAt (dirEntryAt A) 48
          (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 48#64) rest ∗
        (if changedCap = 0 then emp
         else A.live changedPtr (changedCap.toNat * 48) 8 ∗
           memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
             ((changedCap.toNat - x.dir.changed.length) * 48)) ∗
        strRefAt (x.self + 24#64) x.dir.path) ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) cstk ∗
        memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗ Extra)
      (dirGetPostQ rd pathOk A img stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQp rd pathOk A img stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  have _ := hstk; have _ := hfull
  have hfn : libsignalSessionCode.fnOff dirGetName =
      ls_off% "<libsignal_cli::stores::Dir>::get" := dirGet_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 68 12
  clear hfn
  generalize hentry_raw :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName = fnStart at *
  generalize hprog_raw :
    libsignalSessionCode.rebase img.base (Rust.withPanics ext) = prog at *
  clear hentry_raw hprog_raw
  examples_hide_fetches
  have hsuf_lt63 : 48 * ((hdName, hdBytes) :: rest).length < 2 ^ 63 := by
    have hch_len : pre.length + ((hdName, hdBytes) :: rest).length = x.dir.changed.length := by
      rw [hchanged, List.length_append]
    have hle : ((hdName, hdBytes) :: rest).length ≤ changedCap.toNat :=
      Nat.le_trans (hch_len ▸ Nat.le_add_left _ pre.length) hcap_ok.1
    rw [Nat.mul_comm]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 48 hle) hcap_ok.2.1
  have hne_next : ∀ e ∈ pre ++ [(hdName, hdBytes)], e.1 ≠ x.name := by
    intro e he
    rcases List.mem_append.mp he with he1 | he2
    · exact hne e he1
    · rcases List.mem_singleton.mp he2 with rfl
      exact hhd_ne
  have hrest_cases : rest = [] ∨ ∃ nxt tail, rest = nxt :: tail := by
    cases rest with
    | nil => exact Or.inl rfl
    | cons nxt tail => exact Or.inr ⟨nxt, tail, rfl⟩
  rcases hrest_cases with hr_nil | ⟨nxt, tail, hr_cons⟩
  · clear ih
    rw [hr_nil] at hchanged hx24_m ⊢
    have hall_ne : ∀ e ∈ x.dir.changed, e.1 ≠ x.name := by
      simpa [hchanged] using hne_next
    have hrepack_dir :
        (vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
          RustHeap.arrayAt (dirEntryAt A) 48 changedPtr pre ∗
          vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length)) hdName ∗
          vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) hdBytes ∗
          RustHeap.arrayAt (dirEntryAt A) 48
            (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 48#64) [] ∗
          (if changedCap = 0 then emp
           else A.live changedPtr (changedCap.toNat * 48) 8 ∗
             memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
               ((changedCap.toNat - x.dir.changed.length) * 48))) ∗
          strRefAt (x.self + 24#64) x.dir.path ⊢
        dirAt A x.self x.dir := by
      unfold dirAt RustHeap.vecOf RustHeap.vecAt
      refine sepConj_mono ?_ (Entails.refl _)
      refine Entails.trans ?_ (Entails.sepExists_intro changedCap)
      refine Entails.trans ?_ (Entails.sepExists_intro changedPtr)
      rw [vecBuf_dirEntry_expose]
      refine Entails.trans ?_ (sepConj_mono_right (Entails.pure_right hcap_ok (Entails.refl _)))
      rw [hchanged, arrayAt_dirEntry_append]
      dsimp only [RustHeap.arrayAt, dirEntryAt]
      sep_frame
    refine seq_frozen_state (mid := fnStart + 164#64) hfz_m ?_
    simp only [List.length_singleton, Nat.mul_one] at hx24_m
    wp_steps
    apply SepWP.fold hrepack_dir (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hfz_m'
    refine SepWPp.perm
      (hmiss _
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa only [wp_norm, arm64_norm] using hsp_al_m)
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs_m.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        hfz_m'
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hall_ne)
      (by sep_frame)
  · clear hmiss
    have hsuf_lt63' : 48 * ((hdName, hdBytes) :: nxt :: tail).length < 2 ^ 63 := by
      rwa [← hr_cons]
    have hsub48 :
        BitVec.ofNat 64 (48 * ((hdName, hdBytes) :: nxt :: tail).length) - 48#64 =
          BitVec.ofNat 64 (48 * (nxt :: tail).length) :=
      sub48_cons_len
    have hbeq48 :
        (BitVec.ofNat 64 (48 * ((hdName, hdBytes) :: nxt :: tail).length) == 48#64) = false :=
      ofNat48_beq_48_false hsuf_lt63'
    have hpeel :
        RustHeap.arrayAt (dirEntryAt A) 48 changedPtr pre ∗
          vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length)) hdName ∗
          vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) hdBytes ⊢
        RustHeap.arrayAt (dirEntryAt A) 48 changedPtr (pre ++ [(hdName, hdBytes)]) := by
      rw [arrayAt_dirEntry_append]
      dsimp only [RustHeap.arrayAt, dirEntryAt]
      sep_frame
    have hnext_ptr :
        changedPtr + BitVec.ofNat 64 (48 * pre.length) + 48#64 =
          changedPtr + BitVec.ofNat 64 (48 * (pre ++ [(hdName, hdBytes)]).length) := by
      rw [List.length_append, List.length_singleton, Nat.mul_add_one, BitVec.add_assoc, ← BitVec.ofNat_add]
    have hx23_next :
        changedPtr + BitVec.ofNat 64 (48 * pre.length) + 88#64 =
          changedPtr + BitVec.ofNat 64 (48 * (pre ++ [(hdName, hdBytes)]).length) + 40#64 := by
      rw [← hnext_ptr]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine seq_frozen_state (mid := fnStart + 80#64) hfz_m ?_
    wp_step
    wp_step
    wp_step
    simp only [← hr_cons]
    apply SepWP.fold hpeel (by sep_frame)
    rw [hnext_ptr]
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hfz_m'
    refine SepWPp.perm
      (ih (pre ++ [(hdName, hdBytes)]) _
        (by rw [hr_cons]; simp)
        (by rw [hchanged, List.append_assoc]; rfl)
        hne_next
        hfz_m'
        (by simp only [wp_norm, arm64_norm, *])
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa only [wp_norm, arm64_norm] using hsp_al_m)
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs_m.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm]))
      (by sep_frame)

end CryptoVerification.SignalSession.Cli.Get.Helpers
