/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.Pure
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# Miss path (`+196 .. +288`) of `<signal_session::stores::Dir>::put::<alloc::string::String>`
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Put.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.SignalSession.Cli

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Push `{name, bytes}` into an already non-full `Dir.changed` buffer (`+208 .. +244`)
and finish via `step_epilogue_ret` (`+248 .. +272`). -/
theorem step_write_miss {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    {s0 s : State} {x : DirPutGhost}
    {v3 cap ptr nameCap namePtr : BitVec 64} {P R : SepProp}
    (h96 : 0x60 ≤ stk)
    (hle_stk : stk ≤ 2 ^ 64)
    (hmiss : ∀ e ∈ x.dir.changed, e.1 ≠ x.name)
    (hlen_lt32 : x.dir.changed.length < 2 ^ 32)
    (hfit : x.dir.changed.length < cap.toNat)
    (hna_le : x.name.length ≤ nameCap.toNat)
    (hna_lt : nameCap.toNat < 2 ^ 63)
    (hna_ptr : namePtr ≠ 0)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr dirPutName + 208#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = namePtr)
    (hx20 : s.readReg64 .x20 = nameCap)
    (hx21 : s.readReg64 .x21 = x.bytesV)
    (hx22 : s.readReg64 .x22 = x.self)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 x.name.length)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 x.dir.changed.length)
    (hx25 : s.readReg64 .x25 = ptr)
    (hcs : PutCalleeSaved s0 s)
    (hP : P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        RustHeap.vecAt A 48 8 (dirEntryAt A) x.self cap ptr x.dir.changed ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes ∗ A.pool) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s P
      (putRetQ A img stk x s0 R)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpec A img stk).onPanic x s0 sf ∗ R)) := by
  code_fetches_range libsignalSessionCode dirPutBin img.base (Rust.withPanics ext)
    (ls_lemma% fnOff dirPutName) (ls_off% dirPutName) 208 40
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr dirPutName = entry
  examples_hide_fetches
  subst hP
  have hcap0 : cap ≠ 0 := by
    intro h0
    rw [h0] at hfit
    change x.dir.changed.length < 0 at hfit
    omega
  unfold RustHeap.vecAt vecHeader vecU8
  rw [vecBuf_of_ne_zero A 48 8 (dirEntryAt A) cap ptr x.dir.changed hcap0]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun bytesCap => ?_
  refine SepWPp.exists_elim fun bytesPtr => ?_
  rw [vecU8At_eq_header_rest' A x.bytesV bytesCap bytesPtr x.bytes,
      show vecHeader x.bytesV bytesCap bytesPtr (BitVec.ofNat 64 x.bytes.length) =
        (x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) from rfl]
  refine SepWPp.weaken_pre
    (Entails.of_eq (show _ =
      ⌜x.dir.changed.length ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ⌜x.bytes.length ≤ bytesCap.toNat ∧ bytesCap.toNat < 2 ^ 63 ∧ bytesPtr ≠ 0⌝ ∗
      (putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr x.dir.changed ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        (x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Rest A bytesCap bytesPtr x.bytes ∗ A.pool) by ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap48_lt, hptr_ne⟩ => ?_
  refine SepWPp.pure_elim fun ⟨hbs_le, hbs_lt, hbs_ptr⟩ => ?_
  have hspare_eq :
      (cap.toNat - x.dir.changed.length) * 48 =
        48 + (cap.toNat - (x.dir.changed.length + 1)) * 48 := by
    have : cap.toNat - x.dir.changed.length = 1 + (cap.toNat - (x.dir.changed.length + 1)) := by
      omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have hspare_split := ProofLib.memRegion_split
    (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
    48 ((cap.toNat - (x.dir.changed.length + 1)) * 48) (by omega)
  have hslot_next :
      ptr + BitVec.ofNat 64 (x.dir.changed.length * 48) + 48#64 =
        ptr + BitVec.ofNat 64 ((x.dir.changed.length + 1) * 48) := by
    rw [BitVec.add_assoc, show (48#64 : BitVec 64) = BitVec.ofNat 64 48 from rfl,
      ← BitVec.ofNat_add, Nat.succ_mul]
  have hmul_bv :
      BitVec.ofNat 64 (x.dir.changed.length * 48) =
        BitVec.ofNat 64 x.dir.changed.length * 48#64 := by
    rw [show (48#64 : BitVec 64) = BitVec.ofNat 64 48 from rfl, ← BitVec.ofNat_mul]
  rw [hspare_eq, hspare_split, hslot_next, hmul_bv,
      memRegion_48_split_entry (ptr + BitVec.ofNat 64 x.dir.changed.length * 48#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun l1 => ?_
  refine SepWPp.exists_elim fun q1 => ?_
  refine SepWPp.exists_elim fun l0 => ?_
  refine SepWPp.exists_elim fun p0 => ?_
  refine SepWPp.exists_elim fun c0 => ?_
  unfold pointsTo128
  apply SepWPp.of_sepWP_cs (mid := entry + bv% (248))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_w
  set slot := ptr + BitVec.ofNat 64 (x.dir.changed.length * 48)
  have hslot_eq : ptr + BitVec.ofNat 64 x.dir.changed.length * 48#64 = slot :=
    congrArg (ptr + ·) hmul_bv.symm
  have hlen1_eq :
      BitVec.ofNat 64 x.dir.changed.length + 1#64 =
        BitVec.ofNat 64 (x.dir.changed.length + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have hentry_pack :
      ((slot ↦₆₄ nameCap) ∗ ((slot + 8#64) ↦₆₄ namePtr) ∗
        ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 x.name.length) ∗
        vecU8Rest A nameCap namePtr x.name) ∗
      (((slot + 24#64) ↦₆₄ bytesCap) ∗ ((slot + 24#64 + 8#64) ↦₆₄ bytesPtr) ∗
        ((slot + 40#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Rest A bytesCap bytesPtr x.bytes) ⊢
      dirEntryAt A (x.name, x.bytes) slot := by
    have hname_v :
        (slot ↦₆₄ nameCap) ∗ ((slot + 8#64) ↦₆₄ namePtr) ∗
          ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 x.name.length) ∗
          vecU8Rest A nameCap namePtr x.name ⊢ vecU8 A slot x.name := by
      have hhdr :
          (slot ↦₆₄ nameCap) ∗ ((slot + 8#64) ↦₆₄ namePtr) ∗
            ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 x.name.length) ∗
            vecU8Rest A nameCap namePtr x.name =
          vecHeader slot nameCap namePtr (BitVec.ofNat 64 x.name.length) ∗
            vecU8Rest A nameCap namePtr x.name := by
        unfold vecHeader; ac_rfl
      rw [hhdr]
      exact vecU8_intro_header_rest hna_le hna_lt hna_ptr
    have hbytes_v :
        ((slot + 24#64) ↦₆₄ bytesCap) ∗ ((slot + 24#64 + 8#64) ↦₆₄ bytesPtr) ∗
          ((slot + 40#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Rest A bytesCap bytesPtr x.bytes ⊢ vecU8 A (slot + 0x18#64) x.bytes := by
      have h40 : slot + 40#64 = (slot + 0x18#64) + 16#64 := by bv_arith
      have h24 : slot + 24#64 = slot + 0x18#64 := rfl
      rw [h40, h24]
      have hhdr2 :
          ((slot + 0x18#64) ↦₆₄ bytesCap) ∗ (((slot + 0x18#64) + 8#64) ↦₆₄ bytesPtr) ∗
            (((slot + 0x18#64) + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Rest A bytesCap bytesPtr x.bytes =
          vecHeader (slot + 0x18#64) bytesCap bytesPtr (BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Rest A bytesCap bytesPtr x.bytes := by
        unfold vecHeader; ac_rfl
      rw [hhdr2]
      exact vecU8_intro_header_rest hbs_le hbs_lt hbs_ptr
    exact sepConj_mono hname_v hbytes_v
  have hput_eq : (x.dir.put x.name x.bytes) =
      { changed := x.dir.changed ++ [(x.name, x.bytes)], path := x.dir.path } := by
    simp only [DirGhost.put, setOrPush_miss hmiss]
  have hvec_pack :
      (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (x.dir.changed.length + 1)) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        (arrayAt (dirEntryAt A) 48 ptr x.dir.changed ∗ dirEntryAt A (x.name, x.bytes) slot) ∗
        memRegion (ptr + BitVec.ofNat 64 ((x.dir.changed.length + 1) * 48))
          ((cap.toNat - (x.dir.changed.length + 1)) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ⊢
      dirAt A x.self (x.dir.put x.name x.bytes) := by
    have hnew_len : (x.dir.changed ++ [(x.name, x.bytes)]).length = x.dir.changed.length + 1 := by
      simp
    rw [hput_eq, ← arrayAt_concat (dirEntryAt A) 48 ptr x.dir.changed (x.name, x.bytes),
        ← hnew_len]
    refine Entails.trans ?_
      (dirAt_of_vecAt A x.self cap ptr (x.dir.changed ++ [(x.name, x.bytes)]) x.dir.path)
    unfold RustHeap.vecAt vecHeader
    rw [vecBuf_of_ne_zero A 48 8 (dirEntryAt A) cap ptr _ hcap0,
        pure_sepConj_of_true ⟨by rw [hnew_len]; omega, hcap48_lt, hptr_ne⟩]
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre ?_
    (step_epilogue_ret (img := img) (A := A) (ext := ext) (stk := stk) (v3 := v3) (R := R)
      h96 hle_stk
      (by rw [hentry]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      halign
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) hinv_w)
      rfl)
  rw [hslot_eq, hlen1_eq]
  have hbytesV_mem :
      ((x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length)) ⊢ memRegion x.bytesV 24 := by
    have hhdrV :
        ((x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length)) =
        vecHeader x.bytesV bytesCap bytesPtr (BitVec.ofNat 64 x.bytes.length) := by
      unfold vecHeader; ac_rfl
    rw [hhdrV]
    exact vecHeader_entails_memRegion x.bytesV bytesCap bytesPtr (BitVec.ofNat 64 x.bytes.length)
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hvec_pack
        (sepConj_mono_right (sepConj_mono_left hbytesV_mem)))))
  refine Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left
            (sepConj_mono_right hentry_pack)))))))))

/-- Full miss handler (`+196 .. +288`): checks capacity at `+196 .. +204`, calls `grow_one`
at `+276 .. +288` if `len = cap`, and delegates to `step_write_miss` at `+208`. -/
theorem step_miss {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {growStk stk : Nat}
    {s0 s : State} {x : DirPutGhost}
    {v3 cap ptr nameCap namePtr : BitVec 64} {P R : SepProp}
    (hgrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName +
        BitVec.ofNat 64 (ls_rel% dirPutName growOneDirName))
      (withPutCS s0 (growOneDirRawSpec A growStk)))
    (h96 : 0x60 ≤ stk)
    (hgrow_stk : growStk ≤ stk - 96)
    (hle_stk : stk ≤ 2 ^ 64)
    (hmiss : ∀ e ∈ x.dir.changed, e.1 ≠ x.name)
    (hlen_lt32 : x.dir.changed.length < 2 ^ 32)
    (hna_le : x.name.length ≤ nameCap.toNat)
    (hna_lt : nameCap.toNat < 2 ^ 63)
    (hna_ptr : namePtr ≠ 0)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr dirPutName + 196#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = namePtr)
    (hx20 : s.readReg64 .x20 = nameCap)
    (hx21 : s.readReg64 .x21 = x.bytesV)
    (hx22 : s.readReg64 .x22 = x.self)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 x.name.length)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 x.dir.changed.length)
    (hx25 : s.readReg64 .x25 = ptr)
    (hcs : PutCalleeSaved s0 s)
    (hP : P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        RustHeap.vecAt A 48 8 (dirEntryAt A) x.self cap ptr x.dir.changed ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes ∗ A.pool) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s P
      (putRetQ A img stk x s0 R)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpec A img stk).onPanic x s0 sf ∗ R)) := by
  code_fetches_range libsignalSessionCode dirPutBin img.base (Rust.withPanics ext)
    (ls_lemma% fnOff dirPutName) (ls_off% dirPutName) 196 12
  code_fetches_range libsignalSessionCode dirPutBin img.base (Rust.withPanics ext)
    (ls_lemma% fnOff dirPutName) (ls_off% dirPutName) 276 16
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr dirPutName = entry
  examples_hide_fetches
  subst hP
  unfold RustHeap.vecAt vecHeader
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (sepConj_mono_right (vecBuf_expose_arrayAt A 48 8 (dirEntryAt A) cap ptr x.dir.changed))))) ?_
  refine SepWPp.weaken_pre
    (Entails.of_eq (show _ =
      ⌜x.dir.changed.length ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧
        x.dir.changed.length * 48 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
        arrayAt (dirEntryAt A) 48 ptr x.dir.changed ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * 48) 8 ∗
           memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
             ((cap.toNat - x.dir.changed.length) * 48)) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes ∗ A.pool) by ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨hlen_le, hcap48_lt, _, hptr_ne⟩ => ?_
  have hvec_back :
      ((x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
        arrayAt (dirEntryAt A) 48 ptr x.dir.changed ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * 48) 8 ∗
           memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
             ((cap.toNat - x.dir.changed.length) * 48))) =
      RustHeap.vecAt A 48 8 (dirEntryAt A) x.self cap ptr x.dir.changed := by
    unfold RustHeap.vecAt vecHeader vecBuf
    rw [pure_sepConj_of_true ⟨hlen_le, hcap48_lt, hptr_ne⟩]
    by_cases h0 : cap = 0
    · subst h0
      have hnil : x.dir.changed = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen_le)
      simp only [hnil, ↓reduceIte, arrayAt_nil]
      ac_rfl
    · simp only [h0, ↓reduceIte]
      ac_rfl
  by_cases hcap_eq : BitVec.ofNat 64 x.dir.changed.length = cap
  · -- Full capacity (`len = cap`): call `grow_one`
    have hcap_nat : cap.toNat = x.dir.changed.length := by
      rw [← hcap_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    apply SepWPp.of_sepWP_cs
      (mid := entry + BitVec.ofNat 64 (ls_rel% dirPutName growOneDirName))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    let retGrow := entry + bv% (284)
    refine step_grow_call (img := img) (A := A) (ext := ext) (growStk := growStk) (stk := stk)
      (x0 := x) (R := R)
      (F := putSavedCells s0 v3 ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes)
      hgrow hgrow_stk hle_stk x.self cap ptr retGrow x.dir.changed
      (by omega)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      halign
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]; rfl)
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) hinv1)
      (by rw [← hvec_back]; ac_rfl)
      fun sm newPtr hpcm hrunm hspm htrm hcsm hput_csm => ?_
    dsimp only [retGrow] at hpcm
    clear retGrow
    rcases hcsm with ⟨hc19, hc20, hc21, hc22, hc23, hc24, _, _, _, _, _, _⟩
    have sm_x19 : sm.readReg64 .x19 = namePtr := hc19.trans (by simp only [arm64_norm, *])
    have sm_x20 : sm.readReg64 .x20 = nameCap := hc20.trans (by simp only [arm64_norm, *])
    have sm_x21 : sm.readReg64 .x21 = x.bytesV := hc21.trans (by simp only [arm64_norm, *])
    have sm_x22 : sm.readReg64 .x22 = x.self := hc22.trans (by simp only [arm64_norm, *])
    have sm_x23 : sm.readReg64 .x23 = BitVec.ofNat 64 x.name.length :=
      hc23.trans (by simp only [arm64_norm, *])
    have sm_x24 : sm.readReg64 .x24 = BitVec.ofNat 64 x.dir.changed.length :=
      hc24.trans (by simp only [arm64_norm, *])
    set newCap := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
    unfold RustHeap.vecAt vecHeader
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (208))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv2
    have hnew_fit : x.dir.changed.length < newCap.toNat := by
      simp only [newCap, BitVec.toNat_ofNat, hcap_nat]
      omega
    refine SepWPp.weaken_pre ?_
      (step_write_miss (img := img) (A := A) (ext := ext) (stk := stk)
        (v3 := v3) (cap := newCap) (ptr := newPtr) (nameCap := nameCap) (namePtr := namePtr)
        (R := R)
        h96 hle_stk hmiss hlen_lt32 hnew_fit hna_le hna_lt hna_ptr
        (by rw [hentry]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        halign
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hput_csm.step (by simp only [arm64_norm]) hinv2)
        rfl)
    unfold RustHeap.vecAt vecHeader
    exact Entails.of_eq (by ac_rfl)
  · -- Spare capacity (`len < cap`)
    have hfit : x.dir.changed.length < cap.toNat := by
      have hne_nat : x.dir.changed.length ≠ cap.toNat := by
        intro heq
        apply hcap_eq
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact heq
      omega
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (208))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    refine SepWPp.weaken_pre ?_
      (step_write_miss (img := img) (A := A) (ext := ext) (stk := stk)
        (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr)
        (R := R)
        h96 hle_stk hmiss hlen_lt32 hfit hna_le hna_lt hna_ptr
        (by rw [hentry]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        halign
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) hinv1)
        rfl)
    rw [← hvec_back]
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.Put.Helpers
