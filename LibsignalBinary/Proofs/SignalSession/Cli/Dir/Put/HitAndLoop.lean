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
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.Miss
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# Hit exit (`+112 .. +192`) and search loop (`+68 .. +108`) of `Dir::put::<String>`
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

private structure Hide (P : Prop) : Prop where
  out : P

@[irreducible] def PutCalleeOk {α : Type} (img : Obj.Image) (ext : String → Option (State → State))
    (rel : Nat) (spec : Spec α) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName + BitVec.ofNat 64 rel)
    spec

theorem putCalleeOk_mk {α : Type} (img : Obj.Image) (ext : String → Option (State → State))
    (rel : Nat) {spec : Spec α}
    (h : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName + BitVec.ofNat 64 rel) spec) :
    PutCalleeOk img ext rel spec := by
  unfold PutCalleeOk
  exact h

theorem putCalleeOk_get {α : Type} {img : Obj.Image} {ext : String → Option (State → State)}
    {rel : Nat} {spec : Spec α}
    (h : PutCalleeOk img ext rel spec) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName + BitVec.ofNat 64 rel) spec := by
  unfold PutCalleeOk at h
  exact h

theorem pc_of_entry {fn entry pc : BitVec 64}
    (hentry : fn = entry) (k : BitVec 64) (hpc : pc = entry + k) : pc = fn + k :=
  hpc.trans (congrArg (· + k) hentry.symm)

/-- Shared hit-branch continuation (`+136 .. +152`): writes `{bytes}` over `[curPtr + 24 .. +48)`,
reassembles `dirAt A x.self (x.dir.put x.name x.bytes)`, and branches on `nameCap = 0` between
`step_epilogue_ret` (`+248`) and `step_epilogue_tail_dealloc` (`+156`). -/
theorem step_hit_store_and_exit {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    {s0 s : State} {x : DirPutGhost}
    {pre rest : List (List (BitVec 8) × List (BitVec 8))}
    {oldBs : List (BitVec 8)}
    {v3 cap ptr oldCap oldPtr nameCap namePtr : BitVec 64} {P R : SepProp}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName +
        BitVec.ofNat 64 (ls_rel% dirPutName deallocName))
      (withPutCS s0 (rustDeallocExternSpecWithStack A extHookStack)))
    (h96 : 0x60 ≤ stk)
    (hhook : extHookStack ≤ stk)
    (hle_stk : stk ≤ 2 ^ 64)
    (hx_eq : x.dir.changed = pre ++ (x.name, oldBs) :: rest)
    (hpre : ∀ e ∈ pre, e.1 ≠ x.name)
    (hlen_le : x.dir.changed.length ≤ cap.toNat)
    (hcap48_lt : cap.toNat * 48 < 2 ^ 63)
    (hptr_ne : ptr ≠ 0)
    (hna_le : x.name.length ≤ nameCap.toNat)
    (hna_lt : nameCap.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr dirPutName + 136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = namePtr)
    (hx20 : s.readReg64 .x20 = nameCap)
    (hx21 : s.readReg64 .x21 = x.bytesV)
    (hx22 : s.readReg64 .x22 = ptr + BitVec.ofNat 64 (pre.length * 48) + 24#64)
    (hcs : PutCalleeSaved s0 s)
    (hP : P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        vecU8 A (ptr + BitVec.ofNat 64 (pre.length * 48)) x.name ∗
        ((ptr + BitVec.ofNat 64 (pre.length * 48) + 24#64) ↦₆₄ oldCap) ∗
        ((ptr + BitVec.ofNat 64 (pre.length * 48) + 32#64) ↦₆₄ oldPtr) ∗
        ((ptr + BitVec.ofNat 64 (pre.length * 48) + 40#64) ↦₆₄ BitVec.ofNat 64 oldBs.length) ∗
        arrayAt (dirEntryAt A) 48 (ptr + BitVec.ofNat 64 (pre.length * 48) + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes ∗ A.pool) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s P
      (putRetQ A img stk x s0 R)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpec A img stk).onPanic x s0 sf ∗ R)) := by
  have hdealloc0 := putCalleeOk_mk img ext (ls_rel% dirPutName deallocName) hdealloc
  clear hdealloc
  code_fetches_range libsignalSessionCode dirPutBin img.base (Rust.withPanics ext)
    (ls_lemma% fnOff dirPutName) (ls_off% dirPutName) 136 20
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr dirPutName = entry
  examples_hide_fetches
  subst hP
  have hx_eq_h : Hide (x.dir.changed = pre ++ (x.name, oldBs) :: rest) := ⟨hx_eq⟩
  clear hx_eq
  set curPtr := ptr + BitVec.ofNat 64 (pre.length * 48)
  have hcap0 : cap ≠ 0 := by
    intro h0
    rw [h0] at hlen_le
    change x.dir.changed.length ≤ 0 at hlen_le
    rw [hx_eq_h.out, List.length_append, List.length_cons] at hlen_le
    omega
  have h32 : curPtr + 32#64 = (curPtr + 24#64) + 8#64 := by bv_arith
  have h40 : curPtr + 40#64 = (curPtr + 24#64) + 16#64 := by bv_arith
  rw [h32, h40,
      show vecU8 A x.bytesV x.bytes =
        (∃∗ bytesCap : BitVec 64, ∃∗ bytesPtr : BitVec 64,
          vecU8At A x.bytesV bytesCap bytesPtr x.bytes) from rfl]
  clear h32 h40
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun bytesCap => ?_
  refine SepWPp.exists_elim fun bytesPtr => ?_
  rw [vecU8At_eq_header_rest' A x.bytesV bytesCap bytesPtr x.bytes,
      show vecHeader x.bytesV bytesCap bytesPtr (BitVec.ofNat 64 x.bytes.length) =
        (x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) from rfl]
  refine SepWPp.weaken_pre
    (Entails.of_eq (show _ =
      ⌜x.bytes.length ≤ bytesCap.toNat ∧ bytesCap.toNat < 2 ^ 63 ∧ bytesPtr ≠ 0⌝ ∗
      (putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        vecU8 A curPtr x.name ∗
        ((curPtr + 24#64) ↦₆₄ oldCap) ∗ ((curPtr + 24#64 + 8#64) ↦₆₄ oldPtr) ∗
        ((curPtr + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 oldBs.length) ∗
        arrayAt (dirEntryAt A) 48 (curPtr + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        (x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Rest A bytesCap bytesPtr x.bytes ∗ A.pool) by ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨hbs_le, hbs_lt, hbs_ptr⟩ => ?_
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
  have hdir_pack :
      vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        vecU8 A curPtr x.name ∗
        (((curPtr + 24#64) ↦₆₄ bytesCap) ∗ ((curPtr + 24#64 + 8#64) ↦₆₄ bytesPtr) ∗
          ((curPtr + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Rest A bytesCap bytesPtr x.bytes) ∗
        arrayAt (dirEntryAt A) 48 (curPtr + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ⊢
      dirAt A x.self (x.dir.put x.name x.bytes) := by
    have hnew_entry :
        vecU8 A curPtr x.name ∗
          (((curPtr + 24#64) ↦₆₄ bytesCap) ∗ ((curPtr + 24#64 + 8#64) ↦₆₄ bytesPtr) ∗
            ((curPtr + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Rest A bytesCap bytesPtr x.bytes) ⊢
        dirEntryAt A (x.name, x.bytes) curPtr := by
      have hhdr2 :
          ((curPtr + 24#64) ↦₆₄ bytesCap) ∗ ((curPtr + 24#64 + 8#64) ↦₆₄ bytesPtr) ∗
            ((curPtr + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Rest A bytesCap bytesPtr x.bytes =
          vecHeader (curPtr + 0x18#64) bytesCap bytesPtr (BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Rest A bytesCap bytesPtr x.bytes := by
        unfold vecHeader; ac_rfl
      rw [hhdr2]
      exact sepConj_mono_right (vecU8_intro_header_rest hbs_le hbs_lt hbs_ptr)
    have hput_eq : (x.dir.put x.name x.bytes) =
        { changed := pre ++ (x.name, x.bytes) :: rest, path := x.dir.path } := by
      simp only [DirGhost.put, hx_eq_h.out, setOrPush_hit hpre]
    have hlen_same : (pre ++ (x.name, x.bytes) :: rest).length = x.dir.changed.length := by
      rw [hx_eq_h.out, List.length_append, List.length_append, List.length_cons, List.length_cons]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (Entails.trans (by rw [← sepConj_assoc]; exact Entails.refl _)
          (sepConj_mono_left hnew_entry))))) ?_
    have harr_join :
        arrayAt (dirEntryAt A) 48 ptr pre ∗
          (dirEntryAt A (x.name, x.bytes) curPtr ∗
            arrayAt (dirEntryAt A) 48 (curPtr + 48#64) rest) =
        arrayAt (dirEntryAt A) 48 ptr (pre ++ (x.name, x.bytes) :: rest) := by
      rw [arrayAt_append (dirEntryAt A) 48 ptr pre ((x.name, x.bytes) :: rest), arrayAt_cons]
    rw [hput_eq]
    refine Entails.trans ?_
      (dirAt_of_vecAt A x.self cap ptr (pre ++ (x.name, x.bytes) :: rest) x.dir.path)
    unfold RustHeap.vecAt
    rw [vecBuf_of_ne_zero A 48 8 (dirEntryAt A) cap ptr _ hcap0, hlen_same,
        pure_sepConj_of_true ⟨hlen_le, hcap48_lt, hptr_ne⟩, ← harr_join]
    exact Entails.of_eq (by ac_rfl)
  by_cases hncap0 : nameCap = 0
  · -- `nameCap = 0`: shared epilogue (`+248`)
    subst hncap0
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (248))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_s
    refine SepWPp.weaken_pre ?_
      (step_epilogue_ret (img := img) (A := A) (ext := ext) (stk := stk) (v3 := v3) (R := R)
        h96 hle_stk
        (pc_of_entry hentry 248#64 (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm, hsp])
        halign
        (by simp only [arm64_norm, htr])
        (hcs.step (by simp only [arm64_norm]) hinv_s)
        rfl)
    rw [show vecU8Rest A 0 namePtr x.name = emp from rfl]
    simp only [emp_sepConj]
    refine Entails.trans (Entails.of_eq (show _ =
      putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        (vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A) 48 ptr pre ∗
          vecU8 A curPtr x.name ∗
          (((curPtr + 24#64) ↦₆₄ bytesCap) ∗ ((curPtr + 24#64 + 8#64) ↦₆₄ bytesPtr) ∗
            ((curPtr + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Rest A bytesCap bytesPtr x.bytes) ∗
          arrayAt (dirEntryAt A) 48 (curPtr + 48#64) rest ∗
          memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
            ((cap.toNat - x.dir.changed.length) * 48) ∗
          strRefAt (x.self + 0x18#64) x.dir.path) ∗
        memRegion x.nameV 24 ∗
        ((x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length)) ∗ A.pool by ac_rfl))
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hdir_pack
          (sepConj_mono_right (sepConj_mono_left hbytesV_mem)))))
  · -- `nameCap ≠ 0`: tail-dealloc epilogue (`+156`)
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (156))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_s
    refine SepWPp.weaken_pre ?_
      (step_epilogue_tail_dealloc (img := img) (A := A) (ext := ext) (stk := stk)
        (v3 := v3) (nameCap := nameCap) (namePtr := namePtr) (R := R)
        (putCalleeOk_get hdealloc0) h96 hhook hle_stk hncap0 hna_le hna_lt
        (pc_of_entry hentry 156#64 (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm, hsp])
        halign
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx20])
        (hcs.step (by simp only [arm64_norm]) hinv_s)
        rfl)
    refine Entails.trans (Entails.of_eq (show _ =
      putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecU8Rest A nameCap namePtr x.name ∗
        (vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A) 48 ptr pre ∗
          vecU8 A curPtr x.name ∗
          (((curPtr + 24#64) ↦₆₄ bytesCap) ∗ ((curPtr + 24#64 + 8#64) ↦₆₄ bytesPtr) ∗
            ((curPtr + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Rest A bytesCap bytesPtr x.bytes) ∗
          arrayAt (dirEntryAt A) 48 (curPtr + 48#64) rest ∗
          memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
            ((cap.toNat - x.dir.changed.length) * 48) ∗
          strRefAt (x.self + 0x18#64) x.dir.path) ∗
        memRegion x.nameV 24 ∗
        ((x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length)) ∗ A.pool by ac_rfl))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hdir_pack
          (sepConj_mono_right (sepConj_mono_left hbytesV_mem))))))

/-- Full hit exit (`+112 .. +192`): drops `entry.bytes` if `oldCap ≠ 0` (`+112 .. +132`),
then calls `step_hit_store_and_exit` (`+136 .. +152`). -/
theorem step_hit_exit {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    {s0 s : State} {x : DirPutGhost}
    {pre rest : List (List (BitVec 8) × List (BitVec 8))}
    {oldBs : List (BitVec 8)}
    {v3 cap ptr nameCap namePtr : BitVec 64} {P R : SepProp}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName +
        BitVec.ofNat 64 (ls_rel% dirPutName deallocName))
      (withPutCS s0 (rustDeallocExternSpecWithStack A extHookStack)))
    (h96 : 0x60 ≤ stk)
    (hhook96 : extHookStack ≤ stk - 96)
    (hle_stk : stk ≤ 2 ^ 64)
    (hx_eq : x.dir.changed = pre ++ (x.name, oldBs) :: rest)
    (hpre : ∀ e ∈ pre, e.1 ≠ x.name)
    (hlen_le : x.dir.changed.length ≤ cap.toNat)
    (hcap48_lt : cap.toNat * 48 < 2 ^ 63)
    (hptr_ne : ptr ≠ 0)
    (hna_le : x.name.length ≤ nameCap.toNat)
    (hna_lt : nameCap.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr dirPutName + 112#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = namePtr)
    (hx20 : s.readReg64 .x20 = nameCap)
    (hx21 : s.readReg64 .x21 = x.bytesV)
    (hx26 : s.readReg64 .x26 = ptr + BitVec.ofNat 64 (pre.length * 48) + 32#64)
    (hcs : PutCalleeSaved s0 s)
    (hP : P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        dirEntryAt A (x.name, oldBs) (ptr + BitVec.ofNat 64 (pre.length * 48)) ∗
        arrayAt (dirEntryAt A) 48 (ptr + BitVec.ofNat 64 (pre.length * 48) + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes ∗ A.pool) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s P
      (putRetQ A img stk x s0 R)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpec A img stk).onPanic x s0 sf ∗ R)) := by
  have hdealloc0 := putCalleeOk_mk img ext (ls_rel% dirPutName deallocName) hdealloc
  code_fetches_range libsignalSessionCode dirPutBin img.base (Rust.withPanics ext)
    (ls_lemma% fnOff dirPutName) (ls_off% dirPutName) 112 24
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr dirPutName = entry
  examples_hide_fetches
  subst hP
  have hx_eq_h : Hide (x.dir.changed = pre ++ (x.name, oldBs) :: rest) := ⟨hx_eq⟩
  clear hx_eq
  set curPtr := ptr + BitVec.ofNat 64 (pre.length * 48)
  rw [show dirEntryAt A (x.name, oldBs) curPtr =
        vecU8 A curPtr x.name ∗
          (∃∗ oldCap : BitVec 64, ∃∗ oldPtr : BitVec 64,
            vecU8At A (curPtr + 0x18#64) oldCap oldPtr oldBs) from rfl]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun oldCap => ?_
  refine SepWPp.exists_elim fun oldPtr => ?_
  rw [vecU8At_eq_header_rest' A (curPtr + 0x18#64) oldCap oldPtr oldBs,
      show vecHeader (curPtr + 0x18#64) oldCap oldPtr (BitVec.ofNat 64 oldBs.length) =
        ((curPtr + 24#64) ↦₆₄ oldCap) ∗ (((curPtr + 0x18#64) + 8#64) ↦₆₄ oldPtr) ∗
          (((curPtr + 0x18#64) + 16#64) ↦₆₄ BitVec.ofNat 64 oldBs.length) from rfl]
  have hcur24 : curPtr + 32#64 - 8#64 = curPtr + 24#64 := by bv_arith
  have hcur32 : (curPtr + 0x18#64) + 8#64 = curPtr + 32#64 := by bv_arith
  have hcur40 : (curPtr + 0x18#64) + 16#64 = curPtr + 40#64 := by bv_arith
  rw [hcur32, hcur40]
  clear hcur32 hcur40
  refine SepWPp.weaken_pre
    (Entails.of_eq (show _ =
      ⌜oldBs.length ≤ oldCap.toNat ∧ oldCap.toNat < 2 ^ 63 ∧ oldPtr ≠ 0⌝ ∗
      (putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        vecU8 A curPtr x.name ∗
        ((curPtr + 24#64) ↦₆₄ oldCap) ∗
        ((curPtr + 32#64) ↦₆₄ oldPtr) ∗
        ((curPtr + 40#64) ↦₆₄ BitVec.ofNat 64 oldBs.length) ∗
        vecU8Rest A oldCap oldPtr oldBs ∗
        arrayAt (dirEntryAt A) 48 (curPtr + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes ∗ A.pool) by ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨hold_le, hold_lt, _⟩ => ?_
  by_cases hold0 : oldCap = 0
  · -- `oldCap = 0`
    subst hold0
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (136))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    rw [show vecU8Rest A 0 oldPtr oldBs = emp from rfl]
    simp only [emp_sepConj]
    refine SepWPp.weaken_pre ?_
      (step_hit_store_and_exit (img := img) (A := A) (ext := ext) (stk := stk)
        (pre := pre) (rest := rest) (oldBs := oldBs)
        (v3 := v3) (cap := cap) (ptr := ptr)
        (oldCap := 0) (oldPtr := oldPtr) (nameCap := nameCap) (namePtr := namePtr) (R := R)
        (putCalleeOk_get hdealloc0) h96 (by omega) hle_stk
        hx_eq_h.out hpre hlen_le hcap48_lt hptr_ne hna_le hna_lt
        (pc_of_entry hentry 136#64 (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm, hsp])
        halign
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx20])
        (by simp only [arm64_norm, hx21])
        (by simp only [arm64_norm]; rfl)
        (hcs.step (by simp only [arm64_norm]) hinv1)
        rfl)
    exact Entails.refl _
  · -- `oldCap ≠ 0`: deallocate `oldBs`
    apply SepWPp.of_sepWP_cs
      (mid := entry + BitVec.ofNat 64 (ls_rel% dirPutName deallocName))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    let retDealloc := entry + bv% (136)
    refine step_dealloc_call (img := img) (A := A) (ext := ext) (stk := stk)
      (x0 := x) (R := R)
      (F := putSavedCells s0 v3 ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        vecU8 A curPtr x.name ∗
        ((curPtr + 24#64) ↦₆₄ oldCap) ∗
        ((curPtr + 32#64) ↦₆₄ oldPtr) ∗
        ((curPtr + 40#64) ↦₆₄ BitVec.ofNat 64 oldBs.length) ∗
        arrayAt (dirEntryAt A) 48 (curPtr + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes)
      hdealloc hhook96 hle_stk oldCap oldPtr retDealloc oldBs
      hold0 hold_le hold_lt
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm, hsp])
      halign
      (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, *]; rfl)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) hinv1)
      (by ac_rfl)
      fun sm hpcm hrunm hspm htrm hcsm hput_csm => ?_
    dsimp only [retDealloc] at hpcm
    clear retDealloc
    have sm_x19 : sm.readReg64 .x19 = namePtr := hcsm.1.trans (by simp only [arm64_norm, hx19])
    have sm_x20 : sm.readReg64 .x20 = nameCap := hcsm.2.1.trans (by simp only [arm64_norm, hx20])
    have sm_x21 : sm.readReg64 .x21 = x.bytesV := hcsm.2.2.1.trans (by simp only [arm64_norm, hx21])
    have sm_x22 : sm.readReg64 .x22 = ptr + BitVec.ofNat 64 (pre.length * 48) + 24#64 :=
      hcsm.2.2.2.1.trans (by simp only [arm64_norm]; rfl)
    clear hcsm hinv1
    refine SepWPp.weaken_pre ?_
      (step_hit_store_and_exit (img := img) (A := A) (ext := ext) (stk := stk)
        (pre := pre) (rest := rest) (oldBs := oldBs)
        (v3 := v3) (cap := cap) (ptr := ptr)
        (oldCap := oldCap) (oldPtr := oldPtr) (nameCap := nameCap) (namePtr := namePtr) (R := R)
        (putCalleeOk_get hdealloc0) h96 (by omega) hle_stk
        hx_eq_h.out hpre hlen_le hcap48_lt hptr_ne hna_le hna_lt
        (pc_of_entry hentry 136#64 hpcm)
        hrunm hspm halign htrm
        sm_x19 sm_x20 sm_x21 sm_x22
        hput_csm
        rfl)
    exact Entails.of_eq (by dsimp only [curPtr]; ac_rfl)

/-- Loop latch (`+68 .. +76`): advances `X27 -= 48, X26 += 48`, exiting to `step_miss` (`+196`)
when `rest = []` or invoking `hcont` at `+80` when `rest = hd' :: rest'`. -/
theorem step_latch {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {growStk stk : Nat}
    {s0 s : State} {x : DirPutGhost}
    {pre : List (List (BitVec 8) × List (BitVec 8))}
    {hd : List (BitVec 8) × List (BitVec 8)}
    {rest : List (List (BitVec 8) × List (BitVec 8))}
    {v3 cap ptr nameCap namePtr : BitVec 64} {P R : SepProp}
    (hgrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName +
        BitVec.ofNat 64 (ls_rel% dirPutName growOneDirName))
      (withPutCS s0 (growOneDirRawSpec A growStk)))
    (h96 : 0x60 ≤ stk)
    (hgrow_stk : growStk ≤ stk - 96)
    (hle_stk : stk ≤ 2 ^ 64)
    (hx_eq : x.dir.changed = pre ++ hd :: rest)
    (hpre : ∀ e ∈ pre, e.1 ≠ x.name)
    (hhd_ne : hd.1 ≠ x.name)
    (hlen_lt32 : x.dir.changed.length < 2 ^ 32)
    (hlen_le : x.dir.changed.length ≤ cap.toNat)
    (hcap48_lt : cap.toNat * 48 < 2 ^ 63)
    (hptr_ne : ptr ≠ 0)
    (hna_le : x.name.length ≤ nameCap.toNat)
    (hna_lt : nameCap.toNat < 2 ^ 63)
    (hna_ptr : namePtr ≠ 0)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr dirPutName + 68#64)
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
    (hx26 : s.readReg64 .x26 = ptr + BitVec.ofNat 64 (pre.length * 48) + 32#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 (48 * (hd :: rest).length))
    (hcs : PutCalleeSaved s0 s)
    (hP : P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        dirEntryAt A hd (ptr + BitVec.ofNat 64 (pre.length * 48)) ∗
        arrayAt (dirEntryAt A) 48 (ptr + BitVec.ofNat 64 (pre.length * 48) + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes ∗ A.pool)
    (hcont : ∀ (hd' : List (BitVec 8) × List (BitVec 8))
        (rest' : List (List (BitVec 8) × List (BitVec 8))) (sn : State),
      rest = hd' :: rest' →
      sn.pc = (tripleRatchetProgAtExt img.base ext).fnAddr dirPutName + 80#64 →
      sn.status = .Running →
      sn.sp = s0.sp - 96#64 →
      sn.trace = s0.trace →
      sn.readReg64 .x19 = namePtr →
      sn.readReg64 .x20 = nameCap →
      sn.readReg64 .x21 = x.bytesV →
      sn.readReg64 .x22 = x.self →
      sn.readReg64 .x23 = BitVec.ofNat 64 x.name.length →
      sn.readReg64 .x24 = BitVec.ofNat 64 x.dir.changed.length →
      sn.readReg64 .x25 = ptr →
      sn.readReg64 .x26 = ptr + BitVec.ofNat 64 ((pre ++ [hd]).length * 48) + 32#64 →
      sn.readReg64 .x27 = BitVec.ofNat 64 (48 * (hd' :: rest').length) →
      PutCalleeSaved s0 sn →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) sn
        (putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
          vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A) 48 ptr (pre ++ [hd]) ∗
          dirEntryAt A hd' (ptr + BitVec.ofNat 64 ((pre ++ [hd]).length * 48)) ∗
          arrayAt (dirEntryAt A) 48
            (ptr + BitVec.ofNat 64 ((pre ++ [hd]).length * 48) + 48#64) rest' ∗
          memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
            ((cap.toNat - x.dir.changed.length) * 48) ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          vecU8Rest A nameCap namePtr x.name ∗
          memRegion x.nameV 24 ∗
          vecU8 A x.bytesV x.bytes ∗ A.pool)
        (putRetQ A img stk x s0 R)
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpec A img stk).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s P
      (putRetQ A img stk x s0 R)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpec A img stk).onPanic x s0 sf ∗ R)) := by
  have hgrow0 := putCalleeOk_mk img ext (ls_rel% dirPutName growOneDirName) hgrow
  clear hgrow
  code_fetches_range libsignalSessionCode dirPutBin img.base (Rust.withPanics ext)
    (ls_lemma% fnOff dirPutName) (ls_off% dirPutName) 68 12
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr dirPutName = entry
  examples_hide_fetches
  subst hP
  have hpre' : ∀ e ∈ pre ++ [hd], e.1 ≠ x.name := by
    intro e he
    rcases List.mem_append.mp he with h1 | h2
    · exact hpre e h1
    · rcases List.mem_singleton.mp h2 with rfl
      exact hhd_ne
  have hcap0 : cap ≠ 0 := by
    intro h0
    rw [h0] at hlen_le
    change x.dir.changed.length ≤ 0 at hlen_le
    rw [hx_eq, List.length_append, List.length_cons] at hlen_le
    omega
  cases rest with
  | nil =>
    have hx_eq_h : Hide (x.dir.changed = pre ++ [hd]) := ⟨hx_eq⟩
    clear hx_eq
    have _ : Hide _ := ⟨hcont⟩
    clear hcont
    have hx27_48 : s.readReg64 .x27 = 48#64 := hx27
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (196))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_l
    have hvec_join :
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A) 48 ptr pre ∗
          dirEntryAt A hd (ptr + BitVec.ofNat 64 (pre.length * 48)) ∗
          arrayAt (dirEntryAt A) 48 (ptr + BitVec.ofNat 64 (pre.length * 48) + 48#64) [] ∗
          memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
            ((cap.toNat - x.dir.changed.length) * 48) =
        RustHeap.vecAt A 48 8 (dirEntryAt A) x.self cap ptr x.dir.changed := by
      have harr_cat :
          arrayAt (dirEntryAt A) 48 ptr pre ∗
            dirEntryAt A hd (ptr + BitVec.ofNat 64 (pre.length * 48)) =
          arrayAt (dirEntryAt A) 48 ptr x.dir.changed := by
        rw [hx_eq_h.out, show hd :: ([] : List _) = [hd] from rfl,
            arrayAt_concat (dirEntryAt A) 48 ptr pre hd]
      unfold RustHeap.vecAt
      rw [vecBuf_of_ne_zero A 48 8 (dirEntryAt A) cap ptr x.dir.changed hcap0,
          pure_sepConj_of_true ⟨hlen_le, hcap48_lt, hptr_ne⟩,
          arrayAt_nil, emp_sepConj, ← harr_cat]
      ac_rfl
    refine SepWPp.weaken_pre ?_
      (step_miss (img := img) (A := A) (ext := ext) (growStk := growStk) (stk := stk)
        (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr) (R := R)
        (putCalleeOk_get hgrow0) h96 hgrow_stk hle_stk
        (by rwa [hx_eq_h.out])
        hlen_lt32 hna_le hna_lt hna_ptr
        (pc_of_entry hentry 196#64 (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm, hsp])
        halign
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx20])
        (by simp only [arm64_norm, hx21])
        (by simp only [arm64_norm, hx22])
        (by simp only [arm64_norm, hx23])
        (by simp only [arm64_norm, hx24])
        (by simp only [arm64_norm, hx25])
        (hcs.step (by simp only [arm64_norm]) hinv_l)
        rfl)
    refine Entails.of_eq ?_
    rw [← hvec_join]
    ac_rfl
  | cons hd' rest' =>
    have hx_eq_h : Hide (x.dir.changed = pre ++ hd :: hd' :: rest') := ⟨hx_eq⟩
    clear hx_eq
    have hcont_h : Hide _ := ⟨hcont⟩
    clear hcont
    have hrem_bound : 48 * (hd :: hd' :: rest').length < 2 ^ 64 := by
      rw [hx_eq_h.out, List.length_append] at hlen_lt32
      simp only [List.length_cons] at hlen_lt32 ⊢
      omega
    have hx27' : s.readReg64 .x27 = BitVec.ofNat 64 (48 * (hd' :: rest').length) + 48#64 := by
      rw [hx27, List.length_cons (a := hd), Nat.mul_succ, BitVec.ofNat_add]
    clear hx27
    have hx27_ne0 : BitVec.ofNat 64 (48 * (hd' :: rest').length) ≠ 0#64 := by
      intro h0
      have h := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by simp only [List.length_cons] at hrem_bound ⊢; omega),
          BitVec.toNat_zero] at h
      simp only [List.length_cons] at h
      omega
    generalize hrem_eq : BitVec.ofNat 64 (48 * (hd' :: rest').length) = rem at hx27' hx27_ne0
    have hrem_h : Hide _ := ⟨hrem_eq⟩
    clear hrem_eq hrem_bound
    have hcur_next :
        ptr + BitVec.ofNat 64 (pre.length * 48) + 48#64 =
          ptr + BitVec.ofNat 64 ((pre ++ [hd]).length * 48) := by
      have hl : (pre ++ [hd]).length = pre.length + 1 := by simp
      rw [hl, BitVec.add_assoc,
          show (48#64 : BitVec 64) = BitVec.ofNat 64 48 from rfl,
          ← BitVec.ofNat_add, Nat.succ_mul]
    have hcur_next_h : Hide _ := ⟨hcur_next⟩
    clear hcur_next
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (80))
    wp_steps
    apply SepWP.done
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    intro hinv_l
    refine SepWPp.weaken_pre ?_
      (hcont_h.out hd' rest' _ rfl
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm, hsp])
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx20])
        (by simp only [arm64_norm, hx21])
        (by simp only [arm64_norm, hx22])
        (by simp only [arm64_norm, hx23])
        (by simp only [arm64_norm, hx24])
        (by simp only [arm64_norm, hx25])
        (by simp only [arm64_norm]; rw [← hcur_next_h.out]; bv_arith)
        (by simp only [arm64_norm, ← hrem_h.out])
        (hcs.step (by simp only [arm64_norm]) hinv_l))
    rw [hcur_next_h.out, arrayAt_cons, arrayAt_concat (dirEntryAt A) 48 ptr pre hd]
    exact Entails.of_eq (by ac_rfl)

/-- Single iteration of the search loop body (`+80 .. +108`) at entry `(eName, oldBs)` followed by
`rest`: compares lengths (`+80 .. +88`), optionally calls `bcmp` (`+92 .. +108`), exits via
`step_hit_exit` on a match (`eName = x.name`), or advances via `step_latch` on a mismatch (`eName ≠ x.name`). -/
theorem step_loop_body {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {growStk stk : Nat}
    {s0 s : State} {x : DirPutGhost}
    {pre rest : List (List (BitVec 8) × List (BitVec 8))}
    {eName oldBs : List (BitVec 8)}
    {v3 cap ptr nameCap namePtr : BitVec 64} {P R : SepProp}
    (hbcmp : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName +
        BitVec.ofNat 64 (ls_rel% dirPutName cliBcmpName))
      (withPutCS s0 cliBcmpSpec))
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName +
        BitVec.ofNat 64 (ls_rel% dirPutName deallocName))
      (withPutCS s0 (rustDeallocExternSpecWithStack A extHookStack)))
    (hgrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName +
        BitVec.ofNat 64 (ls_rel% dirPutName growOneDirName))
      (withPutCS s0 (growOneDirRawSpec A growStk)))
    (h96 : 0x60 ≤ stk)
    (hhook96 : extHookStack ≤ stk - 96)
    (hgrow_stk : growStk ≤ stk - 96)
    (hle_stk : stk ≤ 2 ^ 64)
    (hx_eq : x.dir.changed = pre ++ (eName, oldBs) :: rest)
    (hpre : ∀ e ∈ pre, e.1 ≠ x.name)
    (hlen_lt32 : x.dir.changed.length < 2 ^ 32)
    (hlen_le : x.dir.changed.length ≤ cap.toNat)
    (hcap48_lt : cap.toNat * 48 < 2 ^ 63)
    (hptr_ne : ptr ≠ 0)
    (hna_le : x.name.length ≤ nameCap.toNat)
    (hna_lt : nameCap.toNat < 2 ^ 63)
    (hna_ptr : namePtr ≠ 0)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr dirPutName + 80#64)
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
    (hx26 : s.readReg64 .x26 = ptr + BitVec.ofNat 64 (pre.length * 48) + 32#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 (48 * ((eName, oldBs) :: rest).length))
    (hcs : PutCalleeSaved s0 s)
    (hP : P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        dirEntryAt A (eName, oldBs) (ptr + BitVec.ofNat 64 (pre.length * 48)) ∗
        arrayAt (dirEntryAt A) 48 (ptr + BitVec.ofNat 64 (pre.length * 48) + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes ∗ A.pool)
    (hcont : eName ≠ x.name →
      ∀ (hd' : List (BitVec 8) × List (BitVec 8))
        (rest' : List (List (BitVec 8) × List (BitVec 8))) (sn : State),
      rest = hd' :: rest' →
      sn.pc = (tripleRatchetProgAtExt img.base ext).fnAddr dirPutName + 80#64 →
      sn.status = .Running →
      sn.sp = s0.sp - 96#64 →
      sn.trace = s0.trace →
      sn.readReg64 .x19 = namePtr →
      sn.readReg64 .x20 = nameCap →
      sn.readReg64 .x21 = x.bytesV →
      sn.readReg64 .x22 = x.self →
      sn.readReg64 .x23 = BitVec.ofNat 64 x.name.length →
      sn.readReg64 .x24 = BitVec.ofNat 64 x.dir.changed.length →
      sn.readReg64 .x25 = ptr →
      sn.readReg64 .x26 = ptr + BitVec.ofNat 64 ((pre ++ [(eName, oldBs)]).length * 48) + 32#64 →
      sn.readReg64 .x27 = BitVec.ofNat 64 (48 * (hd' :: rest').length) →
      PutCalleeSaved s0 sn →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) sn
        (putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
          vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A) 48 ptr (pre ++ [(eName, oldBs)]) ∗
          dirEntryAt A hd' (ptr + BitVec.ofNat 64 ((pre ++ [(eName, oldBs)]).length * 48)) ∗
          arrayAt (dirEntryAt A) 48
            (ptr + BitVec.ofNat 64 ((pre ++ [(eName, oldBs)]).length * 48) + 48#64) rest' ∗
          memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
            ((cap.toNat - x.dir.changed.length) * 48) ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          vecU8Rest A nameCap namePtr x.name ∗
          memRegion x.nameV 24 ∗
          vecU8 A x.bytesV x.bytes ∗ A.pool)
        (putRetQ A img stk x s0 R)
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpec A img stk).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s P
      (putRetQ A img stk x s0 R)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpec A img stk).onPanic x s0 sf ∗ R)) := by
  have hdealloc0 := putCalleeOk_mk img ext (ls_rel% dirPutName deallocName) hdealloc
  have hgrow0 := putCalleeOk_mk img ext (ls_rel% dirPutName growOneDirName) hgrow
  have hcont_h : Hide _ := ⟨hcont⟩
  clear hdealloc hgrow hcont
  code_fetches_range libsignalSessionCode dirPutBin img.base (Rust.withPanics ext)
    (ls_lemma% fnOff dirPutName) (ls_off% dirPutName) 80 32
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr dirPutName = entry
  examples_hide_fetches
  subst hP
  have hx_eq_h : Hide (x.dir.changed = pre ++ (eName, oldBs) :: rest) := ⟨hx_eq⟩
  clear hx_eq
  set curPtr := ptr + BitVec.ofNat 64 (pre.length * 48)
  rw [show dirEntryAt A (eName, oldBs) curPtr =
        (∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64, vecU8At A curPtr eCap ePtr eName) ∗
          vecU8 A (curPtr + 0x18#64) oldBs from rfl]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun eCap => ?_
  refine SepWPp.exists_elim fun ePtr => ?_
  rw [vecU8At_eq_header_rest' A curPtr eCap ePtr eName,
      show vecHeader curPtr eCap ePtr (BitVec.ofNat 64 eName.length) =
        (curPtr ↦₆₄ eCap) ∗ ((curPtr + 8#64) ↦₆₄ ePtr) ∗
          ((curPtr + 16#64) ↦₆₄ BitVec.ofNat 64 eName.length) from rfl]
  refine SepWPp.weaken_pre
    (Entails.of_eq (show _ =
      ⌜eName.length ≤ eCap.toNat ∧ eCap.toNat < 2 ^ 63 ∧ ePtr ≠ 0⌝ ∗
      (putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        (curPtr ↦₆₄ eCap) ∗ ((curPtr + 8#64) ↦₆₄ ePtr) ∗
        ((curPtr + 16#64) ↦₆₄ BitVec.ofNat 64 eName.length) ∗
        vecU8Rest A eCap ePtr eName ∗
        vecU8 A (curPtr + 0x18#64) oldBs ∗
        arrayAt (dirEntryAt A) 48 (curPtr + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes ∗ A.pool) by ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨he_le, he_lt, he_ptr⟩ => ?_
  have he_repack :
      ((curPtr ↦₆₄ eCap) ∗ ((curPtr + 8#64) ↦₆₄ ePtr) ∗
        ((curPtr + 16#64) ↦₆₄ BitVec.ofNat 64 eName.length) ∗
        vecU8Rest A eCap ePtr eName) ∗
        vecU8 A (curPtr + 0x18#64) oldBs ⊢
      dirEntryAt A (eName, oldBs) curPtr := by
    refine sepConj_mono_left ?_
    have hhdr :
        (curPtr ↦₆₄ eCap) ∗ ((curPtr + 8#64) ↦₆₄ ePtr) ∗
          ((curPtr + 16#64) ↦₆₄ BitVec.ofNat 64 eName.length) ∗
          vecU8Rest A eCap ePtr eName =
        vecHeader curPtr eCap ePtr (BitVec.ofNat 64 eName.length) ∗
          vecU8Rest A eCap ePtr eName := by
      unfold vecHeader; ac_rfl
    rw [hhdr]
    exact vecU8_intro_header_rest he_le he_lt he_ptr
  have hcur16 : curPtr + 32#64 - 16#64 = curPtr + 16#64 := by bv_arith
  have hcur8 : curPtr + 32#64 - 24#64 = curPtr + 8#64 := by bv_arith
  by_cases hlen_eq : BitVec.ofNat 64 eName.length = BitVec.ofNat 64 x.name.length
  · have hlen_nat : eName.length = x.name.length := by
      have h := congrArg BitVec.toNat hlen_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h
      exact h
    apply SepWPp.of_sepWP_cs
      (mid := entry + BitVec.ofNat 64 (ls_rel% dirPutName cliBcmpName))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    intro hinv1
    rw [vecU8Rest_expose_bytes (A := A) (cap := eCap) (ptr := ePtr) he_le,
        vecU8Rest_expose_bytes (A := A) (cap := nameCap) (ptr := namePtr) hna_le]
    have hx2_nat : (BitVec.ofNat 64 x.name.length).toNat = eName.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hlen_nat]
    let retBcmp := entry + bv% (108)
    refine step_bcmp_call (img := img) (A := A) (ext := ext) (stk := stk)
      (x0 := x) (R := R)
      (F := putSavedCells s0 v3 ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        (curPtr ↦₆₄ eCap) ∗ ((curPtr + 8#64) ↦₆₄ ePtr) ∗
        ((curPtr + 16#64) ↦₆₄ BitVec.ofNat 64 eName.length) ∗
        (if eCap = 0 then emp
         else A.live ePtr eCap.toNat 1 ∗
           memRegion (ePtr + BitVec.ofNat 64 eName.length) (eCap.toNat - eName.length)) ∗
        vecU8 A (curPtr + 0x18#64) oldBs ∗
        arrayAt (dirEntryAt A) 48 (curPtr + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        (if nameCap = 0 then emp
         else A.live namePtr nameCap.toNat 1 ∗
           memRegion (namePtr + BitVec.ofNat 64 x.name.length) (nameCap.toNat - x.name.length)) ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes ∗ A.pool)
      hbcmp hhook96 hle_stk ePtr namePtr retBcmp eName x.name
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm, hsp])
      halign
      (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, *]; rfl)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hx2_nat])
      hlen_nat.symm
      (hcs.step (by simp only [arm64_norm]) hinv1)
      (by ac_rfl)
      fun sm hpcm hrunm hspm htrm heq_iff hcsm hput_csm => ?_
    dsimp only [retBcmp] at hpcm
    clear retBcmp
    have sm_x19 : sm.readReg64 .x19 = namePtr := hcsm.1.trans (by simp only [arm64_norm, hx19])
    have sm_x20 : sm.readReg64 .x20 = nameCap := hcsm.2.1.trans (by simp only [arm64_norm, hx20])
    have sm_x21 : sm.readReg64 .x21 = x.bytesV := hcsm.2.2.1.trans (by simp only [arm64_norm, hx21])
    have sm_x22 : sm.readReg64 .x22 = x.self := hcsm.2.2.2.1.trans (by simp only [arm64_norm, hx22])
    have sm_x23 : sm.readReg64 .x23 = BitVec.ofNat 64 x.name.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, hx23])
    have sm_x24 : sm.readReg64 .x24 = BitVec.ofNat 64 x.dir.changed.length :=
      hcsm.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx24])
    have sm_x25 : sm.readReg64 .x25 = ptr := hcsm.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx25])
    have sm_x26 : sm.readReg64 .x26 = ptr + BitVec.ofNat 64 (pre.length * 48) + 32#64 :=
      hcsm.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx26]; rfl)
    have sm_x27 : sm.readReg64 .x27 = BitVec.ofNat 64 (48 * ((eName, oldBs) :: rest).length) :=
      hcsm.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx27])
    clear hcsm hinv1
    refine SepWPp.weaken_pre
      (show _ ⊢
        putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
          vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A) 48 ptr pre ∗
          dirEntryAt A (eName, oldBs) curPtr ∗
          arrayAt (dirEntryAt A) 48 (curPtr + 48#64) rest ∗
          memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
            ((cap.toNat - x.dir.changed.length) * 48) ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          vecU8Rest A nameCap namePtr x.name ∗
          memRegion x.nameV 24 ∗
          vecU8 A x.bytesV x.bytes ∗ A.pool by
        refine Entails.trans (Entails.of_eq (show _ =
          putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
            vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
            A.live ptr (cap.toNat * 48) 8 ∗
            arrayAt (dirEntryAt A) 48 ptr pre ∗
            (((curPtr ↦₆₄ eCap) ∗ ((curPtr + 8#64) ↦₆₄ ePtr) ∗
              ((curPtr + 16#64) ↦₆₄ BitVec.ofNat 64 eName.length) ∗
              vecU8Rest A eCap ePtr eName) ∗
              vecU8 A (curPtr + 0x18#64) oldBs) ∗
            arrayAt (dirEntryAt A) 48 (curPtr + 48#64) rest ∗
            memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
              ((cap.toNat - x.dir.changed.length) * 48) ∗
            strRefAt (x.self + 0x18#64) x.dir.path ∗
            vecU8Rest A nameCap namePtr x.name ∗
            memRegion x.nameV 24 ∗
            vecU8 A x.bytesV x.bytes ∗ A.pool by
            rw [vecU8Rest_expose_bytes (A := A) (cap := eCap) (ptr := ePtr) he_le,
                vecU8Rest_expose_bytes (A := A) (cap := nameCap) (ptr := namePtr) hna_le]
            ac_rfl))
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left he_repack))))))) ?_
    by_cases hw0 : (sm.readReg64 .x0).setWidth 32 = 0#32
    · -- Match (`eName = x.name`): jump to `step_hit_exit` (`+112`)
      have heq_name : eName = x.name := heq_iff.mp hw0
      subst heq_name
      apply SepWPp.of_sepWP_cs (mid := entry + bv% (112))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv2
      refine SepWPp.weaken_pre ?_
        (step_hit_exit (img := img) (A := A) (ext := ext) (stk := stk)
          (pre := pre) (rest := rest) (oldBs := oldBs)
          (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr) (R := R)
          (putCalleeOk_get hdealloc0) h96 hhook96 hle_stk
          hx_eq_h.out hpre hlen_le hcap48_lt hptr_ne hna_le hna_lt
          (pc_of_entry hentry 112#64 (by simp only [arm64_norm, *]))
          (by simp only [arm64_norm, hrunm])
          (by simp only [arm64_norm, hspm])
          halign
          (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm, sm_x19])
          (by simp only [arm64_norm, sm_x20])
          (by simp only [arm64_norm, sm_x21])
          (by simp only [arm64_norm, sm_x26])
          (hput_csm.step (by simp only [arm64_norm]) hinv2)
          rfl)
      exact Entails.refl _
    · -- Mismatch (`eName ≠ x.name`): jump to `step_latch` (`+68`)
      have hne_name : eName ≠ x.name := mt heq_iff.mpr hw0
      have hw0_64 :
          (BitVec.zeroExtend 64 (BitVec.truncate 32 (sm.readReg64 (Reg.gpr 0#5))) == 0#64) = false := by
        rw [beq_eq_false_iff_ne]
        intro h0
        exact hw0 (by simpa using congrArg (BitVec.truncate 32) h0)
      apply SepWPp.of_sepWP_cs (mid := entry + bv% (68))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv2
      refine SepWPp.weaken_pre ?_
        (step_latch (img := img) (A := A) (ext := ext) (growStk := growStk) (stk := stk)
          (pre := pre) (hd := (eName, oldBs)) (rest := rest)
          (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr) (R := R)
          (putCalleeOk_get hgrow0) h96 hgrow_stk hle_stk
          hx_eq_h.out hpre hne_name hlen_lt32 hlen_le hcap48_lt hptr_ne
          hna_le hna_lt hna_ptr
          (pc_of_entry hentry 68#64 (by simp only [arm64_norm, *]))
          (by simp only [arm64_norm, hrunm])
          (by simp only [arm64_norm, hspm])
          halign
          (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm, sm_x19])
          (by simp only [arm64_norm, sm_x20])
          (by simp only [arm64_norm, sm_x21])
          (by simp only [arm64_norm, sm_x22])
          (by simp only [arm64_norm, sm_x23])
          (by simp only [arm64_norm, sm_x24])
          (by simp only [arm64_norm, sm_x25])
          (by simp only [arm64_norm, sm_x26])
          (by simp only [arm64_norm, sm_x27])
          (hput_csm.step (by simp only [arm64_norm]) hinv2)
          rfl
          (fun hd' rest' sn hrest hpcsn h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
            hcont_h.out hne_name hd' rest' sn hrest
              (hpcsn.trans (congrArg (· + 80#64) hentry))
              h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12))
      exact Entails.refl _
  · -- Distinct lengths: jump to `step_latch` (`+68`)
    have hne_name : eName ≠ x.name := fun h => hlen_eq (h ▸ rfl)
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (68))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    intro hinv1
    refine SepWPp.weaken_pre ?_
      (step_latch (img := img) (A := A) (ext := ext) (growStk := growStk) (stk := stk)
        (pre := pre) (hd := (eName, oldBs)) (rest := rest)
        (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr) (R := R)
        (putCalleeOk_get hgrow0) h96 hgrow_stk hle_stk
        hx_eq_h.out hpre hne_name hlen_lt32 hlen_le hcap48_lt hptr_ne
        hna_le hna_lt hna_ptr
        (pc_of_entry hentry 68#64 (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm, hsp])
        halign
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx20])
        (by simp only [arm64_norm, hx21])
        (by simp only [arm64_norm, hx22])
        (by simp only [arm64_norm, hx23])
        (by simp only [arm64_norm, hx24])
        (by simp only [arm64_norm, hx25])
        (by simp only [arm64_norm, hx26]; rfl)
        (by simp only [arm64_norm, hx27])
        (hcs.step (by simp only [arm64_norm]) hinv1)
        rfl
        (fun hd' rest' sn hrest hpcsn h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
          hcont_h.out hne_name hd' rest' sn hrest
            (hpcsn.trans (congrArg (· + 80#64) hentry))
            h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12))
    refine Entails.trans (Entails.of_eq (show _ =
      putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        (((curPtr ↦₆₄ eCap) ∗ ((curPtr + 8#64) ↦₆₄ ePtr) ∗
          ((curPtr + 16#64) ↦₆₄ BitVec.ofNat 64 eName.length) ∗
          vecU8Rest A eCap ePtr eName) ∗
          vecU8 A (curPtr + 0x18#64) oldBs) ∗
        arrayAt (dirEntryAt A) 48 (curPtr + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes ∗ A.pool by ac_rfl))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left he_repack))))))

/-- Search loop (`+80 .. +108` + `+68 .. +76`) over `hd :: rest`: finds the first entry whose
name equals `x.name` (`step_hit_exit`) or falls through the end into `step_miss`. -/
theorem step_loop {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {growStk stk : Nat}
    {s0 : State} {x : DirPutGhost}
    {v3 cap ptr nameCap namePtr : BitVec 64} {R : SepProp}
    (hbcmp : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName +
        BitVec.ofNat 64 (ls_rel% dirPutName cliBcmpName))
      (withPutCS s0 cliBcmpSpec))
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName +
        BitVec.ofNat 64 (ls_rel% dirPutName deallocName))
      (withPutCS s0 (rustDeallocExternSpecWithStack A extHookStack)))
    (hgrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName +
        BitVec.ofNat 64 (ls_rel% dirPutName growOneDirName))
      (withPutCS s0 (growOneDirRawSpec A growStk)))
    (h96 : 0x60 ≤ stk)
    (hhook96 : extHookStack ≤ stk - 96)
    (hgrow_stk : growStk ≤ stk - 96)
    (hle_stk : stk ≤ 2 ^ 64)
    (hlen_lt32 : x.dir.changed.length < 2 ^ 32)
    (hlen_le : x.dir.changed.length ≤ cap.toNat)
    (hcap48_lt : cap.toNat * 48 < 2 ^ 63)
    (hptr_ne : ptr ≠ 0)
    (hna_le : x.name.length ≤ nameCap.toNat)
    (hna_lt : nameCap.toNat < 2 ^ 63)
    (hna_ptr : namePtr ≠ 0)
    (halign : s0.sp &&& 15#64 = 0#64)
    (rest : List (List (BitVec 8) × List (BitVec 8))) :
    ∀ (pre : List (List (BitVec 8) × List (BitVec 8)))
      (hd : List (BitVec 8) × List (BitVec 8))
      (s : State) (P : SepProp),
      x.dir.changed = pre ++ hd :: rest →
      (∀ e ∈ pre, e.1 ≠ x.name) →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr dirPutName + 80#64 →
      s.status = .Running →
      s.sp = s0.sp - 96#64 →
      s.trace = s0.trace →
      s.readReg64 .x19 = namePtr →
      s.readReg64 .x20 = nameCap →
      s.readReg64 .x21 = x.bytesV →
      s.readReg64 .x22 = x.self →
      s.readReg64 .x23 = BitVec.ofNat 64 x.name.length →
      s.readReg64 .x24 = BitVec.ofNat 64 x.dir.changed.length →
      s.readReg64 .x25 = ptr →
      s.readReg64 .x26 = ptr + BitVec.ofNat 64 (pre.length * 48) + 32#64 →
      s.readReg64 .x27 = BitVec.ofNat 64 (48 * (hd :: rest).length) →
      PutCalleeSaved s0 s →
      P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
          vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A) 48 ptr pre ∗
          dirEntryAt A hd (ptr + BitVec.ofNat 64 (pre.length * 48)) ∗
          arrayAt (dirEntryAt A) 48 (ptr + BitVec.ofNat 64 (pre.length * 48) + 48#64) rest ∗
          memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
            ((cap.toNat - x.dir.changed.length) * 48) ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          vecU8Rest A nameCap namePtr x.name ∗
          memRegion x.nameV 24 ∗
          vecU8 A x.bytesV x.bytes ∗ A.pool →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s P
        (putRetQ A img stk x s0 R)
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpec A img stk).onPanic x s0 sf ∗ R)) :=
  match rest with
  | [] => fun pre ⟨eName, oldBs⟩ s P hx_eq hpre hpc hrun hsp htr
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hcs hP =>
    step_loop_body (img := img) (A := A) (ext := ext) (growStk := growStk) (stk := stk)
      (s0 := s0) (s := s) (x := x) (pre := pre) (rest := []) (eName := eName) (oldBs := oldBs)
      (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr) (P := P) (R := R)
      hbcmp hdealloc hgrow h96 hhook96 hgrow_stk hle_stk
      hx_eq hpre hlen_lt32 hlen_le hcap48_lt hptr_ne hna_le hna_lt hna_ptr
      hpc hrun hsp halign htr
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hcs hP
      (fun _ _ _ _ hnil => nomatch hnil)
  | hd2 :: rest2 => fun pre ⟨eName, oldBs⟩ s P hx_eq hpre hpc hrun hsp htr
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hcs hP =>
    step_loop_body (img := img) (A := A) (ext := ext) (growStk := growStk) (stk := stk)
      (s0 := s0) (s := s) (x := x) (pre := pre) (rest := hd2 :: rest2)
      (eName := eName) (oldBs := oldBs)
      (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr) (P := P) (R := R)
      hbcmp hdealloc hgrow h96 hhook96 hgrow_stk hle_stk
      hx_eq hpre hlen_lt32 hlen_le hcap48_lt hptr_ne hna_le hna_lt hna_ptr
      hpc hrun hsp halign htr
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hcs hP
      (fun hne_cur _ _ sn hcons hpcsn hrunsn hspsn htrsn
          hx19s hx20s hx21s hx22s hx23s hx24s hx25s hx26s hx27s hcssn => by
        obtain ⟨rfl, rfl⟩ := List.cons.inj hcons
        exact step_loop (img := img) (A := A) (ext := ext) (growStk := growStk) (stk := stk)
          (s0 := s0) (x := x)
          (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr) (R := R)
          hbcmp hdealloc hgrow h96 hhook96 hgrow_stk hle_stk
          hlen_lt32 hlen_le hcap48_lt hptr_ne hna_le hna_lt hna_ptr halign
          rest2 (pre ++ [(eName, oldBs)]) hd2 sn _
          (by rw [hx_eq, List.append_assoc]; rfl)
          (fun e he => by
            rcases List.mem_append.mp he with h1 | h2
            · exact hpre e h1
            · rcases List.mem_singleton.mp h2 with rfl
              exact hne_cur)
          hpcsn hrunsn hspsn htrsn
          hx19s hx20s hx21s hx22s hx23s hx24s hx25s hx26s hx27s hcssn rfl)

end CryptoVerification.SignalSession.Cli.Put.Helpers
