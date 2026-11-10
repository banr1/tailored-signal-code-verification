/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneSysrootExt
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# Base Step Lemmas for `spqr::encode_varint` (`0x54040`, 164 insns)

Proves the `grow_one` call helper, prologue, shared final-byte writer (`412..460`), exit blocks,
and continuation-byte stages 1..4 for `spqr::encode_varint` (`0x54040`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.EncodeVarint

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSpqrV1
  (encodeVarintLoop MAX_VARINT_BYTES_LEN GrowOneCall newCapU8 growOneU8Spec growOneU8Name SpqrHooks)
open CryptoVerification.SpqrV1.Alloc (AllocContracts4K growOneU8_sysroot_ok_at_ext
  growOneU8_sysroot_ok_ext growOneU8_sysroot_ok_at_ext_4k growOneU8_sysroot_ok_ext_4k)
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem spqrEncodeVarint_fnOff :
    libsignalSessionCode.fnOff spqrEncodeVarintName =
      num% (ls_off% "spqr::encode_varint") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "spqr::encode_varint")

theorem growOneU8_fnOff :
    libsignalSessionCode.fnOff growOneU8Name =
      num% (ls_off% "<alloc::raw_vec::RawVec<u8>>::grow_one") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<alloc::raw_vec::RawVec<u8>>::grow_one")

theorem growOneU8_ok_at_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : AllocContracts b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff growOneU8Name := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (growOneU8Spec A) :=
  growOneU8_sysroot_ok_at_ext hA name k hk

theorem growOneU8_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : AllocContracts b A ext) :
    GrowOneU8OkExt b A ext :=
  growOneU8_sysroot_ok_ext hA

theorem growOneU8_ok_at_ext_4k (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff growOneU8Name := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (growOneU8Spec A) :=
  growOneU8_sysroot_ok_at_ext_4k hA name k hk

theorem growOneU8_ok_ext_4k (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : AllocContracts4K b A ext) :
    GrowOneU8OkExt b A ext :=
  growOneU8_sysroot_ok_ext_4k hA

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

gen_decodes libsignalSessionCode_tree libsignalSessionBin [0x4ec48 → 0x4eed8]

open Lean Elab Tactic in
/-- Fetch instructions in `[kStart, kEnd)` (byte offsets from function start `off`)
using decode lemmas in `CryptoVerification.SpqrV1.Top.EncodeVarint`. -/
elab "spqrEncVarint_fetches_range " b:term:max H:term:max hfn:ident
    off:num kStart:num kEnd:num : tactic => do
  let off := off.getNat
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let dec := mkIdent (`CryptoVerification.SpqrV1.Top.EncodeVarint |>.str
      s!"libsignalSessionBin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

/-! ## Callee-saved tracking (`x26..x28`, `StepInv`) and stack / capacity helpers -/

def SpqrEncVarintCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  StepInv s0 s

theorem SpqrEncVarintCalleeSaved.refl (s : State) : SpqrEncVarintCalleeSaved s s :=
  ⟨rfl, rfl, rfl, rfl, StepInv.refl s⟩

theorem SpqrEncVarintCalleeSaved.trans {s0 s1 s2 : State}
    (h1 : SpqrEncVarintCalleeSaved s0 s1) (h2 : SpqrEncVarintCalleeSaved s1 s2) :
    SpqrEncVarintCalleeSaved s0 s2 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
   h2.2.2.2.1.trans h1.2.2.2.1,
   h1.2.2.2.2.trans h2.2.2.2.2⟩

theorem SpqrEncVarintCalleeSaved.of_calleeSavedPreserved {s1 s2 : State}
    (h : CalleeSavedPreserved s1 s2) (hinv : StepInv s1 s2) : SpqrEncVarintCalleeSaved s1 s2 :=
  ⟨h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2, hinv⟩

theorem sp_sub_80_aligned {sp : BitVec 64} (h : sp &&& 15#64 = 0#64) :
    (sp - 80#64) &&& 15#64 = 0#64 := by
  bv_bits

@[scoped simp]
theorem encodeVarintLoop_10_eq (a : BitVec 64) :
    encodeVarintLoop MAX_VARINT_BYTES_LEN a = encodeVarint a :=
  encodeVarintLoop_eq_encodeVarintAux 10 a

@[scoped simp, scoped arm64_norm]
theorem ule_128_eq_not_ult_128 (v : BitVec 64) :
    (128#64).ule v = !v.ult 128#64 := by
  rw [BitVec.ule_eq_decide, BitVec.ult_eq_decide]
  change decide (128 ≤ v.toNat) = !decide (v.toNat < 128)
  by_cases h : v.toNat < 128
  · have h' : ¬ (128 ≤ v.toNat) := by omega
    simp [h, h']
  · have h' : 128 ≤ v.toNat := by omega
    simp [h, h']

@[scoped simp, scoped arm64_norm]
theorem not_len_lt_ofNat_len (n : Nat) : ¬ n < (BitVec.ofNat 64 n).toNat := by
  rw [BitVec.toNat_ofNat]
  exact Nat.not_lt.mpr (Nat.mod_le n (2 ^ 64))

@[scoped simp, scoped arm64_norm]
theorem len_beq_cap_false {cap : BitVec 64} {n : Nat} (hlt : n < cap.toNat) :
    (BitVec.ofNat 64 n == cap) = false := by
  have h := cap_beq_len_false hlt
  rw [beq_eq_false_iff_ne] at h ⊢
  exact Ne.symm h

@[scoped simp, scoped arm64_norm]
theorem len_bne_cap_true {cap : BitVec 64} {n : Nat} (hlt : n < cap.toNat) :
    (BitVec.ofNat 64 n != cap) = true := by
  simp [bne, len_beq_cap_false hlt]

theorem origLen_add_step {origLen : BitVec 64} {curBs : List (BitVec 8)} (byte : BitVec 8)
    (k1 k : BitVec 64) (hk : k1 + 1#64 = k)
    (horig : origLen + k1 = BitVec.ofNat 64 curBs.length) :
    origLen + k = BitVec.ofNat 64 (curBs ++ [byte]).length := by
  rw [← hk, ← BitVec.add_assoc, horig, bv_len_add_one]

theorem stackAt_spqrEncodeVarint_eq (sp : BitVec 64) :
    stackAt sp spqrEncodeVarintStackX =
      stackAt (sp - 80#64) extHookStack ∗
      (∃∗ v80 : BitVec 64, ∃∗ v72 : BitVec 64, ∃∗ v64 : BitVec 64, ∃∗ v56 : BitVec 64,
       ∃∗ v48 : BitVec 64, ∃∗ v40 : BitVec 64, ∃∗ v32 : BitVec 64, ∃∗ v24 : BitVec 64,
       ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v80) ∗ ((sp - 72#64) ↦₆₄ v72) ∗
        ((sp - 64#64) ↦₆₄ v64) ∗ ((sp - 56#64) ↦₆₄ v56) ∗
        ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
        ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
        ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) := by
  change stackAt sp (extHookStack + 8 * 10) = _
  rw [ProofLib.stackAt_split_cells sp extHookStack 10 (by decide)]
  congr 1
  cells_unfold

/-! ## Callee helper: `<alloc::raw_vec::RawVec<u8>>::grow_one` (`entry + bv% (ls_off% "<alloc::raw_vec::RawVec<u8>>::grow_one" - ls_off% "spqr::encode_varint")`) -/

theorem growOneU8_fnAddr_eq (b : BitVec 64) (abs : String → Option (State → State)) :
    (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName + bv% (ls_off% "<alloc::raw_vec::RawVec<u8>>::grow_one" - ls_off% "spqr::encode_varint") =
      (tripleRatchetProgAtExt b abs).fnAddr growOneU8Name := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, spqrEncodeVarint_fnOff, growOneU8_fnOff]
  bv_omega

theorem newCapU8_bounds {cap : BitVec 64} {len : Nat}
    (hcap : cap.toNat = len) (hlen : len < 2 ^ 62) :
    max (2 * cap.toNat) 8 < 2 ^ 63 ∧
    (newCapU8 cap).toNat = max (2 * cap.toNat) 8 ∧
    newCapU8 cap ≠ 0 ∧
    len < (newCapU8 cap).toNat ∧
    cap.toNat ≤ (newCapU8 cap).toNat := by
  unfold newCapU8
  have hmax : max (2 * cap.toNat) 8 < 2 ^ 63 := by omega
  have htoNat : (BitVec.ofNat 64 (max (2 * cap.toNat) 8)).toNat = max (2 * cap.toNat) 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne : BitVec.ofNat 64 (max (2 * cap.toNat) 8) ≠ 0 := by
    intro heq
    have := congrArg BitVec.toNat heq
    rw [htoNat] at this
    change max (2 * cap.toNat) 8 = 0 at this
    omega
  refine ⟨hmax, htoNat, hne, ?_, ?_⟩ <;> omega

theorem vecU8Buf_eq_for_growOne (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hcap : cap.toNat = bs.length) :
    vecU8Buf A cap ptr bs =
      ⌜cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp else A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs)) := by
  unfold vecU8Buf
  have hpure : (bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) =
      (cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) := by
    apply propext; constructor
    · rintro ⟨_, h2, h3⟩; exact ⟨h2, h3⟩
    · rintro ⟨h2, h3⟩; exact ⟨by omega, h2, h3⟩
  rw [hpure]
  by_cases h0 : cap = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte, hcap, Nat.sub_self, memRegion_zero, sepConj_emp]

/-- Execute a `bl <RawVec<u8>>::grow_one` call at `s.pc = entry + bv% (ls_off% "<alloc::raw_vec::RawVec<u8>>::grow_one" - ls_off% "spqr::encode_varint")` when `curCap.toNat = curBs.length`. -/
theorem step_growOneU8_call (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State))
    {s0 s : State}
    (hgrow : GrowOneU8OkExt b A abs)
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hcap_eq : curCap.toNat = curBs.length)
    (hlen_lt : curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName + bv% (ls_off% "<alloc::raw_vec::RawVec<u8>>::grow_one" - ls_off% "spqr::encode_varint"))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hcs_s : SpqrEncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      vecU8Buf A curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x24 = s.readReg64 .x24 →
      sm.readReg64 .x25 = s.readReg64 .x25 →
      SpqrEncVarintCalleeSaved s0 sm →
      curBs.length < newCap.toNat →
      curCap.toNat ≤ newCap.toNat →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          vecU8Buf A newCap p' curBs ∗ A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  rw [growOneU8_fnAddr_eq] at hpc
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_80_aligned halign
  obtain ⟨hmax_lt, hnew_toNat, hnew_ne, hnew_gt, hnew_ge⟩ := newCapU8_bounds hcap_eq hlen_lt
  refine SepWPp.call_cs (x := GrowOneCall.mk v curCap curPtr curBs) (F := F)
    hgrow hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, vecU8Buf_eq_for_growOne A curCap curPtr curBs hcap_eq] at hm
    have hm' : s.mem ⊨ ⌜curCap.toNat < 2 ^ 63 ∧ curPtr ≠ 0⌝ ∗
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          (if curCap = 0 then emp else A.live curPtr curBs.length 1 ∗ (curPtr ↦ₛ curBs)) ∗
          A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ (F ∗ R')) := by
      convert hm using 1; ac_rfl
    rw [satisfies_pure_sepConj] at hm'
    simp only [growOneU8Spec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hcap_eq.symm, hm'.1.2, hmax_lt⟩, ?_⟩
    convert hm'.2 using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [growOneU8Spec, spqrEncodeVarintSpecX, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [growOneU8Spec, hsp, sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun p' => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hpost_eq :
        (⌜p' ≠ 0⌝ ∗ (v ↦₆₄ newCapU8 curCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          A.live p' (max (2 * curCap.toNat) 8) 1 ∗ (p' ↦ₛ curBs) ∗
          memRegion (p' + BitVec.ofNat 64 curBs.length) (max (2 * curCap.toNat) 8 - curCap.toNat)) ∗
          A.pool ∗ stackAt (sp - 80#64) extHookStack ∗ F =
        (((v ↦₆₄ newCapU8 curCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          vecU8Buf A (newCapU8 curCap) p' curBs ∗ A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F) := by
      unfold vecU8Buf
      simp only [hnew_ne, ↓reduceIte, hnew_toNat, hcap_eq]
      have hpure : (curBs.length ≤ max (2 * curBs.length) 8 ∧ max (2 * curBs.length) 8 < 2 ^ 63 ∧ p' ≠ 0) =
          (p' ≠ 0) := by
        apply propext; constructor
        · exact fun h => h.2.2
        · intro hp; exact ⟨by omega, by omega, hp⟩
      rw [hpure]
      ac_rfl
    refine SepWPp.weaken_pre ?_ (hnext sm (newCapU8 curCap) p'
      hpcm hrunm hspm htrm'
      hcsm.1 hcsm.2.1 hcsm.2.2.1 hcsm.2.2.2.1 hcsm.2.2.2.2.1 hcsm.2.2.2.2.2.1 hcsm.2.2.2.2.2.2.1
      (hcs_s.trans (SpqrEncVarintCalleeSaved.of_calleeSavedPreserved hcsm hinv_call))
      hnew_gt hnew_ge)
    exact Entails.of_eq (by rw [← hpost_eq]; ac_rfl)

/-! ## Prologue (`0..44`) and Shared Tail (`412..460`) -/

/-- Prologue (`+0x000..+0x028`, offsets `0..44`): allocates `0x50 = 80` byte stack frame,
saves `fp, lr, x25, x24, x23, x22, x21, x20, x19`, loads `origLen` (`x22`), sets `x19 = v`,
`x20 = val`, and branches on `val.ult 128#64` to `+44` (`0x5406c`) or `+64` (`0x54080`). -/
theorem step_spqrEncVarint_prologue (b : BitVec 64) (abs : String → Option (State → State))
    (val v cap ptr sp v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64) (bs : List (BitVec 8))
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((sp - 80#64) ↦₆₄ v80) ∗ ((sp - 72#64) ↦₆₄ v72) ∗
      ((sp - 64#64) ↦₆₄ v64) ∗ ((sp - 56#64) ↦₆₄ v56) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if val.ult 128#64 then
        (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName + 44#64
      else
        (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName + 64#64) →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = val →
      sm.readReg64 .x22 = BitVec.ofNat 64 bs.length →
      SpqrEncVarintCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((sp - 80#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 72#64) ↦₆₄ s.readReg64 .lr) ∗
          ((sp - 64#64) ↦₆₄ s.readReg64 .x25) ∗ ((sp - 56#64) ↦₆₄ v56) ∗
          ((sp - 48#64) ↦₆₄ s.readReg64 .x24) ∗ ((sp - 40#64) ↦₆₄ s.readReg64 .x23) ∗
          ((sp - 32#64) ↦₆₄ s.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .x21) ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19)) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  spqrEncVarint_fetches_range b (Rust.withPanics abs)
    spqrEncodeVarint_fnOff 322632 0 44
  generalize_entry (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName = entry
  examples_hide_fetches
  subst hP
  apply SepWPp.of_sepWP_cs (mid := if val.ult 128#64 then entry + 44#64 else entry + 64#64)
  wp_steps
  apply SepWP.done (by cases val.ult 128#64 <;> simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_step
  exact hnext _ (by cases val.ult 128#64 <;> simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self])

/-- Shared final-byte writer and epilogue (`+0x19c..+0x1c8`, offsets `412..460`):
given `s.pc = if curBs.length < curCap.toNat then entry + 420#64 else entry + 412#64`,
appends `lastVal.setWidth 8`, restores `x19..x25, fp, lr, sp`, and returns to `s0.readReg64 .lr`. -/
theorem step_spqrEncVarint_tail (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State}
    (hgrow : GrowOneU8OkExt b A abs)
    (x : EncodeVarintGhost) (lastVal curCap curPtr v56 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : VecReserveInv x.cap x.ptr curCap curPtr curBs)
    (hbs : curBs ++ [lastVal.setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {R : SepProp} {P : SepProp}
    (hpc : s.pc = (if curBs.length < curCap.toNat then
      (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName + 420#64
    else
      (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName + 412#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.v)
    (hx20 : (s.readReg64 .x20).setWidth 8 = lastVal.setWidth 8)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length)
    (hcs : SpqrEncVarintCalleeSaved s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      A.pool ∗ stackAt (s0.sp - 80#64) extHookStack) ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  spqrEncVarint_fetches_range b (Rust.withPanics abs)
    spqrEncodeVarint_fnOff 322632 412 460
  generalize_entry hentry : (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName = entry
  examples_hide_fetches
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (s0.sp - 80#64) extHookStack ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (by ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · simp only [hlt, ↓reduceIte] at hpc
    rcases hcs with ⟨h26, h27, h28, hvregs, _⟩
    have hlen1 := bv_len_add_one curBs (lastVal.setWidth 8)
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (lastVal.setWidth 8) hlt]
    have hinv' := hinv.step (byte := lastVal.setWidth 8) (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    rw [hbs] at hinv'
    have ⟨hcap_le, hcap_pres⟩ := hinv'.finish
    refine ⟨?_, by simp only [arm64_norm, *], by encodedLen_cc_close⟩
    intro hm_f
    rw [hbs] at hm_f
    simp only [spqrEncodeVarintSpecX, spqr_encode_varint_eq, encodeVarintLoop_10_eq,
      vecU8At_eq_header_sep_buf, vecHeader, stackAt_spqrEncodeVarint_eq,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x25, v56,
      s0.readReg64 .x24, s0.readReg64 .x23, s0.readReg64 .x22, s0.readReg64 .x21,
      s0.readReg64 .x20, s0.readReg64 .x19, curCap, curPtr,
      by simp only [arm64_norm, *], ⟨hcap_le, hcap_pres⟩, ?_⟩
    convert hm_f using 1
    ac_rfl
  · simp only [hlt, ↓reduceIte] at hpc
    have hcap_eq : curCap.toNat = curBs.length := by omega
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVec<u8>>::grow_one" - ls_off% "spqr::encode_varint"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    refine step_growOneU8_call b A abs hgrow x.v curCap curPtr s0.sp
      (entry + 420#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
        (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hx21m _ _ _ _ hcsm hnew_gt hnew_ge
    rcases hcsm with ⟨h26, h27, h28, hvregs, _⟩
    have hx19m' : sm.readReg64 .x19 = x.v := by simp only [arm64_norm, *]
    have hx20m' : (sm.readReg64 .x20).setWidth 8 = lastVal.setWidth 8 := by
      rw [hx20m]; simp only [arm64_norm, *]
    have hx21m' : sm.readReg64 .x21 = BitVec.ofNat 64 curBs.length := by simp only [arm64_norm, *]
    have hlen1 := bv_len_add_one curBs (lastVal.setWidth 8)
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A newCap p' curBs (lastVal.setWidth 8) hnew_gt]
    have hinv' := hinv.step (nextPtr := p') (byte := lastVal.setWidth 8) hnew_ge (fun h => absurd h hlt)
    rw [hbs] at hinv'
    have ⟨hcap_le, hcap_pres⟩ := hinv'.finish
    refine ⟨?_, by simp only [arm64_norm, *], by encodedLen_cc_close⟩
    intro hm_f
    rw [hbs] at hm_f
    simp only [spqrEncodeVarintSpecX, spqr_encode_varint_eq, encodeVarintLoop_10_eq,
      vecU8At_eq_header_sep_buf, vecHeader, stackAt_spqrEncodeVarint_eq,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x25, v56,
      s0.readReg64 .x24, s0.readReg64 .x23, s0.readReg64 .x22, s0.readReg64 .x21,
      s0.readReg64 .x20, s0.readReg64 .x19, newCap, p',
      by simp only [arm64_norm, *], ⟨hcap_le, hcap_pres⟩, ?_⟩
    convert hm_f using 1
    ac_rfl

/-! ## Exit Blocks (`44..64`, `112..132`, `184..204`, `256..276`, `328..348`, `396..412`, `640..656`) -/

/-- Stage 0 exit (`+44..+64`, `0x5406c..0x54080`): sets `x21 = x22`, checks `x22 == curCap`, and
branches to `step_spqrEncVarint_tail`. -/
theorem step_spqrEncVarint_exit0 (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8OkExt b A abs)
    (x : EncodeVarintGhost) (curCap curPtr v56 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : VecReserveInv x.cap x.ptr curCap curPtr curBs)
    (hbs : curBs ++ [x.val.setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62) {R P : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName + 44#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.v) (hx20 : s.readReg64 .x20 = x.val)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 curBs.length) (hcs : SpqrEncVarintCalleeSaved s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗ A.pool ∗ stackAt (s0.sp - 80#64) extHookStack) ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  spqrEncVarint_fetches_range b (Rust.withPanics abs) spqrEncodeVarint_fnOff 322632 44 64
  generalize_entry hentry : (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName = entry
  examples_hide_fetches; subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (s0.sp - 80#64) extHookStack ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (by ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    apply SepWPp.of_sepWP_cs (mid := entry + 420#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_tail b A abs hgrow x x.val curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self])) rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs (mid := entry + 412#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_tail b A abs hgrow x x.val curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self])) rfl

/-- Stage 1 exit (`+112..+132`, `0x540b0..0x540c4`): shifts `x20 := x20 >>> 7`, checks `x21 == curCap`,
and branches to `step_spqrEncVarint_tail`. -/
theorem step_spqrEncVarint_exit1 (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8OkExt b A abs)
    (x : EncodeVarintGhost) (curCap curPtr v56 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : VecReserveInv x.cap x.ptr curCap curPtr curBs)
    (hbs : curBs ++ [(x.val >>> 7).setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62) {R P : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName + 112#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.v) (hx20 : s.readReg64 .x20 = x.val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length) (hcs : SpqrEncVarintCalleeSaved s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗ A.pool ∗ stackAt (s0.sp - 80#64) extHookStack) ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  spqrEncVarint_fetches_range b (Rust.withPanics abs) spqrEncodeVarint_fnOff 322632 112 132
  generalize_entry hentry : (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName = entry
  examples_hide_fetches; subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (s0.sp - 80#64) extHookStack ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (by ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    apply SepWPp.of_sepWP_cs (mid := entry + 420#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_tail b A abs hgrow x (x.val >>> 7) curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self])) rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs (mid := entry + 412#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_tail b A abs hgrow x (x.val >>> 7) curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self])) rfl

/-- Stage 2 exit (`+184..+204`, `0x540f8..0x5410c`): shifts `x20 := x20 >>> 14`, checks `x21 == curCap`,
and branches to `step_spqrEncVarint_tail`. -/
theorem step_spqrEncVarint_exit2 (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8OkExt b A abs)
    (x : EncodeVarintGhost) (curCap curPtr v56 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : VecReserveInv x.cap x.ptr curCap curPtr curBs)
    (hbs : curBs ++ [(x.val >>> 14).setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62) {R P : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName + 184#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.v) (hx20 : s.readReg64 .x20 = x.val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length) (hcs : SpqrEncVarintCalleeSaved s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗ A.pool ∗ stackAt (s0.sp - 80#64) extHookStack) ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  spqrEncVarint_fetches_range b (Rust.withPanics abs) spqrEncodeVarint_fnOff 322632 184 204
  generalize_entry hentry : (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName = entry
  examples_hide_fetches; subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (s0.sp - 80#64) extHookStack ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (by ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    apply SepWPp.of_sepWP_cs (mid := entry + 420#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_tail b A abs hgrow x (x.val >>> 14) curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self])) rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs (mid := entry + 412#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_tail b A abs hgrow x (x.val >>> 14) curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self])) rfl

/-- Stage 3 exit (`+256..+276`, `0x54140..0x54154`): shifts `x20 := x20 >>> 21`, checks `x21 == curCap`,
and branches to `step_spqrEncVarint_tail`. -/
theorem step_spqrEncVarint_exit3 (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8OkExt b A abs)
    (x : EncodeVarintGhost) (curCap curPtr v56 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : VecReserveInv x.cap x.ptr curCap curPtr curBs)
    (hbs : curBs ++ [(x.val >>> 21).setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62) {R P : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName + 256#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.v) (hx20 : s.readReg64 .x20 = x.val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length) (hcs : SpqrEncVarintCalleeSaved s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗ A.pool ∗ stackAt (s0.sp - 80#64) extHookStack) ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  spqrEncVarint_fetches_range b (Rust.withPanics abs) spqrEncodeVarint_fnOff 322632 256 276
  generalize_entry hentry : (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName = entry
  examples_hide_fetches; subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (s0.sp - 80#64) extHookStack ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (by ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    apply SepWPp.of_sepWP_cs (mid := entry + 420#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_tail b A abs hgrow x (x.val >>> 21) curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self])) rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs (mid := entry + 412#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_tail b A abs hgrow x (x.val >>> 21) curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self])) rfl

/-- Shared exit at `+328..+348` (`0x54188..0x5419c`, used by Stages 4, 6, 8):
moves `w20 := w23`, checks `x21 == curCap`, and branches to `step_spqrEncVarint_tail`. -/
theorem step_spqrEncVarint_exit_328 (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8OkExt b A abs)
    (x : EncodeVarintGhost) (lastVal curCap curPtr v56 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : VecReserveInv x.cap x.ptr curCap curPtr curBs)
    (hbs : curBs ++ [lastVal.setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62) {R P : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName + 328#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.v)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length) (hx23 : s.readReg64 .x23 = lastVal)
    (hcs : SpqrEncVarintCalleeSaved s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗ A.pool ∗ stackAt (s0.sp - 80#64) extHookStack) ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  spqrEncVarint_fetches_range b (Rust.withPanics abs) spqrEncodeVarint_fnOff 322632 328 348
  generalize_entry hentry : (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName = entry
  examples_hide_fetches; subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (s0.sp - 80#64) extHookStack ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (by ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    apply SepWPp.of_sepWP_cs (mid := entry + 420#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_tail b A abs hgrow x lastVal curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [zext8_zext64_trunc32, arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self])) rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs (mid := entry + 412#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_tail b A abs hgrow x lastVal curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [zext8_zext64_trunc32, arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self])) rfl

/-- Shared exit at `+396..+412` (`0x541cc..0x541dc`, used by Stages 5 and 7):
moves `w20 := w24`, checks `x21 == curCap`, and branches to `step_spqrEncVarint_tail`. -/
theorem step_spqrEncVarint_exit_396 (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8OkExt b A abs)
    (x : EncodeVarintGhost) (lastVal curCap curPtr v56 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : VecReserveInv x.cap x.ptr curCap curPtr curBs)
    (hbs : curBs ++ [lastVal.setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62) {R P : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName + 396#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.v)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length) (hx24 : s.readReg64 .x24 = lastVal)
    (hcs : SpqrEncVarintCalleeSaved s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗ A.pool ∗ stackAt (s0.sp - 80#64) extHookStack) ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  spqrEncVarint_fetches_range b (Rust.withPanics abs) spqrEncodeVarint_fnOff 322632 396 412
  generalize_entry hentry : (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName = entry
  examples_hide_fetches; subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (s0.sp - 80#64) extHookStack ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (by ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    apply SepWPp.of_sepWP_cs (mid := entry + 420#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_tail b A abs hgrow x lastVal curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [zext8_zext64_trunc32, arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self])) rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs (mid := entry + 412#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_tail b A abs hgrow x lastVal curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [zext8_zext64_trunc32, arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self])) rfl

/-- Stage 9 exit (`+640..+656`, `0x542c0..0x542d0`): checks `x21 == curCap` with `x20 = 1#64`
and branches to `step_spqrEncVarint_tail`. -/
theorem step_spqrEncVarint_exit9 (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8OkExt b A abs)
    (x : EncodeVarintGhost) (curCap curPtr v56 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : VecReserveInv x.cap x.ptr curCap curPtr curBs)
    (hbs : curBs ++ [(1#64 : BitVec 64).setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62) {R P : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName + 640#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.v) (hx20 : s.readReg64 .x20 = 1#64)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length) (hcs : SpqrEncVarintCalleeSaved s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      A.pool ∗ stackAt (s0.sp - 80#64) extHookStack) ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  spqrEncVarint_fetches_range b (Rust.withPanics abs) spqrEncodeVarint_fnOff 322632 640 656
  generalize_entry hentry : (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName = entry
  examples_hide_fetches; subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (s0.sp - 80#64) extHookStack ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (by ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    apply SepWPp.of_sepWP_cs (mid := entry + 420#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_tail b A abs hgrow x 1#64 curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self])) rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs (mid := entry + 412#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_tail b A abs hgrow x 1#64 curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self])) rfl

theorem grow_frame_reassoc (A : RustAlloc) (v newCap p' sp : BitVec 64)
    (curBs : List (BitVec 8)) (byte : BitVec 8) (F : SepProp) :
    ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗ vecU8Buf A newCap p' (curBs ++ [byte]) ∗
      A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗
      (((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [byte]).length) ∗ F) =
    ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [byte]).length) ∗
      vecU8Buf A newCap p' (curBs ++ [byte]) ∗ A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F := by ac_rfl

/-! ## Continuation-Byte Stages 1..2 -/

/-- Stage 1 (`+64..+112`, `0x54080..0x540b0`): appends `varintContByte val` and branches on
`(val >>> 7).ult 128#64` to `+112` (`exit1`) or `+132` (Stage 2). -/
theorem step_spqrEncVarint_s1 (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8OkExt b A abs)
    (val v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName + 64#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = val)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 curBs.length)
    (hcs : SpqrEncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (if (val >>> 7).ult 128#64 then
        (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName + 112#64
      else
        (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName + 132#64) →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = val →
      sm.readReg64 .x21 = BitVec.ofNat 64 (curBs ++ [varintContByte val]).length →
      sm.readReg64 .x22 = BitVec.ofNat 64 curBs.length →
      SpqrEncVarintCalleeSaved s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte val]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte val]) ∗
          A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  spqrEncVarint_fetches_range b (Rust.withPanics abs)
    spqrEncodeVarint_fnOff 322632 64 112
  generalize_entry hentry : (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName = entry
  examples_hide_fetches
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (sp - 80#64) extHookStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 7).ult 128#64 = true ∨ (val >>> 7).ult 128#64 = false := by
    cases (val >>> 7).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    have hlen1 := bv_len_add_one curBs (varintContByte val)
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs (mid := entry + 112#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte val) hlt]
      exact hnext _ curCap curPtr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply SepWPp.of_sepWP_cs (mid := entry + 132#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte val) hlt]
      exact hnext _ curCap curPtr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVec<u8>>::grow_one" - ls_off% "spqr::encode_varint"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    refine step_growOneU8_call b A abs hgrow v curCap curPtr sp
      (entry + 88#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m _ hx22m hx23m _ _ hcsm hnew_gt hnew_ge
    have hx19m' : sm.readReg64 .x19 = v := by simp only [arm64_norm, *]
    have hx20m' : sm.readReg64 .x20 = val := by simp only [arm64_norm, *]
    have hx22m' : sm.readReg64 .x22 = BitVec.ofNat 64 curBs.length := by simp only [arm64_norm, *]
    have hx23m' : BitVec.zeroExtend 8 (sm.readReg64 .x23) = varintContByte val := by rw [hx23m]; simp only [arm64_norm, *]
    have hlen1 := bv_len_add_one curBs (varintContByte val)
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq := grow_frame_reassoc A v newCap p' sp curBs (varintContByte val) F
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs (mid := entry + 112#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte val) hnew_gt, hGoalEq]
      exact hnext _ newCap p'
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply SepWPp.of_sepWP_cs (mid := entry + 132#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte val) hnew_gt, hGoalEq]
      exact hnext _ newCap p'
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)

/-- Stage 2 (`+132..+184`, `0x540c4..0x540f8`): appends `varintContByte (val >>> 7)` and branches on
`(val >>> 14).ult 128#64` to `+184` (`exit2`) or `+204` (Stage 3). -/
theorem step_spqrEncVarint_s2 (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8OkExt b A abs)
    (val v origLen curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (horig : origLen + 1#64 = BitVec.ofNat 64 curBs.length)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName + 132#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length)
    (hx22 : s.readReg64 .x22 = origLen)
    (hcs : SpqrEncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (if (val >>> 14).ult 128#64 then
        (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName + 184#64
      else
        (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName + 204#64) →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = val →
      sm.readReg64 .x21 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length →
      sm.readReg64 .x22 = origLen →
      SpqrEncVarintCalleeSaved s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 7)]) ∗
          A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  spqrEncVarint_fetches_range b (Rust.withPanics abs)
    spqrEncodeVarint_fnOff 322632 132 184
  generalize_entry hentry : (tripleRatchetProgAtExt b abs).fnAddr spqrEncodeVarintName = entry
  examples_hide_fetches
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (sp - 80#64) extHookStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 14).ult 128#64 = true ∨ (val >>> 14).ult 128#64 = false := by
    cases (val >>> 14).ult 128#64 <;> simp
  have hlen1 := origLen_add_step (varintContByte (val >>> 7)) 1#64 2#64 rfl horig
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs (mid := entry + 184#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 7)) hlt]
      exact hnext _ curCap curPtr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply SepWPp.of_sepWP_cs (mid := entry + 204#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 7)) hlt]
      exact hnext _ curCap curPtr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVec<u8>>::grow_one" - ls_off% "spqr::encode_varint"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    refine step_growOneU8_call b A abs hgrow v curCap curPtr sp
      (entry + 160#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m hx23m _ _ hcsm hnew_gt hnew_ge
    have hx19m' : sm.readReg64 .x19 = v := by simp only [arm64_norm, *]
    have hx20m' : sm.readReg64 .x20 = val := by simp only [arm64_norm, *]
    have hx21m' : sm.readReg64 .x21 = BitVec.ofNat 64 curBs.length := by simp only [arm64_norm, *]
    have hx22m' : sm.readReg64 .x22 = origLen := by simp only [arm64_norm, *]
    have hx23m' : BitVec.zeroExtend 8 (sm.readReg64 .x23) = varintContByte (val >>> 7) := by rw [hx23m]; simp only [arm64_norm, *]
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq := grow_frame_reassoc A v newCap p' sp curBs (varintContByte (val >>> 7)) F
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs (mid := entry + 184#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 7)) hnew_gt, hGoalEq]
      exact hnext _ newCap p'
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply SepWPp.of_sepWP_cs (mid := entry + 204#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 7)) hnew_gt, hGoalEq]
      exact hnext _ newCap p'
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [SpqrEncVarintCalleeSaved, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)

end CryptoVerification.SpqrV1.Top.EncodeVarint
