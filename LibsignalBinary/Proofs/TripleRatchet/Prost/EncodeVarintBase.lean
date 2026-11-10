/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLen
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Prost

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace EncodeVarintNorm

@[scoped simp, scoped arm64_norm]
theorem false_eq_true' : (false = true) = False := Bool.false_eq_true

theorem zext64_trunc32_orr_mask (x : BitVec 64) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 x) ||| 18446743528248704896#64)) =
      BitVec.zeroExtend 64 (BitVec.truncate 32 x) ||| 4294967168#64 := by
  simp

theorem ushr_ushr_7 (v : BitVec 64) (k n : Nat) (h : k + 7 = n := by rfl) :
    (v >>> k) >>> 7 = v >>> n := by
  subst h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
    ← Nat.pow_add]

end EncodeVarintNorm
open EncodeVarintNorm

/-! ## Callee-saved register and image-invariant tracking (`x21..x28`, `StepInv`) for `encode_varint` -/

def StepInv (s s' : State) : Prop :=
  ∀ img : Obj.Image, ImgCallInv img s → ImgCallInv img s'

theorem StepInv.refl (s : State) : StepInv s s :=
  fun _ h => h

theorem StepInv.trans {s0 s1 s2 : State} (h1 : StepInv s0 s1) (h2 : StepInv s1 s2) :
    StepInv s0 s2 :=
  fun img h => h2 img (h1 img h)

theorem StepInv.of_steps {prog : Program} {s s' : State} (hs : Steps prog s s') : StepInv s s' :=
  fun _ h => ⟨h.1.of_keepsFrozen hs.keepsFrozen, hs.symtab_eq.trans h.2⟩

theorem SepWPp.of_sepWP_cs {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun sm Pm => StepInv s sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, hoom⟩⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ := hnext (StepInv.of_steps hsteps) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

def EncVarintCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 .x21 = s0.readReg64 .x21 ∧
  s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  StepInv s0 s

theorem EncVarintCalleeSaved.refl (s : State) : EncVarintCalleeSaved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, StepInv.refl s⟩

theorem EncVarintCalleeSaved.trans {s0 s1 s2 : State}
    (h1 : EncVarintCalleeSaved s0 s1) (h2 : EncVarintCalleeSaved s1 s2) :
    EncVarintCalleeSaved s0 s2 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
   h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
   h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1, h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.1,
   h1.2.2.2.2.2.2.2.2.2.trans h2.2.2.2.2.2.2.2.2.2⟩

theorem EncVarintCalleeSaved.of_calleeSavedPreserved {s1 s2 : State}
    (h : CalleeSavedPreserved s1 s2) (hinv : StepInv s1 s2) : EncVarintCalleeSaved s1 s2 :=
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
   h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2, hinv⟩

/-! ## `vecU8Buf` 1-byte open and snoc equalities -/

theorem vecU8Buf_bounds {A : RustAlloc} {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} {m : Memory} (hm : m ⊨ vecU8Buf A cap ptr bs ∗ R) :
    bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0 := by
  unfold vecU8Buf at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact hm.1

def vecRest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length + 1 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 (bs.length + 1)) (cap.toNat - (bs.length + 1))

theorem memRegion_one_eq (a : BitVec 64) : memRegion a 1 = ∃∗ y : BitVec 8, a ↦₈ y :=
  IsBlock.eq (IsBlock.memRegion a 1)
    (IsBlock.sepExists fun v => IsBlock.pointsTo8 a v)
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩

theorem vecU8Buf_eq_open_one (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hlt : bs.length < cap.toNat) :
    vecU8Buf A cap ptr bs =
      ∃∗ y : BitVec 8, ((ptr + BitVec.ofNat 64 bs.length) ↦₈ y) ∗ vecRest A cap ptr bs := by
  have hne : cap ≠ 0 := by
    intro h0; subst h0; simp at hlt
  have hcap_le : cap.toNat ≤ 2 ^ 64 := Nat.le_of_lt cap.isLt
  have hpure : (bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) =
      (bs.length + 1 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) := by
    apply propext; constructor <;> (intro ⟨_, h2, h3⟩; exact ⟨by omega, h2, h3⟩)
  unfold vecU8Buf vecRest
  simp only [hne, ↓reduceIte, hpure]
  have hsplit := memRegion_split (ptr + BitVec.ofNat 64 bs.length) 1 (cap.toNat - (bs.length + 1)) (by omega)
  rw [show 1 + (cap.toNat - (bs.length + 1)) = cap.toNat - bs.length by omega,
    BitVec.add_assoc, ← BitVec.ofNat_add, memRegion_one_eq] at hsplit
  rw [hsplit]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  congr 1; funext y
  ac_rfl

theorem pointsToBytes_snoc_eq (ptr : BitVec 64) (bs : List (BitVec 8)) (byte : BitVec 8) :
    (ptr ↦ₛ bs) ∗ ((ptr + BitVec.ofNat 64 bs.length) ↦₈ byte) = ptr ↦ₛ (bs ++ [byte]) := by
  rw [pointsToBytes_append, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

theorem vecU8Buf_snoc_eq (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (byte : BitVec 8) (hlt : bs.length < cap.toNat) :
    ((ptr + BitVec.ofNat 64 bs.length) ↦₈ byte) ∗ vecRest A cap ptr bs =
      vecU8Buf A cap ptr (bs ++ [byte]) := by
  have hne : cap ≠ 0 := by
    intro h0; subst h0; simp at hlt
  unfold vecU8Buf vecRest
  simp only [hne, ↓reduceIte]
  have h1 : ((ptr + BitVec.ofNat 64 bs.length) ↦₈ byte) ∗
      (⌜bs.length + 1 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 (bs.length + 1)) (cap.toNat - (bs.length + 1))) =
      ⌜bs.length + 1 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr cap.toNat 1 ∗ ((ptr ↦ₛ bs) ∗ ((ptr + BitVec.ofNat 64 bs.length) ↦₈ byte)) ∗
        memRegion (ptr + BitVec.ofNat 64 (bs.length + 1)) (cap.toNat - (bs.length + 1)) := by
    ac_rfl
  rw [h1, pointsToBytes_snoc_eq]
  simp only [List.length_append, List.length_singleton]

theorem cap_beq_len_false {cap : BitVec 64} {n : Nat} (hlt : n < cap.toNat) :
    (cap == BitVec.ofNat 64 n) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  have hn : n < 2 ^ 64 := Nat.lt_trans hlt cap.isLt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at h1
  omega

theorem cap_eq_ofNat_len {cap : BitVec 64} {n : Nat} (heq : cap.toNat = n) :
    cap = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (heq ▸ cap.isLt)]

theorem bv_len_add_one (bs : List (BitVec 8)) (byte : BitVec 8) :
    BitVec.ofNat 64 bs.length + 1#64 = BitVec.ofNat 64 (bs ++ [byte]).length := by
  simp only [List.length_append, List.length_singleton, BitVec.ofNat_add]

theorem sepWPp_extract_vecU8Buf_le {A : RustAlloc} {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    {prog : Program} {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = vecU8Buf A cap ptr bs ∗ F)
    (h : bs.length ≤ cap.toNat → SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hhm : s.mem ⊨ vecU8Buf A cap ptr bs ∗ (F ∗ R) := by
    rw [← sepConj_assoc, ← hP]; exact hm
  exact h (vecU8Buf_bounds hhm).1 R hm hL

/-! ## Callee helper: `do_reserve_and_handle` call (`entry + 7180#64`) -/

theorem doReserve_fnAddr_eq (b : BitVec 64) (abs : String → Option (State → State)) :
    (tripleRatchetProgAtExt b abs).fnAddr encodeVarintName + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") =
      (tripleRatchetProgAtExt b abs).fnAddr doReserveName := by
  have h1 := (ls_lemma% fnOff "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]")
  have h2 := (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]")
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, encodeVarintName, doReserveName, h1, h2]
  bv_omega

theorem sp_sub_48_aligned {sp : BitVec 64} (h : sp &&& 15#64 = 0#64) :
    (sp - 48#64) &&& 15#64 = 0#64 := by
  bv_bits

theorem reserveCap_bounds {len : Nat} (hlen : len < 2 ^ 62) :
    reserveCap len len 1 + 1 ≤ 2 ^ 63 ∧
    len < (BitVec.ofNat 64 (reserveCap len len 1)).toNat ∧
    len ≤ (BitVec.ofNat 64 (reserveCap len len 1)).toNat := by
  unfold reserveCap
  have hmax : max (max (len + 1) (2 * len)) 8 < 2 ^ 63 := by omega
  have htoNat : (BitVec.ofNat 64 (max (max (len + 1) (2 * len)) 8)).toNat =
      max (max (len + 1) (2 * len)) 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [htoNat]
  omega

def doReserveSpecWith (resStack : Nat) (s0 : State) (A : RustAlloc) : Spec DoReserveCall where
  pre := fun x s =>
    ⌜EncVarintCalleeSaved s0 s ∧
      s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = 1#64 ∧
      s.readReg64 .x4 = 1#64 ∧
      reserveCap x.cap.toNat x.bs.length x.additional + 1 ≤ 2 ^ 63⌝ ∗
    vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp resStack
  post := fun x s0' sf =>
    ⌜sf.trace = s0'.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      vecU8At A x.v (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)) p' x.bs) ∗
    A.pool ∗ stackAt s0'.sp resStack
  onPanic := fun _ s0' sf => ⌜allocFailedIn s0' sf ∧ s0'.trace <+: sf.trace⌝ ∗ anyHeap

theorem doReserve_with_of_ok (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (s0 : State)
    (h : subroutine_ok (tripleRatchetProgAtExt b abs) ((tripleRatchetProgAtExt b abs).fnAddr doReserveName) (doReserveSpec A)) :
    subroutine_ok (tripleRatchetProgAtExt b abs) ((tripleRatchetProgAtExt b abs).fnAddr doReserveName)
      (doReserveSpecWith doReserveStack s0 A) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  simp only [doReserveSpecWith, sepConj_assoc, satisfies_pure_sepConj] at hpre
  refine (h.to_outcome x R s hpc hrun ?_ hsp).mono_outcome fun _ hout => hout
  simp only [doReserveSpec, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpre.1.2, hpre.2⟩

theorem doReserve_with_of_ok_x (img : Obj.Image) (A : RustAlloc)
    (abs : String → Option (State → State)) (s0 : State) (hinv0 : ImgCallInv img s0)
    (h : subroutine_ok (tripleRatchetProgAtExt img.base abs) ((tripleRatchetProgAtExt img.base abs).fnAddr doReserveName)
      ((doReserveSpecX A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base abs) ((tripleRatchetProgAtExt img.base abs).fnAddr doReserveName)
      (doReserveSpecWith doReserveStackX s0 A) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  simp only [doReserveSpecWith, sepConj_assoc, satisfies_pure_sepConj] at hpre
  refine (h.to_outcome x R s hpc hrun ?_ hsp).mono_outcome fun _ hout => hout
  simp only [Spec.inImage, doReserveSpecX, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpre.1.1.2.2.2.2.2.2.2.2.2 img hinv0, hpre.1.2, hpre.2⟩

theorem SepWPp.call_cs {α : Type} {prog : Program} {entry ret ret_pc : BitVec 64}
    {spec : Spec α} {x : α} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R, s.mem ⊨ P ∗ R → s.mem ⊨ spec.pre x s ∗ (F ∗ R))
    (hexit : ∀ sf code R, sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R) → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running → sm.sp = s.sp →
      CalleeSavedPreserved s sm → StepInv s sm →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp)
    (hoom : ∀ sf R, sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R) → False := by
      intro _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout, _⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun (hpre R hm) hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpan_mem⟩ | ⟨code, hex, hex_mem⟩ | ⟨hoom_s, hoom_mem⟩
  · rw [hlr] at hpcm
    rw [← sepConj_assoc] at hpost
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (StepInv.of_steps hsteps) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpan_mem
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpan_mem, hpanic sm hpan⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hex_mem).elim
  · exact (hoom sm (F ∗ R) hoom_s hoom_mem).elim

/-- Execute a `bl do_reserve_and_handle` call at `s.pc = entry + 7180#64` when `curCap.toNat = curBs.length`. -/
theorem step_doReserve_call {resStack : Nat} (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State))
    {s0 s : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b abs)
      ((tripleRatchetProgAtExt b abs).fnAddr doReserveName) (doReserveSpecWith resStack s0 A))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hcap_eq : curCap.toNat = curBs.length)
    (hlen_lt : curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr encodeVarintName + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]"))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hcs_s : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      EncVarintCalleeSaved s0 sm →
      curBs.length < newCap.toNat →
      curCap.toNat ≤ newCap.toNat →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A newCap p' curBs ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  rw [doReserve_fnAddr_eq] at hpc
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_48_aligned halign
  obtain ⟨hres_bound, hnew_gt, hnew_ge⟩ := reserveCap_bounds hlen_lt
  have hx1_toNat : (s.readReg64 .x1).toNat = curBs.length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx2_toNat : (s.readReg64 .x2).toNat = 1 := by
    rw [hx2]; rfl
  refine SepWPp.call_cs (x := DoReserveCall.mk v curCap curPtr curBs 1) (F := F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [doReserveSpecWith, vecU8At_eq_header_sep_buf, vecHeader, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hcs_s, hx0, hx1_toNat, hx2_toNat, hx3, hx4, ?_⟩, ?_⟩
    · rw [hcap_eq]; exact hres_bound
    · convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [doReserveSpecWith, encodeVarintSpec, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [doReserveSpecWith, vecU8At_eq_header_sep_buf, vecHeader, hsp, hcap_eq,
      sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun p' => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hnew_ge' : curCap.toNat ≤ (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)).toNat := by
      rw [hcap_eq]; exact hnew_ge
    refine SepWPp.weaken_pre ?_ (hnext sm (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) p'
      hpcm hrunm hspm htrm' hcsm.1 hcsm.2.1
      (hcs_s.trans (EncVarintCalleeSaved.of_calleeSavedPreserved hcsm hinv_call))
      hnew_gt hnew_ge')
    exact Entails.of_eq (by ac_rfl)

/-! ## BitVec & `encodeVarint` byte/branch lemmas -/

def varintContByte (v : BitVec 64) : BitVec 8 :=
  ((v &&& 0x7F#64) ||| 0x80#64).setWidth 8

@[scoped simp, scoped arm64_norm]
theorem zext8_zext64_trunc32 (x : BitVec 64) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 x)) = BitVec.zeroExtend 8 x := by
  bv_bits

@[scoped simp, scoped arm64_norm]
theorem hw_contByte_w64 (w : BitVec 64) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 w) ||| 18446743528248704896#64) =
      varintContByte w := by
  unfold varintContByte; bv_bits

@[scoped simp, scoped arm64_norm]
theorem hw_contByte_w32_7 (v : BitVec 64) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 v >>> 7) ||| 18446743528248704896#64) =
      varintContByte (v >>> 7) := by
  unfold varintContByte; bv_bits

@[scoped simp, scoped arm64_norm]
theorem hw_contByte_w32_14 (v : BitVec 64) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 v >>> 14) ||| 18446743528248704896#64) =
      varintContByte (v >>> 14) := by
  unfold varintContByte; bv_bits

@[scoped simp, scoped arm64_norm]
theorem hw_contByte_w32_21 (v : BitVec 64) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 v >>> 21) ||| 18446743528248704896#64) =
      varintContByte (v >>> 21) := by
  unfold varintContByte; bv_bits

@[scoped simp, scoped arm64_norm]
theorem varintContByte_w32_7 (v : BitVec 64) :
    varintContByte (BitVec.zeroExtend 64 (BitVec.truncate 32 v) >>> 7) =
      varintContByte (v >>> 7) := by
  unfold varintContByte; bv_bits

@[scoped simp, scoped arm64_norm]
theorem varintContByte_w32_14 (v : BitVec 64) :
    varintContByte (BitVec.zeroExtend 64 (BitVec.truncate 32 v) >>> 14) =
      varintContByte (v >>> 14) := by
  unfold varintContByte; bv_bits

@[scoped simp, scoped arm64_norm]
theorem varintContByte_w32_21 (v : BitVec 64) :
    varintContByte (BitVec.zeroExtend 64 (BitVec.truncate 32 v) >>> 21) =
      varintContByte (v >>> 21) := by
  unfold varintContByte; bv_bits

@[scoped simp, scoped arm64_norm]
theorem ult_0x4000_eq (v : BitVec 64) :
    v.ult 16384#64 = (v >>> 7).ult 128#64 := by
  bv_bits

@[scoped simp, scoped arm64_norm]
theorem ule_0x4000_eq (v : BitVec 64) :
    (16384#64 : BitVec 64).ule v = !(v >>> 7).ult 128#64 := by
  rw [Bool.eq_iff_iff, Bool.not_eq_true']; bv_bits

@[scoped simp, scoped arm64_norm]
theorem ult_0x200000_eq (v : BitVec 64) :
    v.ult 2097152#64 = (v >>> 14).ult 128#64 := by
  bv_bits

@[scoped simp, scoped arm64_norm]
theorem ule_0x200000_eq (v : BitVec 64) :
    (2097152#64 : BitVec 64).ule v = !(v >>> 14).ult 128#64 := by
  rw [Bool.eq_iff_iff, Bool.not_eq_true']; bv_bits

@[scoped simp, scoped arm64_norm]
theorem shr28_beq_zero (v : BitVec 64) :
    (v >>> 28 == 0#64) = (v >>> 21).ult 128#64 := by
  bv_bits

@[scoped simp, scoped arm64_norm]
theorem shr28_bne_zero (v : BitVec 64) :
    (v >>> 28 != 0#64) = !(v >>> 21).ult 128#64 :=
  congrArg Bool.not (shr28_beq_zero v)

@[scoped simp, scoped arm64_norm]
theorem shr35_beq_zero (v : BitVec 64) :
    (v >>> 35 == 0#64) = (v >>> 28).ult 128#64 := by
  bv_bits

@[scoped simp, scoped arm64_norm]
theorem shr35_bne_zero (v : BitVec 64) :
    (v >>> 35 != 0#64) = !(v >>> 28).ult 128#64 :=
  congrArg Bool.not (shr35_beq_zero v)

@[scoped simp, scoped arm64_norm]
theorem shr42_beq_zero (v : BitVec 64) :
    (v >>> 42 == 0#64) = (v >>> 35).ult 128#64 := by
  bv_bits

@[scoped simp, scoped arm64_norm]
theorem shr42_bne_zero (v : BitVec 64) :
    (v >>> 42 != 0#64) = !(v >>> 35).ult 128#64 :=
  congrArg Bool.not (shr42_beq_zero v)

@[scoped simp, scoped arm64_norm]
theorem shr49_beq_zero (v : BitVec 64) :
    (v >>> 49 == 0#64) = (v >>> 42).ult 128#64 := by
  bv_bits

@[scoped simp, scoped arm64_norm]
theorem shr49_bne_zero (v : BitVec 64) :
    (v >>> 49 != 0#64) = !(v >>> 42).ult 128#64 :=
  congrArg Bool.not (shr49_beq_zero v)

@[scoped simp, scoped arm64_norm]
theorem shr56_beq_zero (v : BitVec 64) :
    (v >>> 56 == 0#64) = (v >>> 49).ult 128#64 := by
  bv_bits

@[scoped simp, scoped arm64_norm]
theorem shr56_bne_zero (v : BitVec 64) :
    (v >>> 56 != 0#64) = !(v >>> 49).ult 128#64 :=
  congrArg Bool.not (shr56_beq_zero v)

@[scoped simp, scoped arm64_norm]
theorem getLsbD_63_eq (v : BitVec 64) :
    v.getLsbD 63 = !(v >>> 56).ult 128#64 := by
  rw [Bool.eq_iff_iff, Bool.not_eq_true']; bv_bits

theorem contByte9_contByte_eq (val : BitVec 64) (h : (val >>> 56).ult 128#64 = false) :
    BitVec.zeroExtend 8 (val >>> 56) = varintContByte (val >>> 56) := by
  unfold varintContByte; bv_bits

theorem contByte9_shr63_eq (val : BitVec 64) (h : (val >>> 56).ult 128#64 = false) :
    (1#64 : BitVec 64) = val >>> 63 := by
  bv_bits

theorem shr63_ult_128 (val : BitVec 64) :
    (val >>> 63).ult 128#64 = true := by
  bv_bits

/-! ## Step lemmas for `encode_varint` (`0x30a0`) -/

/-- Prologue (`+0x000..+0x01c`): allocates `0x30` stack frame, saves `fp, lr, x20, x19`,
loads `len` (`x8`) and `cap` (`x9`), and branches on `val.ult 128#64` to `+0x200` (`512`) or `+0x020` (`32`). -/
theorem step_encVarint_prologue (b : BitVec 64) (abs : String → Option (State → State))
    (val v cap ptr sp v48 v40 v32 v24 v16 v8 : BitVec 64) (bs : List (BitVec 8))
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr encodeVarintName)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if val.ult 128#64 then
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarintName + 512#64
      else
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarintName + 32#64) →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s.trace →
      sm.readReg64 .x0 = val →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 bs.length →
      sm.readReg64 .x9 = cap →
      EncVarintCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
          ((sp - 32#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19)) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  tripleRatchetProgAt_fetches_range b (Rust.withPanics abs)
    (ls_lemma% fnOff "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") 12448 0 32
  generalize_entry (tripleRatchetProgAtExt b abs).fnAddr encodeVarintName = entry
  examples_hide_fetches
  subst hP
  apply SepWPp.of_sepWP_cs (mid := if val.ult 128#64 then entry + bv% (512) else entry + bv% (32))
  wp_steps
  apply SepWP.done (by cases val.ult 128#64 <;> simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_step
  exact hnext _ (by cases val.ult 128#64 <;> simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [EncVarintCalleeSaved, arm64_norm, *, and_self])

/-- Shared final-byte writer and epilogue (`+0x200..+0x254`, offsets `512..600`):
appends `lastVal.setWidth 8`, restores `x20, x19, fp, lr, sp`, and returns to `s0.readReg64 .lr`. -/
theorem step_encVarint_final {resStack : Nat} (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b abs)
      ((tripleRatchetProgAtExt b abs).fnAddr doReserveName) (doReserveSpecWith resStack s0 A))
    (lastVal v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr encodeVarintName + 512#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = lastVal)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sf : State) (cap' ptr' : BitVec 64),
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf →
      curCap.toNat ≤ cap'.toNat →
      (curBs.length < curCap.toNat → cap' = curCap ∧ ptr' = curPtr) →
      Q sf (((v ↦₆₄ cap') ∗ ((v + 8#64) ↦₆₄ ptr') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [lastVal.setWidth 8]).length) ∗
        vecU8Buf A cap' ptr' (curBs ++ [lastVal.setWidth 8]) ∗
        ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
        ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  tripleRatchetProgAt_fetches_range b (Rust.withPanics abs)
    (ls_lemma% fnOff "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") 12448 512 600
  generalize_entry hentry : (tripleRatchetProgAtExt b abs).fnAddr encodeVarintName = entry
  examples_hide_fetches
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      A.pool ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28, hvregs, _⟩
    have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs (lastVal.setWidth 8)
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (BitVec.zeroExtend 8 lastVal) hlt]
    exact hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by encodedLen_cc_close) (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    refine step_doReserve_call b A abs hdoReserve v curCap curPtr sp
      (entry + bv% (584)) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
        ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [EncVarintCalleeSaved, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge
    rcases hcsm with ⟨h21, h22, h23, h24, h25, h26, h27, h28, hvregs, _⟩
    have hx19m' : sm.readReg64 .x19 = lastVal := by simp only [arm64_norm, *]
    have hx20m' : sm.readReg64 .x20 = v := by simp only [arm64_norm, *]
    have hbeq := cap_beq_len_false hnew_gt
    have hlen1 := bv_len_add_one curBs (lastVal.setWidth 8)
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A newCap p' curBs (BitVec.zeroExtend 8 lastVal) hnew_gt]
    have hGoalEq :
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [lastVal.setWidth 8]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [lastVal.setWidth 8]) ∗
          A.pool ∗ stackAt (sp - 48#64) resStack) ∗
          (((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
            ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗ F) =
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [lastVal.setWidth 8]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [lastVal.setWidth 8]) ∗
          ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
          ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F := by ac_rfl
    rw [hGoalEq]
    exact hnext _ newCap p' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by encodedLen_cc_close) hnew_ge (fun h => absurd h hlt)

/-! ## Reserve invariant and `encodeVarint` unfolding helpers -/

/-- Tracks the capacity monotonicity and pointer/capacity preservation invariant across the 10
unrolled varint byte stages. -/
def VecReserveInv (cap ptr curCap curPtr : BitVec 64) (curBs : List (BitVec 8)) : Prop :=
  cap.toNat ≤ curCap.toNat ∧ (curBs.length ≤ cap.toNat → curCap = cap ∧ curPtr = ptr)

theorem VecReserveInv.refl (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    VecReserveInv cap ptr cap ptr bs :=
  ⟨Nat.le_refl _, fun _ => ⟨rfl, rfl⟩⟩

theorem VecReserveInv.step {cap ptr curCap curPtr nextCap nextPtr : BitVec 64}
    {curBs : List (BitVec 8)} {byte : BitVec 8}
    (hinv : VecReserveInv cap ptr curCap curPtr curBs)
    (hge : curCap.toNat ≤ nextCap.toNat)
    (hpres : curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) :
    VecReserveInv cap ptr nextCap nextPtr (curBs ++ [byte]) := by
  refine ⟨Nat.le_trans hinv.1 hge, fun hlen => ?_⟩
  rw [List.length_append, List.length_singleton] at hlen
  obtain ⟨rfl, rfl⟩ := hinv.2 (by omega)
  exact hpres (by omega)

theorem VecReserveInv.finish {cap ptr cap' ptr' : BitVec 64} {bs out : List (BitVec 8)}
    (hinv : VecReserveInv cap ptr cap' ptr' (bs ++ out)) :
    cap.toNat ≤ cap'.toNat ∧ (bs.length + out.length ≤ cap.toNat → cap' = cap ∧ ptr' = ptr) := by
  refine ⟨hinv.1, fun hlen => hinv.2 ?_⟩
  rw [List.length_append]
  exact hlen

theorem encodeVarintAux_of_ult {fuel : Nat} {v : BitVec 64} (h : v.ult 128#64 = true) :
    encodeVarintAux (fuel + 1) v = [v.setWidth 8] := by
  have hlt : v.toNat < 128 := by simp [BitVec.ult_eq_decide] at h; exact h
  simp [encodeVarintAux, hlt]

theorem encodeVarintAux_of_not_ult {fuel : Nat} {v : BitVec 64} (h : v.ult 128#64 = false) :
    encodeVarintAux (fuel + 1) v = varintContByte v :: encodeVarintAux fuel (v >>> 7) := by
  have hlt : ¬ v.toNat < 128 := by simp [BitVec.ult_eq_decide] at h; omega
  simp [encodeVarintAux, varintContByte, hlt]

theorem encodeVarint_exit_bs {fuel : Nat} {v : BitVec 64}
    {bs rhs : List (BitVec 8)}
    (hcur : bs ++ encodeVarintAux (fuel + 1) v = rhs)
    (h : v.ult 128#64 = true) :
    bs ++ [v.setWidth 8] = rhs := by
  rw [← encodeVarintAux_of_ult h, hcur]

theorem encodeVarint_step_bs {fuel : Nat} {v nextV : BitVec 64}
    {bs rhs : List (BitVec 8)}
    (hcur : bs ++ encodeVarintAux (fuel + 1) v = rhs)
    (h : v.ult 128#64 = false)
    (hshift : v >>> 7 = nextV) :
    (bs ++ [varintContByte v]) ++ encodeVarintAux fuel nextV = rhs := by
  rw [List.append_assoc, List.singleton_append, ← hshift,
    ← encodeVarintAux_of_not_ult h, hcur]

theorem stackAt_encodeVarint_gen_eq {resStack : Nat} (hres : resStack + 8 * 6 < 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (0x30 + resStack) =
      stackAt (sp - 48#64) resStack ∗
      (∃∗ v48 : BitVec 64, ∃∗ v40 : BitVec 64, ∃∗ v32 : BitVec 64,
       ∃∗ v24 : BitVec 64, ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
        ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
        ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) := by
  rw [Nat.add_comm 0x30 resStack]
  change stackAt sp (resStack + 8 * 6) = _
  rw [stackAt_split_cells sp resStack 6 (Nat.le_of_lt hres)]
  congr 1
  cells_unfold

theorem stackAt_encodeVarint_eq (sp : BitVec 64) :
    stackAt sp encodeVarintStack =
      stackAt (sp - 48#64) doReserveStack ∗
      (∃∗ v48 : BitVec 64, ∃∗ v40 : BitVec 64, ∃∗ v32 : BitVec 64,
       ∃∗ v24 : BitVec 64, ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
        ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
        ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) :=
  stackAt_encodeVarint_gen_eq (by decide) sp

theorem stackAt_encodeVarintX_eq (sp : BitVec 64) :
    stackAt sp encodeVarintStackX =
      stackAt (sp - 48#64) doReserveStackX ∗
      (∃∗ v48 : BitVec 64, ∃∗ v40 : BitVec 64, ∃∗ v32 : BitVec 64,
       ∃∗ v24 : BitVec 64, ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
        ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
        ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) :=
  stackAt_encodeVarint_gen_eq (by decide) sp

def encodeVarintSpecOf (resStack : Nat) (A : RustAlloc) : Spec EncodeVarintGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.val ∧ s.readReg64 .x1 = x.v ∧
      (x.bs.length + 10 ≤ x.cap.toNat ∨ x.bs.length + 10 < 2 ^ 62)⌝ ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (0x30 + resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodeVarint x.val)) ∗
      A.pool ∗ stackAt s0.sp (0x30 + resStack)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem step_encVarint_exit {resStack : Nat} (hres : resStack + 8 * 6 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b abs)
      ((tripleRatchetProgAtExt b abs).fnAddr doReserveName) (doReserveSpecWith resStack s0 A))
    (x : EncodeVarintGhost) (lastVal curCap curPtr v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : VecReserveInv x.cap x.ptr curCap curPtr curBs)
    (hbs : curBs ++ [lastVal.setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {R : SepProp} {P : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr encodeVarintName + 512#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 48#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = lastVal)
    (hx1 : s.readReg64 .x1 = x.v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗
      A.pool ∗ stackAt (s0.sp - 48#64) resStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpecOf resStack A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  refine step_encVarint_final (F := emp) b A abs hdoReserve lastVal x.v curCap curPtr s0.sp v48 v40
    curBs hlen_lt hpc hrun hsp halign htr hx0 hx1 hx8 hx9 hcs (by rw [hP]; ac_rfl) ?_
  intro sf cap' ptr' hpcf hrunf hspf htrf hcsf hge hpres
  have hinv' := hinv.step (byte := lastVal.setWidth 8) hge hpres
  rw [hbs] at hinv'
  have ⟨hcap_le, hcap_pres⟩ := hinv'.finish
  refine ⟨?_, hspf, hcsf⟩
  intro hm_f
  rw [sepConj_emp, hbs] at hm_f
  simp only [encodeVarintSpecOf, vecU8At_eq_header_sep_buf, vecHeader,
    stackAt_encodeVarint_gen_eq hres,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨v48, v40, s0.readReg64 .fp, s0.readReg64 .lr,
    s0.readReg64 .x20, s0.readReg64 .x19, cap', ptr', htrf, ⟨hcap_le, hcap_pres⟩, ?_⟩
  convert hm_f using 1
  ac_rfl

/-! ## Continuation-byte stages 1..3 -/

/-- Stage 1 (`+0x020..+0x084`, offsets `32..136`): appends `varintContByte val` and either exits to
`+0x200` (`512`) with `x0 = val >>> 7` when `(val >>> 7).ult 128#64`, or continues to Stage 2
(`+0x088` = `136`) with `x10 = nextPtr`. -/
theorem step_encVarint_s1 {resStack : Nat} (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b abs)
      ((tripleRatchetProgAtExt b abs).fnAddr doReserveName) (doReserveSpecWith resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr encodeVarintName + 32#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 7).ult 128#64 then
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarintName + 512#64
      else
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarintName + 136#64) →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 7).ult 128#64 then val >>> 7 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte val]).length →
      sm.readReg64 .x9 = nextCap →
      sm.readReg64 .x10 = nextPtr →
      EncVarintCalleeSaved s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte val]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte val]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗
          A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  tripleRatchetProgAt_fetches_range b (Rust.withPanics abs)
    (ls_lemma% fnOff "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") 12448 32 136
  generalize_entry hentry : (tripleRatchetProgAtExt b abs).fnAddr encodeVarintName = entry
  examples_hide_fetches
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 7).ult 128#64 = true ∨ (val >>> 7).ult 128#64 = false := by
    cases (val >>> 7).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs (varintContByte val)
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs (mid := entry + bv% (512))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte val) hlt]
      exact hnext _ curCap curPtr v48 v40
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSaved, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply SepWPp.of_sepWP_cs (mid := entry + bv% (136))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte val) hlt]
      exact hnext _ curCap curPtr v48 v40
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSaved, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    refine step_doReserve_call b A abs hdoReserve v curCap curPtr sp
      (entry + bv% (104)) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [EncVarintCalleeSaved, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge
    have hlen1 := bv_len_add_one curBs (varintContByte val)
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq :
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte val]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte val]) ∗
          A.pool ∗ stackAt (sp - 48#64) resStack) ∗
          (((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F) =
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte val]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte val]) ∗
          ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗
          A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F := by ac_rfl
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs (mid := entry + bv% (512))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step'
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte val) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [EncVarintCalleeSaved, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply SepWPp.of_sepWP_cs (mid := entry + bv% (136))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step'
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte val) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [EncVarintCalleeSaved, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)

/-- Stage 2 (`+0x088..+0x0f8`, offsets `136..252`): appends `varintContByte (val >>> 7)` and either
exits to `+0x200` (`512`) with `x0 = val >>> 14` when `(val >>> 14).ult 128#64`, or continues to
Stage 3 (`+0x0fc` = `252`) with `x10 = nextPtr`. -/
theorem step_encVarint_s2 {resStack : Nat} (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b abs)
      ((tripleRatchetProgAtExt b abs).fnAddr doReserveName) (doReserveSpecWith resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr encodeVarintName + 136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 14).ult 128#64 then
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarintName + 512#64
      else
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarintName + 252#64) →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 14).ult 128#64 then val >>> 14 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length →
      sm.readReg64 .x9 = nextCap →
      sm.readReg64 .x10 = nextPtr →
      EncVarintCalleeSaved s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 7)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗
          A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  tripleRatchetProgAt_fetches_range b (Rust.withPanics abs)
    (ls_lemma% fnOff "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") 12448 136 252
  generalize_entry hentry : (tripleRatchetProgAtExt b abs).fnAddr encodeVarintName = entry
  examples_hide_fetches
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 14).ult 128#64 = true ∨ (val >>> 14).ult 128#64 = false := by
    cases (val >>> 14).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 7))
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs (mid := entry + bv% (512))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 7)) hlt]
      exact hnext _ curCap curPtr v48 v40
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSaved, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply SepWPp.of_sepWP_cs (mid := entry + bv% (252))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 7)) hlt]
      exact hnext _ curCap curPtr v48 v40
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSaved, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    refine step_doReserve_call b A abs hdoReserve v curCap curPtr sp
      (entry + bv% (216)) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [EncVarintCalleeSaved, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge
    have hx19m' : sm.readReg64 .x19 = v := by simp only [arm64_norm, *]
    have hx20m' : sm.readReg64 .x20 =
        BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 val) >>> 7)) |||
          4294967168#64 := by
      simp only [arm64_norm, zext64_trunc32_orr_mask, *]
    have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 7))
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq :
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte (val >>> 7)]) ∗
          A.pool ∗ stackAt (sp - 48#64) resStack) ∗
          (((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F) =
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte (val >>> 7)]) ∗
          ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ val) ∗
          A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F := by ac_rfl
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs (mid := entry + bv% (512))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step'
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 7)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v48 val
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [EncVarintCalleeSaved, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply SepWPp.of_sepWP_cs (mid := entry + bv% (252))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step'
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 7)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v48 val
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [EncVarintCalleeSaved, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)

/-- Stage 3 (`+0x0fc..+0x164`, offsets `252..360`): appends `varintContByte (val >>> 14)` and either
exits to `+0x200` (`512`) with `x0 = val >>> 21` when `(val >>> 21).ult 128#64`, or continues to
Stage 4 (`+0x168` = `360`) with `x12 = val >>> 28`. -/
theorem step_encVarint_s3 {resStack : Nat} (b : BitVec 64) (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b abs)
      ((tripleRatchetProgAtExt b abs).fnAddr doReserveName) (doReserveSpecWith resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr encodeVarintName + 252#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 21).ult 128#64 then
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarintName + 512#64
      else
        (tripleRatchetProgAtExt b abs).fnAddr encodeVarintName + 360#64) →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 21).ult 128#64 then val >>> 21 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length →
      sm.readReg64 .x9 = nextCap →
      sm.readReg64 .x12 = val >>> 28 →
      EncVarintCalleeSaved s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 14)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗
          A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  tripleRatchetProgAt_fetches_range b (Rust.withPanics abs)
    (ls_lemma% fnOff "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") 12448 252 360
  generalize_entry hentry : (tripleRatchetProgAtExt b abs).fnAddr encodeVarintName = entry
  examples_hide_fetches
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 21).ult 128#64 = true ∨ (val >>> 21).ult 128#64 = false := by
    cases (val >>> 21).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 14))
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs (mid := entry + bv% (512))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 14)) hlt]
      exact hnext _ curCap curPtr v48 v40
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSaved, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply SepWPp.of_sepWP_cs (mid := entry + bv% (360))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 14)) hlt]
      exact hnext _ curCap curPtr v48 v40
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSaved, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    refine step_doReserve_call b A abs hdoReserve v curCap curPtr sp
      (entry + bv% (328)) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [EncVarintCalleeSaved, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge
    have hx19m' : sm.readReg64 .x19 =
        BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 val) >>> 14)) |||
          4294967168#64 := by
      simp only [arm64_norm, zext64_trunc32_orr_mask, *]
    have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 14))
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq :
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte (val >>> 14)]) ∗
          A.pool ∗ stackAt (sp - 48#64) resStack) ∗
          (((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F) =
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte (val >>> 14)]) ∗
          ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗
          A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F := by ac_rfl
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs (mid := entry + bv% (512))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step'
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 14)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [EncVarintCalleeSaved, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply SepWPp.of_sepWP_cs (mid := entry + bv% (360))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step'
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 14)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [EncVarintCalleeSaved, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)

/-! ## Relocatable callee-saved and `KeepsFrozen` helpers -/

def StepInvPlaced (s s' : State) : Prop :=
  StepInv s s' ∧ s.mem.KeepsFrozen s'.mem

theorem StepInvPlaced.refl (s : State) : StepInvPlaced s s :=
  ⟨StepInv.refl s, Memory.KeepsFrozen.refl s.mem⟩

theorem StepInvPlaced.trans {s0 s1 s2 : State} (h1 : StepInvPlaced s0 s1) (h2 : StepInvPlaced s1 s2) :
    StepInvPlaced s0 s2 :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem StepInvPlaced.of_steps {prog : Program} {s s' : State} (hs : Steps prog s s') : StepInvPlaced s s' :=
  ⟨StepInv.of_steps hs, hs.keepsFrozen⟩

theorem SepWPp.of_sepWP_cs_placed {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun sm Pm => StepInvPlaced s sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, hoom⟩⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ := hnext (StepInvPlaced.of_steps hsteps) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

def EncVarintCalleeSavedPlaced (s0 s : State) : Prop :=
  s.readReg64 .x21 = s0.readReg64 .x21 ∧
  s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  StepInvPlaced s0 s

theorem EncVarintCalleeSavedPlaced.refl (s : State) : EncVarintCalleeSavedPlaced s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, StepInvPlaced.refl s⟩

theorem EncVarintCalleeSavedPlaced.trans {s0 s1 s2 : State}
    (h1 : EncVarintCalleeSavedPlaced s0 s1) (h2 : EncVarintCalleeSavedPlaced s1 s2) :
    EncVarintCalleeSavedPlaced s0 s2 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
   h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
   h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1, h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.1,
   h1.2.2.2.2.2.2.2.2.2.trans h2.2.2.2.2.2.2.2.2.2⟩

theorem EncVarintCalleeSavedPlaced.of_calleeSavedPreserved {s1 s2 : State}
    (h : CalleeSavedPreserved s1 s2) (hinv : StepInvPlaced s1 s2) : EncVarintCalleeSavedPlaced s1 s2 :=
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
   h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2, hinv⟩

def doReserveSpecWithPlaced (resStack : Nat) (s0 : State) (A : RustAlloc) : Spec DoReserveCall where
  pre := fun x s =>
    ⌜EncVarintCalleeSavedPlaced s0 s ∧
      s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = 1#64 ∧
      s.readReg64 .x4 = 1#64 ∧
      reserveCap x.cap.toNat x.bs.length x.additional + 1 ≤ 2 ^ 63⌝ ∗
    vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp resStack
  post := fun x s0' sf =>
    ⌜sf.trace = s0'.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      vecU8At A x.v (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)) p' x.bs) ∗
    A.pool ∗ stackAt s0'.sp resStack
  onPanic := fun _ s0' sf => ⌜allocFailedIn s0' sf ∧ s0'.trace <+: sf.trace⌝ ∗ anyHeap

theorem SepWPp.call_cs_placed {α : Type} {prog : Program} {entry ret ret_pc : BitVec 64}
    {spec : Spec α} {x : α} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R, s.mem ⊨ P ∗ R → s.mem ⊨ spec.pre x s ∗ (F ∗ R))
    (hexit : ∀ sf code R, sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R) → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running → sm.sp = s.sp →
      CalleeSavedPreserved s sm → StepInvPlaced s sm →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp)
    (hoom : ∀ sf R, sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R) → False := by
      intro _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout, _⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun (hpre R hm) hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpan_mem⟩ | ⟨code, hex, hex_mem⟩ | ⟨hoom_s, hoom_mem⟩
  · rw [hlr] at hpcm
    rw [← sepConj_assoc] at hpost
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (StepInvPlaced.of_steps hsteps) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpan_mem
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpan_mem, hpanic sm hpan⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hex_mem).elim
  · exact (hoom sm (F ∗ R) hoom_s hoom_mem).elim

/-! ### Symbol-table `StepInvPlaced'` and `EncVarintCalleeSavedPlaced'` -/

def StepInvPlaced' (s s' : State) : Prop :=
  s'.symtab = s.symtab ∧ s.mem.KeepsFrozen s'.mem

theorem StepInvPlaced'.refl (s : State) : StepInvPlaced' s s :=
  ⟨rfl, Memory.KeepsFrozen.refl s.mem⟩

theorem StepInvPlaced'.trans {s0 s1 s2 : State} (h1 : StepInvPlaced' s0 s1) (h2 : StepInvPlaced' s1 s2) :
    StepInvPlaced' s0 s2 :=
  ⟨h2.1.trans h1.1, h1.2.trans h2.2⟩

theorem StepInvPlaced'.of_steps {prog : Program} {s s' : State} (hs : Steps prog s s') : StepInvPlaced' s s' :=
  ⟨hs.symtab_eq, hs.keepsFrozen⟩

theorem SepWPp.of_sepWP_cs_placed' {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun sm Pm => StepInvPlaced' s sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, hoom⟩⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ := hnext (StepInvPlaced'.of_steps hsteps) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

def EncVarintCalleeSavedPlaced' (s0 s : State) : Prop :=
  s.readReg64 .x21 = s0.readReg64 .x21 ∧
  s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  StepInvPlaced' s0 s

theorem EncVarintCalleeSavedPlaced'.refl (s : State) : EncVarintCalleeSavedPlaced' s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, StepInvPlaced'.refl s⟩

theorem EncVarintCalleeSavedPlaced'.trans {s0 s1 s2 : State}
    (h1 : EncVarintCalleeSavedPlaced' s0 s1) (h2 : EncVarintCalleeSavedPlaced' s1 s2) :
    EncVarintCalleeSavedPlaced' s0 s2 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
   h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
   h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1, h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.1,
   h1.2.2.2.2.2.2.2.2.2.trans h2.2.2.2.2.2.2.2.2.2⟩

theorem EncVarintCalleeSavedPlaced'.of_calleeSavedPreserved {s1 s2 : State}
    (h : CalleeSavedPreserved s1 s2) (hinv : StepInvPlaced' s1 s2) : EncVarintCalleeSavedPlaced' s1 s2 :=
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
   h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2, hinv⟩

def doReserveSpecWithPlaced' (resStack : Nat) (s0 : State) (A : RustAlloc) : Spec DoReserveCall where
  pre := fun x s =>
    ⌜EncVarintCalleeSavedPlaced' s0 s ∧
      s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = 1#64 ∧
      s.readReg64 .x4 = 1#64 ∧
      reserveCap x.cap.toNat x.bs.length x.additional + 1 ≤ 2 ^ 63⌝ ∗
    vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp resStack
  post := fun x s0' sf =>
    ⌜sf.trace = s0'.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      vecU8At A x.v (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)) p' x.bs) ∗
    A.pool ∗ stackAt s0'.sp resStack
  onPanic := fun _ s0' sf => ⌜allocFailedIn s0' sf ∧ s0'.trace <+: sf.trace⌝ ∗ anyHeap

theorem SepWPp.call_cs_placed' {α : Type} {prog : Program} {entry ret ret_pc : BitVec 64}
    {spec : Spec α} {x : α} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R, s.mem ⊨ P ∗ R → s.mem ⊨ spec.pre x s ∗ (F ∗ R))
    (hexit : ∀ sf code R, sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R) → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running → sm.sp = s.sp →
      CalleeSavedPreserved s sm → StepInvPlaced' s sm →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp)
    (hoom : ∀ sf R, sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R) → False := by
      intro _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout, _⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun (hpre R hm) hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpan_mem⟩ | ⟨code, hex, hex_mem⟩ | ⟨hoom_s, hoom_mem⟩
  · rw [hlr] at hpcm
    rw [← sepConj_assoc] at hpost
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (StepInvPlaced'.of_steps hsteps) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpan_mem
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpan_mem, hpanic sm hpan⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hex_mem).elim
  · exact (hoom sm (F ∗ R) hoom_s hoom_mem).elim

/-! ## Relocatable per-block step lemmas (block 10, calling block 13) -/

theorem doReserve_with_placed_of_ok [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec A))) :
    subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (lsmpl.base 13)
      (doReserveSpecWithPlaced' doReserveStack s0 A) := by
  have h14 := ls_subroutine_ok_of_block (callerProg := (blkPC_10).rebase (blkPl_10).base H) h
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  simp only [doReserveSpecWithPlaced', sepConj_assoc, satisfies_pure_sepConj] at hpre
  refine (h14.to_outcome x R s hpc hrun ?_ hsp).mono_outcome fun _ hout => hout
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  refine ⟨hcl0.of_keepsFrozen hpre.1.1.2.2.2.2.2.2.2.2.2.2, ?_⟩
  simp only [doReserveSpec, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpre.1.2, hpre.2⟩

theorem doReserve_with_placed_of_ok_x [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpecX A))) :
    subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (lsmpl.base 13)
      (doReserveSpecWithPlaced' doReserveStackX s0 A) := by
  have h14 := ls_subroutine_ok_of_block (callerProg := (blkPC_10).rebase (blkPl_10).base H) h
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  simp only [doReserveSpecWithPlaced', sepConj_assoc, satisfies_pure_sepConj] at hpre
  refine (h14.to_outcome x R s hpc hrun ?_ hsp).mono_outcome fun _ hout => hout
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  refine ⟨hcl0.of_keepsFrozen hpre.1.1.2.2.2.2.2.2.2.2.2.2, ?_⟩
  simp only [doReserveSpecX, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpre.1.2, hpre.2⟩

theorem step_doReserve_call_placed [LibsignalPlacement] {resStack : Nat} (A : RustAlloc)
    (H : String → Option (State → State))
    {s0 s : State}
    (hdoReserve : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H)
      (lsmpl.base 13) (doReserveSpecWithPlaced' resStack s0 A))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hcap_eq : curCap.toNat = curBs.length)
    (hlen_lt : curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 13)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hcs_s : EncVarintCalleeSavedPlaced' s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      EncVarintCalleeSavedPlaced' s0 sm →
      curBs.length < newCap.toNat →
      curCap.toNat ≤ newCap.toNat →
      SepWPp ((blkPC_10).rebase (blkPl_10).base H) ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A newCap p' curBs ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_48_aligned halign
  obtain ⟨hres_bound, hnew_gt, hnew_ge⟩ := reserveCap_bounds hlen_lt
  have hx1_toNat : (s.readReg64 .x1).toNat = curBs.length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx2_toNat : (s.readReg64 .x2).toNat = 1 := by
    rw [hx2]; rfl
  refine SepWPp.call_cs_placed' (x := DoReserveCall.mk v curCap curPtr curBs 1) (F := F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [doReserveSpecWithPlaced', vecU8At_eq_header_sep_buf, vecHeader, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hcs_s, hx0, hx1_toNat, hx2_toNat, hx3, hx4, ?_⟩, ?_⟩
    · rw [hcap_eq]; exact hres_bound
    · convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [doReserveSpecWithPlaced', encodeVarintSpec, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [doReserveSpecWithPlaced', vecU8At_eq_header_sep_buf, vecHeader, hsp, hcap_eq,
      sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun p' => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hnew_ge' : curCap.toNat ≤ (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)).toNat := by
      rw [hcap_eq]; exact hnew_ge
    refine SepWPp.weaken_pre ?_ (hnext sm (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) p'
      hpcm hrunm hspm htrm' hcsm.1 hcsm.2.1
      (hcs_s.trans (EncVarintCalleeSavedPlaced'.of_calleeSavedPreserved hcsm hinv_call))
      hnew_gt hnew_ge')
    exact Entails.of_eq (by ac_rfl)

theorem step_encVarint_prologue_placed [LibsignalPlacement] (H : String → Option (State → State))
    (val v cap ptr sp v48 v40 v32 v24 v16 v8 : BitVec 64) (bs : List (BitVec 8))
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_10).base)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if val.ult 128#64 then
        (blkPl_10).base + 512#64
      else
        (blkPl_10).base + 32#64) →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s.trace →
      sm.readReg64 .x0 = val →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 bs.length →
      sm.readReg64 .x9 = cap →
      EncVarintCalleeSavedPlaced' s sm →
      SepWPp ((blkPC_10).rebase (blkPl_10).base H) ret sm
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
          ((sp - 32#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19)) ∗ F) Q Qp) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) ret s P Q Qp := by
  subst hP
  apply SepWPp.of_sepWP_cs_placed' (mid := if val.ult 128#64 then (blkPl_10).base + bv% (512) else (blkPl_10).base + bv% (32))
  wp_steps
  apply SepWP.done (by cases val.ult 128#64 <;> simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_step
  exact hnext _ (by cases val.ult 128#64 <;> simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [EncVarintCalleeSavedPlaced', arm64_norm, *, and_self])

theorem step_encVarint_final_placed [LibsignalPlacement] {resStack : Nat} (A : RustAlloc)
    (H : String → Option (State → State))
    {s0 s : State}
    (hdoReserve : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H)
      (lsmpl.base 13) (doReserveSpecWithPlaced' resStack s0 A))
    (lastVal v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_10).base + 512#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = lastVal)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hcs : EncVarintCalleeSavedPlaced' s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sf : State) (cap' ptr' : BitVec 64),
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf →
      curCap.toNat ≤ cap'.toNat →
      (curBs.length < curCap.toNat → cap' = curCap ∧ ptr' = curPtr) →
      Q sf (((v ↦₆₄ cap') ∗ ((v + 8#64) ↦₆₄ ptr') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [lastVal.setWidth 8]).length) ∗
        vecU8Buf A cap' ptr' (curBs ++ [lastVal.setWidth 8]) ∗
        ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
        ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      A.pool ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28, hvregs, _⟩
    have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs (lastVal.setWidth 8)
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (BitVec.zeroExtend 8 lastVal) hlt]
    exact hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by encodedLen_cc_close) (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed' (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    refine step_doReserve_call_placed A H hdoReserve v curCap curPtr sp
      ((blkPl_10).base + bv% (584)) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
        ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [EncVarintCalleeSavedPlaced', arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge
    rcases hcsm with ⟨h21, h22, h23, h24, h25, h26, h27, h28, hvregs, _⟩
    have hx19m' : sm.readReg64 .x19 = lastVal := by simp only [arm64_norm, *]
    have hx20m' : sm.readReg64 .x20 = v := by simp only [arm64_norm, *]
    have hbeq := cap_beq_len_false hnew_gt
    have hlen1 := bv_len_add_one curBs (lastVal.setWidth 8)
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A newCap p' curBs (BitVec.zeroExtend 8 lastVal) hnew_gt]
    have hGoalEq :
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [lastVal.setWidth 8]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [lastVal.setWidth 8]) ∗
          A.pool ∗ stackAt (sp - 48#64) resStack) ∗
          (((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
            ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗ F) =
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [lastVal.setWidth 8]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [lastVal.setWidth 8]) ∗
          ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
          ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F := by ac_rfl
    rw [hGoalEq]
    exact hnext _ newCap p' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by encodedLen_cc_close) hnew_ge (fun h => absurd h hlt)

theorem step_encVarint_exit_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 8 * 6 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (hdoReserve : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H)
      (lsmpl.base 13) (doReserveSpecWithPlaced' resStack s0 A))
    (x : EncodeVarintGhost) (lastVal curCap curPtr v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : VecReserveInv x.cap x.ptr curCap curPtr curBs)
    (hbs : curBs ++ [lastVal.setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {R : SepProp} {P : SepProp}
    (hpc : s.pc = (blkPl_10).base + 512#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 48#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = lastVal)
    (hx1 : s.readReg64 .x1 = x.v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hcs : EncVarintCalleeSavedPlaced' s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗
      A.pool ∗ stackAt (s0.sp - 48#64) resStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpecOf resStack A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  refine step_encVarint_final_placed (F := emp) A H hdoReserve lastVal x.v curCap curPtr s0.sp v48 v40
    curBs hlen_lt hpc hrun hsp halign htr hx0 hx1 hx8 hx9 hcs (by rw [hP]; ac_rfl) ?_
  intro sf cap' ptr' hpcf hrunf hspf htrf hcsf hge hpres
  have hinv' := hinv.step (byte := lastVal.setWidth 8) hge hpres
  rw [hbs] at hinv'
  have ⟨hcap_le, hcap_pres⟩ := hinv'.finish
  refine ⟨?_, hspf, hcsf⟩
  intro hm_f
  rw [sepConj_emp, hbs] at hm_f
  simp only [encodeVarintSpecOf, vecU8At_eq_header_sep_buf, vecHeader,
    stackAt_encodeVarint_gen_eq hres,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨v48, v40, s0.readReg64 .fp, s0.readReg64 .lr,
    s0.readReg64 .x20, s0.readReg64 .x19, cap', ptr', htrf, ⟨hcap_le, hcap_pres⟩, ?_⟩
  convert hm_f using 1
  ac_rfl

theorem step_encVarint_s1_placed [LibsignalPlacement] {resStack : Nat} (A : RustAlloc)
    (H : String → Option (State → State))
    {s0 s : State}
    (hdoReserve : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H)
      (lsmpl.base 13) (doReserveSpecWithPlaced' resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_10).base + 32#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hcs : EncVarintCalleeSavedPlaced' s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 7).ult 128#64 then
        (blkPl_10).base + 512#64
      else
        (blkPl_10).base + 136#64) →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 7).ult 128#64 then val >>> 7 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte val]).length →
      sm.readReg64 .x9 = nextCap →
      sm.readReg64 .x10 = nextPtr →
      EncVarintCalleeSavedPlaced' s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte val]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte val]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗
          A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 7).ult 128#64 = true ∨ (val >>> 7).ult 128#64 = false := by
    cases (val >>> 7).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs (varintContByte val)
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed' (mid := (blkPl_10).base + bv% (512))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte val) hlt]
      exact hnext _ curCap curPtr v48 v40
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced', arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply SepWPp.of_sepWP_cs_placed' (mid := (blkPl_10).base + bv% (136))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte val) hlt]
      exact hnext _ curCap curPtr v48 v40
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced', arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed' (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    refine step_doReserve_call_placed A H hdoReserve v curCap curPtr sp
      ((blkPl_10).base + bv% (104)) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [EncVarintCalleeSavedPlaced', arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge
    have hlen1 := bv_len_add_one curBs (varintContByte val)
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq :
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte val]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte val]) ∗
          A.pool ∗ stackAt (sp - 48#64) resStack) ∗
          (((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F) =
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte val]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte val]) ∗
          ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗
          A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F := by ac_rfl
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed' (mid := (blkPl_10).base + bv% (512))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step'
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte val) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced', arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply SepWPp.of_sepWP_cs_placed' (mid := (blkPl_10).base + bv% (136))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step'
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte val) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced', arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)

theorem step_encVarint_s2_placed [LibsignalPlacement] {resStack : Nat} (A : RustAlloc)
    (H : String → Option (State → State))
    {s0 s : State}
    (hdoReserve : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H)
      (lsmpl.base 13) (doReserveSpecWithPlaced' resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_10).base + 136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr)
    (hcs : EncVarintCalleeSavedPlaced' s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 14).ult 128#64 then
        (blkPl_10).base + 512#64
      else
        (blkPl_10).base + 252#64) →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 14).ult 128#64 then val >>> 14 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length →
      sm.readReg64 .x9 = nextCap →
      sm.readReg64 .x10 = nextPtr →
      EncVarintCalleeSavedPlaced' s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 7)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗
          A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 14).ult 128#64 = true ∨ (val >>> 14).ult 128#64 = false := by
    cases (val >>> 14).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 7))
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed' (mid := (blkPl_10).base + bv% (512))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 7)) hlt]
      exact hnext _ curCap curPtr v48 v40
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced', arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply SepWPp.of_sepWP_cs_placed' (mid := (blkPl_10).base + bv% (252))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 7)) hlt]
      exact hnext _ curCap curPtr v48 v40
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced', arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed' (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    refine step_doReserve_call_placed A H hdoReserve v curCap curPtr sp
      ((blkPl_10).base + bv% (216)) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [EncVarintCalleeSavedPlaced', arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge
    have hx19m' : sm.readReg64 .x19 = v := by simp only [arm64_norm, *]
    have hx20m' : sm.readReg64 .x20 =
        BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 val) >>> 7)) |||
          4294967168#64 := by
      simp only [arm64_norm, zext64_trunc32_orr_mask, *]
    have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 7))
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq :
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte (val >>> 7)]) ∗
          A.pool ∗ stackAt (sp - 48#64) resStack) ∗
          (((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F) =
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte (val >>> 7)]) ∗
          ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ val) ∗
          A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F := by ac_rfl
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed' (mid := (blkPl_10).base + bv% (512))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step'
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 7)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v48 val
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced', arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply SepWPp.of_sepWP_cs_placed' (mid := (blkPl_10).base + bv% (252))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step'
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 7)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v48 val
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced', arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)

theorem step_encVarint_s3_placed [LibsignalPlacement] {resStack : Nat} (A : RustAlloc)
    (H : String → Option (State → State))
    {s0 s : State}
    (hdoReserve : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H)
      (lsmpl.base 13) (doReserveSpecWithPlaced' resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_10).base + 252#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr)
    (hcs : EncVarintCalleeSavedPlaced' s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 21).ult 128#64 then
        (blkPl_10).base + 512#64
      else
        (blkPl_10).base + 360#64) →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 21).ult 128#64 then val >>> 21 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length →
      sm.readReg64 .x9 = nextCap →
      sm.readReg64 .x12 = val >>> 28 →
      EncVarintCalleeSavedPlaced' s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 14)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗
          A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 21).ult 128#64 = true ∨ (val >>> 21).ult 128#64 = false := by
    cases (val >>> 21).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 14))
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed' (mid := (blkPl_10).base + bv% (512))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 14)) hlt]
      exact hnext _ curCap curPtr v48 v40
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced', arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply SepWPp.of_sepWP_cs_placed' (mid := (blkPl_10).base + bv% (360))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 14)) hlt]
      exact hnext _ curCap curPtr v48 v40
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced', arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed' (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    refine step_doReserve_call_placed A H hdoReserve v curCap curPtr sp
      ((blkPl_10).base + bv% (328)) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [EncVarintCalleeSavedPlaced', arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge
    have hx19m' : sm.readReg64 .x19 =
        BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 val) >>> 14)) |||
          4294967168#64 := by
      simp only [arm64_norm, zext64_trunc32_orr_mask, *]
    have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 14))
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq :
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte (val >>> 14)]) ∗
          A.pool ∗ stackAt (sp - 48#64) resStack) ∗
          (((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F) =
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte (val >>> 14)]) ∗
          ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗
          A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F := by ac_rfl
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed' (mid := (blkPl_10).base + bv% (512))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step'
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 14)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced', arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply SepWPp.of_sepWP_cs_placed' (mid := (blkPl_10).base + bv% (360))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step'
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 14)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced', arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)

end CryptoVerification.LibsignalTripleRatchet.Prost
