/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Heap/header helpers, protobuf bounds, and callee wrappers for `SignalMessage::try_from` post-loop
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Wire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Heap and header unpacking helpers for `wireSignalMessageOf` -/

/-- The heap part of `vecU8At A v cap ptr bs` without the 24-byte `vecHeader`. -/
def vecU8Buf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8At_eq_header_buf (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs :=
  rfl

/-- Heap ownership of an `Option<Vec<u8>>` after reading its 24-byte header `(cap, ptr, len)`. -/
def optVecU8Buf (A : RustAlloc) (cap ptr len : BitVec 64) : Option (List (BitVec 8)) → SepProp
  | none => ⌜cap = noneCap⌝
  | some bs => ⌜len = BitVec.ofNat 64 bs.length⌝ ∗ vecU8Buf A cap ptr bs

theorem vecHeader_entails_memRegion24 (a cap ptr len : BitVec 64) :
    vecHeader a cap ptr len ⊢ memRegion a 24 := by
  unfold vecHeader
  rw [show (24 : Nat) = 8 + (8 + 8) by decide,
    memRegion_split a 8 16 (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion a cap)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 8#64) ptr)
      (pointsTo64_entails_memRegion (a + 16#64) len))

theorem optVecU8At_entails_header_buf (A : RustAlloc) (pin : VecPin) (a : BitVec 64)
    (opt : Option (List (BitVec 8))) :
    optVecU8At A pin a opt ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ len : BitVec 64,
        vecHeader a cap ptr len ∗ optVecU8Buf A cap ptr len opt := by
  cases opt with
  | none =>
    unfold optVecU8At optVecU8Buf vecHeader
    rw [show (16 : Nat) = 8 + 8 by decide,
      memRegion_split (a + 8#64) 8 8 (by decide),
      memRegion_eight, memRegion_eight]
    simp only [BitVec.add_assoc, BitVec.reduceAdd,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Entails.sepExists_elim fun len => Entails.sepExists_elim fun ptr => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro noneCap)
    refine Entails.trans ?_ (Entails.sepExists_intro ptr)
    refine Entails.trans ?_ (Entails.sepExists_intro len)
    simp only [pure_true, sepConj_emp]
    change (a ↦₆₄ noneCap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len) ⊢
      (a ↦₆₄ noneCap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len)
    exact Entails.refl _
  | some bs =>
    unfold optVecU8At optVecU8Buf vecU8At vecU8Buf
    refine Entails.trans ?_ (Entails.sepExists_intro pin.cap)
    refine Entails.trans ?_ (Entails.sepExists_intro pin.ptr)
    refine Entails.trans ?_ (Entails.sepExists_intro (BitVec.ofNat 64 bs.length))
    simp only [pure_true, emp_sepConj]
    exact Entails.refl _

/-- Pure relation between the `(tag, val)` 32-bit words of an `Option<u32>` slot and its value. -/
def optU32TagVal (tag val : BitVec 32) : Option (BitVec 32) → Prop
  | none => tag = 0#32
  | some v => tag = 1#32 ∧ val = v

theorem pointsTo32_pair_entails_memRegion8 (a : BitVec 64) (w0 w1 : BitVec 32) :
    (a ↦₃₂ w0) ∗ ((a + 4#64) ↦₃₂ w1) ⊢ memRegion a 8 := by
  rw [pointsTo32_pair]
  exact pointsTo64_entails_memRegion a (w1 ++ w0)

theorem memRegion_four_entails (a : BitVec 64) :
    memRegion a 4 ⊢ ∃∗ v : BitVec 32, a ↦₃₂ v := by
  rw [memRegion_eq_exists_bytes a 4 (by decide)]
  refine Entails.sepExists_elim fun bs => Entails.pure_left fun hlen => ?_
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> try simp at hlen
  rw [pointsToBytes4_eq_pointsTo32]
  exact Entails.sepExists_intro (b3 ++ b2 ++ b1 ++ b0)

theorem optU32At_entails_tag_val (a : BitVec 64) (opt : Option (BitVec 32)) :
    optU32At a opt ⊢
      ∃∗ tag : BitVec 32, ∃∗ val : BitVec 32,
        ⌜optU32TagVal tag val opt⌝ ∗ (a ↦₃₂ tag) ∗ ((a + 4#64) ↦₃₂ val) := by
  cases opt with
  | none =>
    unfold optU32At optU32TagVal
    refine Entails.trans (sepConj_mono_right (memRegion_four_entails (a + 4#64))) ?_
    simp only [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun val => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro 0#32)
    refine Entails.trans ?_ (Entails.sepExists_intro val)
    simp only [pure_true, emp_sepConj]
    exact Entails.refl _
  | some v =>
    unfold optU32At optU32TagVal
    refine Entails.trans ?_ (Entails.sepExists_intro 1#32)
    refine Entails.trans ?_ (Entails.sepExists_intro v)
    simp only [and_self, pure_true, emp_sepConj]
    exact Entails.refl _

/-! ## Pure protobuf field-length bounds from `decode` -/

theorem mergeBytes_len_le {wt : WireType} {bs out rest : List (BitVec 8)}
    (h : mergeBytes wt bs = some (out, rest)) :
    out.length ≤ bs.length := by
  unfold mergeBytes at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · rename_i len rest0 hp
      split at h
      · contradiction
      · rename_i hlt
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rcases decodeVarint_suffix hp with ⟨k, hk1, hk2, rfl⟩
        simp only [List.length_drop] at hlt ⊢
        have htake : ((bs.drop k).take len.toNat).length = len.toNat :=
          List.length_take_of_le (by simp only [List.length_drop]; omega)
        omega

/-- All four byte-vector fields of `m` have length at most `N`. -/
def MsgFieldsLe (N : Nat) (m : ProtoSignalMessage) : Prop :=
  (m.ratchetKey.getD []).length ≤ N ∧
  (m.ciphertext.getD []).length ≤ N ∧
  (m.pqRatchet.getD []).length ≤ N ∧
  (m.addresses.getD []).length ≤ N

theorem mergeField_fields_le {N : Nat} {m m' : ProtoSignalMessage} {tag : Nat} {wt : WireType}
    {bs rest : List (BitVec 8)}
    (hm : MsgFieldsLe N m) (hbs : bs.length ≤ N)
    (h : mergeField m tag wt bs = some (m', rest)) :
    MsgFieldsLe N m' := by
  rcases hm with ⟨h1, h2, h3, h4⟩
  unfold mergeField at h
  split at h <;> simp only [Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
  · rcases h with ⟨v, r, hv, ⟨rfl, rfl⟩⟩
    exact ⟨Nat.le_trans (mergeBytes_len_le hv) hbs, h2, h3, h4⟩
  · rcases h with ⟨v, r, _, ⟨rfl, rfl⟩⟩
    exact ⟨h1, h2, h3, h4⟩
  · rcases h with ⟨v, r, _, ⟨rfl, rfl⟩⟩
    exact ⟨h1, h2, h3, h4⟩
  · rcases h with ⟨v, r, hv, ⟨rfl, rfl⟩⟩
    exact ⟨h1, Nat.le_trans (mergeBytes_len_le hv) hbs, h3, h4⟩
  · rcases h with ⟨v, r, hv, ⟨rfl, rfl⟩⟩
    exact ⟨h1, h2, Nat.le_trans (mergeBytes_len_le hv) hbs, h4⟩
  · rcases h with ⟨v, r, hv, ⟨rfl, rfl⟩⟩
    exact ⟨h1, h2, h3, Nat.le_trans (mergeBytes_len_le hv) hbs⟩
  · rcases h with ⟨r, _, ⟨rfl, rfl⟩⟩
    exact ⟨h1, h2, h3, h4⟩

theorem decodeLoop_fields_le :
    ∀ (fuel N : Nat) (m m' : ProtoSignalMessage) (bs : List (BitVec 8)),
      MsgFieldsLe N m → bs.length ≤ N →
      decodeLoop fuel m bs = some m' →
      MsgFieldsLe N m'
  | 0, _, _, _, [], hm, _, h => by
    simp only [decodeLoop, Option.some.injEq] at h; subst h; exact hm
  | 0, _, _, _, _ :: _, _, _, h => by simp [decodeLoop] at h
  | fuel + 1, _, m, m', [], hm, _, h => by
    simp only [decodeLoop, Option.some.injEq] at h; subst h; exact hm
  | fuel + 1, N, m, m', b :: rest, hm, hbs, h => by
    simp only [decodeLoop] at h
    split at h
    · contradiction
    · rename_i tag wt rest1 hk
      split at h
      · contradiction
      · rename_i m1 rest2 hmr
        rcases decodeKey_suffix hk with ⟨k1, hk1_pos, hk1_le, rfl, _, _⟩
        have hbs1 : ((b :: rest).drop k1).length ≤ N := by
          simp only [List.length_drop]; omega
        have hm1 := mergeField_fields_le hm hbs1 hmr
        rcases mergeField_suffix hmr with ⟨k2, hk2_le, rfl⟩
        have hbs2 : (((b :: rest).drop k1).drop k2).length ≤ N := by
          simp only [List.length_drop] at hbs1 ⊢; omega
        exact decodeLoop_fields_le fuel N m1 m' (((b :: rest).drop k1).drop k2) hm1 hbs2 h

theorem decode_field_lengths {bs : List (BitVec 8)} {m' : ProtoSignalMessage}
    (h : decode bs = some m') :
    MsgFieldsLe bs.length m' := by
  refine decodeLoop_fields_le bs.length bs.length emptyProtoSignalMessage m' bs ?_ (Nat.le_refl _) h
  simp [MsgFieldsLe, emptyProtoSignalMessage]

/-! ## Buffer deallocation and `into_boxed_slice` helpers for `vecU8Buf` / `optVecU8Buf` -/

theorem vecU8Buf_dealloc (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hcap : cap ≠ 0#64) :
    vecU8Buf A cap ptr bs ⊢
      ⌜0 < cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  unfold vecU8Buf
  have hcap0 : (cap = 0) = False := eq_false hcap
  simp only [hcap0, ↓reduceIte]
  refine Entails.pure_left fun ⟨hle, hlt, hptr⟩ => ?_
  have hpos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap (BitVec.eq_of_toNat_eq hc))
  rw [pure_true_emp ⟨hpos, hlt, hptr⟩, emp_sepConj]
  refine sepConj_mono_right ?_
  have hsplit : cap.toNat = bs.length + (cap.toNat - bs.length) := (Nat.add_sub_of_le hle).symm
  conv => rhs; rw [hsplit, memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)]
  exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)

/-- Dichotomy for deallocating any `optVecU8Buf A cap ptr len opt`: either `active = true`
(`0 < cap.toNat < 2^63`, owning `A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat`) or
`active = false` (`cap = noneCap ∨ cap = 0#64`, owning `emp`). -/
def deallocSlot (A : RustAlloc) (cap ptr : BitVec 64) (active : Bool) : SepProp :=
  if active then
    ⌜0 < cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat
  else
    ⌜cap = noneCap ∨ cap = 0#64⌝

theorem optVecU8Buf_entails_deallocSlot (A : RustAlloc) (cap ptr len : BitVec 64)
    (opt : Option (List (BitVec 8))) :
    optVecU8Buf A cap ptr len opt ⊢ ∃∗ active : Bool, deallocSlot A cap ptr active := by
  cases opt with
  | none =>
    change ⌜cap = noneCap⌝ ⊢ ∃∗ active : Bool, deallocSlot A cap ptr active
    refine Entails.pure_left_only fun hcap => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro false)
    unfold deallocSlot
    simp only [Bool.false_eq_true, ↓reduceIte, pure_true_emp (Or.inl hcap)]
    exact Entails.refl _
  | some bs =>
    change ⌜len = BitVec.ofNat 64 bs.length⌝ ∗ vecU8Buf A cap ptr bs ⊢
      ∃∗ active : Bool, deallocSlot A cap ptr active
    refine Entails.pure_left fun _ => ?_
    by_cases hcap : cap = 0#64
    · subst hcap
      have h0 : vecU8Buf A 0#64 ptr bs = ⌜bs = [] ∧ ptr ≠ 0⌝ := by simp [vecU8Buf]
      rw [h0]
      refine Entails.pure_left_only fun _ => ?_
      refine Entails.trans ?_ (Entails.sepExists_intro false)
      change emp ⊢ ⌜0#64 = noneCap ∨ 0#64 = 0#64⌝
      rw [pure_true_emp (Or.inr rfl)]
      exact Entails.refl _
    · refine Entails.trans (vecU8Buf_dealloc A cap ptr bs hcap) ?_
      refine Entails.trans ?_ (Entails.sepExists_intro true)
      unfold deallocSlot
      simp only [↓reduceIte]
      exact Entails.refl _

theorem cap_slt_one_of_pos {cap : BitVec 64} (hpos : 0 < cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    BitVec.slt cap 1#64 = false := by
  have h1 : 0#64 < cap := by simpa [BitVec.lt_def] using hpos
  have h2 : cap < 0x8000000000000000#64 := by simpa [BitVec.lt_def] using hlt
  bv_kernel

theorem cap_sub1_add3_hi_of_pos {cap : BitVec 64}
    (hpos : 0 < cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    ConditionHolds .HI (addsPState64 (cap - 1#64) 3#64) = false := by
  have h1 : 0#64 < cap := by simpa [BitVec.lt_def] using hpos
  have h2 : cap < 0x8000000000000000#64 := by simpa [BitVec.lt_def] using hlt
  unfold ConditionHolds addsPState64 AddWithCarry64
  dsimp only
  bv_kernel

theorem cap_sub1_add3_hi_of_pos' {cap : BitVec 64}
    (hpos : 0 < cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    ConditionHolds .HI (addsPState64 (cap + bv% (2 ^ 64 - 1)) 3#64) = false := by
  have heq : cap + bv% (2 ^ 64 - 1) = cap - 1#64 := by bv_kernel
  rw [heq]
  exact cap_sub1_add3_hi_of_pos hpos hlt

@[local simp, local arm64_norm, local wp_norm]
theorem cap_sub1_add3_hi_noneCap :
    ConditionHolds .HI (addsPState64 (noneCap - 1#64) 3#64) = true := by
  unfold ConditionHolds addsPState64 AddWithCarry64; decide

@[local simp, local arm64_norm, local wp_norm]
theorem cap_sub1_add3_hi_zero :
    ConditionHolds .HI (addsPState64 (-1#64) 3#64) = true := by
  unfold ConditionHolds addsPState64 AddWithCarry64; decide

theorem cap_add2_ne_of_lt {cap : BitVec 64} (hlt : cap.toNat < 2 ^ 63) :
    (cap + 2#64 != 0#64) = true := by
  have h2 : cap < 0x8000000000000000#64 := by simpa [BitVec.lt_def] using hlt
  bv_kernel

theorem cap_add1_eq_of_lt {cap : BitVec 64} (hlt : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  have h2 : cap < 0x8000000000000000#64 := by simpa [BitVec.lt_def] using hlt
  bv_kernel

theorem vecU8Buf_repack (A : RustAlloc) (v cap ptr len : BitVec 64) (bs : List (BitVec 8)) :
    vecHeader v cap ptr len ∗ ⌜len = BitVec.ofNat 64 bs.length⌝ ∗ vecU8Buf A cap ptr bs ⊢
      vecU8At A v cap ptr bs := by
  rw [sepConj_left_comm (vecHeader v cap ptr len)]
  refine Entails.pure_left fun hlen => ?_
  subst hlen
  exact Entails.refl _

/-- Call a non-panicking callee (`onPanic = ⌜False⌝`, `onExit = ⌜False⌝`) inside `SepWPp`. -/
theorem SepWPp.call_noPanic_tryFrom {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {s0 s : Arm64.State} {P T F : SepProp} {φ : Prop}
    {Q : Arm64.State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F := by sep_focus)
    (hnext : ∀ sf : Arm64.State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → img.FrozenLoaded sf → sf.symtab = img.symtab →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (tryFromQp s0))
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q (tryFromQp s0) := by
  intro R' hm hL
  have hpre : s.mem ⊨ (spec.inImage img).pre x s ∗ (F ∗ R') := by
    dsimp only [Spec.inImage]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hF, hsym⟩, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hspm_align : sm.spAligned = true := by
      rw [Arm64.State.spAligned, hspm, ← Arm64.State.spAligned]; exact hsp
    obtain ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hqf, hvf⟩ | hpanf⟩ :=
      hnext sm hpcm hrunm hspm hspm_align (hsteps.frozenLoaded hF)
        (hsteps.symtab_eq.trans hsym) hcsm R' hpost (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps',
        Or.inl ⟨hpcf, hrunf, Pf, hmf, hqf, hvf.trans hcsm.2.2.2.2.2.2.2.2.2.2.2⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr hpanf⟩
  · dsimp only [Spec.inImage] at hpost
    rw [hpan sm] at hpost
    exact (allowPanic_not_exited hpost).elim
  · dsimp only [Spec.inImage] at hpost
    rw [hexit sm code] at hpost
    exact (allowPanic_not_exited hpost).elim
  · dsimp only [Spec.inImage] at hpost
    rw [hoom sm] at hpost
    exact (allowPanic_not_exited hpost).elim

/-! ## Negative-offset callee wrappers from `try_from` (`0x25868`) -/

theorem fnAddr_sub_rel {b : BitVec 64} {H : String → Option (State → State)}
    {fn callee : String} {off1 off2 : Nat} {k : BitVec 64}
    (h1 : libsignalSessionCode.fnOff fn = off1)
    (h2 : libsignalSessionCode.fnOff callee = off2)
    (hk : BitVec.ofNat 64 off1 + k = BitVec.ofNat 64 off2) :
    (libsignalSessionCode.rebase b H).fnAddr fn + k =
      (libsignalSessionCode.rebase b H).fnAddr callee := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, h1, h2, ← hk]
  bv_omega

theorem dropDecodeError_ok_sub {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : DropDecodeErrorOkW img C A ctl abs) :
    subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]") - (ls_off% "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from")))
      ((dropDecodeErrorSpecX A).inImage img) := by
  rw [fnAddr_sub_rel (ls_lemma% fnOff "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from") (ls_lemma% fnOff "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]") (by decide)]
  exact h

theorem dropSpe_ok_sub {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : DropSpeOkW img C A ctl abs) :
    subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]") - (ls_off% "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from")))
      ((dropSpeSpecX A).inImage img) := by
  rw [fnAddr_sub_rel (ls_lemma% fnOff "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from") (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]") (by decide)]
  exact h

theorem intoBoxedSlice_ok_sub {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : IntoBoxedSliceOk img C A ctl abs) :
    subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + bv% (2 ^ 64 + (ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice") - (ls_off% "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from")))
      ((intoBoxedSliceSpecX A).inImage img) := by
  rw [fnAddr_sub_rel (ls_lemma% fnOff "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from") (ls_lemma% fnOff "<alloc::vec::Vec<u8>>::into_boxed_slice") (by decide)]
  exact h

theorem tryCloneFromRef_ok_sub {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : TryCloneFromRefOk img C A ctl abs) :
    subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + bv% (2 ^ 64 + (ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in") - (ls_off% "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from")))
      ((tryCloneFromRefSpecX A).inImage img) := by
  rw [fnAddr_sub_rel (ls_lemma% fnOff "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from") (ls_lemma% fnOff "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in") (by decide)]
  exact h

theorem vecU8Buf_zero (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A 0#64 ptr bs = ⌜bs = [] ∧ ptr ≠ 0⌝ := by
  simp [vecU8Buf]

macro "tryFrom_fetches2 " b:term:max _C:term:max _ctl:term:max abs:term:max
    k0:num len:num : tactic =>
  `(tactic| tryFrom_fetches $b (Rust.withPanics $abs) $k0 $len)

/-! ## Shared cleanup tails in post-loop (`+0x698`, `+0x684`, `+0x668`, `+0x64c`, `+0x640` → `+0x440`) -/

/-- State invariant at the shared epilogue entry `+0x440` (`0x25ca8`, `entry + 1088#64`). -/
def PostEpilogueState (img : Obj.Image) (s0 : State) (sp' : BitVec 64) (s : State) : Prop :=
  s.sp = sp' ∧ s.spAligned = true ∧ img.FrozenLoaded s ∧ s.symtab = img.symtab ∧ s.trace = s0.trace

theorem PostEpilogueState.of_steps {img : Obj.Image} {s0 s1 s2 : State} {sp' : BitVec 64}
    (hF : img.FrozenLoaded s2) (hsym : s2.symtab = img.symtab)
    (hsp : s2.sp = sp') (hsp0 : s1.sp = sp') (hal : s1.spAligned = true)
    (htr : s2.trace = s0.trace) :
    PostEpilogueState img s0 sp' s2 := by
  refine ⟨hsp, ?_, hF, hsym, htr⟩
  rw [State.spAligned, hsp, ← hsp0, ← State.spAligned]
  exact hal

namespace TryFromPostSpFacts

theorem tryFrom_dealloc_ok {A : RustAlloc} {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooksW img A abs) :
    subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  sub_ok_at_of_fnAddr hA.dealloc tryFromName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))

theorem sp_writeReg32_gpr (s : State) (idx : BitVec 5) (v : BitVec 32) :
    (s.writeReg32 (Reg.gpr idx) v).sp = s.sp := rfl

theorem spAligned_of_sp_eq {s1 s2 : State} (h : s1.sp = s2.sp) (hal : s2.spAligned = true) :
    s1.spAligned = true := by
  rw [State.spAligned, h, ← State.spAligned]
  exact hal

end TryFromPostSpFacts

macro "tryFromPost_sp_step" : tactic =>
  `(tactic| repeat' (first
    | rw [State.sp_setPC]
    | rw [State.sp_advancePC]
    | rw [State.sp_setPState]
    | rw [State.sp_setMem]
    | rw [State.sp_writeReg64_gpr]
    | rw [TryFromPostSpFacts.sp_writeReg32_gpr]
    | rw [State.sp_writeVReg128]
    | rw [State.sp_writeVReg64]
    | rw [State.sp_writeVReg32]))

macro "tryFromPost_sp" : tactic => `(tactic| (tryFromPost_sp_step; try rfl))
macro "tryFromPost_sp " "[" h1:term "]" : tactic =>
  `(tactic| (tryFromPost_sp_step; try rw [$h1:term]; tryFromPost_sp_step; try rfl))
macro "tryFromPost_sp " "[" h1:term "," h2:term "]" : tactic =>
  `(tactic| (tryFromPost_sp_step; try rw [$h1:term]; tryFromPost_sp_step; try rw [$h2:term]; tryFromPost_sp_step; try rfl))
macro "tryFromPost_sp " "[" h1:term "," h2:term "," h3:term "]" : tactic =>
  `(tactic| (tryFromPost_sp_step; try rw [$h1:term]; tryFromPost_sp_step; try rw [$h2:term]; tryFromPost_sp_step; try rw [$h3:term]; tryFromPost_sp_step; try rfl))
macro "tryFromPost_sp " "[" h1:term "," h2:term "," h3:term "," h4:term "]" : tactic =>
  `(tactic| (tryFromPost_sp_step; try rw [$h1:term]; tryFromPost_sp_step; try rw [$h2:term]; tryFromPost_sp_step; try rw [$h3:term]; tryFromPost_sp_step; try rw [$h4:term]; tryFromPost_sp_step; try rfl))

macro "tryFromPost_sp_align " h:term : tactic =>
  `(tactic| exact TryFromPostSpFacts.spAligned_of_sp_eq (by tryFromPost_sp) $h)
macro "tryFromPost_sp_align " "[" h1:term "] " h:term : tactic =>
  `(tactic| exact TryFromPostSpFacts.spAligned_of_sp_eq (by tryFromPost_sp [$h1]) $h)
macro "tryFromPost_sp_align " "[" h1:term "," h2:term "] " h:term : tactic =>
  `(tactic| exact TryFromPostSpFacts.spAligned_of_sp_eq (by tryFromPost_sp [$h1, $h2]) $h)

/-! ## Relocatable `[LibsignalPlacement]` Call Combinator and Post-Epilogue State (Block `85`) -/

theorem SepWPp.call_noPanic_tryFrom_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {s0 s : Arm64.State} {P T F : SepProp} {φ : Prop}
    {Q : Arm64.State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F := by sep_focus)
    (hnext : ∀ sf : Arm64.State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → LibsignalCodeRoLoaded lsmpl sf.mem →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (tryFromQp s0))
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q (tryFromQp s0) := by
  intro R' hm hL
  have hpre : s.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F ∗ R') := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · dsimp only [withLsCodeRoLoaded] at hpost
    have hcl_m := hcl.of_keepsFrozen hsteps.keepsFrozen
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hspm_align : sm.spAligned = true := by
      rw [Arm64.State.spAligned, hspm, ← Arm64.State.spAligned]; exact hsp
    obtain ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hqf, hvf⟩ | hpanf⟩ :=
      hnext sm hpcm hrunm hspm hspm_align hcl_m hcsm R' hpost (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps',
        Or.inl ⟨hpcf, hrunf, Pf, hmf, hqf, hvf.trans hcsm.2.2.2.2.2.2.2.2.2.2.2⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr hpanf⟩
  · dsimp only [withLsCodeRoLoaded] at hpost
    rw [hpan sm] at hpost
    exact (allowPanic_not_exited hpost).elim
  · dsimp only [withLsCodeRoLoaded] at hpost
    rw [hexit sm code] at hpost
    exact (allowPanic_not_exited hpost).elim
  · dsimp only [withLsCodeRoLoaded] at hpost
    rw [hoom sm] at hpost
    exact (allowPanic_not_exited hpost).elim

def PostEpilogueStatePlaced [LibsignalPlacement] (s0 : State) (sp' : BitVec 64) (s : State) : Prop :=
  s.sp = sp' ∧ s.spAligned = true ∧ LibsignalCodeRoLoaded lsmpl s.mem ∧ s.trace = s0.trace

theorem PostEpilogueStatePlaced.of_steps [LibsignalPlacement] {s0 s1 s2 : State} {sp' : BitVec 64}
    (hcl : LibsignalCodeRoLoaded lsmpl s2.mem)
    (hsp : s2.sp = sp') (hsp0 : s1.sp = sp') (hal : s1.spAligned = true)
    (htr : s2.trace = s0.trace) :
    PostEpilogueStatePlaced s0 sp' s2 := by
  refine ⟨hsp, ?_, hcl, htr⟩
  rw [State.spAligned, hsp, ← hsp0, ← State.spAligned]
  exact hal

end CryptoVerification.LibsignalTripleRatchet.Wire
