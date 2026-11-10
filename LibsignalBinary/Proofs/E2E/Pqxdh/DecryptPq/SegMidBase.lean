/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Defs
import all Init.Data.String.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Calls
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.CallsTrap
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegC

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.DecryptPq

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc
attribute [local wp_norm] BitVec.add_assoc

open Lean Elab Tactic in
elab "code_fetches_from " codeId:ident decPrefix:ident b:term:max H:term:max hfn:ident
    off:num k0:num len:num : tactic => do
  let off := off.getNat
  let k0 := k0.getNat
  let len := len.getNat
  let codeBase := codeId.getId.eraseMacroScopes
  let decBase := decPrefix.getId.eraseMacroScopes
  let fetchEntry := mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let hex := String.ofList (Nat.toDigits 16 (off + k))
    let dec := mkIdent (decBase.appendAfter s!"_decode_0x{hex}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

abbrev H2 (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : String → Option (State → State) :=
  Rust.withPanics (tripleRatchetExterns C ctl abs)

macro "decrypt_fetches " b:term:max H:term:max hfn:ident k0:num len:num : tactic =>
  `(tactic| code_fetches_from CryptoVerification.libsignalSessionCode
    libsignalTripleRatchetBin $b $H
    $hfn 0x6eff8 $k0 $len)

namespace BS8

@[irreducible] noncomputable def fnAddr_tryDecrypt (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : BitVec 64 :=
  (tripleRatchetProgAt b C ctl abs).fnAddr tryDecryptName

theorem fnAddr_tryDecrypt_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr tryDecryptName = fnAddr_tryDecrypt b C ctl abs := by
  unfold fnAddr_tryDecrypt
  rfl

theorem fnOff_spqrRecv :
    CryptoVerification.libsignalSessionCode.fnOff spqrRecvName = num% (ls_off% "spqr::recv") :=
  (ls_lemma% fnOff "spqr::recv")

theorem fnOff_formatInner :
    CryptoVerification.libsignalSessionCode.fnOff formatInnerName =
      num% (ls_off% "alloc::fmt::format::format_inner") :=
  (ls_stub% "alloc::fmt::format::format_inner")

theorem fnOff_addrDisplay :
    CryptoVerification.libsignalSessionCode.fnOff addrDisplayName = 259304 :=
  CryptoVerification.libsignalSessionCode_fnOff_0x3f4e8

theorem lt_two_pow_64_of_lt_text {n : Nat} (h : n < num% (ls_field% textEnd)) : n < 2 ^ 64 :=
  Nat.lt_trans h (by decide)

end BS8

theorem pointsTo64_split32 (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) = (a ↦₃₂ v.truncate 32) ∗ ((a + 4#64) ↦₃₂ v.extractLsb' 32 32) :=
  ProofLib.pointsTo64_split32' a v

theorem pointsTo32_merge64 (a : BitVec 64) (lo hi : BitVec 32) :
    ((a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi)) = (a ↦₆₄ (hi ++ lo)) := by
  rw [pointsTo64_split32]
  have h1 : (hi ++ lo).truncate 32 = lo := by bv_slice
  have h2 : (hi ++ lo).extractLsb' 32 32 = hi := by bv_slice
  rw [h1, h2]

theorem pts64_to_mr (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) ⊢ memRegion a 8 := by
  rw [memRegion_eight]
  exact Entails.sepExists_intro v

macro "fold_mr8 " addr:term : tactic =>
  `(tactic| refine SepWP.focus_weaken (pts64_to_mr $addr _) (by sep_focus) ?_)

@[local simp, local wp_norm, local arm64_norm]
theorem extractLsb0_8_append56 (hi : BitVec 56) (d : BitVec 8) :
    (hi ++ d).extractLsb' 0 8 = d := by bv_slice

theorem pointsTo8_memRegion7_to_64 (a : BitVec 64) (d : BitVec 8) :
    ((a ↦₈ d) ∗ memRegion (a + 1#64) 7) ⊢ ∃∗ hi : BitVec 56, a ↦₆₄ (hi ++ d) := by
  refine IsBlock.entails
    ((IsBlock.pointsTo8 a d).sepConj (IsBlock.memRegion (a + 1#64) 7) rfl (by decide))
    (IsBlock.sepExists fun hi : BitVec 56 => IsBlock.pointsTo64 a (hi ++ d)) ?_
  rintro m ⟨hd, -⟩
  refine ⟨(m.read64 a).extractLsb' 8 56, ?_⟩
  have h8 : (m.read64 a).extractLsb' 0 8 = m.read8 a := by
    simp only [Memory.read64]
    have h0 : a + 0#64 = a := by bv_lin
    rw [h0]
    generalize m.read8 a = x0
    generalize m.read8 (a + 1#64) = x1
    generalize m.read8 (a + 2#64) = x2
    generalize m.read8 (a + 3#64) = x3
    generalize m.read8 (a + 4#64) = x4
    generalize m.read8 (a + 5#64) = x5
    generalize m.read8 (a + 6#64) = x6
    generalize m.read8 (a + 7#64) = x7
    bv_bits
  rw [← hd, ← h8]
  generalize m.read64 a = w
  bv_slice

theorem pointsTo64_to_8_memRegion7 (a : BitVec 64) (hi : BitVec 56) (d : BitVec 8) :
    (a ↦₆₄ (hi ++ d)) ⊢ (a ↦₈ d) ∗ memRegion (a + 1#64) 7 := by
  refine IsBlock.entails
    (IsBlock.pointsTo64 a (hi ++ d))
    ((IsBlock.pointsTo8 a d).sepConj (IsBlock.memRegion (a + 1#64) 7) rfl (by decide)) ?_
  intro m hw
  refine ⟨?_, trivial⟩
  have h8 : m.read8 a = (m.read64 a).extractLsb' 0 8 := by
    simp only [Memory.read64]
    have h0 : a + 0#64 = a := by bv_lin
    rw [h0]
    generalize m.read8 a = x0
    generalize m.read8 (a + 1#64) = x1
    generalize m.read8 (a + 2#64) = x2
    generalize m.read8 (a + 3#64) = x3
    generalize m.read8 (a + 4#64) = x4
    generalize m.read8 (a + 5#64) = x5
    generalize m.read8 (a + 6#64) = x6
    generalize m.read8 (a + 7#64) = x7
    bv_bits
  rw [h8, hw, extractLsb0_8_append56]

theorem mr_cut_add (a : BitVec 64) (c n k : Nat) (h : n + k ≤ 2 ^ 64) :
    memRegion (a + BitVec.ofNat 64 c) (n + k) =
      memRegion (a + BitVec.ofNat 64 c) n ∗ memRegion (a + BitVec.ofNat 64 (c + n)) k := by
  refine memRegion_split' rfl ?_ h
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem stackAt_sub (sp : BitVec 64) (N K : Nat) (hK : K ≤ N := by decide)
    (hN : N < 2 ^ 64 := by decide) :
    stackAt sp N = memRegion (sp - BitVec.ofNat 64 N) (N - K) ∗ stackAt sp K := by
  simp only [stackAt]
  refine memRegion_split' (by omega) ?_ (by omega)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have h1 : N % 2 ^ 64 = N := Nat.mod_eq_of_lt hN
  have h2 : (N - K) % 2 ^ 64 = N - K := Nat.mod_eq_of_lt (by omega)
  have h3 : K % 2 ^ 64 = K := Nat.mod_eq_of_lt (by omega)
  omega

def optKeyRest (A : RustAlloc) (w0 w1 w2 : BitVec 64) (x : Salt) : SepProp :=
  match x with
  | none =>
    ∃∗ isNiche : Bool,
      if isNiche then ⌜w0 = noneCap⌝
      else
        ⌜w0.toNat < 2 ^ 63 ∧ w1 ≠ 0#64 ∧ w2 = 0#64⌝ ∗
        (if w0 = 0#64 then emp else A.live w1 w0.toNat 1 ∗ memRegion w1 w0.toNat)
  | some k =>
    ⌜k.toList.length ≤ w0.toNat ∧ w0.toNat < 2 ^ 63 ∧ w1 ≠ 0#64 ∧
      w2 = BitVec.ofNat 64 k.toList.length⌝ ∗
    (if w0 = 0#64 then emp
     else A.live w1 w0.toNat 1 ∗ (w1 ↦ₛ k.toList) ∗
       memRegion (w1 + BitVec.ofNat 64 k.toList.length) (w0.toNat - k.toList.length))

theorem optKeyAt_split (A : RustAlloc) (a : BitVec 64) (x : Salt) :
    spqrRecvKeyAt A a x ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        optKeyRest A w0 w1 w2 x ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) := by
  cases x with
  | none =>
    simp only [spqrRecvKeyAt, optKeyRest]
    refine Entails.sepExists_elim fun isNiche => ?_
    cases isNiche
    · simp only [Bool.false_eq_true, ↓reduceIte, vecU8, vecU8At, vecHeader,
        List.length_nil, Nat.sub_zero, BitVec.ofNat_eq_ofNat, pointsToBytes_nil,
        emp_sepConj, BitVec.add_zero, sepConj_assoc, sepConj_pure_left_comm]
      refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
      refine Entails.pure_left fun ⟨_, hs, hp⟩ => ?_
      refine Entails.trans ?_ (Entails.sepExists_intro cap)
      refine Entails.trans ?_ (Entails.sepExists_intro ptr)
      refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
      rw [sepExists_sepConj_left]
      refine Entails.trans ?_ (Entails.sepExists_intro false)
      simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      refine Entails.pure_right ⟨hs, hp, trivial⟩ ?_
      rw [← sepConj_assoc, ← sepConj_assoc, sepConj_comm]
      simp only [sepConj_assoc]
      exact Entails.refl _
    · simp only [↓reduceIte]
      rw [memRegion_split (a + 8#64) 8 8 (by decide),
        BitVec.add_assoc, show (8#64 : BitVec 64) + 8#64 = 16#64 by rfl,
        memRegion_eight (a + 8#64), memRegion_eight (a + 16#64)]
      rw [sepExists_sepConj_left, sepExists_sepConj_right]
      refine Entails.sepExists_elim fun w1 => ?_
      rw [sepExists_sepConj_right, sepExists_sepConj_right]
      refine Entails.sepExists_elim fun w2 => ?_
      refine Entails.trans ?_ (Entails.sepExists_intro noneCap)
      refine Entails.trans ?_ (Entails.sepExists_intro w1)
      refine Entails.trans ?_ (Entails.sepExists_intro w2)
      rw [sepExists_sepConj_left]
      refine Entails.trans ?_ (Entails.sepExists_intro true)
      simp only [↓reduceIte]
      refine Entails.pure_right trivial ?_
      exact Entails.refl _
  | some k =>
    simp only [spqrRecvKeyAt, optKeyRest, vecU8, vecU8At, vecHeader]
    refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Entails.pure_left fun h => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro cap)
    refine Entails.trans ?_ (Entails.sepExists_intro ptr)
    refine Entails.trans ?_ (Entails.sepExists_intro (BitVec.ofNat 64 k.toList.length))
    refine Entails.pure_right ⟨h.1, h.2.1, h.2.2, rfl⟩ ?_
    rw [← sepConj_assoc, ← sepConj_assoc, sepConj_comm]
    simp only [sepConj_assoc]
    exact Entails.refl _

theorem optKeyAt_fold (A : RustAlloc) (a w0 w1 w2 : BitVec 64) (x : Salt) :
    optKeyRest A w0 w1 w2 x ∗
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢
    spqrRecvKeyAt A a x := by
  cases x with
  | none =>
    simp only [spqrRecvKeyAt, optKeyRest, sepExists_sepConj_left]
    refine Entails.sepExists_elim fun isNiche => ?_
    cases isNiche
    · simp only [Bool.false_eq_true, ↓reduceIte, vecU8, vecU8At, vecHeader,
        List.length_nil, Nat.sub_zero, BitVec.ofNat_eq_ofNat, pointsToBytes_nil,
        emp_sepConj, BitVec.add_zero, sepConj_assoc]
      refine Entails.pure_left fun ⟨hs, hp, hw2⟩ => ?_
      subst hw2
      refine Entails.trans ?_ (Entails.sepExists_intro false)
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine Entails.trans ?_ (Entails.sepExists_intro w0)
      refine Entails.trans ?_ (Entails.sepExists_intro w1)
      simp only [sepConj_pure_left_comm]
      refine Entails.pure_right ⟨Nat.zero_le _, hs, hp⟩ ?_
      rw [sepConj_comm]
      simp only [sepConj_assoc]
      exact Entails.refl _
    · simp only [↓reduceIte]
      refine Entails.pure_left fun hw0 => ?_
      subst hw0
      refine Entails.trans ?_ (Entails.sepExists_intro true)
      simp only [↓reduceIte]
      rw [memRegion_split (a + 8#64) 8 8 (by decide),
        BitVec.add_assoc, show (8#64 : BitVec 64) + 8#64 = 16#64 by rfl,
        memRegion_eight (a + 8#64), memRegion_eight (a + 16#64)]
      rw [sepExists_sepConj_left, sepExists_sepConj_right]
      refine Entails.trans ?_ (Entails.sepExists_intro w1)
      rw [sepExists_sepConj_right, sepExists_sepConj_right]
      refine Entails.trans ?_ (Entails.sepExists_intro w2)
      exact Entails.refl _
  | some k =>
    simp only [spqrRecvKeyAt, optKeyRest, vecU8, vecU8At, vecHeader, sepConj_assoc]
    refine Entails.pure_left fun ⟨h1, h2, h3, hw2⟩ => ?_
    subst hw2
    refine Entails.trans ?_ (Entails.sepExists_intro w0)
    refine Entails.trans ?_ (Entails.sepExists_intro w1)
    simp only [sepConj_pure_left_comm]
    refine Entails.pure_right ⟨h1, h2, h3⟩ ?_
    rw [sepConj_comm]
    simp only [sepConj_assoc]
    exact Entails.refl _

theorem mkgAt_fold (A : RustAlloc) (r seedCap seedPtr : BitVec 64) (pad1 pad2 : BitVec 32)
    (mkg : MessageKeyGenerator)
    (hseed : mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0) :
    (r ↦₃₂ 1#32) ∗ ((r + 4#64) ↦₃₂ pad1) ∗
    ((r + 8#64) ↦₆₄ seedCap) ∗ ((r + 16#64) ↦₆₄ seedPtr) ∗
    ((r + 24#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
    (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
      (seedPtr ↦ₛ mkg.seed) ∗
      memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
    ((r + 32#64) ↦₆₄ (pad2 ++ mkg.counter)) ⊢
    mkgAt A r mkg := by
  unfold mkgAt vecU8 vecU8At vecHeader
  rw [← pointsTo32_merge64 (r + 32#64) mkg.counter pad2,
    BitVec.add_assoc, show (32#64 : BitVec 64) + 4#64 = 36#64 by rfl]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.trans ?_ (Entails.sepExists_intro seedCap)
  refine Entails.trans ?_ (Entails.sepExists_intro seedPtr)
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  refine Entails.pure_right hseed ?_
  refine sepConj_mono (Entails.refl _) (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
        (sepConj_mono (Entails.refl _) (pointsTo32_entails_memRegion _ _)))))))

theorem reaches_pc_of_sepWP {prog : Program} {target_pc : BitVec 64} {s : State}
    {P R : SepProp} {Q : State → Prop}
    (hmem : s.mem ⊨ P ∗ R)
    (hwp : SepWP prog target_pc s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → Q sf)) :
    reaches_pc prog target_pc s Q := by
  intro hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hmem hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, hq hmf⟩⟩

theorem reaches_pc_of_sepWP_frozen {prog : Program} {img : Obj.Image}
    {mid target : BitVec 64} {s : State} {P P_mid R : SepProp}
    {RegMid Q : State → Prop}
    (hmem : s.mem ⊨ P ∗ R)
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h1 : SepWP prog mid s P (fun sm Pm => (sm.mem ⊨ Pm ∗ R) → RegMid sm ∧ (sm.mem ⊨ P_mid ∗ R)))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      img.FrozenLoaded sm → sm.symtab = img.symtab →
      RegMid sm → SepWP prog target sm P_mid (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → Q sf)) :
    reaches_pc prog target s Q := by
  intro hL
  obtain ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, himp⟩ | ⟨_, _hoom⟩⟩ := h1.elim hmem hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨hReg, hmm'⟩ := himp hmm
  obtain ⟨sf, hsteps', ⟨hpcf, hrunf, P_f, hmf, hq⟩ | ⟨_, _hoom2⟩⟩ :=
    (h2 sm hpc hrun (hsteps.frozenLoaded hfrozen) (hsteps.symtab_eq.trans hsym) hReg).elim
      hmm' (hsteps.codeLoaded hL)
  rotate_left; · exact (not_satisfies_false_sepConj _hoom2).elim
  exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpcf, hrunf, hq hmf⟩⟩

def tryDecryptMidMetaCore (s0 s : State) : Prop :=
  s.status = .Running ∧
  s.sp = s0.sp - 1504#64 ∧
  s0.spAligned = true ∧
  s.spAligned = true ∧
  s.readReg64 .x29 = s0.sp - 96#64 ∧
  s.trace = s0.trace ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem tryDecryptMidMeta_of_core {img : Obj.Image} {s0 s : State}
    (hf : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : tryDecryptMidMetaCore s0 s) : tryDecryptMidMeta img s0 s := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  exact ⟨h1, h2, h3, h4, h5, h6, hf, hsym, h7⟩

theorem reaches_pc_midMeta {prog : Program} {img : Obj.Image} {target : BitVec 64}
    {s0 s : State} {Rest : State → Prop}
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : reaches_pc prog target s
      (fun sf => sf.pc = target ∧ tryDecryptMidMetaCore s0 sf ∧ Rest sf)) :
    reaches_pc prog target s
      (fun sf => sf.pc = target ∧ tryDecryptMidMeta img s0 sf ∧ Rest sf) := by
  intro hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, hpc', hcore, hrest⟩ | ⟨_, hoom⟩⟩ := h hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, hpc',
      tryDecryptMidMeta_of_core (hsteps.frozenLoaded hfrozen) (hsteps.symtab_eq.trans hsym) hcore,
      hrest⟩⟩
  · exact False.elim hoom

theorem steps_of_sepWP {prog : Program} {img : Obj.Image}
    {mid : BitVec 64} {s : State} {P P_mid R : SepProp}
    {RegMid Out : State → Prop}
    (hmem : s.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s.mem)
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h1 : SepWP prog mid s P (fun sm Pm => (sm.mem ⊨ Pm ∗ R) → RegMid sm ∧ (sm.mem ⊨ P_mid ∗ R)))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      img.FrozenLoaded sm → sm.symtab = img.symtab →
      prog.CodeLoaded sm.mem → RegMid sm → (sm.mem ⊨ P_mid ∗ R) →
      ∃ s', Steps prog sm s' ∧ Out s') :
    ∃ s', Steps prog s s' ∧ Out s' := by
  obtain ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, himp⟩ | ⟨_, _hoom⟩⟩ := h1.elim hmem hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨hReg, hmm'⟩ := himp hmm
  obtain ⟨s', hsteps', hout⟩ :=
    h2 sm hpc hrun (hsteps.frozenLoaded hfrozen) (hsteps.symtab_eq.trans hsym)
      (hsteps.codeLoaded hL) hReg hmm'
  exact ⟨s', hsteps.trans hsteps', hout⟩

theorem steps_done_of_sepWP_frozen {prog : Program} {img : Obj.Image}
    {target : BitVec 64} {s : State} {P R : SepProp}
    {QCore NormalOut PanicOut : State → Prop}
    (hmem : s.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s.mem)
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (himp : ∀ sf, img.FrozenLoaded sf → sf.symtab = img.symtab → QCore sf → NormalOut sf)
    (hwp : SepWP prog target s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → QCore sf)) :
    ∃ s', Steps prog s s' ∧ (NormalOut s' ∨ PanicOut s') := by
  obtain ⟨sf, hsteps, ⟨_, _, P_f, hmf, hq⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hmem hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  exact ⟨sf, hsteps,
    Or.inl (himp sf (hsteps.frozenLoaded hfrozen) (hsteps.symtab_eq.trans hsym) (hq hmf))⟩

theorem steps_done_of_sepWP_midMeta {prog : Program} {img : Obj.Image}
    {target : BitVec 64} {s0 s : State} {P R : SepProp}
    {Rest PanicOut : State → Prop}
    (hmem : s.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s.mem)
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hwp : SepWP prog target s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
      sf.pc = target ∧ tryDecryptMidMetaCore s0 sf ∧ Rest sf)) :
    ∃ s', Steps prog s s' ∧
      ((s'.pc = target ∧ tryDecryptMidMeta img s0 s' ∧ Rest s') ∨ PanicOut s') := by
  refine steps_done_of_sepWP_frozen hmem hL hfrozen hsym ?_ hwp
  intro sf hff hsymf ⟨hpc', hcore, hrest⟩
  exact ⟨hpc', tryDecryptMidMeta_of_core hff hsymf hcore, hrest⟩

theorem steps_call {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc : BitVec 64} {spec : Spec α} (x : α)
    {sm : State} {F R : SepProp} {NormalOut PanicOut : State → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : sm.pc = entry) (hrun : sm.status = .Running) (hsp : sm.spAligned = true)
    (hlr : sm.readReg64 .lr = ret_pc)
    (hfrozen : img.FrozenLoaded sm) (hsym : sm.symtab = img.symtab)
    (hL : prog.CodeLoaded sm.mem)
    (hpre : sm.mem ⊨ spec.pre x sm ∗ (F ∗ R))
    (hpanic : ∀ sf, sf.status = .Panicked → (sf.mem ⊨ (spec.onPanic x sm sf ∗ F) ∗ R) → PanicOut sf)
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sm.sp → sf.spAligned = true → CalleeSavedPreserved sm sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab → prog.CodeLoaded sf.mem →
      (sf.mem ⊨ (spec.post x sm sf ∗ F) ∗ R) →
      ∃ s', Steps prog sf s' ∧ (NormalOut s' ∨ PanicOut s'))
    (hexit : ∀ sf code R', (sf.mem ⊨ spec.onExit x code sm sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h)
    (hoom : ∀ sf R', (sf.mem ⊨ spec.onOom x sm sf ∗ R') → False := by
      intro _ _ h; first | exact not_satisfies_false_sepConj h | (dsimp only [Spec.inImage] at h; exact not_satisfies_false_sepConj h)) :
    ∃ s', Steps prog sm s' ∧ (NormalOut s' ∨ PanicOut s') := by
  obtain ⟨sf, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) sm hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcf, _, hrunf⟩, ⟨hspf, hcsf⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcf
    have hsp_alf : sf.spAligned = true := by
      unfold State.spAligned at hsp ⊢; rw [hspf]; exact hsp
    obtain ⟨s', hsteps', hout'⟩ :=
      hnext sf hpcf hrunf hspf hsp_alf hcsf
        (hsteps.frozenLoaded hfrozen) (hsteps.symtab_eq.trans hsym) (hsteps.codeLoaded hL) hpost
    exact ⟨s', hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sf, hsteps, Or.inr (hpanic sf hpan hpost)⟩
  · exact (hexit sf code (F ∗ R) hpost).elim
  · exact (hoom sf (F ∗ R) hpost).elim

theorem spqrRecv_ok_at_tripleRatchet {Q : List (BitVec 8) → Prop} {A : RustAlloc} {S : SpqrModel}
    {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)} {img : Obj.Image}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hrecv : SpqrRecvOkQ Q C A ctl S abs img) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff spqrRecvName := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      ((spqrRecvSpec A S img).restrictPre (Q ·.1.bytes)) := by
  have h : subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr spqrRecvName)
      ((spqrRecvSpec A S img).restrictPre (Q ·.1.bytes)) := by
    have h := hrecv
    unfold SpqrRecvOkQ at h
    rwa [tripleRatchetProg_eq_tripleRatchetProgAt hloads,
      entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl) (abs := abs) hloads] at h
  rwa [← Program.fnAddr_rel rfl rfl hk]

theorem formatInner_ok_at_tripleRatchet_trap {A : RustAlloc} {S : SpqrModel} {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (State → State)}
    (hS : TripleRatchetHooks C A S abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff formatInnerName := by fnoff_eq) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (formatInnerSpec A) := by
  have habs := tripleRatchetExterns_abs C 0#64 abs
  have h3 : Rust.withPanics (trTrapExterns C abs) formatInnerName =
      abs formatInnerName := by
    rw [withPanics_trTrap_eq_kit C 0#64 abs (n := formatInnerName) (by decide)]
    exact Option.some.inj (congrArg (·[2]?) habs)
  exact hook_ok_at_raw (hname := formatInnerName) rfl hk
    (by fnoff_eq)
    (by fnoff_eq)
    (by simpa [HookSat, h3] using hS.formatInner)

theorem formatInner_ok_at_tripleRatchet {A : RustAlloc} {S : SpqrModel} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hS : TripleRatchetHooks C A S abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff formatInnerName := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (formatInnerSpec A) := by
  simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap
    (formatInner_ok_at_tripleRatchet_trap (b := b) (C := C) (abs := abs) hS hk)

theorem addrDisplay_ok_at_tripleRatchet_trap {A : RustAlloc} {S : SpqrModel} {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (State → State)}
    (hS : TripleRatchetHooks C A S abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff addrDisplayName := by fnoff_eq) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (addrDisplaySpec A) :=
  addr_display_ok_at_trap b C A abs hS.fmtWrite name k hk

theorem addrDisplay_ok_at_tripleRatchet {A : RustAlloc} {S : SpqrModel} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hS : TripleRatchetHooks C A S abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff addrDisplayName := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (addrDisplaySpec A) :=
  addr_display_ok_at b C A ctl abs hS.fmtWrite name k hk

namespace BS8

end BS8

theorem mr_cut (sp : BitVec 64) (c n k m : Nat) (c' : BitVec 64)
    (hm : m = n + k := by rfl)
    (hc : BitVec.ofNat 64 (c + n) = c' := by rfl)
    (h : n + k ≤ 2 ^ 64 := by decide) :
    memRegion (sp + BitVec.ofNat 64 c) m =
      memRegion (sp + BitVec.ofNat 64 c) n ∗ memRegion (sp + c') k := by
  subst hm hc
  exact mr_cut_add sp c n k h

def trRestAt (A : RustAlloc) (sp : BitVec 64) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) : SepProp :=
  ⌜∀ sc, tr.ratchet.senderChain = some sc →
    Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes⌝ ∗
    ratchetAt A (sp + 56#64) trG.ratchet tr.ratchet ∗
    ((sp + 256#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
    ((sp + 288#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)

theorem trAt_split_pq (A : RustAlloc) (sp : BitVec 64) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) :
    trAt A (sp + 56#64) trG tr =
      vecU8At A (sp + 232#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
      trRestAt A sp trG tr := by
  unfold trAt trRestAt
  rw [BitVec.add_assoc, show (56#64 : BitVec 64) + 0xb0#64 = 232#64 by rfl,
    BitVec.add_assoc, show (56#64 : BitVec 64) + 0xc8#64 = 256#64 by rfl,
    BitVec.add_assoc, show (56#64 : BitVec 64) + 0xe8#64 = 288#64 by rfl]
  ac_rfl

def signalMessageRestAt (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) : SepProp :=
  ⌜macLength + 1 ≤ m.serialized.length ∧ m.serialized.length < 2 ^ 40 ∧
    m.ciphertext.length < 2 ^ 40 ∧ m.pqRatchet.length < 2 ^ 40 ∧
    (∀ ad, m.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
    boxU8At A (a + 0x18#64) g.ctPtr m.ciphertext ∗
    boxU8At A (a + 0x28#64) g.serPtr m.serialized ∗
    ((a + 0x38#64) ↦ₛ m.senderRatchetKey.bytes.toList) ∗
    optBoxU8At A (a + 0x58#64) g.addrPtr m.addresses ∗
    ((a + 0x68#64) ↦₃₂ m.counter) ∗ ((a + 0x6c#64) ↦₃₂ m.previousCounter) ∗
    ((a + 0x70#64) ↦₈ m.messageVersion) ∗ memRegion (a + 0x71#64) 7

theorem signalMessageAt_split_pq (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) :
    signalMessageAt A g a m =
      vecU8At A a g.pqCap g.pqPtr m.pqRatchet ∗
      signalMessageRestAt A g a m := by
  unfold signalMessageAt signalMessageRestAt
  ac_rfl

theorem msg_pqRatchet_lt_of_pre_call {A : RustAlloc} {g : SignalMessageGhost}
    {a : BitVec 64} {m : SignalMessage} {mem : Memory} {P1 P2 P3 P4 : SepProp}
    (h : mem ⊨ P1 ∗ ((P2 ∗ signalMessageRestAt A g a m ∗ P3) ∗ P4)) :
    m.pqRatchet.length < 2 ^ 40 := by
  unfold signalMessageRestAt at h
  simp only [sepConj_assoc] at h
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, satisfies_pure_sepConj] at h
  exact h.1.2.2.2.1

theorem onPanic_drop_frame {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {F R : SepProp} {s0 s' : State}
    (h : s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ (F ∗ R)) :
    s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R := by
  dsimp only [tryDecryptSpec, Spec.inImage] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  rcases h with ⟨hcond, hmem⟩
  rw [← sepConj_assoc] at hmem
  exact ⟨hcond, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmem⟩

theorem spqrRecvStack_le_sub_of_rootStack {sp0 : BitVec 64} (h : rootStack ≤ sp0.toNat) :
    spqrRecvStack ≤ (sp0 - 1504#64).toNat := by
  unfold rootStack spqrRecvStack at *
  bv_omega

theorem onPanic_of_spqrRecv {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {st msg : VecArg} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (htrace : sm.trace = s0.trace)
    (hst : st.bytes = x.st.pqRatchetState)
    (hmsg : msg.bytes = x.msg.pqRatchet)
    (h : sf.mem ⊨ ((spqrRecvSpec A S img).onPanic (st, msg, ret) sm sf ∗ F) ∗ R) :
    sf.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  dsimp only [spqrRecvSpec, tryDecryptSpec, Spec.inImage] at h ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h
  rcases h with ⟨⟨hpan, hpref⟩, hmem⟩
  rw [← sepConj_assoc] at hmem
  rw [hst, hmsg, allocFailedIn, htrace, ← allocFailedIn] at hpan
  rw [htrace] at hpref
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨?_, hpref⟩, ?_⟩
  · rcases hpan with ha | hp
    · exact Or.inr (Or.inr ha)
    · exact Or.inr (Or.inl hp)
  · exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmem

theorem spqrRecv_pre_frame {Q : List (BitVec 8) → Prop} {Pstk : Nat → Prop} {F F' R : SepProp}
    {A : RustAlloc} {S : SpqrModel} {img : Obj.Image}
    {stArg msgArg : VecArg} {ret : BitVec 64} {sm : State}
    (hQ : Q stArg.bytes) (hmsg : msgArg.bytes.length < 2 ^ 40) (hstk : Pstk sm.sp.toNat)
    (h : sm.mem ⊨ (spqrRecvSpec A S img).pre (stArg, msgArg, ret) sm ∗ (F' ∗ (F ∗ R))) :
    sm.mem ⊨ (spqrRecvSpecQF Q Pstk F A S img).pre (stArg, msgArg, ret) sm ∗ (F' ∗ R) := by
  dsimp only [spqrRecvSpecQF]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hQ, hmsg, hstk⟩, ?_⟩
  exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) h

theorem spqrRecv_post_frame {Q : List (BitVec 8) → Prop} {Pstk : Nat → Prop} {F F' R : SepProp}
    {A : RustAlloc} {S : SpqrModel} {img : Obj.Image}
    {stArg msgArg : VecArg} {ret : BitVec 64} {sm sf1 : State}
    (h : sf1.mem ⊨ ((spqrRecvSpecQF Q Pstk F A S img).post
      (stArg, msgArg, ret) sm sf1 ∗ F') ∗ R) :
    sf1.mem ⊨ (((spqrRecvSpec A S img).restrictPre (Q ·.1.bytes)).post
      (stArg, msgArg, ret) sm sf1 ∗ F') ∗ (F ∗ R) := by
  dsimp only [spqrRecvSpecQF, Spec.restrictPre] at h ⊢
  exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) h

theorem BS8.utf8_decrypt_len : (utf8 "decrypt").length = 7 := by
  decide +kernel

theorem onPanic_of_formatInner {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (htrace : sm.trace = s0.trace)
    (h : sf.mem ⊨ ((formatInnerSpec A).onPanic ret sm sf ∗ F) ∗ R) :
    sf.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  dsimp only [formatInnerSpec, tryDecryptSpec, Spec.inImage] at h ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h
  rcases h with ⟨⟨hpan, hpref⟩, hmem⟩
  rw [← sepConj_assoc] at hmem
  rw [allocFailedIn, htrace, ← allocFailedIn] at hpan
  rw [htrace] at hpref
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨Or.inr (Or.inr hpan), hpref⟩, ?_⟩
  exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmem

theorem pointsToBytes_to_mr (a : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦ₛ bs) ⊢ memRegion a bs.length :=
  IsBlock.entails (IsBlock.pointsToBytes a bs) (IsBlock.memRegion a bs.length) (fun _ _ => trivial)

theorem buf_to_mr (ptr : BitVec 64) (bs : List (BitVec 8)) (cap : Nat)
    (h1 : bs.length ≤ cap) (h2 : cap < 2 ^ 63) :
    (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap - bs.length) ⊢
    memRegion ptr cap := by
  refine Entails.trans (sepConj_mono_left (pointsToBytes_to_mr ptr bs)) ?_
  rw [← memRegion_split ptr bs.length (cap - bs.length) (by omega), Nat.add_sub_of_le h1]
  exact Entails.refl _

theorem sp56_weaken (sp seedPtr seedCap : BitVec 64) :
    memRegion sp 16 ∗
    ((sp + 16#64) ↦₆₄ seedPtr) ∗
    memRegion (sp + 24#64) 16 ∗
    ((sp + 40#64) ↦₆₄ seedCap) ∗
    memRegion (sp + 48#64) 8 ⊢
    memRegion sp 56 := by
  rw [memRegion_split sp 16 40 (by decide),
    mr_cut_add sp 16 8 32 (by decide),
    mr_cut_add sp 24 16 16 (by decide),
    mr_cut_add sp 40 8 8 (by decide)]
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono (pts64_to_mr _ _)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (pts64_to_mr _ _) (Entails.refl _))))

theorem sepWP_8_mr7_to_64 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {lo : BitVec 8} {F : SepProp} {post : State → SepProp → Prop}
    (h : ∀ hi : BitVec 56, SepWP prog target s ((a ↦₆₄ (hi ++ lo)) ∗ F) post) :
    SepWP prog target s ((a ↦₈ lo) ∗ memRegion (a + 1#64) 7 ∗ F) post := by
  refine SepWP.focus_weaken (pointsTo8_memRegion7_to_64 a lo) (by sep_focus) ?_
  rw [sepExists_sepConj_left]
  wp_pull_exists
  exact h _

theorem pts8_mr7_to_mr8 (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) ∗ memRegion (a + 1#64) 7 ⊢ memRegion a 8 := by
  rw [memRegion_split a 1 7 (by decide)]
  exact sepConj_mono (pts8_to_mr a b) (Entails.refl _)
  where
    pts8_to_mr (p : BitVec 64) (v : BitVec 8) : (p ↦₈ v) ⊢ memRegion p 1 := by
      rw [memRegion_one]
      exact Entails.sepExists_intro v

theorem extractLsb56_append_setWidth8 (w : BitVec 64) :
    w.extractLsb' 8 56 ++ w.setWidth 8 = w := by
  bv_slice

theorem pointsTo64_to_8_mr7 (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) ⊢ (a ↦₈ w.setWidth 8) ∗ memRegion (a + 1#64) 7 := by
  have h := pointsTo64_to_8_memRegion7 a (w.extractLsb' 8 56) (w.setWidth 8)
  rwa [extractLsb56_append_setWidth8] at h

theorem sp_fp_eq {sp0 sp : BitVec 64} (h : sp0 - 1504#64 = sp) :
    sp0 - 96#64 = sp + 1408#64 := by
  subst h; bv_lin

theorem cap_add_one_ne_zero {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  apply beq_false_of_ne
  intro heq
  have h1 : (cap + 1#64).toNat = 0 := by rw [heq]; rfl
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
  omega

theorem byte_ne_zero_cbz32 {d : BitVec 8} (h : d ≠ 0#8) :
    (BitVec.setWidth 32 d == 0#32) = false := by
  apply beq_false_of_ne
  intro heq
  apply h
  have h8 := congrArg (BitVec.setWidth 8) heq
  simpa using h8

theorem byte_ne_zero_cbz64_32 {d : BitVec 8} (h : d ≠ 0#8) :
    (BitVec.setWidth 32 (BitVec.setWidth 64 d) == 0#32) = false := by
  apply beq_false_of_ne
  intro heq
  apply h
  have h8 := congrArg (BitVec.setWidth 8) heq
  simpa using h8

theorem concat56_8_cbz64_zero (hi : BitVec 56) :
    (BitVec.zeroExtend 64 (BitVec.truncate 8 (hi ++ 0#8)) == 0#64) = true := by
  have htr : BitVec.truncate 8 (hi ++ 0#8) = 0#8 := by bv_slice
  rw [htr]
  rfl

theorem concat56_8_cbz64_ne_zero (hi : BitVec 56) {d : BitVec 8} (h : d ≠ 0#8) :
    (BitVec.zeroExtend 64 (BitVec.truncate 8 (hi ++ d)) == 0#64) = false := by
  have htr : BitVec.truncate 8 (hi ++ d) = d := by bv_slice
  rw [htr]
  apply beq_false_of_ne
  intro heq
  apply h
  have h8 := congrArg (BitVec.setWidth 8) heq
  simpa using h8

theorem concat56_8_cbz32_ne_zero (hi : BitVec 56) {d : BitVec 8} (h : d ≠ 0#8) :
    (BitVec.setWidth 32 (BitVec.zeroExtend 64 (BitVec.truncate 8 (hi ++ d))) == 0#32) = false := by
  have htr : BitVec.truncate 8 (hi ++ d) = d := by bv_slice
  rw [htr]
  exact byte_ne_zero_cbz64_32 h

theorem speBodyAt_invalidState_fold (A : RustAlloc) (sp fmtCap fmtPtr p : BitVec 64)
    (fmtBs : List (BitVec 8))
    (hfb : fmtBs.length ≤ fmtCap.toNat ∧ fmtCap.toNat < 2 ^ 63 ∧ fmtPtr ≠ 0) :
    ((sp + 360#64) ↦₆₄ fmtCap) ∗
    ((sp + 368#64) ↦₆₄ fmtPtr) ∗
    ((sp + 376#64) ↦₆₄ BitVec.ofNat 64 fmtBs.length) ∗
    (if fmtCap = 0 then emp else A.live fmtPtr fmtCap.toNat 1 ∗
      (fmtPtr ↦ₛ fmtBs) ∗
      memRegion (fmtPtr + BitVec.ofNat 64 fmtBs.length) (fmtCap.toNat - fmtBs.length)) ∗
    ((sp + 384#64) ↦₆₄ p) ∗
    ((sp + 392#64) ↦₆₄ 7#64) ∗
    (p ↦ᵣ utf8 "decrypt") ⊢
    speBodyAt A (utf8 "decrypt") (sp + 360#64) .invalidState := by
  dsimp only [speBodyAt, strRefAt, vecU8, vecU8At, vecHeader]
  have hlen : BitVec.ofNat 64 (utf8 "decrypt").length = 7#64 := by decide +kernel
  rw [hlen]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left]
  refine Entails.trans ?_ (Entails.sepExists_intro fmtBs)
  refine Entails.trans ?_ (Entails.sepExists_intro fmtCap)
  refine Entails.trans ?_ (Entails.sepExists_intro fmtPtr)
  simp only [sepExists_sepConj_right]
  refine Entails.trans ?_ (Entails.sepExists_intro p)
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  exact Entails.pure_right hfb (Entails.refl _)

theorem speBodyAt_pqRatchet_fold (A : RustAlloc) (sp fmtCap fmtPtr w392 : BitVec 64)
    (fmtBs : List (BitVec 8)) (mt : MessageType)
    (hfb : fmtBs.length ≤ fmtCap.toNat ∧ fmtCap.toNat < 2 ^ 63 ∧ fmtPtr ≠ 0) :
    ((sp + 360#64) ↦₆₄ fmtCap) ∗
    ((sp + 368#64) ↦₆₄ fmtPtr) ∗
    ((sp + 376#64) ↦₆₄ BitVec.ofNat 64 fmtBs.length) ∗
    (if fmtCap = 0 then emp else A.live fmtPtr fmtCap.toNat 1 ∗
      (fmtPtr ↦ₛ fmtBs) ∗
      memRegion (fmtPtr + BitVec.ofNat 64 fmtBs.length) (fmtCap.toNat - fmtBs.length)) ∗
    ((sp + 384#64) ↦₈ msgTypeByte mt) ∗
    memRegion ((sp + 384#64) + 1#64) 7 ∗
    ((sp + 392#64) ↦₆₄ w392) ⊢
    speBodyAt A (utf8 "decrypt") (sp + 360#64) (.invalidMessage mt .pqRatchet) := by
  refine Entails.trans (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
    (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
        (pts64_to_mr (sp + 392#64) w392))))))) ?_
  dsimp only [speBodyAt, invalidMessageStrAt, vecU8, vecU8At, vecHeader]
  rw [show (sp + 384#64) + 1#64 = sp + 385#64 by rw [BitVec.add_assoc]; rfl,
    show (sp + 360#64) + 24#64 = sp + 384#64 by rw [BitVec.add_assoc]; rfl,
    show (sp + 360#64) + 25#64 = sp + 385#64 by rw [BitVec.add_assoc]; rfl,
    mr_cut sp 385 7 8 15 392#64]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left]
  refine Entails.trans ?_ (Entails.sepExists_intro fmtBs)
  refine Entails.trans ?_ (Entails.sepExists_intro fmtCap)
  refine Entails.trans ?_ (Entails.sepExists_intro fmtPtr)
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  exact Entails.pure_right hfb (Entails.refl _)


end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegC
