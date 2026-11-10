/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `PreKeySignalMessage::new` `sret` Write and Epilogue Helpers

Instruction decodes, heap/stack separation-logic splittings, and symbolic execution of inlined
`into_boxed_slice` and the 248-byte `Result<PreKeySignalMessage, _>` `sret` stores (`+0x4c4..+0x580`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue

set_option maxRecDepth 200000

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split

/-! ## Instruction Decode Lemmas (`+0x4c4..+0x608`) -/

gen_decodes libsignalSessionCode_tree preKeyMsgBin [0x155f4 → 0x155fc, 0x15634 → 0x15738]

abbrev preKeyMsgNewName : String := "<libsignal_protocol::protocol::PreKeySignalMessage>::new"

theorem fnOff_preKeyMsgNew : libsignalSessionCode.fnOff preKeyMsgNewName = 0x15130 := by
  exact CryptoVerification.libsignalSessionCode_fnOff_0x15130

theorem fnAddr_preKeyMsgNew {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyMsgNewName = preKeyMsgNewEntry img := by
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, fnOff_preKeyMsgNew, preKeyMsgNewEntry]

theorem fnAddr_preKeyMsgNew_ext {img : Obj.Image} {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt img.base ext).fnAddr preKeyMsgNewName = preKeyMsgNewEntry img := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, fnOff_preKeyMsgNew, preKeyMsgNewEntry]

theorem fnAddr_preKeyMsgNew_trap {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)} :
    (trTrapProgAt img.base C abs).fnAddr preKeyMsgNewName = preKeyMsgNewEntry img :=
  fnAddr_preKeyMsgNew_ext

open Lean Elab Tactic in
elab "preKeyMsg_fetches_range " b:term:max H:term:max kStart:num kEnd:num : tactic => do
  let off := 0x15130
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let hfn := mkIdent `CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue.fnOff_preKeyMsgNew
  let mut k := kStart
  while k <= kEnd do
    let dec := mkIdent (.str `CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
      s!"preKeyMsgBin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))
    k := k + 4

universe u in
theorem bind_entry {α : Sort u} {P : α → Prop} (e : α) (h : ∀ x : α, P x) : P e := h e

open Lean Meta Elab Tactic in
elab "generalize_entry " e:term:51 " = " x:ident : tactic => withMainContext do
  let eExpr ← elabTerm e none
  let consts : Array Name := #[``Arm64.Program.fnAddr]
  let lctx ← getLCtx
  let mut toRevert : Array FVarId := #[]
  for decl in lctx do
    if !decl.isImplementationDetail && !decl.isLet then
      let ty ← instantiateMVars decl.type
      if (ty.find? fun sub => consts.any sub.isConstOf).isSome then
        toRevert := toRevert.push decl.fvarId
  let (reverted, mvarId) ← (← getMainGoal).revert toRevert true
  mvarId.withContext do
    let target ← instantiateMVars (← mvarId.getType)
    let targetAbst ← kabstract target eExpr
    let eType ← inferType eExpr
    let u ← getLevel eType
    let pLam := Lean.mkLambda x.getId BinderInfo.default eType targetAbst
    let newGoalType := mkForall x.getId BinderInfo.default eType targetAbst
    let newMVar ← mkFreshExprSyntheticOpaqueMVar newGoalType (← mvarId.getTag)
    let proof := mkApp4 (mkConst ``bind_entry [u]) eType pLam eExpr newMVar
    mvarId.assign proof
    let (_, mvarId') ← newMVar.mvarId!.intro1P
    let (_, mvarId'') ← mvarId'.introNP reverted.size
    replaceMainGoal [mvarId'']

/-! ## Separation-Logic Helpers for `sret` Packing -/

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
theorem append64_extract_lo (lo hi : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits
@[local simp, local arm64_norm]
theorem append64_extract_hi (lo hi : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits
@[local simp, local arm64_norm]
theorem append32_extract_lo (lo hi : BitVec 32) : (hi ++ lo).extractLsb' 0 32 = lo := by bv_bits
@[local simp, local arm64_norm]
theorem append32_extract_hi (lo hi : BitVec 32) : (hi ++ lo).extractLsb' 32 32 = hi := by bv_bits
@[local simp, local arm64_norm]
theorem append32_truncate (lo hi : BitVec 32) : (hi ++ lo).truncate 32 = lo := by bv_bits
@[local simp, local arm64_norm]
theorem zeroExtend32_truncate8_eq (v : BitVec 32) :
    (v.zeroExtend 64).truncate 8 = v.setWidth 8 := by bv_bits
@[local simp, local wp_norm, local arm64_norm]
theorem extractLsb0_8_append56 (hi : BitVec 56) (d : BitVec 8) :
    (hi ++ d).extractLsb' 0 8 = d := by bv_bits

theorem entails_of_sep_focus {P Q : SepProp} (h : P = Q ∗ emp) : P ⊢ Q :=
  Entails.of_eq (by rw [h, sepConj_emp])

theorem satisfies_of_sep_focus {m : Memory} {P Q : SepProp} (hm : m ⊨ P)
    (h : P = Q ∗ emp) : m ⊨ Q := by
  rwa [h, sepConj_emp] at hm

theorem pointsTo64_split32 (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) = (a ↦₃₂ v.truncate 32) ∗ ((a + 4#64) ↦₃₂ v.extractLsb' 32 32) := by
  apply IsBlock.eq (IsBlock.pointsTo64 a v)
    ((IsBlock.pointsTo32 a _).sepConj (IsBlock.pointsTo32 (a + 4#64) _) rfl (by decide))
  intro m
  rw [Memory.read32_eq_truncate_read64, Memory.read32_add4_eq_extract_read64]
  generalize m.read64 a = w
  constructor
  · intro h; subst h; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    have hw : w = w.extractLsb' 32 32 ++ w.truncate 32 := by bv_bits
    have hv : v = v.extractLsb' 32 32 ++ v.truncate 32 := by bv_bits
    rw [hw, hv, h1, h2]

theorem pointsTo32_merge64 (a : BitVec 64) (lo hi : BitVec 32) :
    ((a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi)) = (a ↦₆₄ (hi ++ lo)) := by
  rw [pointsTo64_split32, append32_truncate, append32_extract_hi]

theorem pointsTo8_memRegion7_to_64 (a : BitVec 64) (d : BitVec 8) :
    ((a ↦₈ d) ∗ memRegion (a + 1#64) 7) ⊢ ∃∗ hi : BitVec 56, a ↦₆₄ (hi ++ d) := by
  refine IsBlock.entails
    ((IsBlock.pointsTo8 a d).sepConj (IsBlock.memRegion (a + 1#64) 7) rfl (by decide))
    (IsBlock.sepExists fun hi : BitVec 56 => IsBlock.pointsTo64 a (hi ++ d)) ?_
  rintro m ⟨hd, -⟩
  refine ⟨(m.read64 a).extractLsb' 8 56, ?_⟩
  have h8 : (m.read64 a).extractLsb' 0 8 = m.read8 a := by
    simp only [Memory.read64, BitVec.add_zero]
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
  bv_bits

theorem pointsTo64_to_8_memRegion7 (a : BitVec 64) (hi : BitVec 56) (d : BitVec 8) :
    (a ↦₆₄ (hi ++ d)) ⊢ (a ↦₈ d) ∗ memRegion (a + 1#64) 7 := by
  refine IsBlock.entails
    (IsBlock.pointsTo64 a (hi ++ d))
    ((IsBlock.pointsTo8 a d).sepConj (IsBlock.memRegion (a + 1#64) 7) rfl (by decide)) ?_
  intro m hw
  refine ⟨?_, trivial⟩
  have h8 : m.read8 a = (m.read64 a).extractLsb' 0 8 := by
    simp only [Memory.read64, BitVec.add_zero]
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

theorem memRegion_16_eq_cells2 (a : BitVec 64) :
    memRegion a 16 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) := by
  rw [memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 8) (by decide) rfl (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64)]

theorem vecU8AtLen_exact_eq_boxU8Buf (A : RustAlloc) (a ptr lenW : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length < 2 ^ 63) :
    vecU8AtLen A a (BitVec.ofNat 64 bs.length) ptr lenW bs =
      ((a ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ lenW) ∗
        boxU8Buf A ptr bs) := by
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hzero_iff : (BitVec.ofNat 64 bs.length = 0) ↔ bs = [] := by
    constructor
    · intro h
      have ht := congrArg BitVec.toNat h
      rw [htoNat] at ht
      exact List.eq_nil_of_length_eq_zero ht
    · rintro rfl; rfl
  by_cases hbs : bs = []
  · subst hbs
    simp [vecU8AtLen, vecHeader, boxU8Buf, sepConj_assoc]
  · have hcap0 : BitVec.ofNat 64 bs.length ≠ 0 := fun h => hbs (hzero_iff.mp h)
    have hpure : (bs.length ≤ bs.length ∧ bs.length < 2 ^ 63 ∧ ptr ≠ 0) =
        (ptr ≠ 0#64 ∧ bs.length < 2 ^ 63) :=
      propext ⟨fun ⟨_, h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h2, h1⟩ => ⟨Nat.le_refl _, h1, h2⟩⟩
    simp only [vecU8AtLen, vecHeader, boxU8Buf, hcap0, hbs, ↓reduceIte, htoNat,
      Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp, sepConj_assoc, hpure]

theorem sep_entails_replace1 {P Q A B F : SepProp}
    (h1 : A ⊢ B) (hP : P = A ∗ F) (hQ : Q = B ∗ F) : P ⊢ Q := by
  rw [hP, hQ]
  exact sepConj_mono_left h1

theorem sep_entails_replace2 {P Q A1 B1 A2 B2 F : SepProp}
    (h1 : A1 ⊢ B1) (h2 : A2 ⊢ B2) (hP : P = A1 ∗ A2 ∗ F) (hQ : Q = B1 ∗ B2 ∗ F) : P ⊢ Q := by
  rw [hP, hQ]
  exact sepConj_mono h1 (sepConj_mono_left h2)

def kyberWords3At (a ky0 ky1 ky2 : BitVec 64) : SepProp :=
  (a ↦₆₄ ky0) ∗ ((a + 8#64) ↦₆₄ ky1) ∗ ((a + 16#64) ↦₆₄ ky2)

def kyberHeap (A : RustAlloc) (ptr : BitVec 64) (kp : Option KyberPayload)
    (ky0 ky1 ky2 : BitVec 64) : SepProp :=
  match kp with
  | none => ⌜ky0 = 0#64⌝
  | some k =>
    ⌜ky0 = ptr ∧ ky1 = BitVec.ofNat 64 k.ciphertext.length ∧
      ∃ hi32 : BitVec 32, ky2 = hi32 ++ k.preKeyId⌝ ∗
      boxU8Buf A ptr k.ciphertext

theorem kyberWords3At_entails_memRegion (a ky0 ky1 ky2 : BitVec 64) :
    kyberWords3At a ky0 ky1 ky2 ⊢ memRegion a 24 := by
  unfold kyberWords3At
  rw [memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 16) (by decide) rfl (by decide),
      memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k := 8) (by decide)
        (by bv_lin) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64)]
  exact sepConj_mono (Entails.sepExists_intro ky0)
    (sepConj_mono (Entails.sepExists_intro ky1) (Entails.sepExists_intro ky2))

theorem optKyberAt_unpack (A : RustAlloc) (a ptr : BitVec 64) (kp : Option KyberPayload) :
    optKyberAt A a ptr kp ⊢
      ∃∗ ky0 : BitVec 64, ∃∗ ky1 : BitVec 64, ∃∗ ky2 : BitVec 64,
        kyberWords3At a ky0 ky1 ky2 ∗ kyberHeap A ptr kp ky0 ky1 ky2 := by
  cases kp with
  | none =>
    simp only [optKyberAt, kyberWords3At, kyberHeap, memRegion_16_eq_cells2 (a + 8#64),
      show a + 8#64 + 8#64 = a + 16#64 by bv_lin, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc]
    apply Entails.sepExists_elim; intro ky2
    apply Entails.sepExists_elim; intro ky1
    refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
    refine Entails.trans ?_ (Entails.sepExists_intro ky1)
    refine Entails.trans ?_ (Entails.sepExists_intro ky2)
    simp only [pure_true, sepConj_emp]
    exact Entails.refl _
  | some k =>
    have h4 : ((a + 0x10#64) ↦₃₂ k.preKeyId) ∗ memRegion (a + 0x14#64) 4 =
        ∃∗ hi32 : BitVec 32, (a + 0x10#64) ↦₆₄ (hi32 ++ k.preKeyId) := by
      rw [memRegion_four (a + 0x14#64), sepExists_sepConj_right]
      congr 1; funext hi32
      have h20 : a + 0x14#64 = (a + 0x10#64) + 4#64 := by bv_lin
      rw [h20, pointsTo32_merge64]
    simp only [optKyberAt, boxU8At_eq_boxU8Buf, kyberWords3At, kyberHeap, sepConj_assoc]
    rw [h4]
    simp only [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro hi32
    refine Entails.trans ?_ (Entails.sepExists_intro ptr)
    refine Entails.trans ?_ (Entails.sepExists_intro (BitVec.ofNat 64 k.ciphertext.length))
    refine Entails.trans ?_ (Entails.sepExists_intro (hi32 ++ k.preKeyId))
    have hpull :
        (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
          ((a + 0x10#64) ↦₆₄ (hi32 ++ k.preKeyId)) ∗
          ⌜ptr = ptr ∧ BitVec.ofNat 64 k.ciphertext.length = BitVec.ofNat 64 k.ciphertext.length ∧
            ∃ hi32' : BitVec 32, hi32 ++ k.preKeyId = hi32' ++ k.preKeyId⌝ ∗
          boxU8Buf A ptr k.ciphertext =
        ⌜ptr = ptr ∧ BitVec.ofNat 64 k.ciphertext.length = BitVec.ofNat 64 k.ciphertext.length ∧
          ∃ hi32' : BitVec 32, hi32 ++ k.preKeyId = hi32' ++ k.preKeyId⌝ ∗
          ((a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
           ((a + 0x10#64) ↦₆₄ (hi32 ++ k.preKeyId)) ∗ boxU8Buf A ptr k.ciphertext) := by
      sep_focus
    rw [hpull]
    refine Entails.pure_right ⟨rfl, rfl, hi32, rfl⟩ ?_
    exact entails_of_sep_focus (by sep_focus)

theorem optKyberAt_pack (A : RustAlloc) (a ptr : BitVec 64) (kp : Option KyberPayload)
    (ky0 ky1 ky2 : BitVec 64) :
    kyberWords3At a ky0 ky1 ky2 ∗ kyberHeap A ptr kp ky0 ky1 ky2 ⊢ optKyberAt A a ptr kp := by
  cases kp with
  | none =>
    simp only [optKyberAt, kyberWords3At, kyberHeap, sepConj_assoc]
    have hpull :
        (a ↦₆₄ ky0) ∗ ((a + 8#64) ↦₆₄ ky1) ∗ ((a + 16#64) ↦₆₄ ky2) ∗ ⌜ky0 = 0#64⌝ =
        ⌜ky0 = 0#64⌝ ∗ ((a ↦₆₄ ky0) ∗ ((a + 8#64) ↦₆₄ ky1) ∗ ((a + 16#64) ↦₆₄ ky2)) := by
      sep_focus
    rw [hpull]
    apply Entails.pure_left; rintro rfl
    rw [memRegion_16_eq_cells2 (a + 8#64), show a + 8#64 + 8#64 = a + 16#64 by bv_lin]
    exact sepConj_mono_right
      (sepConj_mono (Entails.sepExists_intro ky1) (Entails.sepExists_intro ky2))
  | some k =>
    simp only [optKyberAt, boxU8At_eq_boxU8Buf, kyberWords3At, kyberHeap, sepConj_assoc]
    have hpull :
        (a ↦₆₄ ky0) ∗ ((a + 8#64) ↦₆₄ ky1) ∗ ((a + 16#64) ↦₆₄ ky2) ∗
          ⌜ky0 = ptr ∧ ky1 = BitVec.ofNat 64 k.ciphertext.length ∧
            ∃ hi32 : BitVec 32, ky2 = hi32 ++ k.preKeyId⌝ ∗
          boxU8Buf A ptr k.ciphertext =
        ⌜ky0 = ptr ∧ ky1 = BitVec.ofNat 64 k.ciphertext.length ∧
          ∃ hi32 : BitVec 32, ky2 = hi32 ++ k.preKeyId⌝ ∗
          ((a ↦₆₄ ky0) ∗ ((a + 8#64) ↦₆₄ ky1) ∗ ((a + 16#64) ↦₆₄ ky2) ∗
           boxU8Buf A ptr k.ciphertext) := by
      sep_focus
    rw [hpull]
    apply Entails.pure_left; rintro ⟨rfl, rfl, hi32, rfl⟩
    have h4 : ((a + 16#64) ↦₆₄ (hi32 ++ k.preKeyId)) ⊢
        ((a + 0x10#64) ↦₃₂ k.preKeyId) ∗ memRegion (a + 0x14#64) 4 := by
      rw [show (16#64 : BitVec 64) = 0x10#64 from rfl, ← pointsTo32_merge64,
        show (a + 0x10#64) + 4#64 = a + 0x14#64 by bv_lin,
        memRegion_four (a + 0x14#64)]
      exact sepConj_mono_right (Entails.sepExists_intro hi32)
    exact sep_entails_replace1
      (F := (a ↦₆₄ ky0) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
        boxU8Buf A ky0 k.ciphertext) h4 (by ac_rfl) (by ac_rfl)

def vecU8Heap (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8At_eq_vecU8Heap (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs =
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Heap A cap ptr bs := by
  simp only [vecU8At, vecHeader, vecU8Heap, sepConj_assoc]

def optBoxU8Heap (A : RustAlloc) (ptr w0 w1 : BitVec 64) : Option (List (BitVec 8)) → SepProp
  | none => ⌜w0 = 0#64⌝
  | some bs => ⌜w0 = ptr ∧ w1 = BitVec.ofNat 64 bs.length⌝ ∗ boxU8Buf A ptr bs

theorem optBoxU8At_unpack (A : RustAlloc) (a ptr : BitVec 64) (o : Option (List (BitVec 8))) :
    optBoxU8At A a ptr o ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ optBoxU8Heap A ptr w0 w1 o := by
  cases o with
  | none =>
    simp only [optBoxU8At, ProofLib.memRegion_eight (a + 8#64), optBoxU8Heap,
      sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro w1
    refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
    refine Entails.trans ?_ (Entails.sepExists_intro w1)
    simp only [pure_true, sepConj_emp]
    exact Entails.refl _
  | some bs =>
    simp only [optBoxU8At, boxU8At_eq_boxU8Buf, optBoxU8Heap]
    refine Entails.trans ?_ (Entails.sepExists_intro ptr)
    refine Entails.trans ?_ (Entails.sepExists_intro (BitVec.ofNat 64 bs.length))
    simp only [and_self, pure_true, emp_sepConj]
    exact Entails.refl _

theorem optBoxU8At_pack (A : RustAlloc) (a ptr w0 w1 : BitVec 64) (o : Option (List (BitVec 8))) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ optBoxU8Heap A ptr w0 w1 o ⊢ optBoxU8At A a ptr o := by
  cases o with
  | none =>
    simp only [optBoxU8At, optBoxU8Heap]
    have hpull : (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ⌜w0 = 0#64⌝ =
        ⌜w0 = 0#64⌝ ∗ ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) := by sep_focus
    rw [hpull]
    apply Entails.pure_left; rintro rfl
    rw [ProofLib.memRegion_eight (a + 8#64)]
    exact sepConj_mono_right (Entails.sepExists_intro w1)
  | some bs =>
    simp only [optBoxU8At, boxU8At_eq_boxU8Buf, optBoxU8Heap]
    have hpull : (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
        ⌜w0 = ptr ∧ w1 = BitVec.ofNat 64 bs.length⌝ ∗ boxU8Buf A ptr bs =
        ⌜w0 = ptr ∧ w1 = BitVec.ofNat 64 bs.length⌝ ∗
          ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ boxU8Buf A ptr bs) := by sep_focus
    rw [hpull]
    apply Entails.pure_left; rintro ⟨rfl, rfl⟩
    exact Entails.refl _

def msgWords15At (a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
  ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
  ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
  ((a + 96#64) ↦₆₄ w12) ∗ ((a + 104#64) ↦₆₄ w13) ∗ ((a + 112#64) ↦₆₄ w14)

theorem msgWords15At_entails_memRegion
    (a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64) :
    msgWords15At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 ⊢ memRegion a 120 := by
  unfold msgWords15At
  rw [show (120 : Nat) = 8 * 15 from rfl, ProofLib.memRegion_cells a 15 (by decide)]
  simp only [cells, sepConj_emp, ← sepExists_sepConj_left,
    show a + 8#64 + 8#64 = a + 16#64 by bv_lin,
    show a + 16#64 + 8#64 = a + 24#64 by bv_lin,
    show a + 24#64 + 8#64 = a + 32#64 by bv_lin,
    show a + 32#64 + 8#64 = a + 40#64 by bv_lin,
    show a + 40#64 + 8#64 = a + 48#64 by bv_lin,
    show a + 48#64 + 8#64 = a + 56#64 by bv_lin,
    show a + 56#64 + 8#64 = a + 64#64 by bv_lin,
    show a + 64#64 + 8#64 = a + 72#64 by bv_lin,
    show a + 72#64 + 8#64 = a + 80#64 by bv_lin,
    show a + 80#64 + 8#64 = a + 88#64 by bv_lin,
    show a + 88#64 + 8#64 = a + 96#64 by bv_lin,
    show a + 96#64 + 8#64 = a + 104#64 by bv_lin,
    show a + 104#64 + 8#64 = a + 112#64 by bv_lin]
  exact sepConj_mono (Entails.sepExists_intro w0)
    (sepConj_mono (Entails.sepExists_intro w1)
      (sepConj_mono (Entails.sepExists_intro w2)
        (sepConj_mono (Entails.sepExists_intro w3)
          (sepConj_mono (Entails.sepExists_intro w4)
            (sepConj_mono (Entails.sepExists_intro w5)
              (sepConj_mono (Entails.sepExists_intro w6)
                (sepConj_mono (Entails.sepExists_intro w7)
                  (sepConj_mono (Entails.sepExists_intro w8)
                    (sepConj_mono (Entails.sepExists_intro w9)
                      (sepConj_mono (Entails.sepExists_intro w10)
                        (sepConj_mono (Entails.sepExists_intro w11)
                          (sepConj_mono (Entails.sepExists_intro w12)
                            (sepConj_mono (Entails.sepExists_intro w13)
                              (Entails.sepExists_intro w14))))))))))))))

def signalMessageBounds (m : SignalMessage) : Prop :=
  macLength + 1 ≤ m.serialized.length ∧ m.serialized.length < 2 ^ 40 ∧
    m.ciphertext.length < 2 ^ 40 ∧ m.pqRatchet.length < 2 ^ 40 ∧
    (∀ ad, m.addresses = some ad → ad.length < 2 ^ 40)

def msgHeapAt (A : RustAlloc) (g : SignalMessageGhost) (m : SignalMessage)
    (addrW0 addrW1 : BitVec 64) : SepProp :=
  ⌜signalMessageBounds m⌝ ∗
    vecU8Heap A g.pqCap g.pqPtr m.pqRatchet ∗
    boxU8Buf A g.ctPtr m.ciphertext ∗
    boxU8Buf A g.serPtr m.serialized ∗
    optBoxU8Heap A g.addrPtr addrW0 addrW1 m.addresses

theorem signalMessageAt_unpack (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) (rk0 rk1 rk2 rk3 : BitVec 64)
    (hrk : ∀ b : BitVec 64, (b ↦ₛ m.senderRatchetKey.bytes.toList) =
      (b ↦₆₄ rk0) ∗ ((b + 8#64) ↦₆₄ rk1) ∗ ((b + 16#64) ↦₆₄ rk2) ∗ ((b + 24#64) ↦₆₄ rk3)) :
    signalMessageAt A g a m ⊢
      ∃∗ addrW0 : BitVec 64, ∃∗ addrW1 : BitVec 64, ∃∗ verHi56 : BitVec 56,
        msgWords15At a
          g.pqCap g.pqPtr (BitVec.ofNat 64 m.pqRatchet.length)
          g.ctPtr (BitVec.ofNat 64 m.ciphertext.length)
          g.serPtr (BitVec.ofNat 64 m.serialized.length)
          rk0 rk1 rk2 rk3 addrW0 addrW1
          (m.previousCounter ++ m.counter) (verHi56 ++ m.messageVersion) ∗
        msgHeapAt A g m addrW0 addrW1 := by
  unfold signalMessageAt msgWords15At msgHeapAt
  change (⌜signalMessageBounds m⌝ ∗ _) ⊢ _
  rw [vecU8At_eq_vecU8Heap A a g.pqCap g.pqPtr m.pqRatchet,
      boxU8At_eq_boxU8Buf A (a + 0x18#64) g.ctPtr m.ciphertext,
      boxU8At_eq_boxU8Buf A (a + 0x28#64) g.serPtr m.serialized,
      hrk (a + 0x38#64)]
  have hcnt : ((a + 0x68#64) ↦₃₂ m.counter) ∗ ((a + 0x6c#64) ↦₃₂ m.previousCounter) =
      ((a + 104#64) ↦₆₄ (m.previousCounter ++ m.counter)) := by
    have h6c : a + 0x6c#64 = (a + 0x68#64) + 4#64 := by bv_lin
    rw [h6c, pointsTo32_merge64]
  have hver := pointsTo8_memRegion7_to_64 (a + 0x70#64) m.messageVersion
  rw [show a + 0x70#64 + 1#64 = a + 0x71#64 by bv_lin] at hver
  have haddr := optBoxU8At_unpack A (a + 0x58#64) g.addrPtr m.addresses
  rw [← sepConj_assoc ((a + 0x68#64) ↦₃₂ m.counter), hcnt]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono haddr (sepConj_mono_right hver))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
  apply Entails.sepExists_elim; intro verHi56
  apply Entails.sepExists_elim; intro addrW0
  apply Entails.sepExists_elim; intro addrW1
  refine Entails.trans ?_ (Entails.sepExists_intro addrW0)
  refine Entails.trans ?_ (Entails.sepExists_intro addrW1)
  refine Entails.trans ?_ (Entails.sepExists_intro verHi56)
  exact entails_of_sep_focus (by sep_focus)

theorem signalMessageAt_pack (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) (rk0 rk1 rk2 rk3 addrW0 addrW1 : BitVec 64) (verHi56 : BitVec 56)
    (hrk : ∀ b : BitVec 64, (b ↦ₛ m.senderRatchetKey.bytes.toList) =
      (b ↦₆₄ rk0) ∗ ((b + 8#64) ↦₆₄ rk1) ∗ ((b + 16#64) ↦₆₄ rk2) ∗ ((b + 24#64) ↦₆₄ rk3)) :
    msgWords15At a
      g.pqCap g.pqPtr (BitVec.ofNat 64 m.pqRatchet.length)
      g.ctPtr (BitVec.ofNat 64 m.ciphertext.length)
      g.serPtr (BitVec.ofNat 64 m.serialized.length)
      rk0 rk1 rk2 rk3 addrW0 addrW1
      (m.previousCounter ++ m.counter) (verHi56 ++ m.messageVersion) ∗
      msgHeapAt A g m addrW0 addrW1 ⊢
    signalMessageAt A g a m := by
  unfold signalMessageAt msgWords15At msgHeapAt
  change _ ⊢ ⌜signalMessageBounds m⌝ ∗ _
  rw [vecU8At_eq_vecU8Heap A a g.pqCap g.pqPtr m.pqRatchet,
      boxU8At_eq_boxU8Buf A (a + 0x18#64) g.ctPtr m.ciphertext,
      boxU8At_eq_boxU8Buf A (a + 0x28#64) g.serPtr m.serialized,
      hrk (a + 0x38#64)]
  have hcnt : ((a + 104#64) ↦₆₄ (m.previousCounter ++ m.counter)) =
      ((a + 0x68#64) ↦₃₂ m.counter) ∗ ((a + 0x6c#64) ↦₃₂ m.previousCounter) := by
    have h6c : a + 0x6c#64 = (a + 0x68#64) + 4#64 := by bv_lin
    rw [h6c, pointsTo32_merge64]
  have hver := pointsTo64_to_8_memRegion7 (a + 0x70#64) verHi56 m.messageVersion
  rw [show a + 0x70#64 + 1#64 = a + 0x71#64 by bv_lin] at hver
  have haddr := optBoxU8At_pack A (a + 0x58#64) g.addrPtr addrW0 addrW1 m.addresses
  rw [hcnt]
  simp only [sepConj_assoc, arm64_norm] at haddr hver ⊢
  refine sep_entails_replace2 (F :=
    (a ↦₆₄ g.pqCap) ∗ ((a + 8#64) ↦₆₄ g.pqPtr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 m.pqRatchet.length) ∗
      ((a + 24#64) ↦₆₄ g.ctPtr) ∗ ((a + 32#64) ↦₆₄ BitVec.ofNat 64 m.ciphertext.length) ∗
      ((a + 40#64) ↦₆₄ g.serPtr) ∗ ((a + 48#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
      ((a + 56#64) ↦₆₄ rk0) ∗ ((a + 64#64) ↦₆₄ rk1) ∗
      ((a + 72#64) ↦₆₄ rk2) ∗ ((a + 80#64) ↦₆₄ rk3) ∗
      ((a + 104#64) ↦₃₂ m.counter) ∗ ((a + 108#64) ↦₃₂ m.previousCounter) ∗
      ⌜signalMessageBounds m⌝ ∗
      vecU8Heap A g.pqCap g.pqPtr m.pqRatchet ∗
      boxU8Buf A g.ctPtr m.ciphertext ∗
      boxU8Buf A g.serPtr m.serialized) hver haddr (by ac_rfl) (by ac_rfl)

theorem memRegion_sret_248 (r : BitVec 64) :
    memRegion r 248 =
      cells r 15 ∗
        (∃∗ p0 : BitVec 32, (r + 0x78#64) ↦₃₂ p0) ∗
        (∃∗ p1 : BitVec 32, (r + 0x7c#64) ↦₃₂ p1) ∗
        cells (r + 0x80#64) 13 ∗
        (∃∗ u0 : BitVec 32, (r + 0xe8#64) ↦₃₂ u0) ∗
        (∃∗ u1 : BitVec 32, (r + 0xec#64) ↦₃₂ u1) ∗
        (∃∗ b0 : BitVec 8, (r + 0xf0#64) ↦₈ b0) ∗
        memRegion (r + 0xf1#64) 7 := by
  rw [memRegion_split' (b := r) (b' := r + 0x78#64) (n := 120) (k := 128) (by decide) rfl (by decide),
      show (120 : Nat) = 8 * 15 by rfl, ProofLib.memRegion_cells r 15 (by decide),
      memRegion_split' (b := r + 0x78#64) (b' := r + 0x7c#64) (n := 4) (k := 124) (by decide)
        (by bv_lin) (by decide),
      memRegion_four (r + 0x78#64),
      memRegion_split' (b := r + 0x7c#64) (b' := r + 0x80#64) (n := 4) (k := 120) (by decide)
        (by bv_lin) (by decide),
      memRegion_four (r + 0x7c#64),
      memRegion_split' (b := r + 0x80#64) (b' := r + 0xe8#64) (n := 104) (k := 16) (by decide)
        (by bv_lin) (by decide),
      show (104 : Nat) = 8 * 13 by rfl, ProofLib.memRegion_cells (r + 0x80#64) 13 (by decide),
      memRegion_split' (b := r + 0xe8#64) (b' := r + 0xec#64) (n := 4) (k := 12) (by decide)
        (by bv_lin) (by decide),
      memRegion_four (r + 0xe8#64),
      memRegion_split' (b := r + 0xec#64) (b' := r + 0xf0#64) (n := 4) (k := 8) (by decide)
        (by bv_lin) (by decide),
      memRegion_four (r + 0xec#64),
      memRegion_split' (b := r + 0xf0#64) (b' := r + 0xf1#64) (n := 1) (k := 7) (by decide)
        (by bv_lin) (by decide),
      memRegion_one (r + 0xf0#64)]

theorem pointsTo32_entails_optU32At (a : BitVec 64) (preKeyId : Option (BitVec 32))
    (val32 : BitVec 32) (hval : ∀ v, preKeyId = some v → val32 = v) :
    (a ↦₃₂ (if preKeyId.isSome then 1#32 else 0#32)) ∗ ((a + 4#64) ↦₃₂ val32) ⊢
      LibsignalPublicApiRepr.optU32At a preKeyId := by
  cases preKeyId with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, LibsignalPublicApiRepr.optU32At,
      memRegion_four (a + 4#64)]
    exact sepConj_mono_right (Entails.sepExists_intro val32)
  | some v =>
    simp only [Option.isSome_some, ↓reduceIte, LibsignalPublicApiRepr.optU32At, hval v rfl]
    exact Entails.refl _

theorem sret_cells_entails_preKeyMsgAt (A : RustAlloc) (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost)
    (rk0 rk1 rk2 rk3 addrW0 addrW1 ky0 ky1 ky2 bk0 bk1 bk2 bk3 ik0 ik1 ik2 ik3 : BitVec 64)
    (verHi56 : BitVec 56)
    (hpre : ∀ v, x.preKeyId = some v → g.preKeyVal32 = v)
    (hrk : ∀ b : BitVec 64, (b ↦ₛ x.msg.senderRatchetKey.bytes.toList) =
      (b ↦₆₄ rk0) ∗ ((b + 8#64) ↦₆₄ rk1) ∗ ((b + 16#64) ↦₆₄ rk2) ∗ ((b + 24#64) ↦₆₄ rk3))
    (hbk : ∀ b : BitVec 64, (b ↦ₛ x.baseKey.bytes.toList) =
      (b ↦₆₄ bk0) ∗ ((b + 8#64) ↦₆₄ bk1) ∗ ((b + 16#64) ↦₆₄ bk2) ∗ ((b + 24#64) ↦₆₄ bk3))
    (hik : ∀ b : BitVec 64, (b ↦ₛ x.ik.publicKey.bytes.toList) =
      (b ↦₆₄ ik0) ∗ ((b + 8#64) ↦₆₄ ik1) ∗ ((b + 16#64) ↦₆₄ ik2) ∗ ((b + 24#64) ↦₆₄ ik3)) :
    (msgWords15At x.ret
      x.msgG.pqCap x.msgG.pqPtr (BitVec.ofNat 64 x.msg.pqRatchet.length)
      x.msgG.ctPtr (BitVec.ofNat 64 x.msg.ciphertext.length)
      x.msgG.serPtr (BitVec.ofNat 64 x.msg.serialized.length)
      rk0 rk1 rk2 rk3 addrW0 addrW1
      (x.msg.previousCounter ++ x.msg.counter) (verHi56 ++ x.msg.messageVersion) ∗
      msgHeapAt A x.msgG x.msg addrW0 addrW1) ∗
      (((x.ret + 120#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
        ((x.ret + 124#64) ↦₃₂ g.preKeyVal32)) ∗
      (kyberWords3At (x.ret + 0x90#64) ky0 ky1 ky2 ∗
        kyberHeap A x.kyPtr x.kp ky0 ky1 ky2) ∗
      ((x.ret + 128#64) ↦₆₄ g.serPtr) ∗
      ((x.ret + 136#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      boxU8Buf A g.serPtr x.model.serialized ∗
      ((x.ret + 168#64) ↦₆₄ bk0) ∗ ((x.ret + 176#64) ↦₆₄ bk1) ∗
      ((x.ret + 184#64) ↦₆₄ bk2) ∗ ((x.ret + 192#64) ↦₆₄ bk3) ∗
      ((x.ret + 200#64) ↦₆₄ ik0) ∗ ((x.ret + 208#64) ↦₆₄ ik1) ∗
      ((x.ret + 216#64) ↦₆₄ ik2) ∗ ((x.ret + 224#64) ↦₆₄ ik3) ∗
      ((x.ret + 232#64) ↦₃₂ x.regId) ∗ ((x.ret + 236#64) ↦₃₂ x.spk) ∗
      ((x.ret + 240#64) ↦₈ x.ver) ∗ memRegion (x.ret + 241#64) 7 ⊢
    ∃∗ g' : PreKeyMsgGhost, preKeyMsgAt A g' x.ret x.model := by
  refine Entails.trans ?_ (Entails.sepExists_intro ⟨x.msgG, g.serPtr, x.kyPtr⟩)
  have hmsg := signalMessageAt_pack A x.msgG x.ret x.msg rk0 rk1 rk2 rk3 addrW0 addrW1 verHi56 hrk
  have hu32 := pointsTo32_entails_optU32At (x.ret + 0x78#64) x.preKeyId g.preKeyVal32 hpre
  simp only [arm64_norm] at hu32
  have hky := optKyberAt_pack A (x.ret + 0x90#64) x.kyPtr x.kp ky0 ky1 ky2
  refine Entails.trans (sepConj_mono hmsg (sepConj_mono hu32 (sepConj_mono_left hky))) ?_
  unfold preKeyMsgAt
  have hm_msg : x.model.message = x.msg := rfl
  have hm_pk : x.model.preKeyId = x.preKeyId := rfl
  have hm_ky : x.model.kyberPayload = x.kp := rfl
  have hm_bk : x.model.baseKey = x.baseKey := rfl
  have hm_ik : x.model.identityKey = x.ik := rfl
  have hm_reg : x.model.registrationId = x.regId := rfl
  have hm_spk : x.model.signedPreKeyId = x.spk := rfl
  have hm_ver : x.model.messageVersion = x.ver := rfl
  rw [hm_msg, hm_pk, hm_ky, hm_bk, hm_ik, hm_reg, hm_spk, hm_ver,
      boxU8At_eq_boxU8Buf A (x.ret + 0x80#64) g.serPtr x.model.serialized,
      hbk (x.ret + 0xa8#64), hik (x.ret + 0xc8#64)]
  simp only [sepConj_assoc, arm64_norm]
  exact entails_of_sep_focus (by sep_focus)

/-! ## `into_boxed_slice` and 248-Byte `sret` Stores (`+0x4c4..+0x580`) -/

theorem sepWP_elim_optKyberAt {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {a ptr : BitVec 64} {kp : Option KyberPayload} {R : SepProp}
    {Q : State → SepProp → Prop}
    (h : ∀ ky0 ky1 ky2 : BitVec 64,
      SepWP prog ret s (R ∗ kyberWords3At a ky0 ky1 ky2 ∗ kyberHeap A ptr kp ky0 ky1 ky2) Q) :
    SepWP prog ret s (optKyberAt A a ptr kp ∗ R) Q := by
  refine SepWP.weaken_pre (sepConj_mono_left (optKyberAt_unpack A a ptr kp)) ?_
  simp only [sepExists_sepConj_left]
  refine SepWP.exists_elim fun ky0 => SepWP.exists_elim fun ky1 => SepWP.exists_elim fun ky2 => ?_
  rw [sepConj_comm _ R]
  exact h ky0 ky1 ky2

theorem sepWP_elim_signalMessageAt {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {g : SignalMessageGhost} {a : BitVec 64} {m : SignalMessage}
    {rk0 rk1 rk2 rk3 : BitVec 64}
    (hrk : ∀ b : BitVec 64, (b ↦ₛ m.senderRatchetKey.bytes.toList) =
      (b ↦₆₄ rk0) ∗ ((b + 8#64) ↦₆₄ rk1) ∗ ((b + 16#64) ↦₆₄ rk2) ∗ ((b + 24#64) ↦₆₄ rk3))
    {R : SepProp} {Q : State → SepProp → Prop}
    (h : ∀ (addrW0 addrW1 : BitVec 64) (verHi56 : BitVec 56),
      SepWP prog ret s
        (R ∗ msgWords15At a g.pqCap g.pqPtr (BitVec.ofNat 64 m.pqRatchet.length)
          g.ctPtr (BitVec.ofNat 64 m.ciphertext.length)
          g.serPtr (BitVec.ofNat 64 m.serialized.length)
          rk0 rk1 rk2 rk3 addrW0 addrW1
          (m.previousCounter ++ m.counter) (verHi56 ++ m.messageVersion) ∗
          msgHeapAt A g m addrW0 addrW1) Q) :
    SepWP prog ret s (signalMessageAt A g a m ∗ R) Q := by
  refine SepWP.weaken_pre
    (sepConj_mono_left (signalMessageAt_unpack A g a m rk0 rk1 rk2 rk3 hrk)) ?_
  simp only [sepExists_sepConj_left]
  refine SepWP.exists_elim fun addrW0 => SepWP.exists_elim fun addrW1 =>
    SepWP.exists_elim fun verHi56 => ?_
  rw [sepConj_comm _ R]
  exact h addrW0 addrW1 verHi56

theorem sepWP_elim_sret_248 {prog : Program} {ret : BitVec 64} {s : State}
    {r : BitVec 64} {R : SepProp} {Q : State → SepProp → Prop}
    (h : ∀ (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64)
           (p0 p1 : BitVec 32)
           (w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 : BitVec 64)
           (u0 u1 : BitVec 32) (b0 : BitVec 8),
      SepWP prog ret s
        ((r ↦₆₄ w0) ∗ ((r + 8#64) ↦₆₄ w1) ∗ ((r + 16#64) ↦₆₄ w2) ∗ ((r + 24#64) ↦₆₄ w3) ∗
         ((r + 32#64) ↦₆₄ w4) ∗ ((r + 40#64) ↦₆₄ w5) ∗ ((r + 48#64) ↦₆₄ w6) ∗
         ((r + 56#64) ↦₆₄ w7) ∗ ((r + 64#64) ↦₆₄ w8) ∗ ((r + 72#64) ↦₆₄ w9) ∗
         ((r + 80#64) ↦₆₄ w10) ∗ ((r + 88#64) ↦₆₄ w11) ∗ ((r + 96#64) ↦₆₄ w12) ∗
         ((r + 104#64) ↦₆₄ w13) ∗ ((r + 112#64) ↦₆₄ w14) ∗
         ((r + 120#64) ↦₃₂ p0) ∗ ((r + 124#64) ↦₃₂ p1) ∗
         ((r + 128#64) ↦₆₄ w16) ∗ ((r + 136#64) ↦₆₄ w17) ∗ ((r + 144#64) ↦₆₄ w18) ∗
         ((r + 152#64) ↦₆₄ w19) ∗ ((r + 160#64) ↦₆₄ w20) ∗ ((r + 168#64) ↦₆₄ w21) ∗
         ((r + 176#64) ↦₆₄ w22) ∗ ((r + 184#64) ↦₆₄ w23) ∗ ((r + 192#64) ↦₆₄ w24) ∗
         ((r + 200#64) ↦₆₄ w25) ∗ ((r + 208#64) ↦₆₄ w26) ∗ ((r + 216#64) ↦₆₄ w27) ∗
         ((r + 224#64) ↦₆₄ w28) ∗
         ((r + 232#64) ↦₃₂ u0) ∗ ((r + 236#64) ↦₃₂ u1) ∗
         ((r + 240#64) ↦₈ b0) ∗ memRegion (r + 241#64) 7 ∗ R) Q) :
    SepWP prog ret s (memRegion r 248 ∗ R) Q := by
  rw [memRegion_sret_248 r]
  simp only [cells, sepConj_emp, sepConj_assoc, sepExists_sepConj_left, arm64_norm]
  exact SepWP.exists_elim fun w0 => SepWP.exists_elim fun w1 => SepWP.exists_elim fun w2 =>
    SepWP.exists_elim fun w3 => SepWP.exists_elim fun w4 => SepWP.exists_elim fun w5 =>
    SepWP.exists_elim fun w6 => SepWP.exists_elim fun w7 => SepWP.exists_elim fun w8 =>
    SepWP.exists_elim fun w9 => SepWP.exists_elim fun w10 => SepWP.exists_elim fun w11 =>
    SepWP.exists_elim fun w12 => SepWP.exists_elim fun w13 => SepWP.exists_elim fun w14 =>
    SepWP.exists_elim fun p0 => SepWP.exists_elim fun p1 =>
    SepWP.exists_elim fun w16 => SepWP.exists_elim fun w17 => SepWP.exists_elim fun w18 =>
    SepWP.exists_elim fun w19 => SepWP.exists_elim fun w20 => SepWP.exists_elim fun w21 =>
    SepWP.exists_elim fun w22 => SepWP.exists_elim fun w23 => SepWP.exists_elim fun w24 =>
    SepWP.exists_elim fun w25 => SepWP.exists_elim fun w26 => SepWP.exists_elim fun w27 =>
    SepWP.exists_elim fun w28 => SepWP.exists_elim fun u0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun b0 => h w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 p0 p1
      w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 u0 u1 b0

theorem entails_replace3_left {P A1 B1 A2 B2 A3 B3 F : SepProp}
    (h1 : A1 ⊢ B1) (h2 : A2 ⊢ B2) (h3 : A3 ⊢ B3)
    (hP : P = (A1 ∗ A2 ∗ A3 ∗ F) ∗ emp) :
    P ⊢ B1 ∗ B2 ∗ B3 ∗ F := by
  rw [hP, sepConj_emp]
  exact sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_left h3))

theorem preKeyMsg_sret_stores_wp_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp0 lenW : BitVec 64)
    (hser_bound : x.model.serialized.length < 2 ^ 42)
    (hver : g.ver32.setWidth 8 = x.ver)
    (hpre : ∀ v, x.preKeyId = some v → g.preKeyVal32 = v)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 1220#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp_align : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = x.bkA)
    (hx19 : s.readReg64 .x19 =
      match x.kp with
      | none => noneCap
      | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hx20 : (s.readReg64 .x20).setWidth 32 = (if x.preKeyId.isSome then 1#32 else 0#32))
    (hx21 : (s.readReg64 .x21).setWidth 32 = x.spk)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 x.model.serialized.length)
    (hx24 : s.readReg64 .x24 = 33#64)
    (hx25 : (s.readReg64 .x25).setWidth 32 = g.preKeyVal32)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = g.bkSerPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      (if (match x.kp with
           | none => noneCap
           | some k => BitVec.ofNat 64 k.ciphertext.length).slt 1#64 then
        (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 1428#64
       else
        (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 1412#64)
      s
      (optKyberAt A x.kyA x.kyPtr x.kp ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       memRegion x.ret 248 ∗
       ((sp0 - 368#64) ↦₆₄ g.msgCopyPtr) ∗
       ((sp0 - 360#64) ↦₆₄ x.ikA) ∗
       ((sp0 - 344#64) ↦₃₂ x.regId) ∗
       ((sp0 - 332#64) ↦₃₂ g.ver32) ∗
       ((sp0 - 304#64) ↦₆₄ x.ret) ∗
       ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
       ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
       vecU8AtLen A (sp0 - 144#64) (BitVec.ofNat 64 x.model.serialized.length) g.serPtr lenW
         x.model.serialized ∗
       (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
       (x.ikA ↦ₛ x.ik.publicKey.bytes.toList))
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 =
           (match x.kp with
            | none => noneCap
            | some k => BitVec.ofNat 64 k.ciphertext.length) ∧
         sm.readReg64 .x20 = g.msgCopyPtr ∧
         sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = g.bkSerPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢
          memRegion x.kyA 24 ∗
          memRegion x.msgA 120 ∗
          (∃∗ g' : PreKeyMsgGhost, preKeyMsgAt A g' x.ret x.model) ∗
          ((sp0 - 368#64) ↦₆₄ g.msgCopyPtr) ∗
          ((sp0 - 360#64) ↦₆₄ x.ikA) ∗
          ((sp0 - 344#64) ↦₃₂ x.regId) ∗
          ((sp0 - 332#64) ↦₃₂ g.ver32) ∗
          ((sp0 - 304#64) ↦₆₄ x.ret) ∗
          ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
          ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
          ((sp0 - 144#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          ((sp0 - 136#64) ↦₆₄ g.serPtr) ∗
          ((sp0 - 128#64) ↦₆₄ lenW) ∗
          (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
          (x.ikA ↦ₛ x.ik.publicKey.bytes.toList))) := by
  preKeyMsg_fetches_range b (Rust.withPanics ext) 0x4c4 0x4cc
  preKeyMsg_fetches_range b (Rust.withPanics ext) 0x504 0x580
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry
  examples_hide_fetches
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length x.msg.senderRatchetKey.bytes)
  obtain ⟨bk0, bk1, bk2, bk3, _, hbk⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length x.baseKey.bytes)
  obtain ⟨ik0, ik1, ik2, ik3, _, hik⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length x.ik.publicKey.bytes)
  refine sepWP_elim_optKyberAt fun ky0 ky1 ky2 => ?_
  wp_conv_pre => rw [sepConj_assoc]
  refine sepWP_elim_signalMessageAt hrk fun addrW0 addrW1 verHi56 => ?_
  wp_conv_pre => rw [sepConj_assoc, sepConj_assoc]
  refine sepWP_elim_sret_248 fun w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 p0 p1
    w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 u0 u1 b0 => ?_
  wp_conv_pre =>
    rw [vecU8AtLen_exact_eq_boxU8Buf A (sp0 - 144#64) g.serPtr lenW x.model.serialized (by omega),
        hbk x.bkA, hik x.ikA]
    simp only [kyberWords3At, msgWords15At, sepConj_assoc, arm64_norm]
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
  · refine ⟨by simp only [wp_norm, arm64_norm, *],
      by simpa [State.spAligned, arm64_norm] using hsp_align,
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *]⟩
  · have hky_mem := kyberWords3At_entails_memRegion x.kyA ky0 ky1 ky2
    simp only [kyberWords3At, arm64_norm] at hky_mem
    have hmsg_mem := msgWords15At_entails_memRegion x.msgA
      x.msgG.pqCap x.msgG.pqPtr (BitVec.ofNat 64 x.msg.pqRatchet.length)
      x.msgG.ctPtr (BitVec.ofNat 64 x.msg.ciphertext.length)
      x.msgG.serPtr (BitVec.ofNat 64 x.msg.serialized.length)
      rk0 rk1 rk2 rk3 addrW0 addrW1
      (x.msg.previousCounter ++ x.msg.counter) (verHi56 ++ x.msg.messageVersion)
    simp only [msgWords15At, arm64_norm] at hmsg_mem
    have hsret := sret_cells_entails_preKeyMsgAt A x g
      rk0 rk1 rk2 rk3 addrW0 addrW1 ky0 ky1 ky2 bk0 bk1 bk2 bk3 ik0 ik1 ik2 ik3 verHi56
      hpre hrk hbk hik
    simp only [msgWords15At, kyberWords3At, Option.isSome, sepConj_assoc, arm64_norm] at hsret
    rw [hbk x.bkA, hik x.ikA]
    exact entails_replace3_left hky_mem hmsg_mem hsret
      (by (conv => rhs; arg 1; simp only [sepConj_assoc]); sep_focus)

theorem preKeyMsg_sret_stores_wp_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp0 lenW : BitVec 64)
    (hser_bound : x.model.serialized.length < 2 ^ 42) (hver : g.ver32.setWidth 8 = x.ver)
    (hpre : ∀ v, x.preKeyId = some v → g.preKeyVal32 = v) (s : State)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr preKeyMsgNewName + 1220#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = x.bkA)
    (hx19 : s.readReg64 .x19 = match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hx20 : (s.readReg64 .x20).setWidth 32 = (if x.preKeyId.isSome then 1#32 else 0#32))
    (hx21 : (s.readReg64 .x21).setWidth 32 = x.spk) (hx22 : s.readReg64 .x22 = 33#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 x.model.serialized.length) (hx24 : s.readReg64 .x24 = 33#64)
    (hx25 : (s.readReg64 .x25).setWidth 32 = g.preKeyVal32)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = g.bkSerPtr) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWP (trTrapProgAt b C abs)
      (if (match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length).slt 1#64 then
        (trTrapProgAt b C abs).fnAddr preKeyMsgNewName + 1428#64
       else (trTrapProgAt b C abs).fnAddr preKeyMsgNewName + 1412#64)
      s
      (optKyberAt A x.kyA x.kyPtr x.kp ∗ signalMessageAt A x.msgG x.msgA x.msg ∗ memRegion x.ret 248 ∗
       ((sp0 - 368#64) ↦₆₄ g.msgCopyPtr) ∗ ((sp0 - 360#64) ↦₆₄ x.ikA) ∗ ((sp0 - 344#64) ↦₃₂ x.regId) ∗
       ((sp0 - 332#64) ↦₃₂ g.ver32) ∗ ((sp0 - 304#64) ↦₆₄ x.ret) ∗ ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
       ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
       vecU8AtLen A (sp0 - 144#64) (BitVec.ofNat 64 x.model.serialized.length) g.serPtr lenW x.model.serialized ∗
       (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗ (x.ikA ↦ₛ x.ik.publicKey.bytes.toList))
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧
         sm.readReg64 .x19 = (match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length) ∧
         sm.readReg64 .x20 = g.msgCopyPtr ∧ sm.readReg64 .x22 = 33#64 ∧ sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧ sm.readReg64 .x28 = g.bkSerPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢ memRegion x.kyA 24 ∗ memRegion x.msgA 120 ∗
          (∃∗ g' : PreKeyMsgGhost, preKeyMsgAt A g' x.ret x.model) ∗
          ((sp0 - 368#64) ↦₆₄ g.msgCopyPtr) ∗ ((sp0 - 360#64) ↦₆₄ x.ikA) ∗ ((sp0 - 344#64) ↦₃₂ x.regId) ∗
          ((sp0 - 332#64) ↦₃₂ g.ver32) ∗ ((sp0 - 304#64) ↦₆₄ x.ret) ∗ ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
          ((sp0 - 280#64) ↦₆₄ x.kyA) ∗ ((sp0 - 144#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          ((sp0 - 136#64) ↦₆₄ g.serPtr) ∗ ((sp0 - 128#64) ↦₆₄ lenW) ∗
          (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗ (x.ikA ↦ₛ x.ik.publicKey.bytes.toList))) :=
  preKeyMsg_sret_stores_wp_ext (ext := trTrapExterns C abs) x g sp0 lenW hser_bound hver hpre s hpc hrun hsp
    hsp_align hx8 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29

theorem preKeyMsg_sret_stores_wp {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp0 lenW : BitVec 64)
    (hser_bound : x.model.serialized.length < 2 ^ 42)
    (hver : g.ver32.setWidth 8 = x.ver)
    (hpre : ∀ v, x.preKeyId = some v → g.preKeyVal32 = v)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 1220#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp_align : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = x.bkA)
    (hx19 : s.readReg64 .x19 =
      match x.kp with
      | none => noneCap
      | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hx20 : (s.readReg64 .x20).setWidth 32 = (if x.preKeyId.isSome then 1#32 else 0#32))
    (hx21 : (s.readReg64 .x21).setWidth 32 = x.spk)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 x.model.serialized.length)
    (hx24 : s.readReg64 .x24 = 33#64)
    (hx25 : (s.readReg64 .x25).setWidth 32 = g.preKeyVal32)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = g.bkSerPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      (if (match x.kp with
           | none => noneCap
           | some k => BitVec.ofNat 64 k.ciphertext.length).slt 1#64 then
        (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 1428#64
       else
        (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 1412#64)
      s
      (optKyberAt A x.kyA x.kyPtr x.kp ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       memRegion x.ret 248 ∗
       ((sp0 - 368#64) ↦₆₄ g.msgCopyPtr) ∗
       ((sp0 - 360#64) ↦₆₄ x.ikA) ∗
       ((sp0 - 344#64) ↦₃₂ x.regId) ∗
       ((sp0 - 332#64) ↦₃₂ g.ver32) ∗
       ((sp0 - 304#64) ↦₆₄ x.ret) ∗
       ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
       ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
       vecU8AtLen A (sp0 - 144#64) (BitVec.ofNat 64 x.model.serialized.length) g.serPtr lenW
         x.model.serialized ∗
       (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
       (x.ikA ↦ₛ x.ik.publicKey.bytes.toList))
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 =
           (match x.kp with
            | none => noneCap
            | some k => BitVec.ofNat 64 k.ciphertext.length) ∧
         sm.readReg64 .x20 = g.msgCopyPtr ∧
         sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = g.bkSerPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢
          memRegion x.kyA 24 ∗
          memRegion x.msgA 120 ∗
          (∃∗ g' : PreKeyMsgGhost, preKeyMsgAt A g' x.ret x.model) ∗
          ((sp0 - 368#64) ↦₆₄ g.msgCopyPtr) ∗
          ((sp0 - 360#64) ↦₆₄ x.ikA) ∗
          ((sp0 - 344#64) ↦₃₂ x.regId) ∗
          ((sp0 - 332#64) ↦₃₂ g.ver32) ∗
          ((sp0 - 304#64) ↦₆₄ x.ret) ∗
          ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
          ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
          ((sp0 - 144#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          ((sp0 - 136#64) ↦₆₄ g.serPtr) ∗
          ((sp0 - 128#64) ↦₆₄ lenW) ∗
          (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
          (x.ikA ↦ₛ x.ik.publicKey.bytes.toList))) := by
  rw [← trTrapProgAt_fnAddr_eq b C ctl abs preKeyMsgNewName] at hpc ⊢
  exact SepWP_kit_of_trTrap (preKeyMsg_sret_stores_wp_trap x g sp0 lenW hser_bound hver hpre s hpc hrun hsp hsp_align hx8 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29)

/-! ## Stack Frame Collapse Helpers (`+0x584..+0x608`) -/

theorem preKeyMsg_dealloc_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x15130)) (rustDeallocSpec A) :=
  dealloc_ok_at_norm hA (name := preKeyMsgNewName) (k := num% (ls_off% "__rustc::__rust_dealloc" - 0x15130))

theorem preKeyMsg_dealloc_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocHooks A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x15130))
      (rustDeallocSpec A) :=
  hook_ok_at (k := num% (ls_off% "__rustc::__rust_dealloc" - 0x15130))
    (stub := libsignalSessionCode.fnOff "__rustc::__rust_dealloc")
    (hname := "__rustc::__rust_dealloc") rfl
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    hA.dealloc

theorem preKeyMsg_dealloc_ok_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr preKeyMsgNewName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x15130)) (rustDeallocSpec A) :=
  dealloc_ok_at_norm_ext (AllocContracts.of_tripleRatchetProgAt_trap b C A abs hA)
    (name := preKeyMsgNewName) (k := num% (ls_off% "__rustc::__rust_dealloc" - 0x15130))

theorem stackAt_preKeyMsgSub_to_allocHook (sp : BitVec 64) :
    stackAt sp preKeyMsgSubStack = memRegion (sp - 7824#64) 3728 ∗ stackAt sp allocHookStack := by
  simp only [stackAt]
  exact memRegion_split' (N := 7824) (b := sp - 7824#64) (b' := sp - 4096#64) (n := 3728) (k := 4096)
    (by decide) (by bv_lin) (by decide)

theorem stackAt_preKeyMsgNew_to_allocHook (sp0 : BitVec 64) :
    stackAt sp0 preKeyMsgNewStack = memRegion (sp0 - 8192#64) 4096 ∗ stackAt sp0 allocHookStack := by
  simp only [stackAt]
  exact memRegion_split' (N := 8192) (b := sp0 - 8192#64) (b' := sp0 - 4096#64) (n := 4096) (k := 4096)
    (by decide) (by bv_lin) (by decide)

theorem preKeyMsgSavedRegs_entails_memRegion (sp0 : BitVec 64) (s0 : State) :
    preKeyMsgSavedRegs sp0 s0 ⊢ memRegion (sp0 - 96#64) 96 := by
  unfold preKeyMsgSavedRegs
  rw [memRegion_split' (b := sp0 - 96#64) (b' := sp0 - 88#64) (n := 8) (k := 88)
        (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 88#64) (b' := sp0 - 80#64) (n := 8) (k := 80)
        (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 80#64) (b' := sp0 - 72#64) (n := 8) (k := 72)
        (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 72#64) (b' := sp0 - 64#64) (n := 8) (k := 64)
        (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 64#64) (b' := sp0 - 56#64) (n := 8) (k := 56)
        (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 56#64) (b' := sp0 - 48#64) (n := 8) (k := 48)
        (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 48#64) (b' := sp0 - 40#64) (n := 8) (k := 40)
        (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 40#64) (b' := sp0 - 32#64) (n := 8) (k := 32)
        (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 32#64) (b' := sp0 - 24#64) (n := 8) (k := 24)
        (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 24#64) (b' := sp0 - 16#64) (n := 8) (k := 16)
        (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 16#64) (b' := sp0 - 8#64) (n := 8) (k := 8)
        (by decide) (by bv_lin) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (pointsTo64_entails_memRegion _ _)
                      (sepConj_mono (pointsTo64_entails_memRegion _ _)
                        (pointsTo64_entails_memRegion _ _)))))))))))

theorem preKeyMsgFrameWords_entails_stackAt (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (s0 : State)
    (sp0 lenW : BitVec 64) :
    stackAt (sp0 - 368#64) preKeyMsgSubStack ∗
      ((sp0 - 368#64) ↦₆₄ g.msgCopyPtr) ∗
      ((sp0 - 360#64) ↦₆₄ x.ikA) ∗
      ((sp0 - 352#64) ↦₆₄ g.ikSerPtr) ∗
      ((sp0 - 344#64) ↦₃₂ x.regId) ∗
      memRegion (sp0 - 340#64) 8 ∗
      ((sp0 - 332#64) ↦₃₂ g.ver32) ∗
      ((sp0 - 328#64) ↦₃₂ x.spk) ∗
      ((sp0 - 324#64) ↦₃₂ g.kyberId32) ∗
      ((sp0 - 320#64) ↦₆₄ g.kyberCopyPtr) ∗
      ((sp0 - 312#64) ↦₆₄ x.bkA) ∗
      ((sp0 - 304#64) ↦₆₄ x.ret) ∗
      ((sp0 - 296#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
      ((sp0 - 292#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
      ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
      ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
      memRegion (sp0 - 272#64) 128 ∗
      ((sp0 - 144#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      ((sp0 - 136#64) ↦₆₄ g.serPtr) ∗
      ((sp0 - 128#64) ↦₆₄ lenW) ∗
      memRegion (sp0 - 120#64) 24 ∗
      preKeyMsgSavedRegs sp0 s0 ⊢
    stackAt sp0 preKeyMsgNewStack := by
  have htop : stackAt sp0 preKeyMsgNewStack =
      stackAt (sp0 - 368#64) preKeyMsgSubStack ∗ memRegion (sp0 - 368#64) 368 := by
    simp only [stackAt, preKeyMsgSubStack, preKeyMsgNewStack, allocHookStack, preKeyMsgFrameSize, Nat.reduceAdd,
      Nat.reduceSub]
    rw [show sp0 - 368#64 - 7824#64 = sp0 - 8192#64 by bv_lin]
    exact memRegion_split' (N := 8192) (b := sp0 - 8192#64) (b' := sp0 - 368#64) (n := 7824) (k := 368)
      (by decide) (by bv_lin) (by decide)
  rw [htop,
      memRegion_split' (b := sp0 - 368#64) (b' := sp0 - 360#64) (n := 8) (k := 360) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 360#64) (b' := sp0 - 352#64) (n := 8) (k := 352) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 352#64) (b' := sp0 - 344#64) (n := 8) (k := 344) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 344#64) (b' := sp0 - 340#64) (n := 4) (k := 340) (by decide) (by bv_lin) (by decide),
      memRegion_split' (N := 340) (b := sp0 - 340#64) (b' := sp0 - 332#64) (n := 8) (k := 332) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 332#64) (b' := sp0 - 328#64) (n := 4) (k := 328) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 328#64) (b' := sp0 - 324#64) (n := 4) (k := 324) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 324#64) (b' := sp0 - 320#64) (n := 4) (k := 320) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 320#64) (b' := sp0 - 312#64) (n := 8) (k := 312) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 312#64) (b' := sp0 - 304#64) (n := 8) (k := 304) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 304#64) (b' := sp0 - 296#64) (n := 8) (k := 296) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 296#64) (b' := sp0 - 292#64) (n := 4) (k := 292) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 292#64) (b' := sp0 - 288#64) (n := 4) (k := 288) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 288#64) (b' := sp0 - 280#64) (n := 8) (k := 280) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 280#64) (b' := sp0 - 272#64) (n := 8) (k := 272) (by decide) (by bv_lin) (by decide),
      memRegion_split' (N := 272) (b := sp0 - 272#64) (b' := sp0 - 144#64) (n := 128) (k := 144) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 144#64) (b' := sp0 - 136#64) (n := 8) (k := 136) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 136#64) (b' := sp0 - 128#64) (n := 8) (k := 128) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 128#64) (b' := sp0 - 120#64) (n := 8) (k := 120) (by decide) (by bv_lin) (by decide),
      memRegion_split' (N := 120) (b := sp0 - 120#64) (b' := sp0 - 96#64) (n := 24) (k := 96) (by decide) (by bv_lin) (by decide)]
  exact sepConj_mono_right
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo32_entails_memRegion _ _)
            (sepConj_mono_right
              (sepConj_mono (pointsTo32_entails_memRegion _ _)
                (sepConj_mono (pointsTo32_entails_memRegion _ _)
                  (sepConj_mono (pointsTo32_entails_memRegion _ _)
                    (sepConj_mono (pointsTo64_entails_memRegion _ _)
                      (sepConj_mono (pointsTo64_entails_memRegion _ _)
                        (sepConj_mono (pointsTo64_entails_memRegion _ _)
                          (sepConj_mono (pointsTo32_entails_memRegion _ _)
                            (sepConj_mono (pointsTo32_entails_memRegion _ _)
                              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                                  (sepConj_mono_right
                                    (sepConj_mono (pointsTo64_entails_memRegion _ _)
                                      (sepConj_mono (pointsTo64_entails_memRegion _ _)
                                        (sepConj_mono (pointsTo64_entails_memRegion _ _)
                                          (sepConj_mono_right
                                            (preKeyMsgSavedRegs_entails_memRegion sp0 s0)))))))))))))))))))))

/-! ## Relocatable Placement Proofs -/

section Placed

open CryptoVerification.LibsignalPublicApi.Placed

theorem preKeyMsg_sret_stores_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp0 lenW : BitVec 64)
    (hser_bound : x.model.serialized.length < 2 ^ 42)
    (hver : g.ver32.setWidth 8 = x.ver)
    (hpre : ∀ v, x.preKeyId = some v → g.preKeyVal32 = v)
    (s : State)
    (hpc : s.pc = (blkPl_41).base + 1220#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp_align : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = x.bkA)
    (hx19 : s.readReg64 .x19 =
      match x.kp with
      | none => noneCap
      | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hx20 : (s.readReg64 .x20).setWidth 32 = (if x.preKeyId.isSome then 1#32 else 0#32))
    (hx21 : (s.readReg64 .x21).setWidth 32 = x.spk)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 x.model.serialized.length)
    (hx24 : s.readReg64 .x24 = 33#64)
    (hx25 : (s.readReg64 .x25).setWidth 32 = g.preKeyVal32)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = g.bkSerPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWP (lsProg_41 H)
      (if (match x.kp with
           | none => noneCap
           | some k => BitVec.ofNat 64 k.ciphertext.length).slt 1#64 then
        (blkPl_41).base + 1428#64
       else
        (blkPl_41).base + 1412#64)
      s
      (optKyberAt A x.kyA x.kyPtr x.kp ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       memRegion x.ret 248 ∗
       ((sp0 - 368#64) ↦₆₄ g.msgCopyPtr) ∗
       ((sp0 - 360#64) ↦₆₄ x.ikA) ∗
       ((sp0 - 344#64) ↦₃₂ x.regId) ∗
       ((sp0 - 332#64) ↦₃₂ g.ver32) ∗
       ((sp0 - 304#64) ↦₆₄ x.ret) ∗
       ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
       ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
       vecU8AtLen A (sp0 - 144#64) (BitVec.ofNat 64 x.model.serialized.length) g.serPtr lenW
         x.model.serialized ∗
       (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
       (x.ikA ↦ₛ x.ik.publicKey.bytes.toList))
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 =
           (match x.kp with
            | none => noneCap
            | some k => BitVec.ofNat 64 k.ciphertext.length) ∧
         sm.readReg64 .x20 = g.msgCopyPtr ∧
         sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = g.bkSerPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢
          memRegion x.kyA 24 ∗
          memRegion x.msgA 120 ∗
          (∃∗ g' : PreKeyMsgGhost, preKeyMsgAt A g' x.ret x.model) ∗
          ((sp0 - 368#64) ↦₆₄ g.msgCopyPtr) ∗
          ((sp0 - 360#64) ↦₆₄ x.ikA) ∗
          ((sp0 - 344#64) ↦₃₂ x.regId) ∗
          ((sp0 - 332#64) ↦₃₂ g.ver32) ∗
          ((sp0 - 304#64) ↦₆₄ x.ret) ∗
          ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
          ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
          ((sp0 - 144#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          ((sp0 - 136#64) ↦₆₄ g.serPtr) ∗
          ((sp0 - 128#64) ↦₆₄ lenW) ∗
          (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
          (x.ikA ↦ₛ x.ik.publicKey.bytes.toList))) := by
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length x.msg.senderRatchetKey.bytes)
  obtain ⟨bk0, bk1, bk2, bk3, _, hbk⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length x.baseKey.bytes)
  obtain ⟨ik0, ik1, ik2, ik3, _, hik⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length x.ik.publicKey.bytes)
  refine sepWP_elim_optKyberAt fun ky0 ky1 ky2 => ?_
  wp_conv_pre => rw [sepConj_assoc]
  refine sepWP_elim_signalMessageAt hrk fun addrW0 addrW1 verHi56 => ?_
  wp_conv_pre => rw [sepConj_assoc, sepConj_assoc]
  refine sepWP_elim_sret_248 fun w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 p0 p1
    w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 u0 u1 b0 => ?_
  wp_conv_pre =>
    rw [vecU8AtLen_exact_eq_boxU8Buf A (sp0 - 144#64) g.serPtr lenW x.model.serialized (by omega),
        hbk x.bkA, hik x.ikA]
    simp only [kyberWords3At, msgWords15At, sepConj_assoc, arm64_norm]
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
  · refine ⟨by simp only [wp_norm, arm64_norm, *],
      by simpa [State.spAligned, arm64_norm] using hsp_align,
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *]⟩
  · have hky_mem := kyberWords3At_entails_memRegion x.kyA ky0 ky1 ky2
    simp only [kyberWords3At, arm64_norm] at hky_mem
    have hmsg_mem := msgWords15At_entails_memRegion x.msgA
      x.msgG.pqCap x.msgG.pqPtr (BitVec.ofNat 64 x.msg.pqRatchet.length)
      x.msgG.ctPtr (BitVec.ofNat 64 x.msg.ciphertext.length)
      x.msgG.serPtr (BitVec.ofNat 64 x.msg.serialized.length)
      rk0 rk1 rk2 rk3 addrW0 addrW1
      (x.msg.previousCounter ++ x.msg.counter) (verHi56 ++ x.msg.messageVersion)
    simp only [msgWords15At, arm64_norm] at hmsg_mem
    have hsret := sret_cells_entails_preKeyMsgAt A x g
      rk0 rk1 rk2 rk3 addrW0 addrW1 ky0 ky1 ky2 bk0 bk1 bk2 bk3 ik0 ik1 ik2 ik3 verHi56
      hpre hrk hbk hik
    simp only [msgWords15At, kyberWords3At, Option.isSome, sepConj_assoc, arm64_norm] at hsret
    rw [hbk x.bkA, hik x.ikA]
    exact entails_replace3_left hky_mem hmsg_mem hsret
      (by (conv => rhs; arg 1; simp only [sepConj_assoc]); sep_focus)

theorem preKeyMsg_dealloc_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_41 H) (lsρ lsRustDeallocSym) (rustDeallocSpec A) :=
  ls_hook_ok_of_mem (prog := lsProg_41 H) (sym := lsRustDeallocSym) hdealloc

end Placed

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
