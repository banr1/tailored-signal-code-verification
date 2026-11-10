/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.OptImageHelper
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import ProofLib.SepLogic.WPp

/-!
# Verification of `core::ptr::drop_glue::<prost::error::DecodeError>`

Proves that `core::ptr::drop_glue::<prost::error::DecodeError>` (`0x242c`) satisfies
`dropDecodeErrorSpec` and `dropDecodeErrorSpecX`, both in-image and under `[LibsignalPlacement]`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Prost

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.InImageLift

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- `core::ptr::drop_glue::<prost::error::DecodeError>` meets `dropDecodeErrorSpec` on `tripleRatchetProgAtExt`. -/
def DropDecodeErrorOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr dropDecodeErrorName)
    (dropDecodeErrorSpec A)

/-- `prost::encoding::varint::decode_varint_slice` meets `decodeVarintSliceSpec` on `tripleRatchetProgAtExt`. -/
def DecodeVarintSliceOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr decodeVarintSliceName)
    (decodeVarintSliceSpec A)

/-- `prost::encoding::int32::merge::<&mut &[u8]>` meets `int32MergeSpec` on `tripleRatchetProgAtExt`. -/
def Int32MergeOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr int32MergeName)
    (int32MergeSpec A)

/-- `prost::encoding::skip_field::<&mut &[u8]> [local#1]` meets `skipFieldSpec` on `tripleRatchetProgAtExt`. -/
def SkipFieldOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr skipFieldName)
    (skipFieldSpec A)

/-- Add instruction-fetch hypotheses for a triple-ratchet function in `libsignalSessionCode`. -/
elab "tripleRatchet_fetches " b:term:max H:term:max hfn:term:max off:term:max len:term:max : tactic => open Lean Meta Elab Tactic in do
  let offLit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat off "tripleRatchet_fetches "))
  let k0Lit := Syntax.mkNumLit "0"
  let lenLit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat len "tripleRatchet_fetches "))
  let hfnId : Ident ← if hfn.raw.isIdent then pure ⟨hfn.raw⟩ else do
    let g ← getMainGoal
    let c? ← g.withContext do
      tryCatchRuntimeEx (do
        let e := (← instantiateMVars (← Term.elabTermAndSynthesize hfn none)).consumeMData
        return if e.isConst then some e.constName! else none) (fun _ => pure none)
    match c? with
    | some c => pure (mkCIdentFrom hfn c)
    | none =>
      let id := mkIdent `_hfn_layout
      evalTactic (← `(tactic| have $id := $hfn))
      pure id
  evalTactic (← `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin $b $H $hfnId:ident $offLit:num $k0Lit:num $lenLit:num))

/-! ## Hook lemma for `__rustc::__rust_dealloc` -/

theorem dealloc_ok_at {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = libsignalSessionCode.fnOff "__rustc::__rust_dealloc") :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (rustDeallocSpec A) := by
  refine hook_ok_at_raw (hname := "__rustc::__rust_dealloc") hfn hk
    (by fnoff_eq) (by fnoff_eq) ?_
  have h1 : Rust.withPanics (tripleRatchetExterns C ctl abs) "__rustc::__rust_dealloc" =
      abs "__rustc::__rust_dealloc" := by
    have h := congrArg (fun l => l[5]?) (tripleRatchetExterns_abs C ctl abs)
    simpa using h
  simpa only [HookSat, h1] using hA.dealloc

/-! ## Memory and stack helpers -/

theorem memRegion_split (a : BitVec 64) (n k : Nat) (h : n + k ≤ 2 ^ 64) :
    memRegion a (n + k) = memRegion a n ∗ memRegion (a + BitVec.ofNat 64 n) k :=
  IsBlock.eq (IsBlock.memRegion a (n + k))
    ((IsBlock.memRegion a n).sepConj (IsBlock.memRegion _ k) rfl h)
    fun _ => ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩

theorem memRegion_eight (a : BitVec 64) : memRegion a 8 = ∃∗ v, a ↦₆₄ v :=
  IsBlock.eq (IsBlock.memRegion a 8)
    (IsBlock.sepExists fun v => IsBlock.pointsTo64 a v)
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩

theorem pointsTo64_entails_memRegion8 (a v : BitVec 64) : (a ↦₆₄ v) ⊢ memRegion a 8 := by
  rw [memRegion_eight]
  exact Entails.sepExists_intro v

theorem stackAt_dropDecodeErrorGen {dStack : Nat} (hd : 0x20 + dStack ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (0x20 + dStack) =
      stackAt (sp - 32#64) dStack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
          ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
          ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) := by
  have h1 := stackAt_split_cells sp dStack 4 (by omega)
  rw [show 0x20 + dStack = dStack + 8 * 4 by omega, h1]
  change stackAt (sp - 32#64) dStack ∗ cells (sp - 32#64) 4 = _
  have hc4 : cells (sp - 32#64) 4 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
        ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) := by
    cells_unfold
  rw [hc4]

theorem stackAt_dropDecodeErrorGen_bottom {dStack : Nat} (hd : 0x20 + dStack ≤ 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp (0x20 + dStack) =
      memRegion (sp - BitVec.ofNat 64 (0x20 + dStack)) 32 ∗ stackAt sp dStack := by
  rw [show 0x20 + dStack = dStack + 32 by omega]
  exact ProofLib.stackAt_split_bottom sp dStack 32 (by omega)

theorem stackAt_dropDecodeErrorGen_tail {dStack : Nat} (hd : 0x20 + dStack ≤ 2 ^ 64)
    (sp v0 v1 v2 v3 : BitVec 64) :
    stackAt (sp - 32#64) dStack ∗
      ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
      ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
      memRegion (sp - BitVec.ofNat 64 (0x20 + dStack)) 32 ∗ stackAt sp dStack := by
  rw [← stackAt_dropDecodeErrorGen_bottom hd sp, stackAt_dropDecodeErrorGen hd sp]
  refine sepConj_mono_right ?_
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1
    (Entails.sepExists_right v2 (Entails.sepExists_right v3 (Entails.refl _))))

theorem stackAt_dropDecodeErrorGen_post {dStack : Nat} (hd : 0x20 + dStack ≤ 2 ^ 64)
    (sp : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 (0x20 + dStack)) 32 ∗ stackAt sp dStack =
      stackAt (sp - 32#64) dStack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
          ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
          ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) := by
  rw [← stackAt_dropDecodeErrorGen_bottom hd sp, stackAt_dropDecodeErrorGen hd sp]

theorem stackAt_dropDecodeError (sp : BitVec 64) :
    stackAt sp dropDecodeErrorStack =
      stackAt (sp - 32#64) allocHookStack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
          ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
          ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) :=
  stackAt_dropDecodeErrorGen (by decide) sp

theorem arrayAt_stackEntryAt (n : Nat) (p : BitVec 64) (h : n * 32 ≤ 2 ^ 64) :
    arrayAt stackEntryAt 32 p (List.replicate n ()) = memRegion p (n * 32) := by
  induction n generalizing p with
  | zero =>
    simp [arrayAt, memRegion_zero]
  | succ n ih =>
    rw [List.replicate_succ, arrayAt, stackEntryAt, ih (p + 32#64) (by omega),
      show (n + 1) * 32 = 32 + n * 32 by omega, memRegion_split p 32 (n * 32) (by omega)]

theorem stackVec_buf_memRegion {ptr : BitVec 64} {n cap : Nat}
    (h1 : n ≤ cap) (h2 : cap * 32 < 2 ^ 63) :
    arrayAt stackEntryAt 32 ptr (List.replicate n ()) ∗
      memRegion (ptr + BitVec.ofNat 64 (n * 32)) ((cap - n) * 32) =
      memRegion ptr (cap * 32) := by
  rw [arrayAt_stackEntryAt n ptr (by omega),
    ← memRegion_split ptr (n * 32) ((cap - n) * 32) (by omega)]
  congr 1
  omega

theorem box72_entails_memRegion (e cap ptr len w : BitVec 64) :
    (e ↦₆₄ cap) ∗ ((e + 8#64) ↦₆₄ ptr) ∗ ((e + 16#64) ↦₆₄ len) ∗
      ((e + 24#64) ↦₆₄ w) ∗ memRegion (e + 32#64) 40 ⊢ memRegion e 72 := by
  have h0 : (e ↦₆₄ cap) ⊢ memRegion e 8 := pointsTo64_entails_memRegion8 e cap
  have h1 : ((e + 8#64) ↦₆₄ ptr) ⊢ memRegion (e + 8#64) 8 :=
    pointsTo64_entails_memRegion8 (e + 8#64) ptr
  have h2 : ((e + 16#64) ↦₆₄ len) ⊢ memRegion (e + 16#64) 8 :=
    pointsTo64_entails_memRegion8 (e + 16#64) len
  have h3 : ((e + 24#64) ↦₆₄ w) ⊢ memRegion (e + 24#64) 8 :=
    pointsTo64_entails_memRegion8 (e + 24#64) w
  have s1 := memRegion_split e 8 64 (by decide)
  change memRegion e 72 = memRegion e 8 ∗ memRegion (e + 8#64) 64 at s1
  have s2 := memRegion_split (e + 8#64) 8 56 (by decide)
  change memRegion (e + 8#64) 64 = memRegion (e + 8#64) 8 ∗ memRegion (e + 8#64 + 8#64) 56 at s2
  rw [BitVec.add_assoc, show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl] at s2
  have s3 := memRegion_split (e + 16#64) 8 48 (by decide)
  change memRegion (e + 16#64) 56 = memRegion (e + 16#64) 8 ∗ memRegion (e + 16#64 + 8#64) 48 at s3
  rw [BitVec.add_assoc, show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl] at s3
  have s4 := memRegion_split (e + 24#64) 8 40 (by decide)
  change memRegion (e + 24#64) 48 = memRegion (e + 24#64) 8 ∗ memRegion (e + 24#64 + 8#64) 40 at s4
  rw [BitVec.add_assoc, show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl] at s4
  rw [s1, s2, s3, s4]
  exact sepConj_mono h0 (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (Entails.refl _))))

/-! ## Arithmetic lemmas for `drop_glue::<DecodeError>` -/

theorem shl5_toNat {cap : BitVec 64} (h : cap.toNat * 32 < 2 ^ 63) :
    (cap <<< 5).toNat = cap.toNat * 32 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  change (cap.toNat * 32) % 2 ^ 64 = cap.toNat * 32
  exact Nat.mod_eq_of_lt (by omega)

theorem kindNoHeap_branch_false {w : BitVec 64} (hw : KindNoHeap w) :
    (11#64).ule
      (if ConditionHolds CondCode.MI (subsPState64 w 0#64) = true then
        w ^^^ 9223372036854775808#64
       else 11#64) = false := by
  obtain ⟨h1, h2⟩ := hw
  unfold ConditionHolds subsPState64 AddWithCarry64
  have hw_eq : w = 0x8000000000000000#64 + (w.truncate 8).zeroExtend 64 := by bv_bits
  have hw8 : w.truncate 8 < 11#8 := by bv_bits
  rw [hw_eq]
  generalize w.truncate 8 = b at hw8 ⊢
  revert b hw8; decide

theorem stackAt_dropDecodeError_bottom (sp : BitVec 64) :
    stackAt sp dropDecodeErrorStack =
      memRegion (sp - BitVec.ofNat 64 dropDecodeErrorStack) 32 ∗ stackAt sp allocHookStack :=
  stackAt_dropDecodeErrorGen_bottom (by decide) sp

theorem stackAt_dropDecodeError_tail (sp v0 v1 v2 v3 : BitVec 64) :
    stackAt (sp - 32#64) allocHookStack ∗
      ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
      ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
      memRegion (sp - BitVec.ofNat 64 dropDecodeErrorStack) 32 ∗ stackAt sp allocHookStack :=
  stackAt_dropDecodeErrorGen_tail (by decide) sp v0 v1 v2 v3

theorem stackAt_dropDecodeError_post (sp : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 dropDecodeErrorStack) 32 ∗ stackAt sp allocHookStack =
      stackAt (sp - 32#64) allocHookStack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
          ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
          ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) :=
  stackAt_dropDecodeErrorGen_post (by decide) sp

theorem layoutOk_72_8 : LayoutOk 72 8 :=
  ⟨by decide, ⟨3, rfl⟩, by decide⟩

theorem layoutOk_mul32_8 {cap : BitVec 64} (hcap : cap ≠ 0) (hlt : cap.toNat * 32 < 2 ^ 63) :
    LayoutOk (cap.toNat * 32) 8 := by
  have hpos : 0 < cap.toNat := Nat.pos_of_ne_zero (fun h0 => hcap (BitVec.eq_of_toNat_eq h0))
  exact ⟨by omega, ⟨3, rfl⟩, by omega⟩

/-! ## Unified parameterized specification and proof -/

/-- Stack-parameterized `dropDecodeErrorSpec` (`= dropDecodeErrorSpec A` at `allocHookStack`,
`= dropDecodeErrorSpecX A` at `extHookStack`). -/
def dropDecodeErrorSpecGen (A : RustAlloc) (dStack : Nat) : Spec (BitVec 64) where
  pre := fun e s =>
    ⌜s.readReg64 .x0 = e⌝ ∗ decodeErrorAt A e ∗ A.pool ∗ stackAt s.sp (0x20 + dStack)
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp (0x20 + dStack)

section
attribute [local irreducible] _root_.Arm64.Program.fnOff

theorem dropDecodeError_ok_of_hooks_gen {oimg : Option Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)} {dStack : Nat} (hd : 0x20 + dStack ≤ 2 ^ 64)
    (hdealloc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr dropDecodeErrorName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]"))
      (specWithOptInv oimg (rustDeallocExternSpecWithStack A dStack))) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr dropDecodeErrorName)
      (specWithOptInv oimg (dropDecodeErrorSpecGen A dStack)) := by
  simp only [specWithOptInv, dropDecodeErrorSpecGen, decodeErrorAt, decodeErrorAtStackLen, vecOf, vecAt,
    vecHeader, vecBuf, stackAt_dropDecodeErrorGen hd, sepExists_sepConj_left, sepExists_sepConj_right,
    List.length_replicate, pure_sepConj_pure_assoc]
  simp only [specWithOptInv, rustDeallocExternSpecWithStack, pure_sepConj_pure_assoc] at hdealloc
  have hfn := (ls_lemma% fnOff "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]")
  tripleRatchet_fetches b H hfn (num% (ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]")) 164
  wp_init e s0
  examples_generalize_entry
  examples_hide_fetches
  have hkv : KindNoHeap v_stk_5 := by assumption
  have hbr := kindNoHeap_branch_false hkv
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have h_len_le : v_stk_4 ≤ v_stk_6.toNat := by assumption
  have h_cap_lt : v_stk_6.toNat * 32 < 2 ^ 63 := by assumption
  have hinv0 : OptCallInv oimg s0 := by assumption
  by_cases hcap0 : v_stk_6 = 0
  · subst hcap0
    simp only [ite_true, emp_sepConj]
    apply SepWP.seq_optImage (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]")) hinv0
    wp_steps
    apply SepWP.fold (box72_entails_memRegion e 0 v_stk_7 (BitVec.ofNat 64 v_stk_4) v_stk_5)
      (by sep_focus)
    apply SepWP.fold (stackAt_dropDecodeErrorGen_tail hd s0.sp _ _ _ _) (by sep_focus)
    apply SepWP.done (by rfl) (by simp only [arm64_norm, hrun])
    intro hinv1
    wp_call hdealloc (e, 72, 8)
    apply SepWP.fold (Entails.of_eq (stackAt_dropDecodeErrorGen_post hd s0.sp)) (by sep_focus)
    wp_done
  · have hcap_beq : (v_stk_6 == 0#64) = false := beq_eq_false_iff_ne.mpr hcap0
    have hshl : (v_stk_6 <<< 5).toNat = v_stk_6.toNat * 32 := shl5_toNat h_cap_lt
    have hlay_vec : LayoutOk (v_stk_6.toNat * 32) 8 := layoutOk_mul32_8 hcap0 h_cap_lt
    have hpos_vec : 0 < v_stk_6.toNat * 32 := hlay_vec.1
    have hsum_vec : v_stk_6.toNat * 32 + 8 ≤ 2 ^ 63 := hlay_vec.2.2
    simp only [hcap0, ite_false, stackVec_buf_memRegion h_len_le h_cap_lt]
    apply SepWP.seq_optImage (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]")) hinv0
    wp_steps
    apply SepWP.done (by rfl) (by simp only [arm64_norm, hrun])
    intro hinv1
    apply SepWP.seq_optImage (mid := entry + bv% (72)) hinv1
    wp_call hdealloc (v_stk_7, v_stk_6.toNat * 32, 8)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1'
    apply SepWP.seq_optImage (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]")) hinv1'
    wp_steps
    apply SepWP.fold (box72_entails_memRegion e v_stk_6 v_stk_7 (BitVec.ofNat 64 v_stk_4) v_stk_5)
      (by sep_focus)
    apply SepWP.fold (stackAt_dropDecodeErrorGen_tail hd s0.sp _ _ _ _) (by sep_focus)
    apply SepWP.done (by rfl) (by simp only [arm64_norm, *])
    intro hinv2
    wp_call hdealloc (e, 72, 8)
    apply SepWP.fold (Entails.of_eq (stackAt_dropDecodeErrorGen_post hd s0.sp)) (by sep_focus)
    wp_done

end

theorem dropDecodeError_ok_of_contract {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr dropDecodeErrorName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]"))
      (rustDeallocSpec A)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr dropDecodeErrorName)
      (dropDecodeErrorSpec A) :=
  subroutine_ok_of_optNone
    (dropDecodeError_ok_of_hooks_gen (oimg := none) (dStack := allocHookStack) (by decide)
      (subroutine_ok_to_optNone (rustDeallocExternWithStack_of_rustDealloc hdealloc)))

theorem dropDecodeError_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    DropDecodeErrorOkExt b A ext :=
  dropDecodeError_ok_of_contract
    (hA.dealloc_ok_at dropDecodeErrorName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]"))
      (by fnoff_eq))

theorem dropDecodeError_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    DropDecodeErrorOk b C A ctl abs :=
  dropDecodeError_ok_of_contract
    (dealloc_ok_at (b := b) (C := C) (ctl := ctl)
      hA (ls_lemma% fnOff "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]")
      (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]"))
      (by decide))

/-! ## Extended-stack variants and shared `SepWPp` invariant combinators -/

/-- `core::ptr::drop_glue::<prost::error::DecodeError>` meets `(dropDecodeErrorSpecX A).inImage img` on `tripleRatchetProgAtExt`. -/
def DropDecodeErrorOkExtX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr dropDecodeErrorName)
    ((dropDecodeErrorSpecX A).inImage img)

/-- `prost::encoding::varint::decode_varint_slice` meets `(decodeVarintSliceSpecX A).inImage img` on `tripleRatchetProgAtExt`. -/
def DecodeVarintSliceOkExtX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr decodeVarintSliceName)
    ((decodeVarintSliceSpecX A).inImage img)

/-- `prost::encoding::int32::merge::<&mut &[u8]>` meets `(int32MergeSpecX A).inImage img` on `tripleRatchetProgAtExt`. -/
def Int32MergeOkExtX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr int32MergeName)
    ((int32MergeSpecX A).inImage img)

/-- `prost::encoding::skip_field::<&mut &[u8]> [local#1]` meets `(skipFieldSpecX A).inImage img` on `tripleRatchetProgAtExt`. -/
def SkipFieldOkExtX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr skipFieldName)
    ((skipFieldSpecX A).inImage img)

theorem SepWP.seq_callInv {prog : Program} {img : Obj.Image} {mid_pc target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h1 : SepWP prog mid_pc s P (fun sm P_m =>
      img.FrozenLoaded sm → sm.symtab = img.symtab → SepWP prog target_pc sm P_m post)) :
    SepWP prog target_pc s P post :=
  SepWP.seq_optImage (oimg := some img) ⟨hfrozen, hsym⟩
    (SepWP.mono h1 fun _ _ _ _ hnext hinv => hnext hinv.1 hinv.2)

theorem SepWPp.of_sepWP_inv {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog mid s P (fun sm Pm =>
      img.FrozenLoaded sm → sm.symtab = img.symtab → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP_optImage (oimg := some img) ⟨hfl, hsym⟩
    (SepWP.mono h fun _ _ _ _ hnext hinv => hnext hinv.1 hinv.2)

theorem SepWPp.call_inv {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.call_wpp_frozen hcall (x := x) (F := F) hfl hsym hpc hrun hsp hlr hpre hexit
    (fun sf hpan _ => hpanic sf hpan) hnext
    (fun sf R' hoom_s hpost => (hoom sf (F ∗ R') hoom_s hpost).elim)

theorem SepWPp.call_frame_inv {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = ⌜img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗ (⌜φ⌝ ∗ T))
    (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call_inv (x := x) (F := F) hcall hfl hsym hpc hrun hsp hlr ?_ hexit hpanic hnext hoom
  intro R hm
  rw [hspec, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hfl, hsym⟩, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
  exact ⟨hφ, hm⟩

theorem subroutine_ok_inImage_of_sepWPp {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} {img : Obj.Image}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry → s0.status = .Running →
      img.FrozenLoaded s0 → s0.symtab = img.symtab →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
        SepWPp prog (s0.readReg64 Reg.lr) s0 P
          (fun sf P_f => ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    subroutine_ok prog entry (spec.inImage img) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h x R s0 hpc hrun hpre.1.1 hpre.1.2 hpre.2 hsp

open Lean Elab Tactic Meta in
elab "wpp_init_inImage " a:ident s0:ident hfl:ident hsym:ident : tactic => do
  let rId := mkIdent `R
  let hpcId := mkIdent `hpc
  let hrunId := mkIdent `hrun
  let hpreId := mkIdent `hpre
  let hspId := mkIdent `hsp_align
  evalTactic (← `(tactic| (
    apply subroutine_ok_inImage_of_sepWPp
    wp_unfold_specs
    intro $a:ident $rId:ident $s0:ident $hpcId:ident $hrunId:ident $hfl:ident $hsym:ident $hpreId:ident $hspId:ident)))
  wpSplitAndNormHyps (unpackProds := false)
  let g ← getMainGoal
  let (pExpr, fExpr) ← g.withContext do
    let lctx ← getLCtx
    let rFVar := (lctx.findFromUserName? rId.getId).map (·.toExpr)
    let mut fullPreOpt : Option Expr := none
    for decl in lctx do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let ty ← instantiateMVars decl.type
        if ty.isAppOfArity ``SepProp.Satisfies 2 then
          fullPreOpt := some (ty.getArg! 0)
          break
    let fullPre := fullPreOpt.getD (rFVar.getD (mkConst ``SepProp.emp))
    let atoms := SepSolver.atoms fullPre
    let spatial := atoms.filter (fun (e : Expr) => rFVar != some e)
    let conj : Expr :=
      if spatial.isEmpty then mkConst ``SepProp.emp
      else
        let n := spatial.size
        (List.range (n - 1)).foldr
          (fun i acc => mkApp2 (mkConst ``SepProp.sepConj) spatial[i]! acc) spatial[n - 1]!
    Pure.pure (conj, rFVar.getD (mkConst ``SepProp.emp))
  let pStx ← g.withContext (PrettyPrinter.delab pExpr)
  let fStx ← g.withContext (PrettyPrinter.delab fExpr)
  evalTactic (← `(tactic| (
    refine ⟨$pStx, $fStx, ?_, ?_⟩
    wp_focus_close arm64_sep_close)))

theorem SepWPp.call_optImage {α : Type} {prog : Program} {oimg : Option Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (specWithOptInv oimg spec))
    (hinv : OptCallInv oimg s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      OptCallInv oimg sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPp prog ret s P Q Qp := by
  cases oimg with
  | none =>
    exact SepWPp.call_wpp hcall (x := x) (F := F) hpc hrun hsp hlr
      (fun R hm => by
        dsimp only [specWithOptInv]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨hinv, hpre R hm⟩)
      hexit (fun sf hpan _ => hpanic sf hpan)
      (fun sf hpcm hrunm hspm hcsm => hnext sf hpcm hrunm hspm hcsm trivial)
      (fun sf R' hoom_s hpost => (hoom sf (F ∗ R') hoom_s hpost).elim)
  | some img =>
    exact SepWPp.call_inv (x := x) (F := F) hcall hinv.1 hinv.2 hpc hrun hsp hlr
      (fun R hm => by
        dsimp only [specWithOptInv]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨hinv, hpre R hm⟩)
      hexit hpanic
      (fun sf hpcm hrunm hspm hcsm hflm hsymm => hnext sf hpcm hrunm hspm hcsm ⟨hflm, hsymm⟩)
      hoom

theorem SepWPp.call_frame_optImage {α : Type} {prog : Program} {oimg : Option Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (specWithOptInv oimg spec))
    (hinv : OptCallInv oimg s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = ⌜φ⌝ ∗ T)
    (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      OptCallInv oimg sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call_optImage (x := x) (F := F) hcall hinv hpc hrun hsp hlr ?_ hexit hpanic hnext hoom
  intro R hm
  rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
  exact ⟨hφ, hm⟩

theorem subroutine_ok_optImage_of_sepWPp {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} {oimg : Option Obj.Image}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry → s0.status = .Running →
      OptCallInv oimg s0 →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
        SepWPp prog (s0.readReg64 Reg.lr) s0 P
          (fun sf P_f => ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    subroutine_ok prog entry (specWithOptInv oimg spec) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  rw [specWithOptInv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h x R s0 hpc hrun hpre.1 hpre.2 hsp

open Lean Elab Tactic Meta in
elab "wpp_init_optImage " a:ident s0:ident hinv:ident : tactic => do
  let rId := mkIdent `R
  let hpcId := mkIdent `hpc
  let hrunId := mkIdent `hrun
  let hpreId := mkIdent `hpre
  let hspId := mkIdent `hsp_align
  evalTactic (← `(tactic| (
    apply subroutine_ok_optImage_of_sepWPp
    wp_unfold_specs
    intro $a:ident $rId:ident $s0:ident $hpcId:ident $hrunId:ident $hinv:ident $hpreId:ident $hspId:ident)))
  wpSplitAndNormHyps (unpackProds := false)
  let g ← getMainGoal
  let (pExpr, fExpr) ← g.withContext do
    let lctx ← getLCtx
    let rFVar := (lctx.findFromUserName? rId.getId).map (·.toExpr)
    let mut fullPreOpt : Option Expr := none
    for decl in lctx do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let ty ← instantiateMVars decl.type
        if ty.isAppOfArity ``SepProp.Satisfies 2 then
          fullPreOpt := some (ty.getArg! 0)
          break
    let fullPre := fullPreOpt.getD (rFVar.getD (mkConst ``SepProp.emp))
    let atoms := SepSolver.atoms fullPre
    let spatial := atoms.filter (fun (e : Expr) => rFVar != some e)
    let conj : Expr :=
      if spatial.isEmpty then mkConst ``SepProp.emp
      else
        let n := spatial.size
        (List.range (n - 1)).foldr
          (fun i acc => mkApp2 (mkConst ``SepProp.sepConj) spatial[i]! acc) spatial[n - 1]!
    Pure.pure (conj, rFVar.getD (mkConst ``SepProp.emp))
  let pStx ← g.withContext (PrettyPrinter.delab pExpr)
  let fStx ← g.withContext (PrettyPrinter.delab fExpr)
  evalTactic (← `(tactic| (
    refine ⟨$pStx, $fStx, ?_, ?_⟩
    wp_focus_close arm64_sep_close)))

theorem decodeErrorFromSpecWithStack_inImage_mono {P : Program} {addr : BitVec 64} {img : Obj.Image}
    {A : RustAlloc} {s1 s2 : Nat}
    (h : subroutine_ok P addr ((decodeErrorFromSpecWithStack A s1).inImage img))
    (hle : s1 ≤ s2 := by decide) (hmax : s2 ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr ((decodeErrorFromSpecWithStack A s2).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨k, w⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h1 := stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R
  have hpre' : s0.mem ⊨ ((decodeErrorFromSpecWithStack A s1).inImage img).pre (k, w) s0 ∗ R' := by
    dsimp only [Spec.inImage, decodeErrorFromSpecWithStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (k, w) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, decodeErrorFromSpecWithStack, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, decodeErrorFromSpecWithStack, R'] at hpost ⊢
    rw [← sepConj_assoc] at hpost
    exact allowPanic_frame id hpost
  · dsimp only [Spec.inImage, decodeErrorFromSpecWithStack] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [Spec.inImage, decodeErrorFromSpecWithStack] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem stackAt_dropDecodeErrorX (sp : BitVec 64) :
    stackAt sp dropDecodeErrorStackX =
      stackAt (sp - 32#64) extHookStack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
          ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
          ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) :=
  stackAt_dropDecodeErrorGen (dStack := extHookStack) (by decide) sp

theorem stackAt_dropDecodeErrorX_bottom (sp : BitVec 64) :
    stackAt sp dropDecodeErrorStackX =
      memRegion (sp - BitVec.ofNat 64 dropDecodeErrorStackX) 32 ∗ stackAt sp extHookStack :=
  stackAt_dropDecodeErrorGen_bottom (dStack := extHookStack) (by decide) sp

theorem stackAt_dropDecodeErrorX_tail (sp v0 v1 v2 v3 : BitVec 64) :
    stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
      ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
      memRegion (sp - BitVec.ofNat 64 dropDecodeErrorStackX) 32 ∗ stackAt sp extHookStack :=
  stackAt_dropDecodeErrorGen_tail (dStack := extHookStack) (by decide) sp v0 v1 v2 v3

theorem stackAt_dropDecodeErrorX_post (sp : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 dropDecodeErrorStackX) 32 ∗ stackAt sp extHookStack =
      stackAt (sp - 32#64) extHookStack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
          ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
          ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) :=
  stackAt_dropDecodeErrorGen_post (dStack := extHookStack) (by decide) sp

theorem dropDecodeError_ok_of_contract_x {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr dropDecodeErrorName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr dropDecodeErrorName)
      ((dropDecodeErrorSpecX A).inImage img) :=
  dropDecodeError_ok_of_hooks_gen (oimg := some img) (dStack := extHookStack) (by decide) hdealloc

theorem dropDecodeError_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    DropDecodeErrorOkExtX img A ext :=
  dropDecodeError_ok_of_contract_x
    (hA.dealloc_ok_at dropDecodeErrorName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]"))
      (by fnoff_eq))

/-! ## Relocatable per-block contract (block 5) -/

theorem drop_decode_error_placed_ok_gen [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {dStack : Nat} (hd : 0x20 + dStack ≤ 2 ^ 64 := by decide)
    (hdealloc : subroutine_ok ((blkPC_4).rebase (blkPl_4).base H) (lsρ lsRustDeallocSym)
      (rustDeallocExternSpecWithStack A dStack)) :
    subroutine_ok ((blkPC_4).rebase (blkPl_4).base H) (blkPl_4).base
      (dropDecodeErrorSpecGen A dStack) := by
  simp only [dropDecodeErrorSpecGen, decodeErrorAt, decodeErrorAtStackLen, vecOf, vecAt,
    vecHeader, vecBuf, stackAt_dropDecodeErrorGen hd, sepExists_sepConj_left, sepExists_sepConj_right,
    List.length_replicate]
  simp only [rustDeallocExternSpecWithStack] at hdealloc
  wp_init e s0
  have hkv : KindNoHeap v_stk_5 := by assumption
  have hbr := kindNoHeap_branch_false hkv
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have h_len_le : v_stk_4 ≤ v_stk_6.toNat := by assumption
  have h_cap_lt : v_stk_6.toNat * 32 < 2 ^ 63 := by assumption
  by_cases hcap0 : v_stk_6 = 0
  · subst hcap0
    simp only [ite_true, emp_sepConj]
    wp_steps
    apply SepWP.fold (box72_entails_memRegion e 0 v_stk_7 (BitVec.ofNat 64 v_stk_4) v_stk_5)
      (by sep_focus)
    apply SepWP.fold (stackAt_dropDecodeErrorGen_tail hd s0.sp _ _ _ _) (by sep_focus)
    wp_call hdealloc (e, 72, 8)
    apply SepWP.fold (Entails.of_eq (stackAt_dropDecodeErrorGen_post hd s0.sp)) (by sep_focus)
    wp_done
  · have hcap_beq : (v_stk_6 == 0#64) = false := beq_eq_false_iff_ne.mpr hcap0
    have hshl : (v_stk_6 <<< 5).toNat = v_stk_6.toNat * 32 := shl5_toNat h_cap_lt
    have hlay_vec : LayoutOk (v_stk_6.toNat * 32) 8 := layoutOk_mul32_8 hcap0 h_cap_lt
    have hpos_vec : 0 < v_stk_6.toNat * 32 := hlay_vec.1
    have hsum_vec : v_stk_6.toNat * 32 + 8 ≤ 2 ^ 63 := hlay_vec.2.2
    simp only [hcap0, ite_false, stackVec_buf_memRegion h_len_le h_cap_lt]
    wp_steps
    wp_call hdealloc (v_stk_7, v_stk_6.toNat * 32, 8)
    wp_steps
    apply SepWP.fold (box72_entails_memRegion e v_stk_6 v_stk_7 (BitVec.ofNat 64 v_stk_4) v_stk_5)
      (by sep_focus)
    apply SepWP.fold (stackAt_dropDecodeErrorGen_tail hd s0.sp _ _ _ _) (by sep_focus)
    wp_call hdealloc (e, 72, 8)
    apply SepWP.fold (Entails.of_eq (stackAt_dropDecodeErrorGen_post hd s0.sp)) (by sep_focus)
    wp_done

theorem drop_decode_error_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_4).rebase (blkPl_4).base H) (blkPl_4).base
      (dropDecodeErrorSpec A) :=
  drop_decode_error_placed_ok_gen (dStack := allocHookStack) (by decide)
    (rustDeallocExternWithStack_of_rustDealloc (ls_hook_ok_of_mem hdealloc))

theorem drop_decode_error_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_4).rebase (blkPl_4).base H) (blkPl_4).base
      (dropDecodeErrorSpecX A) :=
  drop_decode_error_placed_ok_gen (dStack := extHookStack) (by decide)
    (rustDeallocExternWithStack_of_rustDealloc (ls_hook_ok_of_mem hdealloc) (by decide) (by decide))

end CryptoVerification.LibsignalTripleRatchet.Prost
