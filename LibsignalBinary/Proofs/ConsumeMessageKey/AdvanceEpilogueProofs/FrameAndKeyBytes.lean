/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.Seams
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.SpecLemmas.ReachesOutcome
import ProofLib.SepLogic.WP.Structural

@[expose] public section

set_option maxHeartbeats 800000
set_option autoImplicit false

namespace CryptoVerification.LibsignalSession.AdvanceEpilogue

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.SessionModel

noncomputable abbrev SP (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State)) : Program :=
  libsignalSessionCode.rebase b (Rust.withPanics (sessionExterns F alloc))

def sessionShimSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝

theorem sessionShim_hookOk : HookOk hookNoop sessionShimSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  simp only [sessionShimSpec, hookNoop, retHook, id_eq, State.trace_setPC,
    satisfies_pure_sepConj, true_and, emp_sepConj] at hpre ⊢
  exact hpre

/-- `alloc::raw_vec::handle_error` (`0x47f6c`) transitions to panic. -/
theorem panic_at_handle_error {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "alloc::raw_vec::handle_error")) :
    (SP b F alloc).externAt? ((SP b F alloc).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_panicSymbol hfn hk (by decide) (ls_hook% "alloc::raw_vec::handle_error")
    (by simp [Rust.isPanicSymbol])

theorem shim_ok_at {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2")) :
    subroutine_ok (SP b F alloc) ((SP b F alloc).fnAddr name + BitVec.ofNat 64 k)
      sessionShimSpec :=
  hook_ok_at hfn hk (by decide) (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (by simp [Rust.isPanicSymbol])
    ⟨hookNoop, rfl, sessionShim_hookOk⟩

theorem alloc_ok_at {A : RustAlloc} {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} (hA : AllocHooks A alloc)
    {name : String} {off k : Nat} (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = num% (ls_off% "__rustc::__rust_alloc")) :
    subroutine_ok (SP b F alloc) ((SP b F alloc).fnAddr name + BitVec.ofNat 64 k)
      (rustAllocSpec A) :=
  hook_ok_at_raw hfn hk (by decide) (ls_hook% "__rustc::__rust_alloc")
    (allocHooks_sessionExterns F A alloc hA).alloc

theorem dealloc_ok_at {A : RustAlloc} {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} (hA : AllocHooks A alloc)
    {name : String} {off k : Nat} (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = num% (ls_off% "__rustc::__rust_dealloc")) :
    subroutine_ok (SP b F alloc) ((SP b F alloc).fnAddr name + BitVec.ofNat 64 k)
      (rustDeallocSpec A) :=
  hook_ok_at_raw hfn hk (by decide) (ls_hook% "__rustc::__rust_dealloc")
    (allocHooks_sessionExterns F A alloc hA).dealloc

theorem chainStepN_one (F : ShaState → List (BitVec 8) → ShaState) (ckc : ChainKey) :
    chainStepN F 1 ckc =
      ⟨bytesToKey32 (Ratchet.chainHmac F ckc.key Ratchet.chainKeySeed), ckc.index + 1⟩ := rfl

theorem hmacWith_two_eq_chainStep (F : ShaState → List (BitVec 8) → ShaState) (k : BitVec 256) :
    hmacWith F (keyToBytes32 k) [0x02#8] = Ratchet.chainHmac F k Ratchet.chainKeySeed := rfl

theorem hmacWith_one_eq_messageKeys_seed (F : ShaState → List (BitVec 8) → ShaState) (ckc : ChainKey) :
    hmacWith F (keyToBytes32 ckc.key) [0x01#8] = (ckc.messageKeys F).seed := rfl

@[local simp] private theorem toBEBytes_length (n : ℕ) (w : BitVec (8 * n)) :
    (toBEBytes n w).length = n := by
  simp [toBEBytes]

@[local simp] private theorem shaState_flatMap_length (h : ShaState) :
    (h.toList.flatMap (toBEBytes 4)).length = 32 := by
  rcases h with ⟨l, hl⟩
  simp [List.length_flatMap, hl]

@[local simp]
theorem length_hmacWith (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) : (hmacWith F key msg).length = 32 := by
  unfold hmacWith sha256With
  exact shaState_flatMap_length _

private theorem extractLsb'_zero_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h256 : i < 256 := by omega
  simp [hi, h256]

private theorem extractLsb'_succ_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) (j : ℕ)
    (hj : j + 1 < 32) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' (8 * (j + 1)) 8 =
      acc.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h1 : ¬ (8 * (j + 1) + i < 8) := by omega
  have h2 : 8 * (j + 1) + i < 256 := by omega
  have h3 : 8 * (j + 1) + i - 8 = 8 * j + i := by omega
  have hb : b.getLsbD (8 * (j + 1) + i) = false := by
    unfold BitVec.getLsbD
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
  simp [h1, h2, h3, hb]

private theorem extractLsb'_bytesToKey32 (bs : List (BitVec 8)) (j : ℕ)
    (hj : j < bs.length) (h32 : j < 32) :
    (bytesToKey32 bs).extractLsb' (8 * j) 8 = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
    cases j with
    | zero =>
      simpa [bytesToKey32] using extractLsb'_zero_bytesToKey32_cons b (bytesToKey32 rest)
    | succ j =>
      have hcons : bytesToKey32 (b :: rest) = (bytesToKey32 rest <<< 8) ||| b.zeroExtend 256 := rfl
      rw [hcons, extractLsb'_succ_bytesToKey32_cons b (bytesToKey32 rest) j h32,
        List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

theorem keyToBytes32_bytesToKey32 (bs : List (BitVec 8)) (h : bs.length = 32) :
    keyToBytes32 (bytesToKey32 bs) = bs := by
  refine List.ext_getElem (by simp [keyToBytes32, h]) fun j h1 h2 => ?_
  simp only [keyToBytes32, List.getElem_ofFn]
  exact extractLsb'_bytesToKey32 bs j h2 (by omega)

theorem keyToBytes32_chainStepN_one (F : ShaState → List (BitVec 8) → ShaState) (ckc : ChainKey) :
    keyToBytes32 (chainStepN F 1 ckc).key = hmacWith F (keyToBytes32 ckc.key) [0x02#8] := by
  rw [chainStepN_one, ← hmacWith_two_eq_chainStep]
  exact keyToBytes32_bytesToKey32 _ (length_hmacWith F _ _)

@[local simp]
theorem length_messageKeys_seed (F : ShaState → List (BitVec 8) → ShaState) (ckc : ChainKey) :
    (ckc.messageKeys F).seed.length = 32 := by
  rw [← hmacWith_one_eq_messageKeys_seed]
  exact length_hmacWith F _ _

theorem reaches_outcome_of_sepWPp {α : Type} {prog : Program} {spec : Spec α}
    {x : α} {R P : SepProp} {s0 s : State}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp prog (s0.readReg64 Reg.lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    reaches_outcome prog spec x R s0 s :=
  Arm64.ReachesOutcome.reaches_outcome_of_sepWPp hm hwp

theorem SepWPp.call_frozen {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hcall : subroutine_ok prog entry spec)
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
  ProofLib.SepWPp.call_wpp_frozen hcall hF hsym hpc hrun hsp hlr hpre hexit
    (fun sf hpan _ => hpanic sf hpan) hnext
    (fun sf R' hoom_st hp => (hoom sf (F ∗ R') hoom_st hp).elim)

theorem pointsToBytes_chainKeyBytes_entails (a : BitVec 64) (ck : ChainKey) :
    (a ↦ₛ chainKeyBytes ck) ⊢ (a ↦ₛ keyToBytes32 ck.key) ∗ memRegion (a + 32#64) 4 := by
  unfold chainKeyBytes
  rw [pointsToBytes_append, length_keyToBytes32]
  apply sepConj_mono_right
  have hlen : (leBytes 4 ck.index.toNat).length = 4 := by simp [leBytes]
  have h := pointsToBytes_entails_memRegion (a + 32#64) (leBytes 4 ck.index.toNat)
  rwa [hlen] at h

theorem chainKey_parts_entails_memRegion (a : BitVec 64) (ck : ChainKey) :
    (a ↦ₛ keyToBytes32 ck.key) ∗ memRegion (a + 32#64) 4 ⊢ memRegion a 36 := by
  have h1 := pointsToBytes_entails_memRegion a (keyToBytes32 ck.key)
  rw [length_keyToBytes32] at h1
  refine Entails.trans (sepConj_mono_left h1) ?_
  rw [← memRegion_split a 32 4 (by decide)]
  exact Entails.refl _

theorem stackAt_7712_split_2048 (sp : BitVec 64) :
    stackAt sp 7712 = memRegion (sp - 7712#64) 5664 ∗ stackAt sp 2048 :=
  stackAt_split_bottom sp 2048 5664 (by decide)

theorem stackAt_7712_split_1024 (sp : BitVec 64) :
    stackAt sp 7712 = memRegion (sp - 7712#64) 6688 ∗ stackAt sp 1024 :=
  stackAt_split_bottom sp 1024 6688 (by decide)

theorem pointsTo8_eq_pointsToBytes1 (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) = (a ↦ₛ [b]) := by
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

theorem pointsToBytes1_31_entails_memRegion32 (a : BitVec 64) (b : BitVec 8) :
    (a ↦ₛ [b]) ∗ memRegion (a + 1#64) 31 ⊢ memRegion a 32 := by
  rw [← pointsTo8_eq_pointsToBytes1]
  refine Entails.trans (sepConj_mono_left (pointsTo8_entails_memRegion a b)) ?_
  rw [← memRegion_split a 1 31 (by decide)]
  exact Entails.refl _

theorem memRegion32_eq_exists_cells4 (a : BitVec 64) :
    memRegion a 32 =
      ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64,
        (a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗ ((a + 24#64) ↦₆₄ d3) := by
  rw [show (32 : Nat) = 8 + 24 from rfl, memRegion_split a 8 24 (by decide),
      memRegion_eight a, memRegion_24_eq_exists_vecHeader (a + 8#64)]
  unfold vecHeader
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_arith
  have h24 : a + 8#64 + 16#64 = a + 24#64 := by bv_arith
  rw [h16, h24, sepExists_sepConj_left]
  apply congrArg SepProp.sepExists; funext d0
  rw [sepExists_sepConj_right]
  apply congrArg SepProp.sepExists; funext d1
  rw [sepExists_sepConj_right]
  apply congrArg SepProp.sepExists; funext d2
  rw [sepExists_sepConj_right]

theorem cells4_entails_memRegion32 (a d0 d1 d2 d3 : BitVec 64) :
    (a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗ ((a + 24#64) ↦₆₄ d3) ⊢
      memRegion a 32 := by
  rw [memRegion32_eq_exists_cells4]
  exact Entails.sepExists_right d0
    (Entails.sepExists_right d1
      (Entails.sepExists_right d2
        (Entails.sepExists_right d3 (Entails.refl _))))

theorem memRegion32_entails_byte_31 (a : BitVec 64) :
    memRegion a 32 ⊢ (∃∗ b : BitVec 8, (a ↦₈ b)) ∗ memRegion (a + 1#64) 31 := by
  rw [show (32 : Nat) = 1 + 31 from rfl, memRegion_split a 1 31 (by decide), memRegion_one a]
  exact Entails.refl _

theorem cells4_entails_byte_31 (a d0 d1 d2 d3 : BitVec 64) :
    (a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗ ((a + 24#64) ↦₆₄ d3) ⊢
      (∃∗ b : BitVec 8, (a ↦₈ b)) ∗ memRegion (a + 1#64) 31 :=
  Entails.trans (cells4_entails_memRegion32 a d0 d1 d2 d3) (memRegion32_entails_byte_31 a)

theorem pointsToBytes1_31_entails_cells4 (a : BitVec 64) (b : BitVec 8) :
    (a ↦ₛ [b]) ∗ memRegion (a + 1#64) 31 ⊢
      ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64,
        (a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗ ((a + 24#64) ↦₆₄ d3) := by
  rw [← memRegion32_eq_exists_cells4]
  exact pointsToBytes1_31_entails_memRegion32 a b

/-- Untouched stack slots of `cmkLoopFrame` during the epilogue. -/
def cmkLoopFrameRest (sp0 : BitVec 64) : SepProp :=
  memRegion (sp0 - 480#64) 112 ∗
  memRegion (sp0 - 360#64) 4 ∗
  memRegion (sp0 - 352#64) 32 ∗
  memRegion (sp0 - 288#64) 64 ∗
  memRegion (sp0 - 192#64) 96

theorem cmkLoopFrame_unpack (sp0 ret : BitVec 64) (counter : BitVec 32) :
    cmkLoopFrame sp0 ret counter ⊢
      ((sp0 - 368#64) ↦₆₄ ret) ∗
      ((sp0 - 356#64) ↦₃₂ counter) ∗
      (∃∗ b0 : BitVec 8, ((sp0 - 320#64) ↦₈ b0)) ∗
      memRegion (sp0 - 319#64) 31 ∗
      memRegion (sp0 - 224#64) 32 ∗
      cmkLoopFrameRest sp0 := by
  unfold cmkLoopFrame cmkLoopFrameRest
  rw [show memRegion (sp0 - 352#64) 256 =
        memRegion (sp0 - 352#64) 32 ∗ memRegion (sp0 - 352#64 + 32#64) 224 from
        memRegion_split (sp0 - 352#64) 32 224 (by decide)]
  have h320 : sp0 - 352#64 + 32#64 = sp0 - 320#64 := by bv_arith
  rw [h320, show memRegion (sp0 - 320#64) 224 =
        memRegion (sp0 - 320#64) 1 ∗ memRegion (sp0 - 320#64 + 1#64) 223 from
        memRegion_split (sp0 - 320#64) 1 223 (by decide)]
  have h319 : sp0 - 320#64 + 1#64 = sp0 - 319#64 := by bv_arith
  rw [h319, show memRegion (sp0 - 319#64) 223 =
        memRegion (sp0 - 319#64) 31 ∗ memRegion (sp0 - 319#64 + 31#64) 192 from
        memRegion_split (sp0 - 319#64) 31 192 (by decide)]
  have h288 : sp0 - 319#64 + 31#64 = sp0 - 288#64 := by bv_arith
  rw [h288, show memRegion (sp0 - 288#64) 192 =
        memRegion (sp0 - 288#64) 64 ∗ memRegion (sp0 - 288#64 + 64#64) 128 from
        memRegion_split (sp0 - 288#64) 64 128 (by decide)]
  have h224 : sp0 - 288#64 + 64#64 = sp0 - 224#64 := by bv_arith
  rw [h224, show memRegion (sp0 - 224#64) 128 =
        memRegion (sp0 - 224#64) 32 ∗ memRegion (sp0 - 224#64 + 32#64) 96 from
        memRegion_split (sp0 - 224#64) 32 96 (by decide)]
  have h192 : sp0 - 224#64 + 32#64 = sp0 - 192#64 := by bv_arith
  rw [h192, memRegion_one (sp0 - 320#64)]
  have hassoc :
      (memRegion (sp0 - 480#64) 112 ∗
        ((sp0 - 368#64) ↦₆₄ ret) ∗
        memRegion (sp0 - 360#64) 4 ∗
        ((sp0 - 356#64) ↦₃₂ counter) ∗
        (memRegion (sp0 - 352#64) 32 ∗
         ((∃∗ v : BitVec 8, (sp0 - 320#64) ↦₈ v) ∗
          (memRegion (sp0 - 319#64) 31 ∗
           (memRegion (sp0 - 288#64) 64 ∗
            (memRegion (sp0 - 224#64) 32 ∗ memRegion (sp0 - 192#64) 96)))))) =
      (((sp0 - 368#64) ↦₆₄ ret) ∗
        ((sp0 - 356#64) ↦₃₂ counter) ∗
        (∃∗ b0 : BitVec 8, ((sp0 - 320#64) ↦₈ b0)) ∗
        memRegion (sp0 - 319#64) 31 ∗
        memRegion (sp0 - 224#64) 32 ∗
        (memRegion (sp0 - 480#64) 112 ∗
         memRegion (sp0 - 360#64) 4 ∗
         memRegion (sp0 - 352#64) 32 ∗
         memRegion (sp0 - 288#64) 64 ∗
         memRegion (sp0 - 192#64) 96)) := by ac_rfl
  rw [hassoc]
  exact Entails.refl _

theorem cmkLoopFrame_entails_memRegion384 (sp0 ret : BitVec 64) (counter : BitVec 32) :
    cmkLoopFrame sp0 ret counter ⊢ memRegion (sp0 - 480#64) 384 := by
  unfold cmkLoopFrame
  have h1 := pointsTo64_entails_memRegion (sp0 - 368#64) ret
  have h2 := pointsTo32_entails_memRegion (sp0 - 356#64) counter
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono h1 (sepConj_mono_right (sepConj_mono_left h2)))) ?_
  have h368 : sp0 - 480#64 + 112#64 = sp0 - 368#64 := by bv_arith
  have h360 : sp0 - 368#64 + 8#64 = sp0 - 360#64 := by bv_arith
  have h356 : sp0 - 360#64 + 4#64 = sp0 - 356#64 := by bv_arith
  have h352 : sp0 - 356#64 + 4#64 = sp0 - 352#64 := by bv_arith
  rw [← h352, ← memRegion_split (sp0 - 356#64) 4 256 (by decide),
      ← h356, ← memRegion_split (sp0 - 360#64) 4 260 (by decide),
      ← h360, ← memRegion_split (sp0 - 368#64) 8 264 (by decide),
      ← h368, ← memRegion_split (sp0 - 480#64) 112 272 (by decide)]
  exact Entails.refl _

theorem cmkLoopFrame_repack (sp0 ret : BitVec 64) (counter : BitVec 32) (b0 : BitVec 8) :
    ((sp0 - 368#64) ↦₆₄ ret) ∗
    ((sp0 - 356#64) ↦₃₂ counter) ∗
    ((sp0 - 320#64) ↦ₛ [b0]) ∗
    memRegion (sp0 - 319#64) 31 ∗
    memRegion (sp0 - 224#64) 32 ∗
    cmkLoopFrameRest sp0 ⊢
      memRegion (sp0 - 480#64) 384 := by
  refine Entails.trans ?_ (cmkLoopFrame_entails_memRegion384 sp0 ret counter)
  unfold cmkLoopFrame cmkLoopFrameRest
  have hb : ((sp0 - 320#64) ↦ₛ [b0]) ∗ memRegion (sp0 - 319#64) 31 ⊢ memRegion (sp0 - 320#64) 32 := by
    have h319 : sp0 - 320#64 + 1#64 = sp0 - 319#64 := by bv_arith
    rw [← h319]
    exact pointsToBytes1_31_entails_memRegion32 (sp0 - 320#64) b0
  have hpull1 :
      (((sp0 - 368#64) ↦₆₄ ret) ∗
        ((sp0 - 356#64) ↦₃₂ counter) ∗
        ((sp0 - 320#64) ↦ₛ [b0]) ∗
        memRegion (sp0 - 319#64) 31 ∗
        memRegion (sp0 - 224#64) 32 ∗
        (memRegion (sp0 - 480#64) 112 ∗
         memRegion (sp0 - 360#64) 4 ∗
         memRegion (sp0 - 352#64) 32 ∗
         memRegion (sp0 - 288#64) 64 ∗
         memRegion (sp0 - 192#64) 96)) =
      ((((sp0 - 320#64) ↦ₛ [b0]) ∗ memRegion (sp0 - 319#64) 31) ∗
        (memRegion (sp0 - 480#64) 112 ∗
         ((sp0 - 368#64) ↦₆₄ ret) ∗
         memRegion (sp0 - 360#64) 4 ∗
         ((sp0 - 356#64) ↦₃₂ counter) ∗
         (memRegion (sp0 - 352#64) 32 ∗
          memRegion (sp0 - 288#64) 64 ∗
          memRegion (sp0 - 224#64) 32 ∗
          memRegion (sp0 - 192#64) 96))) := by ac_rfl
  rw [hpull1]
  refine Entails.trans (sepConj_mono_left hb) ?_
  have hpull2 :
      (memRegion (sp0 - 320#64) 32 ∗
        (memRegion (sp0 - 480#64) 112 ∗
         ((sp0 - 368#64) ↦₆₄ ret) ∗
         memRegion (sp0 - 360#64) 4 ∗
         ((sp0 - 356#64) ↦₃₂ counter) ∗
         (memRegion (sp0 - 352#64) 32 ∗
          memRegion (sp0 - 288#64) 64 ∗
          memRegion (sp0 - 224#64) 32 ∗
          memRegion (sp0 - 192#64) 96))) =
      (memRegion (sp0 - 480#64) 112 ∗
        ((sp0 - 368#64) ↦₆₄ ret) ∗
        memRegion (sp0 - 360#64) 4 ∗
        ((sp0 - 356#64) ↦₃₂ counter) ∗
        (memRegion (sp0 - 352#64) 32 ∗
         (memRegion (sp0 - 320#64) 32 ∗
          (memRegion (sp0 - 288#64) 64 ∗
           (memRegion (sp0 - 224#64) 32 ∗ memRegion (sp0 - 192#64) 96))))) := by ac_rfl
  rw [hpull2]
  have h192 : sp0 - 224#64 + 32#64 = sp0 - 192#64 := by bv_arith
  have h224 : sp0 - 288#64 + 64#64 = sp0 - 224#64 := by bv_arith
  have h288 : sp0 - 320#64 + 32#64 = sp0 - 288#64 := by bv_arith
  have h320 : sp0 - 352#64 + 32#64 = sp0 - 320#64 := by bv_arith
  rw [← h192, ← memRegion_split (sp0 - 224#64) 32 96 (by decide),
      ← h224, ← memRegion_split (sp0 - 288#64) 64 128 (by decide),
      ← h288, ← memRegion_split (sp0 - 320#64) 32 192 (by decide),
      ← h320, ← memRegion_split (sp0 - 352#64) 32 224 (by decide)]
  exact Entails.refl _

theorem cmkSavedRegs_entails_memRegion96 (sp0 : BitVec 64) (s0 : State) :
    cmkSavedRegs sp0 s0 ⊢ memRegion (sp0 - 96#64) 96 := by
  unfold cmkSavedRegs
  refine Entails.trans
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
                        (sepConj_mono (pointsTo64_entails_memRegion _ _)
                          (pointsTo64_entails_memRegion _ _)))))))))))) ?_
  have h88 : sp0 - 96#64 + 8#64 = sp0 - 88#64 := by bv_arith
  have h80 : sp0 - 88#64 + 8#64 = sp0 - 80#64 := by bv_arith
  have h72 : sp0 - 80#64 + 8#64 = sp0 - 72#64 := by bv_arith
  have h64 : sp0 - 72#64 + 8#64 = sp0 - 64#64 := by bv_arith
  have h56 : sp0 - 64#64 + 8#64 = sp0 - 56#64 := by bv_arith
  have h48 : sp0 - 56#64 + 8#64 = sp0 - 48#64 := by bv_arith
  have h40 : sp0 - 48#64 + 8#64 = sp0 - 40#64 := by bv_arith
  have h32 : sp0 - 40#64 + 8#64 = sp0 - 32#64 := by bv_arith
  have h24 : sp0 - 32#64 + 8#64 = sp0 - 24#64 := by bv_arith
  have h16 : sp0 - 24#64 + 8#64 = sp0 - 16#64 := by bv_arith
  have h8  : sp0 - 16#64 + 8#64 = sp0 - 8#64 := by bv_arith
  rw [← h8,  ← memRegion_split (sp0 - 16#64) 8 8 (by decide),
      ← h16, ← memRegion_split (sp0 - 24#64) 8 16 (by decide),
      ← h24, ← memRegion_split (sp0 - 32#64) 8 24 (by decide),
      ← h32, ← memRegion_split (sp0 - 40#64) 8 32 (by decide),
      ← h40, ← memRegion_split (sp0 - 48#64) 8 40 (by decide),
      ← h48, ← memRegion_split (sp0 - 56#64) 8 48 (by decide),
      ← h56, ← memRegion_split (sp0 - 64#64) 8 56 (by decide),
      ← h64, ← memRegion_split (sp0 - 72#64) 8 64 (by decide),
      ← h72, ← memRegion_split (sp0 - 80#64) 8 72 (by decide),
      ← h80, ← memRegion_split (sp0 - 88#64) 8 80 (by decide),
      ← h88, ← memRegion_split (sp0 - 96#64) 8 88 (by decide)]
  exact Entails.refl _

theorem stackAt_cmkStack_repack (sp0 : BitVec 64) (s0 : State) :
    stackAt (sp0 - 480#64) 7712 ∗ memRegion (sp0 - 480#64) 384 ∗ cmkSavedRegs sp0 s0 ⊢
      stackAt sp0 cmkStack := by
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (cmkSavedRegs_entails_memRegion96 sp0 s0))) ?_
  have h96 : sp0 - 480#64 + 384#64 = sp0 - 96#64 := by bv_arith
  rw [← h96, ← memRegion_split (sp0 - 480#64) 384 96 (by decide)]
  unfold stackAt cmkStack
  have h8192 : sp0 - 480#64 - 7712#64 = sp0 - 8192#64 := by bv_arith
  have h480 : sp0 - 8192#64 + 7712#64 = sp0 - 480#64 := by bv_arith
  rw [h8192, ← h480, ← memRegion_split (sp0 - 8192#64) 7712 480 (by decide)]
  exact Entails.refl _

theorem memRegion88_unpack (r : BitVec 64) :
    memRegion r 88 ⊢
      (∃∗ t0 : BitVec 32, (r ↦₃₂ t0)) ∗
      memRegion (r + 4#64) 4 ∗
      (∃∗ c0 : BitVec 64, ((r + 8#64) ↦₆₄ c0)) ∗
      (∃∗ p0 : BitVec 64, ((r + 16#64) ↦₆₄ p0)) ∗
      (∃∗ l0 : BitVec 64, ((r + 24#64) ↦₆₄ l0)) ∗
      (∃∗ i0 : BitVec 32, ((r + 32#64) ↦₃₂ i0)) ∗
      memRegion (r + 36#64) 52 := by
  rw [show memRegion r 88 = memRegion r 4 ∗ memRegion (r + 4#64) 84 from
        memRegion_split r 4 84 (by decide),
      show memRegion (r + 4#64) 84 = memRegion (r + 4#64) 4 ∗ memRegion (r + 4#64 + 4#64) 80 from
        memRegion_split (r + 4#64) 4 80 (by decide)]
  have h8 : r + 4#64 + 4#64 = r + 8#64 := by bv_arith
  rw [h8, show memRegion (r + 8#64) 80 = memRegion (r + 8#64) 8 ∗ memRegion (r + 8#64 + 8#64) 72 from
        memRegion_split (r + 8#64) 8 72 (by decide)]
  have h16 : r + 8#64 + 8#64 = r + 16#64 := by bv_arith
  rw [h16, show memRegion (r + 16#64) 72 = memRegion (r + 16#64) 8 ∗ memRegion (r + 16#64 + 8#64) 64 from
        memRegion_split (r + 16#64) 8 64 (by decide)]
  have h24 : r + 16#64 + 8#64 = r + 24#64 := by bv_arith
  rw [h24, show memRegion (r + 24#64) 64 = memRegion (r + 24#64) 8 ∗ memRegion (r + 24#64 + 8#64) 56 from
        memRegion_split (r + 24#64) 8 56 (by decide)]
  have h32 : r + 24#64 + 8#64 = r + 32#64 := by bv_arith
  rw [h32, show memRegion (r + 32#64) 56 = memRegion (r + 32#64) 4 ∗ memRegion (r + 32#64 + 4#64) 52 from
        memRegion_split (r + 32#64) 4 52 (by decide)]
  have h36 : r + 32#64 + 4#64 = r + 36#64 := by bv_arith
  rw [h36, memRegion_four r, memRegion_eight (r + 8#64), memRegion_eight (r + 16#64),
      memRegion_eight (r + 24#64), memRegion_four (r + 32#64)]
  have hassoc :
      ((∃∗ v : BitVec 32, r ↦₃₂ v) ∗
        (memRegion (r + 4#64) 4 ∗
         ((∃∗ v : BitVec 64, (r + 8#64) ↦₆₄ v) ∗
          ((∃∗ v : BitVec 64, (r + 16#64) ↦₆₄ v) ∗
           ((∃∗ v : BitVec 64, (r + 24#64) ↦₆₄ v) ∗
            ((∃∗ v : BitVec 32, (r + 32#64) ↦₃₂ v) ∗ memRegion (r + 36#64) 52)))))) =
      ((∃∗ t0 : BitVec 32, (r ↦₃₂ t0)) ∗
       memRegion (r + 4#64) 4 ∗
       (∃∗ c0 : BitVec 64, ((r + 8#64) ↦₆₄ c0)) ∗
       (∃∗ p0 : BitVec 64, ((r + 16#64) ↦₆₄ p0)) ∗
       (∃∗ l0 : BitVec 64, ((r + 24#64) ↦₆₄ l0)) ∗
       (∃∗ i0 : BitVec 32, ((r + 32#64) ↦₃₂ i0)) ∗
       memRegion (r + 36#64) 52) := by ac_rfl
  rw [hassoc]
  exact Entails.refl _

theorem resultAt_ok_of_parts (A : RustAlloc) (r ptr : BitVec 64) (k : MessageKeyGenerator)
    (hseed : k.seed.length = 32) (hptr : ptr ≠ 0) :
    (r ↦₃₂ 1#32) ∗ memRegion (r + 4#64) 4 ∗
      ((r + 8#64) ↦₆₄ 32#64) ∗ ((r + 16#64) ↦₆₄ ptr) ∗ ((r + 24#64) ↦₆₄ 32#64) ∗
      ((r + 32#64) ↦₃₂ k.counter) ∗ memRegion (r + 36#64) 52 ∗
      A.live ptr 32 1 ∗ (ptr ↦ₛ k.seed) ⊢
      consumeMessageKeyResultAt A r (.ok k) := by
  unfold consumeMessageKeyResultAt
  have hex := vecU8At_entails_vecU8 A (r + 8#64) 32#64 ptr k.seed
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hex)))
  unfold vecU8At vecHeader
  have h16 : r + 8#64 + 8#64 = r + 16#64 := by bv_arith
  have h24 : r + 8#64 + 16#64 = r + 24#64 := by bv_arith
  have hcap_ne : (32#64 : BitVec 64) ≠ 0 := by decide
  have h32_eq : BitVec.ofNat 64 k.seed.length = 32#64 := by rw [hseed]
  have hrem_zero : (32#64 : BitVec 64).toNat - k.seed.length = 0 := by
    change 32 - k.seed.length = 0; omega
  simp only [h16, h24, hcap_ne, ↓reduceIte, h32_eq, hrem_zero, memRegion_zero, sepConj_emp]
  have hpure : k.seed.length ≤ (32#64 : BitVec 64).toNat ∧ (32#64 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0 := by
    refine ⟨?_, by decide, hptr⟩
    change k.seed.length ≤ 32; omega
  have hpull :
      ((r ↦₃₂ 1#32) ∗ memRegion (r + 4#64) 4 ∗
        ((((r + 8#64) ↦₆₄ 32#64) ∗ ((r + 16#64) ↦₆₄ ptr) ∗ ((r + 24#64) ↦₆₄ 32#64)) ∗
         ⌜k.seed.length ≤ (32#64 : BitVec 64).toNat ∧ (32#64 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
         (A.live ptr (32#64 : BitVec 64).toNat 1 ∗ (ptr ↦ₛ k.seed))) ∗
        ((r + 32#64) ↦₃₂ k.counter) ∗ memRegion (r + 36#64) 52) =
      (⌜k.seed.length ≤ (32#64 : BitVec 64).toNat ∧ (32#64 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
       ((r ↦₃₂ 1#32) ∗ memRegion (r + 4#64) 4 ∗
        ((r + 8#64) ↦₆₄ 32#64) ∗ ((r + 16#64) ↦₆₄ ptr) ∗ ((r + 24#64) ↦₆₄ 32#64) ∗
        ((r + 32#64) ↦₃₂ k.counter) ∗ memRegion (r + 36#64) 52 ∗
        A.live ptr 32 1 ∗ (ptr ↦ₛ k.seed))) := by
    ac_rfl
  rw [hpull]
  exact Entails.pure_right hpure (Entails.refl _)

theorem optChainKeyAt_none_unpack (A : RustAlloc) (pin : VecPin) (a : BitVec 64) :
    optChainKeyAt A pin none a ⊢
      (a ↦₆₄ optChainKeyNone) ∗
      (∃∗ p0 : BitVec 64, ((a + 8#64) ↦₆₄ p0)) ∗
      (∃∗ l0 : BitVec 64, ((a + 16#64) ↦₆₄ l0)) ∗
      (∃∗ idx0 : BitVec 32, ((a + 24#64) ↦₃₂ idx0)) ∗
      memRegion (a + 28#64) 4 := by
  unfold optChainKeyAt
  rw [show memRegion (a + 8#64) 24 = memRegion (a + 8#64) 8 ∗ memRegion (a + 8#64 + 8#64) 16 from
        memRegion_split (a + 8#64) 8 16 (by decide)]
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_arith
  rw [h16, show memRegion (a + 16#64) 16 = memRegion (a + 16#64) 8 ∗ memRegion (a + 16#64 + 8#64) 8 from
        memRegion_split (a + 16#64) 8 8 (by decide)]
  have h24 : a + 16#64 + 8#64 = a + 24#64 := by bv_arith
  rw [h24, show memRegion (a + 24#64) 8 = memRegion (a + 24#64) 4 ∗ memRegion (a + 24#64 + 4#64) 4 from
        memRegion_split (a + 24#64) 4 4 (by decide)]
  have h28 : a + 24#64 + 4#64 = a + 28#64 := by bv_arith
  rw [h28, memRegion_eight (a + 8#64), memRegion_eight (a + 16#64), memRegion_four (a + 24#64)]
  have hassoc :
      ((a ↦₆₄ optChainKeyNone) ∗
        ((∃∗ v : BitVec 64, (a + 8#64) ↦₆₄ v) ∗
         ((∃∗ v : BitVec 64, (a + 16#64) ↦₆₄ v) ∗
          ((∃∗ v : BitVec 32, (a + 24#64) ↦₃₂ v) ∗ memRegion (a + 28#64) 4)))) =
      ((a ↦₆₄ optChainKeyNone) ∗
       (∃∗ p0 : BitVec 64, ((a + 8#64) ↦₆₄ p0)) ∗
       (∃∗ l0 : BitVec 64, ((a + 16#64) ↦₆₄ l0)) ∗
       (∃∗ idx0 : BitVec 32, ((a + 24#64) ↦₃₂ idx0)) ∗
       memRegion (a + 28#64) 4) := by ac_rfl
  rw [hassoc]
  exact Entails.refl _

theorem optChainKeyAt_some_of_parts (A : RustAlloc) (a ptr : BitVec 64) (ck : ChainKey)
    (hptr : ptr ≠ 0) :
    (a ↦₆₄ 32#64) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 32#64) ∗
      ((a + 24#64) ↦₃₂ ck.index) ∗ memRegion (a + 28#64) 4 ∗
      A.live ptr 32 1 ∗ (ptr ↦ₛ keyToBytes32 ck.key) ⊢
      optChainKeyAt A ⟨32#64, ptr⟩ (some ck) a := by
  unfold optChainKeyAt vecU8At vecHeader
  have hcap_ne : (32#64 : BitVec 64) ≠ 0 := by decide
  have hlen : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  have h32_eq : BitVec.ofNat 64 (keyToBytes32 ck.key).length = 32#64 := by rw [hlen]
  have hrem_zero : (32#64 : BitVec 64).toNat - (keyToBytes32 ck.key).length = 0 := by
    change 32 - (keyToBytes32 ck.key).length = 0; omega
  simp only [hcap_ne, ↓reduceIte, h32_eq, hrem_zero, memRegion_zero, sepConj_emp]
  have hpure : (keyToBytes32 ck.key).length ≤ (32#64 : BitVec 64).toNat ∧
      (32#64 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0 := by
    refine ⟨?_, by decide, hptr⟩
    change (keyToBytes32 ck.key).length ≤ 32; omega
  have hpull :
      ((((a ↦₆₄ 32#64) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 32#64)) ∗
        ⌜(keyToBytes32 ck.key).length ≤ (32#64 : BitVec 64).toNat ∧
          (32#64 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (A.live ptr (32#64 : BitVec 64).toNat 1 ∗ (ptr ↦ₛ keyToBytes32 ck.key))) ∗
       ((a + 24#64) ↦₃₂ ck.index) ∗ memRegion (a + 28#64) 4) =
      (⌜(keyToBytes32 ck.key).length ≤ (32#64 : BitVec 64).toNat ∧
        (32#64 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
       ((a ↦₆₄ 32#64) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 32#64) ∗
        ((a + 24#64) ↦₃₂ ck.index) ∗ memRegion (a + 28#64) 4 ∗
        A.live ptr 32 1 ∗ (ptr ↦ₛ keyToBytes32 ck.key))) := by
    ac_rfl
  rw [hpull]
  exact Entails.pure_right hpure (Entails.refl _)

/-- Untouched fields of `ratchetAt` during `find_receiver_chain_index`. -/
def ratchetTail (A : RustAlloc) (self : BitVec 64) (Gc : RatchetGhost) (stc : RatchetState) : SepProp :=
  (self ↦₆₄ Gc.chainsCap) ∗
  A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
  memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
    ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
  ((self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
  ((self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
  ((self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
  ((self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (self + 172#64) 4

theorem ratchetAt_expose_for_findIndex (A : RustAlloc) (self : BitVec 64)
    (Gc : RatchetGhost) (stc : RatchetState) {ci : Nat} (hci : ci < stc.receiverChains.length) :
    ratchetAt A self Gc stc ⊢
      ⌜Gc.chains.length = stc.receiverChains.length ∧ Gc.senderPad.length = 100 ∧
        stc.maxForwardJumps < 2 ^ 64 ∧
        stc.receiverChains.length ≤ Gc.chainsCap.toNat ∧
        Gc.chainsCap.toNat * 104 < 2 ^ 63 ∧ Gc.chainsPtr ≠ 0 ∧ Gc.chainsCap ≠ 0⌝ ∗
      ((self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
      ((self + 16#64) ↦₆₄ BitVec.ofNat 64 stc.receiverChains.length) ∗
      arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
      ratchetTail A self Gc stc := by
  unfold ratchetAt vecAt vecBuf vecHeader ratchetTail
  apply Entails.pure_left
  rintro ⟨hchains_len, hpad_len, hmax_jumps⟩
  have hzip_len : (Gc.chains.zip stc.receiverChains).length = stc.receiverChains.length := by
    simp [hchains_len]
  rw [hzip_len]
  have hpull1 :
      ((((self ↦₆₄ Gc.chainsCap) ∗ ((self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
          ((self + 16#64) ↦₆₄ BitVec.ofNat 64 stc.receiverChains.length)) ∗
        (⌜stc.receiverChains.length ≤ Gc.chainsCap.toNat ∧
          Gc.chainsCap.toNat * 104 < 2 ^ 63 ∧ Gc.chainsPtr ≠ 0⌝ ∗
         if Gc.chainsCap = 0 then emp
         else
           A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
             arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
             memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
               ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104))) ∗
       ((self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
       ((self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
       ((self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
       ((self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (self + 172#64) 4) =
      (⌜stc.receiverChains.length ≤ Gc.chainsCap.toNat ∧
        Gc.chainsCap.toNat * 104 < 2 ^ 63 ∧ Gc.chainsPtr ≠ 0⌝ ∗
       (((self ↦₆₄ Gc.chainsCap) ∗ ((self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
          ((self + 16#64) ↦₆₄ BitVec.ofNat 64 stc.receiverChains.length)) ∗
        (if Gc.chainsCap = 0 then emp
         else
           A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
             arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
             memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
               ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104)) ∗
        ((self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (self + 172#64) 4)) := by
    ac_rfl
  rw [hpull1]
  apply Entails.pure_left
  rintro ⟨hcap_le, hcap_lt, hptr_ne⟩
  have hcap_ne : Gc.chainsCap ≠ 0 := by
    intro h0; rw [h0] at hcap_le; change stc.receiverChains.length ≤ 0 at hcap_le; omega
  simp only [hcap_ne, ↓reduceIte]
  apply Entails.pure_right ⟨hchains_len, hpad_len, hmax_jumps, hcap_le, hcap_lt, hptr_ne, hcap_ne⟩
  have hpull2 :
      (((self ↦₆₄ Gc.chainsCap) ∗ ((self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
          ((self + 16#64) ↦₆₄ BitVec.ofNat 64 stc.receiverChains.length)) ∗
        (A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
          arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
          memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
            ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104)) ∗
        ((self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (self + 172#64) 4) =
      (((self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
       ((self + 16#64) ↦₆₄ BitVec.ofNat 64 stc.receiverChains.length) ∗
       arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
       ((self ↦₆₄ Gc.chainsCap) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (self + 172#64) 4)) := by
    ac_rfl
  rw [hpull2]
  exact Entails.refl _

/-- Frame of `ratchetAt` and `chainAt` outside `optChainKeyAt` at chain `ci`. -/
def ratchetRestAtChain (A : RustAlloc) (self : BitVec 64)
    (Gc : RatchetGhost) (stc : RatchetState) (ci : Nat) (chc : ReceiverChain)
    (hgi : ci < Gc.chains.length) : SepProp :=
  let g := Gc.chains[ci]'hgi
  let c_Addr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  ⌜g.srk.bytes.length = 33 ∧ g.priv.bytes = []⌝ ∗
  ((self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
  ((self + 16#64) ↦₆₄ BitVec.ofNat 64 stc.receiverChains.length) ∗
  vecGhostAt A g.srk c_Addr ∗
  vecGhostAt A g.priv (c_Addr + 24#64) ∗
  vecAt A 104 8 (messageKeyAt A) (c_Addr + 48#64) g.mkCap g.mkPtr
    (g.keys.zip chc.messageKeys) ∗
  arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
  arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
    ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
  ratchetTail A self Gc stc

theorem focus_optChainKeyAt (A : RustAlloc) (self : BitVec 64)
    (Gc : RatchetGhost) (stc : RatchetState) (ci : Nat) (chc : ReceiverChain)
    (hci : ci < stc.receiverChains.length) (hgi : ci < Gc.chains.length)
    (hchc : stc.receiverChains[ci] = chc) :
    ((self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
      ((self + 16#64) ↦₆₄ BitVec.ofNat 64 stc.receiverChains.length) ∗
      arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
      ratchetTail A self Gc stc ⊢
      ⌜PublicKey.deserialize (Gc.chains[ci]'hgi).srk.bytes = .ok chc.senderRatchetKey ∧
        chc.messageKeys.length ≤ maxMessageKeys ∧
        (Gc.chains[ci]'hgi).keys.length = chc.messageKeys.length⌝ ∗
      optChainKeyAt A (Gc.chains[ci]'hgi).ck chc.chainKey
        (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) + 72#64) ∗
      ratchetRestAtChain A self Gc stc ci chc hgi := by
  have hi_zip : ci < (Gc.chains.zip stc.receiverChains).length := by
    simp [hci, hgi]
  rw [arrayAt_split_at (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) hi_zip]
  have hget : (Gc.chains.zip stc.receiverChains)[ci] = (Gc.chains[ci]'hgi, chc) := by
    rw [List.getElem_zip, hchc]
  rw [hget]
  have hc_def :
      chainAt A (Gc.chains[ci]'hgi, chc) (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) =
      (⌜PublicKey.deserialize (Gc.chains[ci]'hgi).srk.bytes = .ok chc.senderRatchetKey ∧
          chc.messageKeys.length ≤ maxMessageKeys ∧
          (Gc.chains[ci]'hgi).keys.length = chc.messageKeys.length ∧
          (Gc.chains[ci]'hgi).srk.bytes.length = 33 ∧
          (Gc.chains[ci]'hgi).priv.bytes = []⌝ ∗
        vecGhostAt A (Gc.chains[ci]'hgi).srk (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) ∗
        vecGhostAt A (Gc.chains[ci]'hgi).priv (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) + 24#64) ∗
        vecAt A 104 8 (messageKeyAt A) (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) + 48#64)
          (Gc.chains[ci]'hgi).mkCap (Gc.chains[ci]'hgi).mkPtr
          ((Gc.chains[ci]'hgi).keys.zip chc.messageKeys) ∗
        optChainKeyAt A (Gc.chains[ci]'hgi).ck chc.chainKey
          (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) + 72#64)) := rfl
  rw [hc_def]
  unfold ratchetRestAtChain
  dsimp only
  have hpull1 :
      (((self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
        ((self + 16#64) ↦₆₄ BitVec.ofNat 64 stc.receiverChains.length) ∗
        ((⌜PublicKey.deserialize (Gc.chains[ci]'hgi).srk.bytes = .ok chc.senderRatchetKey ∧
            chc.messageKeys.length ≤ maxMessageKeys ∧
            (Gc.chains[ci]'hgi).keys.length = chc.messageKeys.length ∧
            (Gc.chains[ci]'hgi).srk.bytes.length = 33 ∧
            (Gc.chains[ci]'hgi).priv.bytes = []⌝ ∗
          vecGhostAt A (Gc.chains[ci]'hgi).srk (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) ∗
          vecGhostAt A (Gc.chains[ci]'hgi).priv (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) + 24#64) ∗
          vecAt A 104 8 (messageKeyAt A) (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) + 48#64)
            (Gc.chains[ci]'hgi).mkCap (Gc.chains[ci]'hgi).mkPtr
            ((Gc.chains[ci]'hgi).keys.zip chc.messageKeys) ∗
          optChainKeyAt A (Gc.chains[ci]'hgi).ck chc.chainKey
            (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) + 72#64)) ∗
         (arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
          arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
            ((Gc.chains.zip stc.receiverChains).drop (ci + 1)))) ∗
        ratchetTail A self Gc stc) =
      (⌜PublicKey.deserialize (Gc.chains[ci]'hgi).srk.bytes = .ok chc.senderRatchetKey ∧
        chc.messageKeys.length ≤ maxMessageKeys ∧
        (Gc.chains[ci]'hgi).keys.length = chc.messageKeys.length ∧
        (Gc.chains[ci]'hgi).srk.bytes.length = 33 ∧
        (Gc.chains[ci]'hgi).priv.bytes = []⌝ ∗
       (optChainKeyAt A (Gc.chains[ci]'hgi).ck chc.chainKey
          (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) + 72#64) ∗
        (((self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
         ((self + 16#64) ↦₆₄ BitVec.ofNat 64 stc.receiverChains.length) ∗
         vecGhostAt A (Gc.chains[ci]'hgi).srk (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) ∗
         vecGhostAt A (Gc.chains[ci]'hgi).priv (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) + 24#64) ∗
         vecAt A 104 8 (messageKeyAt A) (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) + 48#64)
           (Gc.chains[ci]'hgi).mkCap (Gc.chains[ci]'hgi).mkPtr
           ((Gc.chains[ci]'hgi).keys.zip chc.messageKeys) ∗
         arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
         arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
           ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
         ratchetTail A self Gc stc))) := by
    ac_rfl
  rw [hpull1]
  apply Entails.pure_left
  rintro ⟨hsrk, hmax, hklen, hsrk_len, hpriv⟩
  apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
  apply sepConj_mono_right
  exact Entails.pure_right ⟨hsrk_len, hpriv⟩ (Entails.refl _)

theorem repack_optChainKeyAt (A : RustAlloc) (self : BitVec 64)
    (Gc : RatchetGhost) (stc : RatchetState) (ci : Nat) (chc : ReceiverChain)
    (hci : ci < stc.receiverChains.length) (hgi : ci < Gc.chains.length)
    (ckPin' : VecPin) (chainKey' : Option ChainKey)
    (hchains_len : Gc.chains.length = stc.receiverChains.length)
    (hpad_len : Gc.senderPad.length = 100)
    (hmax_jumps : stc.maxForwardJumps < 2 ^ 64)
    (hcap_le : stc.receiverChains.length ≤ Gc.chainsCap.toNat)
    (hcap_lt : Gc.chainsCap.toNat * 104 < 2 ^ 63)
    (hptr_ne : Gc.chainsPtr ≠ 0)
    (hsrk : PublicKey.deserialize (Gc.chains[ci]'hgi).srk.bytes = .ok chc.senderRatchetKey)
    (hmax : chc.messageKeys.length ≤ maxMessageKeys)
    (hklen : (Gc.chains[ci]'hgi).keys.length = chc.messageKeys.length) :
    optChainKeyAt A ckPin' chainKey' (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) + 72#64) ∗
      ratchetRestAtChain A self Gc stc ci chc hgi ⊢
      ratchetAt A self
        (Gc.setChain ci { Gc.chains[ci]'hgi with ck := ckPin' })
        (stc.setChain ci { chc with chainKey := chainKey' }) := by
  have hrat := ratchetAt_set_chain A self Gc stc hci
    { Gc.chains[ci]'hgi with ck := ckPin' } { chc with chainKey := chainKey' }
    hchains_len hpad_len hmax_jumps hcap_le hcap_lt hptr_ne
  refine Entails.trans ?_ hrat
  unfold ratchetRestAtChain ratchetTail vecHeader
  dsimp only
  have hpull0 :
      (optChainKeyAt A ckPin' chainKey' (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) + 72#64) ∗
        (⌜(Gc.chains[ci]'hgi).srk.bytes.length = 33 ∧ (Gc.chains[ci]'hgi).priv.bytes = []⌝ ∗
         ((self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
         ((self + 16#64) ↦₆₄ BitVec.ofNat 64 stc.receiverChains.length) ∗
         vecGhostAt A (Gc.chains[ci]'hgi).srk (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) ∗
         vecGhostAt A (Gc.chains[ci]'hgi).priv (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) + 24#64) ∗
         vecAt A 104 8 (messageKeyAt A) (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) + 48#64)
           (Gc.chains[ci]'hgi).mkCap (Gc.chains[ci]'hgi).mkPtr
           ((Gc.chains[ci]'hgi).keys.zip chc.messageKeys) ∗
         arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
         arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
           ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
         ((self ↦₆₄ Gc.chainsCap) ∗
          A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
          memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
            ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
          ((self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
          ((self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
          ((self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
          ((self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (self + 172#64) 4))) =
      (⌜(Gc.chains[ci]'hgi).srk.bytes.length = 33 ∧ (Gc.chains[ci]'hgi).priv.bytes = []⌝ ∗
       (((self ↦₆₄ Gc.chainsCap) ∗ ((self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
           ((self + 16#64) ↦₆₄ BitVec.ofNat 64 stc.receiverChains.length)) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        (vecGhostAt A (Gc.chains[ci]'hgi).srk (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) ∗
         vecGhostAt A (Gc.chains[ci]'hgi).priv (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) + 24#64) ∗
         vecAt A 104 8 (messageKeyAt A) (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) + 48#64)
           (Gc.chains[ci]'hgi).mkCap (Gc.chains[ci]'hgi).mkPtr
           ((Gc.chains[ci]'hgi).keys.zip chc.messageKeys) ∗
         optChainKeyAt A ckPin' chainKey' (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) + 72#64)) ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (self + 172#64) 4)) := by
    ac_rfl
  rw [hpull0]
  apply Entails.pure_left
  rintro ⟨hsrk_len, hpriv⟩
  have hchain := chainAt_of_update_chainKey A (Gc.chains[ci]'hgi) chc
    (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) ckPin' chainKey' hsrk hmax hklen hsrk_len hpriv
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hchain))

end CryptoVerification.LibsignalSession.AdvanceEpilogue






