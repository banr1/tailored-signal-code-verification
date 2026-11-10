/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.TrapRng
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalTripleRatchetProofDefs

/-!
# Verification of In-Image `spqr::decode_state` on an Empty State

Proves `decodeStateEmpty_ok_F`: on an empty `Vec<u8>` (`st.bytes = []`), `spqr::decode_state`
checks `len = 0`, writes the empty `PriorChainSpec` tags (`-1` at `+0`, `pqChainNone` at `+48`,
`pqInnerNone` at `+128`), and returns without invoking any extern hook.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.DecodeStateEmpty

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet

gen_decodes libsignalSessionCode_tree decodeStateBin
  [(ls_off% "spqr::decode_state") → (ls_off% "spqr::decode_state" + 44), (ls_off% "spqr::decode_state" + 1604) → (ls_off% "spqr::decode_state" + 1624), (ls_off% "spqr::decode_state" + 2500) → (ls_off% "spqr::decode_state" + 2528)]

theorem mr_cut' (sp : BitVec 64) (c c' n k N : Nat) (hN : n + k = N) (hc' : c - n = c')
    (hn : n ≤ c) (hc : c < 2 ^ 64) (h : N ≤ 2 ^ 64) :
    memRegion (sp - BitVec.ofNat 64 c) N =
      memRegion (sp - BitVec.ofNat 64 c) n ∗ memRegion (sp - BitVec.ofNat 64 c') k := by
  subst hN hc'
  refine memRegion_split' rfl ?_ h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have h1 : c % 2 ^ 64 = c := Nat.mod_eq_of_lt hc
  have h2 : (c - n) % 2 ^ 64 = c - n := Nat.mod_eq_of_lt (by omega)
  have h3 : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2, h3]
  omega

/-- The stack of `spqr::decode_state` (`extHookStack = 16384` bytes), split at the slots touched
by the prologue (`sp - 1392` probe and `sp - 96 .. sp - 8` callee-saved registers). -/
theorem stackAt_decodeState_split (sp : BitVec 64) :
    stackAt sp extHookStack =
      memRegion (sp - 16384#64) 14992 ∗
      (∃∗ v0 : BitVec 64, (sp - 1392#64) ↦₆₄ v0) ∗
      memRegion (sp - 1384#64) 1288 ∗
      (∃∗ s29 : BitVec 64, (sp - 96#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (sp - 88#64) ↦₆₄ s30) ∗
      (∃∗ s28 : BitVec 64, (sp - 80#64) ↦₆₄ s28) ∗
      (∃∗ s27 : BitVec 64, (sp - 72#64) ↦₆₄ s27) ∗
      (∃∗ s26 : BitVec 64, (sp - 64#64) ↦₆₄ s26) ∗
      (∃∗ s25 : BitVec 64, (sp - 56#64) ↦₆₄ s25) ∗
      (∃∗ s24 : BitVec 64, (sp - 48#64) ↦₆₄ s24) ∗
      (∃∗ s23 : BitVec 64, (sp - 40#64) ↦₆₄ s23) ∗
      (∃∗ s22 : BitVec 64, (sp - 32#64) ↦₆₄ s22) ∗
      (∃∗ s21 : BitVec 64, (sp - 24#64) ↦₆₄ s21) ∗
      (∃∗ s20 : BitVec 64, (sp - 16#64) ↦₆₄ s20) ∗
      (∃∗ s19 : BitVec 64, (sp - 8#64) ↦₆₄ s19) := by
  show memRegion (sp - BitVec.ofNat 64 16384) 16384 = _
  rw [mr_cut' sp 16384 1392 14992 1392 16384 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 1392 1384 8 1384 1392 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 1384 96 1288 96 1384 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 96 88 8 88 96 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 88 80 8 80 88 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 80 72 8 72 80 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 72 64 8 64 72 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 64 56 8 56 64 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 56 48 8 48 56 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 48 40 8 40 48 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 40 32 8 32 40 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 32 24 8 24 32 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 24 16 8 16 24 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 16 8 8 8 16 rfl rfl (by decide) (by decide) (by decide)]
  simp only [memRegion_eight]

/-- The 352-byte result buffer `ret`, split at the three words written on the empty-state path
(`+0`, `+48`, `+128`). -/
theorem ret_352_split (r : BitVec 64) :
    memRegion r 352 =
      (∃∗ w0 : BitVec 64, r ↦₆₄ w0) ∗
      memRegion (r + 8#64) 40 ∗
      (∃∗ w48 : BitVec 64, (r + 48#64) ↦₆₄ w48) ∗
      memRegion (r + 56#64) 72 ∗
      (∃∗ w128 : BitVec 64, (r + 128#64) ↦₆₄ w128) ∗
      memRegion (r + 136#64) 216 := by
  rw [ProofLib.memRegion_split' (b := r) (n := 8) (k := 344)
        (b' := r + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := r + 8#64) (n := 40) (k := 304)
        (b' := r + 48#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := r + 48#64) (n := 8) (k := 296)
        (b' := r + 56#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := r + 56#64) (n := 72) (k := 224)
        (b' := r + 128#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := r + 128#64) (n := 8) (k := 216)
        (b' := r + 136#64) rfl (by bv_arith) (by decide),
      memRegion_eight r, memRegion_eight (r + 48#64), memRegion_eight (r + 128#64)]

/-- The buffer tail of `vecU8At`, kept intact during symbolic execution of `decode_state`. -/
def vecU8Tail (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecArg_at_nil (A : RustAlloc) (v cap ptr : BitVec 64) :
    VecArg.at A ⟨v, cap, ptr, []⟩ =
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
        vecU8Tail A cap ptr [] := by
  simp only [VecArg.at, vecU8At, vecHeader, vecU8Tail, List.length_nil, BitVec.ofNat_eq_ofNat,
    sepConj_assoc]

/-- On an empty state (`st.bytes = []`), `spqr::decode_state` satisfies `decodeStateEmptySpec A`
for any hook table `hooks`. -/
theorem decodeStateEmpty_ok_F (b : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) :
    subroutine_ok (libsignalSessionCode.rebase b hooks)
      ((libsignalSessionCode.rebase b hooks).fnAddr decodeStateName)
      (decodeStateEmptySpec A) := by
  have hfn : libsignalSessionCode.fnOff decodeStateName = num% (ls_off% "spqr::decode_state") :=
    (ls_lemma% fnOff "spqr::decode_state")
  code_fetches_range CryptoVerification.libsignalSessionCode decodeStateBin
    b hooks hfn (num% (ls_off% "spqr::decode_state")) 0 48
  code_fetches_range CryptoVerification.libsignalSessionCode decodeStateBin
    b hooks hfn (num% (ls_off% "spqr::decode_state")) 1604 24
  code_fetches_range CryptoVerification.libsignalSessionCode decodeStateBin
    b hooks hfn (num% (ls_off% "spqr::decode_state")) 2500 32
  clear hfn
  simp only [decodeStateEmptySpec, decodeStateEmptyAt, pqChainNone, pqInnerNone]
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨⟨v, cap, ptr, bs⟩, ret⟩ := x
  dsimp only at *
  subst bs
  rw [vecArg_at_nil A v cap ptr, ret_352_split ret, stackAt_decodeState_split s0.sp]
  wp_pull_exists
  wp_steps
  wp_done

theorem decodeStateEmpty_ok_aux_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) :
    subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr decodeStateName)
      (decodeStateEmptySpec A) :=
  decodeStateEmpty_ok_F b (Rust.withPanics (trTrapExterns C abs)) A

theorem decodeStateEmpty_ok_aux (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr decodeStateName)
      (decodeStateEmptySpec A) :=
  subroutine_ok_kit_of_trTrap (decodeStateEmpty_ok_aux_trap b C A abs)

end CryptoVerification.LibsignalTripleRatchet.InImage.DecodeStateEmpty
