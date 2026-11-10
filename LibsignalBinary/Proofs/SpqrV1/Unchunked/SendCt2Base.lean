/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble
public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.SpqrV1.Drop.Repr
import ProofLib.SepLogic.WPp
import GeneratedLean.LibsignalSessionObj

/-!
# `<Ct1SentEkReceived>::send_ct2`: Pure Inversion and Memory Helpers

**Checked by Lean.**

Provides pure model inversion lemmas (`send_ct2`, `macCt`, `encaps2`), `.rodata` slices,
and `Vec<u8>` / encapsulation-state byte-slice splitting helpers for `Ct1SentEkReceived::send_ct2`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Unchunked

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem send_ct2_ok_elim {F : ShaCompress} {K : MlKem}
    {st : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)}
    {outUc : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)}
    {ct2 : Bytes} {mac : Mac}
    (h : st.send_ct2 K = .ok (outUc, ct2, mac)) :
    encaps2 K st.ek st.es = .ok ct2 ∧
    st.auth.macCt F st.epoch (st.ct1 ++ ct2) = .ok mac ∧
    outUc = { epoch := st.epoch, auth := st.auth } := by
  unfold Unchunked.SendCt.Ct1SentEkReceived.send_ct2 at h
  dsimp only [Bind.bind, Except.bind, spqrAuthApi, MonadLift.monadLift, liftSpqrPanic] at h
  revert h
  cases henc : encaps2 K st.ek st.es with
  | error e => intro h; cases h
  | ok ct2' =>
    dsimp only []
    cases hmac : st.auth.macCt F st.epoch (st.ct1 ++ ct2') with
    | error e => intro h; cases h
    | ok mac' =>
      intro h
      injection h with htuple
      injection htuple with h1 h2
      injection h2 with hct2 hmac_eq
      subst h1 hct2 hmac_eq
      exact ⟨rfl, hmac, rfl⟩

theorem macCt_ok_elim {F : ShaCompress} {auth : Authenticator} {ep : Epoch} {ct : Bytes} {mac : Mac}
    (h : auth.macCt F ep ct = .ok mac) :
    auth.macKey.length < 2 ^ 32 ∧
    (Authenticator.ctLabel ++ toBEBytes 8 ep ++ ct).length < 2 ^ 32 ∧
    mac = auth.macCtUnchecked F ep ct := by
  unfold Authenticator.macCt at h
  dsimp only [] at h
  split_ifs at h with hlt
  · injection h with heq
    exact ⟨hlt.1, hlt.2, heq.symm⟩

@[simp]
theorem length_swapAdjacentPairs : ∀ (bs : Bytes), (swapAdjacentPairs bs).length = bs.length
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: rest => by
    simp only [swapAdjacentPairs, List.length_cons, length_swapAdjacentPairs rest]

@[simp]
theorem length_flipEndiannessOfEncapsulationStateBytes (es : EncapsulationState) :
    (flipEndiannessOfEncapsulationStateBytes es).length = es.length := by
  unfold flipEndiannessOfEncapsulationStateBytes
  dsimp only []
  rw [List.length_append, length_swapAdjacentPairs, List.length_take, List.length_drop]
  omega

theorem encaps2_ok_elim {K : MlKem} {ek : EncapsulationKey} {es : EncapsulationState} {ct2 : Bytes}
    (h : encaps2 K ek es = .ok ct2) :
    es.length = 2080 ∧ ek.length = 1152 ∧
    ∃ (esVec : List.Vector (BitVec 8) 2080) (ekVec : List.Vector (BitVec 8) 1152),
      esVec.toList = (if issue1275NeedsFlip ((es.drop 1536).take 512) then
        flipEndiannessOfEncapsulationStateBytes es else es) ∧
      ekVec.toList = ek ∧
      ct2 = (K.encaps2 esVec ekVec).toList := by
  unfold encaps2 potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275
    flip_endianness_of_encapsulation_state at h
  dsimp only [Bind.bind, Except.bind] at h
  split_ifs at h with hbad hflip hmod
  · dsimp only [Option.getD] at h
    split at h
    · rename_i esVec ekVec h1 h2
      revert h1 h2
      change (if h : (flipEndiannessOfEncapsulationStateBytes es).length = 2080 then
          some ⟨flipEndiannessOfEncapsulationStateBytes es, h⟩ else none) = some esVec →
        (if h : ek.length = 1152 then some ⟨ek, h⟩ else none) = some ekVec → _
      intro h1 h2
      split_ifs at h1 with hes0
      split_ifs at h2 with hek
      injection h1 with hesVec
      injection h2 with hekVec
      injection h with hct2
      have hes : es.length = 2080 := by simpa using hes0
      have hflip' : issue1275NeedsFlip ((es.drop 1536).take 512) = true := hflip
      exact ⟨hes, hek, esVec, ekVec, by simp only [hflip', ↓reduceIte, ← hesVec]; rfl,
        by rw [← hekVec]; rfl, hct2.symm⟩
    · cases h
  · dsimp only [Option.getD] at h
    split at h
    · rename_i esVec ekVec h1 h2
      revert h1 h2
      change (if h : es.length = 2080 then some ⟨es, h⟩ else none) = some esVec →
        (if h : ek.length = 1152 then some ⟨ek, h⟩ else none) = some ekVec → _
      intro h1 h2
      split_ifs at h1 with hes0
      split_ifs at h2 with hek
      injection h1 with hesVec
      injection h2 with hekVec
      injection h with hct2
      have hflip' : ¬(issue1275NeedsFlip ((es.drop 1536).take 512) = true) := hflip
      exact ⟨hes0, hek, esVec, ekVec, by simp only [hflip', ↓reduceIte, ← hesVec]; rfl,
        by rw [← hekVec]; rfl, hct2.symm⟩
    · cases h

@[simp]
theorem ctLabel_length : Authenticator.ctLabel.length = 35 := by decide

theorem macCtUnchecked_eq_hmacWith (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (ct : Bytes) :
    self.macCtUnchecked F ep ct =
      hmacWith F self.macKey (Authenticator.ctLabel ++ toBEBytes 8 ep ++ ct) := by
  unfold Authenticator.macCtUnchecked Authenticator.macSize
  exact List.take_of_length_le (by rw [length_hmacWith])

/-- `.rodata` slice (35 bytes): `Authenticator.ctLabel`. -/
theorem rodata_ctLabel {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) (n := 35) (bs := Authenticator.ctLabel)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

/-- Remaining heap tail of a `Vec<u8>` when `(ptr ↦ₛ bs)` is borrowed out. -/
def vecU8Tail (A : RustAlloc) (cap ptr : BitVec 64) (bs : Bytes) : SepProp :=
  if (cap == 0#64) = true then emp
  else A.live ptr cap.toNat 1 ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)

/-- Unpack `vecU8 A a bs` into its header words `(cap, ptr, len)`, live slice `(ptr ↦ₛ bs)`,
and `vecU8Tail A cap ptr bs`. -/
theorem vecU8_entails_slice_and_tail (A : RustAlloc) (a : BitVec 64) (bs : Bytes) :
    vecU8 A a bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗
        vecU8Tail A cap ptr bs := by
  unfold vecU8 vecU8At vecHeader vecU8Tail
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [sepConj_left_comm (a ↦₆₄ cap ∗ (a + 8#64) ↦₆₄ ptr ∗ (a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)]
  apply Entails.pure_left; rintro ⟨hle, hcap_lt, hptr_ne⟩
  refine Entails.pure_right ⟨hle, hcap_lt, hptr_ne⟩ ?_
  by_cases hc : cap = 0#64
  · subst hc
    have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hbs0
    simp only [beq_self_eq_true, ↓reduceIte, pointsToBytes_nil, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)
  · have hcb : (cap == 0#64) = false := beq_false_of_ne hc
    have hc0 : cap ≠ 0 := hc
    simp only [hc0, hcb, Bool.false_eq_true, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

/-- Recombine `(ptr ↦ₛ bs)` and `vecU8Tail A cap ptr bs` into `vecCapPtrDealloc A cap ptr`. -/
theorem slice_and_tail_entails_vecCapPtrDealloc (A : RustAlloc) (cap ptr : BitVec 64) (bs : Bytes)
    (hle : bs.length ≤ cap.toNat) (hcap_lt : cap.toNat < 2 ^ 63) :
    (ptr ↦ₛ bs) ∗ vecU8Tail A cap ptr bs ⊢ vecCapPtrDealloc A cap ptr := by
  unfold vecU8Tail vecCapPtrDealloc
  by_cases hc : (cap == 0#64) = true
  · simp only [hc, ↓reduceIte, sepConj_emp]
    have hcap0 : cap = 0#64 := eq_of_beq hc
    subst hcap0
    have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hbs0
    rw [pointsToBytes_nil]
    exact Entails.refl _
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    refine Entails.trans (Entails.of_eq (show _ =
      A.live ptr cap.toNat 1 ∗ ((ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) by ac_rfl)) ?_
    refine sepConj_mono_right ?_
    have hsplit : memRegion ptr cap.toNat =
        memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) := by
      conv_lhs => rw [show cap.toNat = bs.length + (cap.toNat - bs.length) by omega]
      exact ProofLib.memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)
    rw [hsplit]
    exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)

/-- Split `(ptr ↦ₛ es)` (`es.length = 2080`) to expose `((ptr + 1536#64) ↦ₛ ((es.drop 1536).take 512))`. -/
theorem es_scan_split (ptr : BitVec 64) (es : Bytes) (hes : es.length = 2080) :
    (ptr ↦ₛ es) =
      ((ptr + 1536#64) ↦ₛ ((es.drop 1536).take 512)) ∗
      ((ptr ↦ₛ (es.take 1536)) ∗ ((ptr + 2048#64) ↦ₛ (es.drop 2048))) := by
  have h1 : es = es.take 1536 ++ es.drop 1536 := (List.take_append_drop 1536 es).symm
  have h2 : es.drop 1536 = (es.drop 1536).take 512 ++ (es.drop 1536).drop 512 :=
    (List.take_append_drop 512 (es.drop 1536)).symm
  have h3 : (es.drop 1536).drop 512 = es.drop 2048 := by
    rw [List.drop_drop]
  have hlen1 : (es.take 1536).length = 1536 := by
    rw [List.length_take, hes]; rfl
  have hlen2 : ((es.drop 1536).take 512).length = 512 := by
    rw [List.length_take, List.length_drop, hes]; rfl
  conv_lhs => rw [h1, h2, h3]
  rw [pointsToBytes_append, pointsToBytes_append, hlen1, hlen2]
  have hadd : ptr + BitVec.ofNat 64 1536 + BitVec.ofNat 64 512 = ptr + 2048#64 := by bv_omega
  change (ptr ↦ₛ es.take 1536) ∗
    (((ptr + 1536#64) ↦ₛ (es.drop 1536).take 512) ∗
     ((ptr + BitVec.ofNat 64 1536 + BitVec.ofNat 64 512) ↦ₛ es.drop 2048)) = _
  rw [hadd]
  ac_rfl

/-- Split `(ptr ↦ₛ es)` (`es.length = 2080`) for `swap_loop_ok` (`0..2048` and `2048..2080`). -/
theorem es_swap_split (ptr : BitVec 64) (es : Bytes) (hes : es.length = 2080) :
    (ptr ↦ₛ es) =
      ((ptr + 0#64) ↦ₛ (es.take 2048)) ∗ ((ptr + 2048#64) ↦ₛ (es.drop 2048)) := by
  have h1 : es = es.take 2048 ++ es.drop 2048 := (List.take_append_drop 2048 es).symm
  have hlen1 : (es.take 2048).length = 2048 := by
    rw [List.length_take, hes]; rfl
  conv_lhs => rw [h1]
  rw [pointsToBytes_append, hlen1, BitVec.add_zero]

/-- Recombine `((ptr + 0#64) ↦ₛ swapAdjacentPairs (es.take 2048)) ∗ ((ptr + 2048#64) ↦ₛ (es.drop 2048))`
into `(ptr ↦ₛ flipEndiannessOfEncapsulationStateBytes es)` when `es.length = 2080`. -/
theorem es_swap_join (ptr : BitVec 64) (es : Bytes) (hes : es.length = 2080) :
    ((ptr + 0#64) ↦ₛ swapAdjacentPairs (es.take 2048)) ∗ ((ptr + 2048#64) ↦ₛ (es.drop 2048)) =
      (ptr ↦ₛ flipEndiannessOfEncapsulationStateBytes es) := by
  unfold flipEndiannessOfEncapsulationStateBytes
  dsimp only []
  have hsub : es.length - 32 = 2048 := by omega
  rw [hsub, pointsToBytes_append, length_swapAdjacentPairs, List.length_take, hes, BitVec.add_zero]
  rfl

end CryptoVerification.SpqrV1.Unchunked
