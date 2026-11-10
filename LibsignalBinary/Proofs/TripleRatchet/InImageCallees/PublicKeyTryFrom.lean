/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WPp

/-!
# Verification of `<PublicKey as TryFrom<&[u8]>>::try_from`

Proves that `<libsignal_core::curve::PublicKey as TryFrom<&[u8]>>::try_from` deserializes
33-byte SEC1/DJB Curve25519 public keys (type byte `0x05`) and rejects malformed inputs with
`CurveError`, satisfying `pkTryFromCodeSpec` and `pkTryFromPlacedSpec`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
  CryptoVerification.LibsignalTripleRatchetRepr

namespace PublicKeyTryFrom

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

attribute [local irreducible] Program.fetch Program.externAt?

theorem publicKey_deserialize_ok_inversion {bs : List (BitVec 8)} {pk : PublicKey}
    (h : PublicKey.deserialize bs = .ok pk) :
    bs = djbType :: pk.bytes.toList ++ bs.drop 33 ∧ 33 ≤ bs.length := by
  unfold PublicKey.deserialize at h
  rcases bs with _ | ⟨b0, b1⟩
  · contradiction
  · dsimp only at h
    split at h <;> try contradiction
    rename_i h_djb
    split at h <;> try contradiction
    rename_i h_len
    cases h
    have hb0 : b0 = djbType := Classical.not_not.mp h_djb
    subst hb0
    have hlen : 32 ≤ b1.length := by omega
    refine ⟨?_, by simp; omega⟩
    simp only [List.cons_append, List.cons.injEq, true_and]
    change b1 = (Vector.mk (b1.take 32).toArray (by simp [hlen]) : Vector (BitVec 8) 32).toList ++ b1.drop 32
    simp [List.take_append_drop]

theorem fnAddr_adrp_3eafc {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr pkTryFromName + 32#64) &&&
      0xfffffffffffff000#64) = b + bv% (page% (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 652)) := by
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from")]
  revert hb; bv_bits

theorem pointsToBytes_deserialize_split (ptr : BitVec 64) {bs : List (BitVec 8)} {pk : PublicKey}
    (h : PublicKey.deserialize bs = .ok pk) :
    (ptr ↦ₛ bs) =
      ((ptr ↦₈ 5#8) ∗ ((ptr + 1#64) ↦ₛ pk.bytes.toList) ∗ ((ptr + 33#64) ↦ₛ bs.drop 33)) := by
  obtain ⟨hbs, _⟩ := publicKey_deserialize_ok_inversion h
  conv_lhs => rw [hbs]
  change (ptr ↦ₛ (5#8 :: pk.bytes.toList ++ bs.drop 33)) = _
  rw [List.cons_append, pointsToBytes_cons, pointsToBytes_append]
  have hlen : pk.bytes.toList.length = 32 := by simp
  rw [hlen]
  have h33 : ptr + 1#64 + BitVec.ofNat 64 32 = ptr + 33#64 := by bv_arith
  rw [h33]

theorem publicKey_deserialize_nil :
    PublicKey.deserialize [] = .error .noKeyTypeIdentifier := rfl

theorem publicKey_deserialize_badKeyType {b0 : BitVec 8} (bs : List (BitVec 8))
    (hb0 : b0 ≠ 5#8) :
    PublicKey.deserialize (b0 :: bs) = .error (.badKeyType b0) := by
  unfold PublicKey.deserialize djbType
  simp [hb0]

theorem publicKey_deserialize_badKeyLength (bs : List (BitVec 8))
    (hlen : bs.length < 32) :
    PublicKey.deserialize (5#8 :: bs) = .error (.badKeyLength (bs.length + 1)) := by
  unfold PublicKey.deserialize djbType
  have hnot : ¬ (32 ≤ bs.length) := by omega
  simp [hnot]

theorem publicKey_deserialize_ok_of_ge32 (bs : List (BitVec 8))
    (hlen : 32 ≤ bs.length) :
    PublicKey.deserialize (5#8 :: bs) =
      .ok ⟨⟨bs.take 32, by simp [List.length_take, Nat.min_eq_left hlen]⟩⟩ := by
  unfold PublicKey.deserialize djbType
  simp [hlen]

theorem pointsTo64_zero_entails (out : BitVec 64) :
    ((out + 8#64) ↦₆₄ 0#64) ∗ memRegion (out + 16#64) 24 ⊢
      ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 31 := by
  rw [pointsTo64_eq_pointsToBytes]
  change ((out + 8#64) ↦ₛ (0#8 :: [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8])) ∗
    memRegion (out + 16#64) 24 ⊢ _
  rw [pointsToBytes_cons, show out + 8#64 + 1#64 = out + 9#64 by bv_arith, sepConj_assoc]
  refine sepConj_mono_right ?_
  refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion _ _)) ?_
  change memRegion (out + 9#64) 7 ∗ memRegion (out + 16#64) 24 ⊢ memRegion (out + 9#64) 31
  rw [show out + 16#64 = (out + 9#64) + 7#64 by bv_arith,
      ← memRegion_split (out + 9#64) 7 24 (by decide)]
  exact Entails.refl _

theorem pointsTo64_two_entails (out : BitVec 64) :
    ((out + 8#64) ↦₆₄ 2#64) ⊢ ((out + 8#64) ↦₈ 2#8) ∗ memRegion (out + 9#64) 7 := by
  rw [pointsTo64_eq_pointsToBytes]
  change ((out + 8#64) ↦ₛ (2#8 :: [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8])) ⊢ _
  rw [pointsToBytes_cons, show out + 8#64 + 1#64 = out + 9#64 by bv_arith]
  exact sepConj_mono_right (pointsToBytes_entails_memRegion _ _)

theorem memRegion_40_split_nil (out : BitVec 64) :
    memRegion out 40 =
      (∃∗ u0 : BitVec 8, out ↦₈ u0) ∗ memRegion (out + 1#64) 7 ∗
        (∃∗ w8 : BitVec 64, (out + 8#64) ↦₆₄ w8) ∗ memRegion (out + 16#64) 24 := by
  rw [show (40 : Nat) = 1 + (7 + (8 + 24)) by decide,
      memRegion_split out 1 39 (by decide),
      memRegion_split (out + 1#64) 7 32 (by decide),
      show out + 1#64 + 7#64 = out + 8#64 by bv_arith,
      memRegion_split (out + 8#64) 8 24 (by decide),
      show out + 8#64 + 8#64 = out + 16#64 by bv_arith,
      memRegion_one, memRegion_eight]

theorem memRegion_40_split_badType (out : BitVec 64) :
    memRegion out 40 =
      (∃∗ u0 : BitVec 8, out ↦₈ u0) ∗ memRegion (out + 1#64) 7 ∗
        (∃∗ u8 : BitVec 8, (out + 8#64) ↦₈ u8) ∗ (∃∗ u9 : BitVec 8, (out + 9#64) ↦₈ u9) ∗
        memRegion (out + 10#64) 30 := by
  rw [show (40 : Nat) = 1 + (7 + (1 + (1 + 30))) by decide,
      memRegion_split out 1 39 (by decide),
      memRegion_split (out + 1#64) 7 32 (by decide),
      show out + 1#64 + 7#64 = out + 8#64 by bv_arith,
      memRegion_split (out + 8#64) 1 31 (by decide),
      show out + 8#64 + 1#64 = out + 9#64 by bv_arith,
      memRegion_split (out + 9#64) 1 30 (by decide),
      show out + 9#64 + 1#64 = out + 10#64 by bv_arith,
      memRegion_one, memRegion_one, memRegion_one]

theorem memRegion_40_split_badLen (out : BitVec 64) :
    memRegion out 40 =
      (∃∗ u0 : BitVec 8, out ↦₈ u0) ∗ memRegion (out + 1#64) 7 ∗
        (∃∗ w8 : BitVec 64, (out + 8#64) ↦₆₄ w8) ∗
        (∃∗ w16 : BitVec 64, (out + 16#64) ↦₆₄ w16) ∗ memRegion (out + 24#64) 16 := by
  rw [show (40 : Nat) = 1 + (7 + (8 + (8 + 16))) by decide,
      memRegion_split out 1 39 (by decide),
      memRegion_split (out + 1#64) 7 32 (by decide),
      show out + 1#64 + 7#64 = out + 8#64 by bv_arith,
      memRegion_split (out + 8#64) 8 24 (by decide),
      show out + 8#64 + 8#64 = out + 16#64 by bv_arith,
      memRegion_split (out + 16#64) 8 16 (by decide),
      show out + 16#64 + 8#64 = out + 24#64 by bv_arith,
      memRegion_one, memRegion_eight, memRegion_eight]

theorem memRegion_40_split_ok (out : BitVec 64) :
    memRegion out 40 =
      (∃∗ u0 : BitVec 8, out ↦₈ u0) ∗
        (∃∗ w1 : BitVec 64, (out + 1#64) ↦₆₄ w1) ∗
        (∃∗ w9 : BitVec 64, (out + 9#64) ↦₆₄ w9) ∗
        (∃∗ w17 : BitVec 64, (out + 17#64) ↦₆₄ w17) ∗
        (∃∗ w25 : BitVec 64, (out + 25#64) ↦₆₄ w25) ∗
        memRegion (out + 33#64) 7 := by
  rw [show (40 : Nat) = 1 + (8 + (8 + (8 + (8 + 7)))) by decide,
      memRegion_split out 1 39 (by decide),
      memRegion_split (out + 1#64) 8 31 (by decide),
      show out + 1#64 + 8#64 = out + 9#64 by bv_arith,
      memRegion_split (out + 9#64) 8 23 (by decide),
      show out + 9#64 + 8#64 = out + 17#64 by bv_arith,
      memRegion_split (out + 17#64) 8 15 (by decide),
      show out + 17#64 + 8#64 = out + 25#64 by bv_arith,
      memRegion_split (out + 25#64) 8 7 (by decide),
      show out + 25#64 + 8#64 = out + 33#64 by bv_arith,
      memRegion_one, memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight]

theorem nil_pre_weaken (p out lfa : BitVec 64) :
    (p ↦ₛ []) ∗ (out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗
      ((out + 8#64) ↦₆₄ 0#64) ∗ memRegion (out + 16#64) 24 ∗ (lfa ↦₆₄ 0#64) ⊢
    (p ↦ₛ []) ∗ ((out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗
      ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 31) ∗ (lfa ↦₆₄ 0#64) := by
  rw [show (p ↦ₛ []) ∗ (out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗
        ((out + 8#64) ↦₆₄ 0#64) ∗ memRegion (out + 16#64) 24 ∗ (lfa ↦₆₄ 0#64) =
      (((out + 8#64) ↦₆₄ 0#64) ∗ memRegion (out + 16#64) 24) ∗
        ((p ↦ₛ []) ∗ (out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗ (lfa ↦₆₄ 0#64)) by ac_rfl]
  refine Entails.trans (sepConj_mono_left (pointsTo64_zero_entails out)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem badLen_pre_weaken (p out n lfa : BitVec 64) (rest : List (BitVec 8)) :
    (p ↦₈ 5#8) ∗ ((p + 1#64) ↦ₛ rest) ∗ (out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗
      ((out + 8#64) ↦₆₄ 2#64) ∗ ((out + 16#64) ↦₆₄ n) ∗
      memRegion (out + 24#64) 16 ∗ (lfa ↦₆₄ 0#64) ⊢
    ((p ↦₈ 5#8) ∗ ((p + 1#64) ↦ₛ rest)) ∗
      ((out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗ ((out + 8#64) ↦₈ 2#8) ∗
        memRegion (out + 9#64) 7 ∗ ((out + 16#64) ↦₆₄ n) ∗ memRegion (out + 24#64) 16) ∗
      (lfa ↦₆₄ 0#64) := by
  rw [show (p ↦₈ 5#8) ∗ ((p + 1#64) ↦ₛ rest) ∗ (out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗
        ((out + 8#64) ↦₆₄ 2#64) ∗ ((out + 16#64) ↦₆₄ n) ∗
        memRegion (out + 24#64) 16 ∗ (lfa ↦₆₄ 0#64) =
      ((out + 8#64) ↦₆₄ 2#64) ∗
        ((p ↦₈ 5#8) ∗ ((p + 1#64) ↦ₛ rest) ∗ (out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗
          ((out + 16#64) ↦₆₄ n) ∗ memRegion (out + 24#64) 16 ∗ (lfa ↦₆₄ 0#64)) by ac_rfl]
  refine Entails.trans (sepConj_mono_left (pointsTo64_two_entails out)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem ult_sub_of_lt32 {x1 : BitVec 64} (h1 : 1 ≤ x1.toNat) (h2 : x1.toNat ≤ 32) :
    (x1 - 1#64).ult (x1 - 33#64) = true := by
  simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    decide_eq_true_eq]
  omega

theorem ult_sub_of_ge33 {x1 : BitVec 64} (h1 : 33 ≤ x1.toNat) :
    (x1 - 1#64).ult (x1 - 33#64) = false := by
  have hlt := x1.isLt
  simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    decide_eq_false_iff_not]
  omega

theorem pointsToBytes_ok_split (p : BitVec 64) {rest : List (BitVec 8)} (hge32 : 32 ≤ rest.length) :
    (p ↦ₛ (5#8 :: rest)) =
      (p ↦₈ 5#8) ∗ ((p + 1#64) ↦ₛ rest.take 32) ∗ ((p + 33#64) ↦ₛ rest.drop 32) := by
  conv_lhs => rw [← List.take_append_drop 32 rest]
  rw [pointsToBytes_cons, pointsToBytes_append]
  have hlen : (rest.take 32).length = 32 := by simp [List.length_take, Nat.min_eq_left hge32]
  rw [hlen, show p + 1#64 + BitVec.ofNat 64 32 = p + 33#64 by bv_arith]

open Lean Elab Tactic in
elab "code_fetches_from " codeId:ident decPrefix:ident b:term:max H:term:max hfn:term:max
    off:term:max k0:num len:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat off "fetches"
  let k0 := k0.getNat
  let len := len.getNat
  let codeBase := codeId.getId.eraseMacroScopes
  let decBase := decPrefix.getId.eraseMacroScopes
  let fetchEntry := mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := mkIdent (decBase.appendAfter s!"_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

gen_decodes libsignalSessionCode_tree pkTryFrom [(ls_off% "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from") → (ls_off% "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from" + 44), (ls_off% "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from" + 196) → (ls_off% "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from" + 268)]

macro "pkTryFrom_fetches " b:term:max H:term:max : tactic =>
  `(tactic| (
    code_fetches_from CryptoVerification.libsignalSessionCode pkTryFrom $b $H
      (ls_lemma% fnOff "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from") (num% (ls_off% "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from")) 0 48
    code_fetches_from CryptoVerification.libsignalSessionCode pkTryFrom $b $H
      (ls_lemma% fnOff "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from") (num% (ls_off% "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from")) 196 76))

theorem pkTryFrom_ok_of_aligned (img : Obj.Image) (H : String → Option (State → State))
    (hb : img.base &&& 0xfff#64 = 0#64) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr pkTryFromName) (pkTryFromCodeSpec img) := by
  simp only [pkTryFromCodeSpec, pkTryFromSpec, logOff,
    CryptoVerification.LibsignalSession.logFilterAddr]
  pkTryFrom_fetches img.base H
  wp_init g s0
  have hadrp := fnAddr_adrp_3eafc (b := img.base) (H := H) hb
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨ptr, bs, out⟩ := g
  dsimp only at *
  subst h_1 h
  rcases bs with _ | ⟨b0, rest⟩
  · have hx1 : s0.readReg64 (Reg.gpr 1#5) = 0#64 := by
      apply BitVec.eq_of_toNat_eq; simpa using h_2
    rw [publicKey_deserialize_nil, pkTryFromResultAt,
      memRegion_40_split_nil (s0.readReg64 (Reg.gpr 8#5))]
    wp_pull_exists
    wp_steps
    refine SepWP.weaken_pre
      (nil_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 8#5))
        (img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) ?_
    wp_done
  · have hx1_ne : s0.readReg64 (Reg.gpr 1#5) ≠ 0#64 := by
      intro heq; rw [heq] at h_2; simp at h_2
    by_cases hb0 : b0 = 5#8
    · subst hb0
      by_cases hlen : rest.length < 32
      · have hult : (s0.readReg64 (Reg.gpr 1#5) - 1#64).ult
            (s0.readReg64 (Reg.gpr 1#5) - 33#64) = true :=
          ult_sub_of_lt32 (by simp only [List.length_cons] at h_2; omega)
            (by simp only [List.length_cons] at h_2; omega)
        rw [publicKey_deserialize_badKeyLength rest hlen, pkTryFromResultAt,
          pointsToBytes_cons, memRegion_40_split_badLen (s0.readReg64 (Reg.gpr 8#5))]
        wp_pull_exists
        wp_steps
        have hx1_eq : s0.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (rest.length + 1) := by
          apply BitVec.eq_of_toNat_eq
          simp only [List.length_cons] at h_2
          rw [h_2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        rw [hx1_eq]
        refine SepWP.weaken_pre
          (badLen_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 8#5))
            (BitVec.ofNat 64 (rest.length + 1)) (img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) rest) ?_
        wp_done
      · have hge32 : 32 ≤ rest.length := by omega
        have hult : (s0.readReg64 (Reg.gpr 1#5) - 1#64).ult
            (s0.readReg64 (Reg.gpr 1#5) - 33#64) = false :=
          ult_sub_of_ge33 (by simp only [List.length_cons] at h_2; omega)
        obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
          exists_unpack64_of_length_32 (bs := rest.take 32)
            (by simp [List.length_take, Nat.min_eq_left hge32])
        rw [publicKey_deserialize_ok_of_ge32 rest hge32, pkTryFromResultAt]
        change SepWP _ _ _ _ fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨
              ((⌜sf.trace = s0.trace⌝ ∗
                s0.readReg64 (Reg.gpr 0#5) ↦ₛ (5#8 :: rest) ∗
                (s0.readReg64 (Reg.gpr 8#5) ↦₈ 0#8 ∗
                  (s0.readReg64 (Reg.gpr 8#5) + 1#64) ↦ₛ rest.take 32 ∗
                  memRegion (s0.readReg64 (Reg.gpr 8#5) + 33#64) 7)) ∗
                (img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ R) ∧ _
        rw [pointsToBytes_ok_split (s0.readReg64 (Reg.gpr 0#5)) hge32,
          hpk_cells (s0.readReg64 (Reg.gpr 0#5) + 1#64),
          memRegion_40_split_ok (s0.readReg64 (Reg.gpr 8#5))]
        wp_pull_exists
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        wp_steps
        wp_if hcbz9
        · wp_steps
          rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
          wp_done
        · wp_steps
          rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
          wp_done
    · rw [publicKey_deserialize_badKeyType rest hb0, pkTryFromResultAt,
        pointsToBytes_cons, memRegion_40_split_badType (s0.readReg64 (Reg.gpr 8#5))]
      wp_pull_exists
      wp_steps
      wp_done

end PublicKeyTryFrom

theorem pkTryFrom_ok_rebase (img : Obj.Image) (H : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr pkTryFromName) (pkTryFromCodeSpec img) :=
  PublicKeyTryFrom.pkTryFrom_ok_of_aligned img H (ProofLib.ObjectLoad.base_aligned_of_loads himg)

theorem pkTryFrom_ok_ext (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pkTryFromName) (pkTryFromCodeSpec img) :=
  pkTryFrom_ok_rebase img (Rust.withPanics ext) himg

theorem pkTryFrom_ok_trap (img : Obj.Image) (C : Crypto)
    (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr pkTryFromName) (pkTryFromCodeSpec img) :=
  pkTryFrom_ok_ext img (trTrapExterns C abs) himg

theorem pkTryFrom_ok (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr pkTryFromName) (pkTryFromCodeSpec img) := by
  rw [← (trapsOnly_trTrap_kit img.base C ctl abs).fnAddr pkTryFromName]
  exact subroutine_ok_kit_of_trTrap (pkTryFrom_ok_trap img C abs himg)

/-! ## Relocatable per-block proofs (`[LibsignalPlacement]`) -/

/-- Relocatable `logOff` invariant at `lsLogFilterAddr`. -/
abbrev lsLogOff [LibsignalPlacement] : SepProp := lsLogFilterAddr ↦₆₄ 0#64

/-- Relocatable `pkTryFromCodeSpec` (`pkTryFromSpec` + `lsLogOff`). -/
def pkTryFromPlacedSpec [LibsignalPlacement] : Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun x s => pkTryFromSpec.pre x s ∗ lsLogOff
  post := fun x s0 sf => pkTryFromSpec.post x s0 sf ∗ lsLogOff

namespace PublicKeyTryFrom

theorem pkTryFrom_placed_ok_impl [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_211).rebase (blkPl_211).base H)
      (blkPl_211).base pkTryFromPlacedSpec := by
  simp only [pkTryFromPlacedSpec, pkTryFromSpec, lsLogOff]
  wp_init g s0
  obtain ⟨ptr, bs, out⟩ := g
  dsimp only at *
  subst h_1 h
  rcases bs with _ | ⟨b0, rest⟩
  · have hx1 : s0.readReg64 (Reg.gpr 1#5) = 0#64 := by
      apply BitVec.eq_of_toNat_eq; simpa using h_2
    rw [publicKey_deserialize_nil, pkTryFromResultAt,
      memRegion_40_split_nil (s0.readReg64 (Reg.gpr 8#5))]
    wp_pull_exists
    wp_steps
    refine SepWP.weaken_pre
      (nil_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 8#5))
        lsLogFilterAddr) ?_
    wp_done
  · have hx1_ne : s0.readReg64 (Reg.gpr 1#5) ≠ 0#64 := by
      intro heq; rw [heq] at h_2; simp at h_2
    by_cases hb0 : b0 = 5#8
    · subst hb0
      by_cases hlen : rest.length < 32
      · have hult : (s0.readReg64 (Reg.gpr 1#5) - 1#64).ult
            (s0.readReg64 (Reg.gpr 1#5) - 33#64) = true :=
          ult_sub_of_lt32 (by simp only [List.length_cons] at h_2; omega)
            (by simp only [List.length_cons] at h_2; omega)
        rw [publicKey_deserialize_badKeyLength rest hlen, pkTryFromResultAt,
          pointsToBytes_cons, memRegion_40_split_badLen (s0.readReg64 (Reg.gpr 8#5))]
        wp_pull_exists
        wp_steps
        have hx1_eq : s0.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (rest.length + 1) := by
          apply BitVec.eq_of_toNat_eq
          simp only [List.length_cons] at h_2
          rw [h_2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        rw [hx1_eq]
        refine SepWP.weaken_pre
          (badLen_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 8#5))
            (BitVec.ofNat 64 (rest.length + 1)) lsLogFilterAddr rest) ?_
        wp_done
      · have hge32 : 32 ≤ rest.length := by omega
        have hult : (s0.readReg64 (Reg.gpr 1#5) - 1#64).ult
            (s0.readReg64 (Reg.gpr 1#5) - 33#64) = false :=
          ult_sub_of_ge33 (by simp only [List.length_cons] at h_2; omega)
        obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
          exists_unpack64_of_length_32 (bs := rest.take 32)
            (by simp [List.length_take, Nat.min_eq_left hge32])
        rw [publicKey_deserialize_ok_of_ge32 rest hge32, pkTryFromResultAt]
        change SepWP _ _ _ _ fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨
              ((⌜sf.trace = s0.trace⌝ ∗
                s0.readReg64 (Reg.gpr 0#5) ↦ₛ (5#8 :: rest) ∗
                (s0.readReg64 (Reg.gpr 8#5) ↦₈ 0#8 ∗
                  (s0.readReg64 (Reg.gpr 8#5) + 1#64) ↦ₛ rest.take 32 ∗
                  memRegion (s0.readReg64 (Reg.gpr 8#5) + 33#64) 7)) ∗
                lsLogFilterAddr ↦₆₄ 0#64) ∗ R) ∧ _
        rw [pointsToBytes_ok_split (s0.readReg64 (Reg.gpr 0#5)) hge32,
          hpk_cells (s0.readReg64 (Reg.gpr 0#5) + 1#64),
          memRegion_40_split_ok (s0.readReg64 (Reg.gpr 8#5))]
        wp_pull_exists
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        wp_steps
        wp_if hcbz9
        · wp_steps
          rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
          wp_done
        · wp_steps
          rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
          wp_done
    · rw [publicKey_deserialize_badKeyType rest hb0, pkTryFromResultAt,
        pointsToBytes_cons, memRegion_40_split_badType (s0.readReg64 (Reg.gpr 8#5))]
      wp_pull_exists
      wp_steps
      wp_done

end PublicKeyTryFrom

/-- Relocatable `<PublicKey as TryFrom<&[u8]>>::try_from` (Block `211`) meets `pkTryFromPlacedSpec`. -/
theorem pkTryFrom_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_211).rebase (blkPl_211).base H)
      (blkPl_211).base pkTryFromPlacedSpec :=
  PublicKeyTryFrom.pkTryFrom_placed_ok_impl H

end CryptoVerification.LibsignalTripleRatchet
