/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.TraceExplanation
public import Symbolic.Proofs.SpecLemmas.ExternInterpretationProofDefs

/-!
# Pure Witness Interpretation

Constructs the pure `ExternInterpretation` witness (`witnessInterpretation`) overriding
`exampleInterpretation` on all 16 PQXDH and SPQR extern symbols, and proves little-endian X25519
`u`-coordinate lemmas, `ExternCryptoLawsHold`, and `X25519PubCanonical`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.WIT.Pure

/-! ## Little-Endian and X25519 `u`-Coordinate Helpers -/

section X25519Arith

open DY.X25519 DY.Libsignal
open DY.Libsignal.Composed.Refinement (leBytes x25519UCoord variantBytes)

theorem length_leBytes : ∀ n w, (leBytes n w).length = n
  | 0, _ => rfl
  | n + 1, w => by simp [leBytes, length_leBytes n]

theorem leValue_leBytes : ∀ n w, leValue ((leBytes n w).map BitVec.toNat) = w % 256 ^ n
  | 0, _ => by simp [leBytes, leValue, Nat.mod_one]
  | n + 1, w => by
    have h : w % 256 ^ (n + 1) = w % 256 + 256 * (w / 256 % 256 ^ n) := by
      rw [Nat.pow_succ', Nat.mod_mul]
    rw [h, leBytes, List.map_cons, leValue, leValue_leBytes n, BitVec.toNat_ofNat]

theorem uOf_leBytes (w : Nat) (hw : w < 2 ^ 256) : x25519UCoord (leBytes 32 w) = w % 2 ^ 255 % p25519 := by
  unfold x25519UCoord uCoord
  rw [leValue_leBytes, Nat.mod_eq_of_lt (a := w) (b := 256 ^ 32) (by omega)]

end X25519Arith

/-! ## Base Double Ratchet `exampleInterpretation` and `X25519PubCanonical` -/

section GammaAndCanonical

open DY.Libsignal (HwBytes)
open CryptoProofLib.Refinement (ExternInterpretation ByteString)
open DY.Libsignal.Refinement (ExternCryptoLawsHold StubSymbol x25519PublicKeySymbol
  x25519AgreementSymbol x25519TorsionSymbol torsionShift aesCbcEncryptSymbol aesCbcDecryptSymbol)
open DY.Libsignal.Composed.Refinement (leBytes x25519UCoord clamp variantBytes X25519PubCanonical)

def exampleBasepoint : HwBytes := 9 :: List.replicate 31 0

def exampleAgreement (a p : HwBytes) : HwBytes :=
  if DY.X25519.isLowOrderKey (p.map BitVec.toNat) then List.replicate 32 0
  else leBytes 32 (2 + (x25519UCoord p + DY.X25519.leValue ((clamp a).map BitVec.toNat)) % 2 ^ 200)

theorem exampleAgreement_of_not_low (a p : HwBytes)
    (h : DY.X25519.isLowOrderKey (p.map BitVec.toNat) = false) :
    exampleAgreement a p =
      leBytes 32 (2 + (x25519UCoord p + DY.X25519.leValue ((clamp a).map BitVec.toNat)) % 2 ^ 200) := by
  simp only [exampleAgreement, h, Bool.false_eq_true, ↓reduceIte]

theorem example_result (w : Nat) (hw : 2 ≤ w) (hw' : w < 2 ^ 200 + 2) :
    x25519UCoord (leBytes 32 w) = w ∧ DY.X25519.isLowOrderKey ((leBytes 32 w).map BitVec.toNat) = false := by
  have hu : x25519UCoord (leBytes 32 w) = w := by
    rw [uOf_leBytes _ (by omega)]; unfold DY.X25519.p25519; omega
  refine ⟨hu, ?_⟩
  have hu' : DY.X25519.uCoord ((leBytes 32 w).map BitVec.toNat) = w := hu
  simp only [DY.X25519.isLowOrderKey, hu', DY.X25519.lowOrderUs, DY.X25519.p25519,
    List.contains_cons, List.contains_nil, Bool.or_false, Bool.and_eq_false_iff,
    Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  right; omega

theorem exampleBasepoint_not_low :
    DY.X25519.isLowOrderKey (exampleBasepoint.map BitVec.toNat) = false := by decide

theorem uOf_exampleBasepoint : x25519UCoord exampleBasepoint = 9 := by decide

theorem exampleAgreement_commutes (a b : HwBytes) :
    exampleAgreement a (exampleAgreement b exampleBasepoint) =
      exampleAgreement b (exampleAgreement a exampleBasepoint) := by
  have step (s t : HwBytes) : exampleAgreement s (exampleAgreement t exampleBasepoint) =
      leBytes 32 (2 + (11 + DY.X25519.leValue ((clamp t).map BitVec.toNat) +
        DY.X25519.leValue ((clamp s).map BitVec.toNat)) % 2 ^ 200) := by
    have hw := example_result
      (2 + (9 + DY.X25519.leValue ((clamp t).map BitVec.toNat)) % 2 ^ 200) (by omega) (by omega)
    rw [exampleAgreement_of_not_low _ _ exampleBasepoint_not_low, uOf_exampleBasepoint,
      exampleAgreement_of_not_low _ _ hw.2, hw.1]
    exact congrArg (leBytes 32) (by omega)
  rw [step, step]; exact congrArg (leBytes 32) (by omega)

theorem length_exampleAgreement (a p : HwBytes) : (exampleAgreement a p).length = 32 := by
  unfold exampleAgreement; split <;> simp [length_leBytes]

/-- Base Double Ratchet witness interpretation (additive mod `2^200` X25519 + identity AES-CBC). -/
def exampleInterpretation : ExternInterpretation := fun symbol arguments =>
  if symbol = x25519PublicKeySymbol then
    match arguments with | [secret] => some (exampleAgreement secret exampleBasepoint) | _ => none
  else if symbol = x25519AgreementSymbol then
    match arguments with | [secret, point] => some (exampleAgreement secret point) | _ => none
  else if symbol = aesCbcEncryptSymbol ∨ symbol = aesCbcDecryptSymbol then
    match arguments with | [text, _, _] => some text | _ => none
  else none

theorem exampleInterpretation_publicKey (secret : HwBytes) :
    exampleInterpretation x25519PublicKeySymbol [secret] =
      some (exampleAgreement secret exampleBasepoint) := by simp [exampleInterpretation]

theorem exampleInterpretation_agreement (secret point : HwBytes) :
    exampleInterpretation x25519AgreementSymbol [secret, point] =
      some (exampleAgreement secret point) := by
  simp [exampleInterpretation, x25519PublicKeySymbol, x25519AgreementSymbol]

theorem exampleInterpretation_cryptoEquationsHold : ExternCryptoLawsHold exampleInterpretation where
  x25519_agreement_commutes a b := by
    simp only [exampleInterpretation_publicKey, exampleInterpretation_agreement, Option.getD_some,
      exampleAgreement_commutes]
  x25519_agreement_length a p := by
    simp only [exampleInterpretation_agreement, Option.getD_some, length_exampleAgreement]
  x25519_public_key_length a := by
    simp only [exampleInterpretation_publicKey, Option.getD_some, length_exampleAgreement]
  x25519_agreement_reads_u_coordinate a b b' hb hb' hu := by
    simp only [exampleInterpretation_agreement]
    have hl : DY.X25519.isLowOrderKey (b.map BitVec.toNat) =
        DY.X25519.isLowOrderKey (b'.map BitVec.toNat) := by
      simp only [DY.X25519.isLowOrderKey, List.length_map, hb, hb']
      exact congrArg (fun u => (32 == 32 && DY.X25519.lowOrderUs.contains u)) hu
    have hu' : x25519UCoord b = x25519UCoord b' := hu
    simp only [exampleAgreement, hl, hu']
  x25519_agreement_torsion_invariant _ _ _ := by unfold torsionShift; split <;> rfl
  x25519_agreement_zero_iff_low_order a b _ _ := by
    simp only [exampleInterpretation_agreement, Option.getD_some]; unfold exampleAgreement
    split
    · simp_all
    · rename_i h; simp only [h, Bool.false_eq_true, iff_false]; intro he
      have h1 := leValue_leBytes 32
        (2 + (x25519UCoord b + DY.X25519.leValue ((clamp a).map BitVec.toNat)) % 2 ^ 200)
      rw [he] at h1
      have h0 : DY.X25519.leValue ((List.replicate 32 (0 : BitVec 8)).map BitVec.toNat) = 0 := by
        decide
      omega
  x25519_public_key_not_low_order a _ := by
    simp only [exampleInterpretation_publicKey, Option.getD_some]
    rw [exampleAgreement_of_not_low _ _ exampleBasepoint_not_low, uOf_exampleBasepoint]
    exact (example_result _ (by omega) (by omega)).2
  aes_cbc_decrypt_inverts_encrypt _ _ _ := by
    simp [exampleInterpretation, x25519PublicKeySymbol, x25519AgreementSymbol,
      aesCbcEncryptSymbol, aesCbcDecryptSymbol]
  aes_cbc_encrypt_of_decrypt _ _ _ _ _ _ h := by
    simp [exampleInterpretation, x25519PublicKeySymbol, x25519AgreementSymbol,
      aesCbcEncryptSymbol, aesCbcDecryptSymbol] at h ⊢
    exact h.symm
  hmac_tag_length _ _ _ h := by
    simp [exampleInterpretation, DY.Libsignal.PQXDH.Refinement.libcruxHmacSymbol,
      x25519PublicKeySymbol, x25519AgreementSymbol,
      aesCbcEncryptSymbol, aesCbcDecryptSymbol] at h

/-- `exampleInterpretation` produces canonical X25519 public keys (`< 2^255 - 19`). -/
theorem example_pubCanonical : X25519PubCanonical exampleInterpretation := by
  intro s
  rw [exampleInterpretation_publicKey, Option.getD_some,
    exampleAgreement_of_not_low _ _ exampleBasepoint_not_low, leValue_leBytes]
  unfold DY.X25519.p25519; omega

end GammaAndCanonical

/-! ## Composed `witnessInterpretation` -/

section WitnessInterpretation

open CryptoProofLib.Refinement (ByteString ExternInterpretation)
open DY.Libsignal.Refinement (ExternCryptoLawsHold StubSymbol x25519AgreementSymbol
  x25519PublicKeySymbol x25519TorsionSymbol torsionShift aesCbcEncryptSymbol aesCbcDecryptSymbol)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol kyberDecapsSymbol sha512CompressSymbol
  toEdwardsSymbol edwardsCompressSymbol edwardsNegSymbol torsionFreeSymbol doubleScalarMulSymbol
  scalarModOrderSymbol scalarModOrderWideSymbol mlkem768FromSeedSymbol mlkem768Encaps1Symbol
  mlkem768Encaps2Symbol mlkem768DecapsSymbol mlkem768ValidatePkSymbol libcruxHmacSymbol)
open DY.Libsignal.Composed.Refinement (ReturnsLength X25519PubCanonical leBytes x25519UCoord clamp
  variantBytes)

/-- Fixed output byte length for each of the 16 `ExternInterpretationTotalOnUsedSymbols` extern
symbols (`torsionFreeSymbol ↦ 1` yields `[0#8]`, which satisfies `.isSome` and refutes
`X25519TorsionFree`). -/
def witnessLength (s : StubSymbol) : Option Nat :=
  if s = kyberEncapsSymbol then some 1600
  else if s = kyberDecapsSymbol then some 32
  else if s = sha512CompressSymbol then some 64
  else if s = toEdwardsSymbol then some 160
  else if s = edwardsCompressSymbol then some 32
  else if s = edwardsNegSymbol then some 160
  else if s = torsionFreeSymbol then some 1
  else if s = doubleScalarMulSymbol then some 160
  else if s = scalarModOrderSymbol then some 32
  else if s = scalarModOrderWideSymbol then some 32
  else if s = mlkem768FromSeedSymbol then some 2400
  else if s = mlkem768Encaps1Symbol then some (960 + 2080 + 32)
  else if s = mlkem768Encaps2Symbol then some 128
  else if s = mlkem768DecapsSymbol then some 32
  else if s = mlkem768ValidatePkSymbol then some 0
  else if s = libcruxHmacSymbol then some 32
  else none

/-- Witness interpretation: `exampleInterpretation` overridden on all 16 PQXDH + SPQR externs. -/
def witnessInterpretation : ExternInterpretation := fun s args =>
  match witnessLength s with
  | some n => some (List.replicate n 0#8)
  | none => exampleInterpretation s args

theorem witnessInterpretation_of_some {s : StubSymbol} {n : Nat} (h : witnessLength s = some n)
    (args : List ByteString) : ReturnsLength witnessInterpretation s args n :=
  ⟨List.replicate n 0#8, by simp [witnessInterpretation, h], List.length_replicate⟩

theorem witnessInterpretation_of_none {s : StubSymbol} (h : witnessLength s = none) :
    witnessInterpretation s = exampleInterpretation s := by
  funext args; simp [witnessInterpretation, h]

theorem cryptoEquationsHold_congr {I J : ExternInterpretation}
    (ha : ∀ args, J x25519AgreementSymbol args = I x25519AgreementSymbol args)
    (hp : ∀ args, J x25519PublicKeySymbol args = I x25519PublicKeySymbol args)
    (ht : ∀ args, J x25519TorsionSymbol args = I x25519TorsionSymbol args)
    (he : ∀ args, J aesCbcEncryptSymbol args = I aesCbcEncryptSymbol args)
    (hd : ∀ args, J aesCbcDecryptSymbol args = I aesCbcDecryptSymbol args)
    (hh : ∀ k d t, J "libcrux_hmac::hmac" [k, d] = some t → t.length = 32)
    (h : ExternCryptoLawsHold I) : ExternCryptoLawsHold J := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _⟩ := h
  have hts : ∀ p t, torsionShift J p t = torsionShift I p t := fun p t => by
    unfold torsionShift; rw [ht]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hh⟩ <;>
    simp only [ha, hp, hts, he, hd] <;> assumption

theorem witnessInterpretation_cryptoEquationsHold : ExternCryptoLawsHold witnessInterpretation :=
  cryptoEquationsHold_congr
    (fun args => congrFun (witnessInterpretation_of_none (by decide)) args)
    (fun args => congrFun (witnessInterpretation_of_none (by decide)) args)
    (fun args => congrFun (witnessInterpretation_of_none (by decide)) args)
    (fun args => congrFun (witnessInterpretation_of_none (by decide)) args)
    (fun args => congrFun (witnessInterpretation_of_none (by decide)) args)
    (fun k d t ht => by
      obtain ⟨v, hv, hl⟩ :=
        witnessInterpretation_of_some (s := "libcrux_hmac::hmac") (n := 32) (by decide) [k, d]
      rw [ht] at hv; cases hv; exact hl)
    exampleInterpretation_cryptoEquationsHold

theorem witnessInterpretation_pubCanonical : X25519PubCanonical witnessInterpretation := by
  intro s; rw [witnessInterpretation_of_none (by decide)]; exact example_pubCanonical s

end WitnessInterpretation

end Symbolic.Proofs.Swarm.WIT.Pure
