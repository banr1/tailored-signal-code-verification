/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.LeakRecordsCompat
public import Symbolic.Proofs.SpecLemmas.ImageSymbolsProofDefs
public import Symbolic.Proofs.Swarm.CREF.Cli.RecordBridge
public import Symbolic.Proofs.Refinement.Composed.Cli.OldShape

/-!
# CLI Parameter and SPQR Override Bridges

Defines `interpOfParams interp P`, overriding the six SPQR and `libcrux_hmac` extern symbols using
`P.Q.K` and `P.C.F`, and proves that non-SPQR contracts, `ModelAgree`, `initDirs`, and `gamma` are
preserved and that `ModelHookBridge (interpOfParams interp P) P` holds whenever `ModelAgree interp P`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Cli

open DY DY.Comparse DY.Libsignal
open DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.Refinement (sha256CompressFunction sha256CompressSymbol x25519AgreementSymbol
  x25519PublicKeySymbol x25519TorsionSymbol aesCbcEncryptSymbol aesCbcDecryptSymbol torsionShift)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol kyberDecapsSymbol toEdwardsSymbol torsionFreeSymbol mlkem768FromSeedSymbol mlkem768ValidatePkSymbol mlkem768Encaps1Symbol mlkem768Encaps2Symbol mlkem768DecapsSymbol libcruxHmacSymbol)open CryptoProofLib.Refinement (ByteString ExternInterpretation)
open CryptoGames CryptoGames.LibsignalSession CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives pqxdhSpqrModel)
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.SR (interpW cbcW)
open Symbolic.Swarm.TRREF.SpqrSemOf (mlkemOf hmacFnOf hmacFnOfSha bytesToVec spqrModelOf
  spqrV1WithMac_hmacFnOfSha)

/-! ## `interpOfParams` and non-SPQR symbol preservation -/

/-- Whether `sym` is one of the six SPQR / `libcrux_hmac` symbols overridden by `interpOfParams`. -/
def isSpqrOrHmacSymbol (sym : String) : Bool :=
  sym == mlkem768FromSeedSymbol || sym == mlkem768ValidatePkSymbol ||
    sym == mlkem768Encaps1Symbol || sym == mlkem768Encaps2Symbol ||
    sym == mlkem768DecapsSymbol || sym == libcruxHmacSymbol

/-- Override `interp` on the six SPQR / `libcrux_hmac` symbols using `P.Q.K` and `P.C.F` at their
exact input shapes and byte lengths, falling back to `interp sym args` everywhere else. -/
def interpOfParams (interp : ExternInterpretation) (P : PEParams) : ExternInterpretation :=
  fun sym args =>
    if sym == mlkem768FromSeedSymbol then
      match args with
      | [seed] =>
        if seed.length = 64 then some (P.Q.K.keyPair (bytesToVec 64 seed)).toList else interp sym args
      | _ => interp sym args
    else if sym == mlkem768ValidatePkSymbol then
      match args with
      | [hdr, ek] => if P.Q.K.validPk hdr ek then some [] else none
      | _ => interp sym args
    else if sym == mlkem768Encaps1Symbol then
      match args with
      | [hdr, rand] =>
        if rand.length = 32 then
          (P.Q.K.encaps1 hdr (bytesToVec 32 rand)).map fun (es, ek, ss) =>
            es.toList ++ ek.toList ++ ss.toList
        else interp sym args
      | _ => interp sym args
    else if sym == mlkem768Encaps2Symbol then
      match args with
      | [es, ek] =>
        if es.length = 2080 ∧ ek.length = 1152 then
          some (P.Q.K.encaps2 (bytesToVec 2080 es) (bytesToVec 1152 ek)).toList
        else interp sym args
      | _ => interp sym args
    else if sym == mlkem768DecapsSymbol then
      match args with
      | [dk, ct1, ct2] =>
        if dk.length = 2400 ∧ ct1.length = 960 ∧ ct2.length = 128 then
          some (P.Q.K.decaps (bytesToVec 2400 dk) (bytesToVec 960 ct1) (bytesToVec 128 ct2)).toList
        else interp sym args
      | _ => interp sym args
    else if sym == libcruxHmacSymbol then
      match args with
      | [key, data] => hmacFnOfSha P.C.F key data
      | _ => interp sym args
    else interp sym args

theorem interpOfParams_other (interp : ExternInterpretation) (P : PEParams)
    (sym : String) (args : List ByteString) (hsym : isSpqrOrHmacSymbol sym = false) :
    interpOfParams interp P sym args = interp sym args := by
  unfold isSpqrOrHmacSymbol at hsym; simp only [Bool.or_eq_false_iff] at hsym
  rcases hsym with ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
  simp only [interpOfParams, h1, h2, h3, h4, h5, h6]; rfl

@[simp] theorem sha256CompressFunction_interpOfParams (interp : ExternInterpretation) (P : PEParams) :
    sha256CompressFunction (interpOfParams interp P) = sha256CompressFunction interp := by
  funext st blk
  simp only [sha256CompressFunction, interpOfParams_other interp P sha256CompressSymbol _ (by decide)]

@[simp] theorem torsionShift_interpOfParams (interp : ExternInterpretation) (P : PEParams)
    (pt : ByteString) (t : Fin 8) :
    torsionShift (interpOfParams interp P) pt t = torsionShift interp pt t := by
  unfold torsionShift; split <;> [rfl; rw [interpOfParams_other interp P x25519TorsionSymbol _ (by decide)]]

/-! ## `mlkemOf`, `hmacFnOf`, and `spqrModelOf` on `interpOfParams` -/

private theorem bytesToVec_toList {n : Nat} (v : List.Vector (BitVec 8) n) :
    bytesToVec n v.toList = v := by
  rcases v with ⟨l, hl⟩; apply Subtype.ext
  change (l ++ List.replicate n 0#8).take n = l
  rw [List.take_append_of_le_length (Nat.le_of_eq hl.symm), List.take_of_length_le (Nat.le_of_eq hl)]

@[simp]
theorem mlkemOf_interpOfParams (interp : ExternInterpretation) (P : PEParams) :
    mlkemOf (interpOfParams interp P) = P.Q.K := by
  unfold mlkemOf
  have hs : ∀ seed : List.Vector (BitVec 8) 64,
      interpOfParams interp P mlkem768FromSeedSymbol [seed.toList] =
        some (P.Q.K.keyPair seed).toList := fun seed => by
    unfold interpOfParams
    simp only [beq_self_eq_true, List.Vector.toList_length, bytesToVec_toList, ↓reduceIte]
  have he1 : ∀ (hdr : HwBytes) (rand : List.Vector (BitVec 8) 32),
      interpOfParams interp P mlkem768Encaps1Symbol [hdr, rand.toList] =
        (P.Q.K.encaps1 hdr rand).map fun (es, ek, ss) =>
          es.toList ++ ek.toList ++ ss.toList := fun hdr rand => by
    unfold interpOfParams
    simp only [show (mlkem768Encaps1Symbol == mlkem768FromSeedSymbol) = false by decide,
      show (mlkem768Encaps1Symbol == mlkem768ValidatePkSymbol) = false by decide,
      Bool.false_eq_true, beq_self_eq_true, List.Vector.toList_length, bytesToVec_toList, ↓reduceIte]
  have he2 : ∀ (es : List.Vector (BitVec 8) 2080) (ek : List.Vector (BitVec 8) 1152),
      interpOfParams interp P mlkem768Encaps2Symbol [es.toList, ek.toList] =
        some (P.Q.K.encaps2 es ek).toList := fun es ek => by
    unfold interpOfParams
    simp only [show (mlkem768Encaps2Symbol == mlkem768FromSeedSymbol) = false by decide,
      show (mlkem768Encaps2Symbol == mlkem768ValidatePkSymbol) = false by decide,
      show (mlkem768Encaps2Symbol == mlkem768Encaps1Symbol) = false by decide,
      Bool.false_eq_true, beq_self_eq_true, List.Vector.toList_length, and_self, bytesToVec_toList, ↓reduceIte]
  have hdc : ∀ (dk : List.Vector (BitVec 8) 2400) (ct1 : List.Vector (BitVec 8) 960)
      (ct2 : List.Vector (BitVec 8) 128),
      interpOfParams interp P mlkem768DecapsSymbol [dk.toList, ct1.toList, ct2.toList] =
        some (P.Q.K.decaps dk ct1 ct2).toList := fun dk ct1 ct2 => by
    unfold interpOfParams
    simp only [show (mlkem768DecapsSymbol == mlkem768FromSeedSymbol) = false by decide,
      show (mlkem768DecapsSymbol == mlkem768ValidatePkSymbol) = false by decide,
      show (mlkem768DecapsSymbol == mlkem768Encaps1Symbol) = false by decide,
      show (mlkem768DecapsSymbol == mlkem768Encaps2Symbol) = false by decide,
      Bool.false_eq_true, beq_self_eq_true, List.Vector.toList_length, and_self, bytesToVec_toList, ↓reduceIte]
  have hv : ∀ hdr ek : HwBytes,
      interpOfParams interp P mlkem768ValidatePkSymbol [hdr, ek] =
        if P.Q.K.validPk hdr ek then some [] else none := fun hdr ek => by
    unfold interpOfParams
    simp only [show (mlkem768ValidatePkSymbol == mlkem768FromSeedSymbol) = false by decide,
      Bool.false_eq_true, beq_self_eq_true, ↓reduceIte]
  cases hK : P.Q.K with | mk kp e1 e2 dc vp =>
  congr 1
  · funext seed; rw [hs, Option.getD_some, bytesToVec_toList, hK]
  · funext hdr rand; rw [he1, hK]; dsimp only
    rcases e1 hdr rand with _ | ⟨es, ek, ss⟩
    · rfl
    · dsimp only [Option.map_some]; congr 1; apply Prod.ext
      · dsimp only
        rw [List.append_assoc, List.take_append_of_le_length (by rw [List.Vector.toList_length]),
            List.take_of_length_le (by rw [List.Vector.toList_length]), bytesToVec_toList]
      · apply Prod.ext
        · dsimp only
          rw [List.append_assoc, List.drop_append_of_le_length (by rw [List.Vector.toList_length]),
              List.drop_of_length_le (by rw [List.Vector.toList_length]), List.nil_append,
              List.take_append_of_le_length (by rw [List.Vector.toList_length]),
              List.take_of_length_le (by rw [List.Vector.toList_length]), bytesToVec_toList]
        · dsimp only
          have hdrop : (es.toList ++ ek.toList ++ ss.toList).drop 3040 = ss.toList := by
            rw [show (3040 : Nat) = (es.toList ++ ek.toList).length by
                  rw [List.length_append, List.Vector.toList_length, List.Vector.toList_length],
                List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append]
          rw [hdrop, bytesToVec_toList]
  · funext es ek; rw [he2, Option.getD_some, bytesToVec_toList, hK]
  · funext dk ct1 ct2; rw [hdc, Option.getD_some, bytesToVec_toList, hK]
  · funext hdr ek; rw [hv, hK]; dsimp only; by_cases hvp : vp hdr ek = true <;> simp [hvp]

@[simp]
theorem hmacFnOf_interpOfParams (interp : ExternInterpretation) (P : PEParams) :
    hmacFnOf (interpOfParams interp P) = hmacFnOfSha P.C.F := by
  funext key data; unfold hmacFnOf interpOfParams
  simp only [show (libcruxHmacSymbol == mlkem768FromSeedSymbol) = false by decide,
    show (libcruxHmacSymbol == mlkem768ValidatePkSymbol) = false by decide,
    show (libcruxHmacSymbol == mlkem768Encaps1Symbol) = false by decide,
    show (libcruxHmacSymbol == mlkem768Encaps2Symbol) = false by decide,
    show (libcruxHmacSymbol == mlkem768DecapsSymbol) = false by decide,
    Bool.false_eq_true, beq_self_eq_true, ↓reduceIte]

theorem spqrModelOf_interpOfParams_of_sha (interp : ExternInterpretation) (P : PEParams)
    (hF : P.C.F = sha256CompressFunction interp) :
    spqrModelOf (interpOfParams interp P) = pqxdhSpqrModel P := by
  unfold spqrModelOf pqxdhSpqrModel
  rw [sha256CompressFunction_interpOfParams, mlkemOf_interpOfParams, hmacFnOf_interpOfParams,
      ← hF, spqrV1WithMac_hmacFnOfSha]

theorem spqrModelOf_interpOfParams {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) :
    spqrModelOf (interpOfParams interp P) = pqxdhSpqrModel P :=
  spqrModelOf_interpOfParams_of_sha interp P hagree.1

/-! ## Invariance of contracts, `ModelAgree`, `initDirs`, and `gamma` -/

private theorem length_flatMap_toBEBytes4 :
    ∀ l : List (BitVec 32), (l.flatMap (CryptoGames.HMAC.toBEBytes 4)).length = 4 * l.length
  | [] => rfl
  | w :: ws => by
    simp only [List.flatMap_cons, List.length_append, length_flatMap_toBEBytes4 ws, List.length_cons]
    have h4 : (CryptoGames.HMAC.toBEBytes 4 w).length = 4 := by simp [CryptoGames.HMAC.toBEBytes]
    omega

private theorem length_hmacWith_eq_32
    (F : CryptoGames.HMAC.ShaState → List (BitVec 8) → CryptoGames.HMAC.ShaState)
    (key data : ByteString) :
    (CryptoGames.HMAC.hmacWith F key data).length = 32 := by
  unfold CryptoGames.HMAC.hmacWith CryptoGames.HMAC.sha256With
  rw [length_flatMap_toBEBytes4, List.Vector.toList_length]

private theorem externContractsHoldCli_congr_nonSpqr {i₁ i₂ : ExternInterpretation}
    (ho : ∀ sym args, isSpqrOrHmacSymbol sym = false → i₁ sym args = i₂ sym args)
    (hhmac : ∀ key data tag : ByteString, i₂ "libcrux_hmac::hmac" [key, data] = some tag → tag.length = 32)
    (h : ExternContractsHoldCli i₁) : ExternContractsHoldCli i₂ := by
  rcases h with ⟨hce, hcan, htor⟩
  have hts : ∀ pt t, torsionShift i₁ pt t = torsionShift i₂ pt t := fun pt t => by
    unfold torsionShift; split <;> [rfl; rw [ho x25519TorsionSymbol _ (by decide)]]
  refine ⟨?_, fun s => by rw [← ho x25519PublicKeySymbol _ (by decide)]; exact hcan s,
          fun s t k hk hu1 hu2 => ?_⟩
  · refine
      { x25519_agreement_commutes := fun a b => by
          simpa only [← ho x25519AgreementSymbol _ (by decide),
            ← ho x25519PublicKeySymbol _ (by decide)] using hce.x25519_agreement_commutes a b
        x25519_agreement_length := fun s p => by
          simpa only [← ho x25519AgreementSymbol _ (by decide)] using hce.x25519_agreement_length s p
        x25519_public_key_length := fun s => by
          simpa only [← ho x25519PublicKeySymbol _ (by decide)] using hce.x25519_public_key_length s
        x25519_agreement_reads_u_coordinate := fun s p p' hp hp' hu => by
          simpa only [← ho x25519AgreementSymbol _ (by decide)] using
            hce.x25519_agreement_reads_u_coordinate s p p' hp hp' hu
        x25519_agreement_torsion_invariant := fun s p t => by
          simpa only [← hts, ← ho x25519AgreementSymbol _ (by decide)] using
            hce.x25519_agreement_torsion_invariant s p t
        x25519_agreement_zero_iff_low_order := fun s p hs hp => by
          simpa only [← ho x25519AgreementSymbol _ (by decide)] using
            hce.x25519_agreement_zero_iff_low_order s p hs hp
        x25519_public_key_not_low_order := fun s hs => by
          simpa only [← ho x25519PublicKeySymbol _ (by decide)] using
            hce.x25519_public_key_not_low_order s hs
        aes_cbc_decrypt_inverts_encrypt := fun pt k iv => by
          simpa only [← ho aesCbcEncryptSymbol _ (by decide),
            ← ho aesCbcDecryptSymbol _ (by decide)] using hce.aes_cbc_decrypt_inverts_encrypt pt k iv
        aes_cbc_encrypt_of_decrypt := fun c k iv p hk hiv hdec => by
          rw [← ho aesCbcDecryptSymbol _ (by decide)] at hdec
          simpa only [← ho aesCbcEncryptSymbol _ (by decide)] using
            hce.aes_cbc_encrypt_of_decrypt c k iv p hk hiv hdec
        hmac_tag_length := hhmac }
  · rw [← ho x25519PublicKeySymbol _ (by decide), ← hts] at hu1
    rw [← ho x25519PublicKeySymbol _ (by decide)] at hu2
    intro ⟨pt, hpt, hme, htf⟩
    rw [← ho toEdwardsSymbol _ (by decide)] at hme
    rw [← ho torsionFreeSymbol _ (by decide)] at htf
    exact htor s t k hk hu1 hu2 ⟨pt, hpt, hme, htf⟩

theorem externContractsHoldCli_interpOfParams {interp : ExternInterpretation} (P : PEParams)
    (h : ExternContractsHoldCli interp) :
    ExternContractsHoldCli (interpOfParams interp P) := by
  refine externContractsHoldCli_congr_nonSpqr
    (fun sym args hsym => (interpOfParams_other interp P sym args hsym).symm) ?_ h
  intro key data tag htag
  have hh : interpOfParams interp P "libcrux_hmac::hmac" [key, data] =
      some (CryptoGames.HMAC.hmacWith P.C.F key data) :=
    congrFun (congrFun (hmacFnOf_interpOfParams interp P) key) data
  rw [hh] at htag; injection htag with htag'; rw [← htag', length_hmacWith_eq_32]

@[simp]
theorem modelAgree_interpOfParams (interp : ExternInterpretation) (P : PEParams) :
    ModelAgree (interpOfParams interp P) P ↔ ModelAgree interp P := by
  unfold ModelAgree
  simp only [sha256CompressFunction_interpOfParams,
    interpOfParams_other interp P aesCbcEncryptSymbol _ (by decide),
    interpOfParams_other interp P aesCbcDecryptSymbol _ (by decide),
    interpOfParams_other interp P x25519AgreementSymbol _ (by decide),
    interpOfParams_other interp P x25519PublicKeySymbol _ (by decide),
    interpOfParams_other interp P kyberEncapsSymbol _ (by decide),
    interpOfParams_other interp P kyberDecapsSymbol _ (by decide),
    interpOfParams_other interp P toEdwardsSymbol _ (by decide),
    interpOfParams_other interp P torsionFreeSymbol _ (by decide)]

@[simp] theorem pubBytes_interpOfParams (interp : ExternInterpretation) (P : PEParams) :
    pubBytes (interpOfParams interp P) = pubBytes interp := by
  funext sk; simp only [pubBytes, interpOfParams_other interp P x25519PublicKeySymbol _ (by decide)]

@[simp] theorem initDirs_interpOfParams (interp : ExternInterpretation) (P : PEParams) :
    initDirs (interpOfParams interp P) = initDirs interp := by
  funext r p path; simp only [initDirs, commonFiles, bobPreKeyFiles, pubBytes_interpOfParams]

private theorem gAll_interpOfParams (interp : ExternInterpretation) (P : PEParams)
    (S : OpaqueSymbolSemantics) (g : Ghost) :
    concretizeAll (interpOfParams interp P) S g = concretizeAll interp S g := by
  have hdh : dhFuns (interpOfParams interp P) = dhFuns interp := by
    funext id; match id with
    | ⟨0, _⟩ => funext x rec; simp only [dhFuns, concretizeDhPk,
        interpOfParams_other interp P x25519PublicKeySymbol _ (by decide)]
    | ⟨1, _⟩ => funext x rec; simp only [dhFuns, concretizeDh,
        interpOfParams_other interp P x25519AgreementSymbol _ (by decide)]
  have hkdf : kdfFuns (interpOfParams interp P) = kdfFuns interp := by
    funext ⟨0, _⟩ x rec; simp only [kdfFuns, concretizeKdf, sha256CompressFunction_interpOfParams]
  have hsym : symFuns (interpOfParams interp P) = symFuns interp := by
    funext ⟨0, _⟩ x rec
    simp only [symFuns, concretizeSym, interpOfParams_other interp P aesCbcEncryptSymbol _ (by decide)]
  have hx255 : x25519Funs (interpOfParams interp P) = x25519Funs interp := by
    funext ⟨0, _⟩ x rec; simp only [x25519Funs, concretizeVariant, torsionShift_interpOfParams]
  have hkem : kemFuns (interpOfParams interp P) S = kemFuns interp S := by
    funext id; match id with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => funext x rec; simp only [kemFuns, concretizeKemEncap,
        interpOfParams_other interp P kyberEncapsSymbol _ (by decide)]
    | ⟨2, _⟩ => funext x rec; simp only [kemFuns, concretizeKemSS,
        interpOfParams_other interp P kyberEncapsSymbol _ (by decide)]
    | ⟨3, _⟩ => rfl
  have hall : allFuns (interpOfParams interp P) S g = allFuns interp S g := by
    funext id; match id with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨6, _⟩ | ⟨9, _⟩ | ⟨10, _⟩ | ⟨11, _⟩ => rfl
    | ⟨3, _⟩ => unfold allFuns; rw [hdh]
    | ⟨4, _⟩ => unfold allFuns; rw [hkdf]
    | ⟨5, _⟩ => unfold allFuns; rw [hsym]
    | ⟨7, _⟩ => unfold allFuns; rw [hx255]
    | ⟨8, _⟩ => unfold allFuns; rw [hkem]
  simp only [concretizeAll, hall]

@[simp] theorem gamma'_interpOfParams (interp : ExternInterpretation) (P : PEParams) :
    gamma' (interpOfParams interp P) = gamma' interp := by
  funext S g t; simp only [gamma', gAll_interpOfParams]

@[simp] theorem gamma_interpOfParams (interp : ExternInterpretation) (P : PEParams) :
    gamma (interpOfParams interp P) = gamma interp := by
  funext S g t; simp only [gamma, gamma'_interpOfParams]

@[simp] theorem kyberEncapsBytes_interpOfParams (interp : ExternInterpretation) (P : PEParams) :
    kyberEncapsBytes (interpOfParams interp P) = kyberEncapsBytes interp := by
  funext r e; simp only [kyberEncapsBytes, interpOfParams_other interp P kyberEncapsSymbol _ (by decide)]

@[simp] theorem kyberDecapsBytes_interpOfParams (interp : ExternInterpretation) (P : PEParams) :
    kyberDecapsBytes (interpOfParams interp P) = kyberDecapsBytes interp := by
  funext r ct; simp only [kyberDecapsBytes, interpOfParams_other interp P kyberDecapsSymbol _ (by decide)]

/-! ## `ModelHookBridge` from `ModelAgree` -/

/-- Pure default `UnreachedPqxdhPrimitives` witness (handshake models only read `PEParams` on reached paths). -/
def Xof (_interp : ExternInterpretation) (_P : PEParams) : UnreachedPqxdhPrimitives :=
  { sigPkGen := fun _ => [], sigSign := fun _ _ _ => [], scalarMul := fun _ _ => [],
    scalarAdd := fun _ _ => [], kemKeyGen := fun _ => ([], []), pow8 := fun _ => [],
    isValidDhTriple := fun _ _ _ => false }

private theorem foldr_extractLsb'_getLsbD {w : Nat} (x : BitVec w) :
    ∀ (k offset i : Nat), i < w →
      ((List.ofFn fun j : Fin k => x.extractLsb' (8 * (offset + j.val)) 8).foldr
        (fun (b : BitVec 8) (acc : BitVec w) => (acc <<< 8) ||| b.setWidth w) 0).getLsbD i =
      (decide (i < 8 * k) && x.getLsbD (8 * offset + i))
  | 0, _, _, _ => by simp
  | k + 1, offset, i, hi => by
    rw [List.ofFn_succ]
    have htl : (fun j : Fin k => x.extractLsb' (8 * (offset + (j.succ).val)) 8) =
        (fun j : Fin k => x.extractLsb' (8 * (offset + 1 + j.val)) 8) := by
      funext j; congr 1; rw [Fin.val_succ]; omega
    rw [Fin.val_zero, Nat.add_zero, htl, List.foldr_cons]
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    by_cases h8 : i < 8
    · simp [h8, decide_eq_true (show i < 8 * (k + 1) by omega)]
    · rw [foldr_extractLsb'_getLsbD x k (offset + 1) (i - 8) (by omega)]
      have hidx : 8 * (offset + 1) + (i - 8) = 8 * offset + i := by omega
      have hlt : decide (i - 8 < 8 * k) = decide (i < 8 * (k + 1)) := by
        by_cases h : i < 8 * (k + 1) <;> [simp [h, show i - 8 < 8 * k by omega];
          simp [h, show ¬ (i - 8 < 8 * k) by omega]]
      simp [h8, hidx, hlt]

private theorem bytesToBlock_blockToBytesLE (iv : CryptoGames.CBC.Block) :
    CryptoGames.CBC.bytesToBlock (CryptoGames.CBC.blockToBytesLE iv) = iv := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simpa [CryptoGames.CBC.blockToBytesLE, CryptoGames.CBC.bytesToBlock, show i < 8 * 16 from hi]
    using foldr_extractLsb'_getLsbD iv 16 0 i hi

private theorem bytesToKey32_keyToBytes32 (k : CryptoGames.CBC.AesKey) :
    CryptoGames.HKDF.bytesToKey32 (CryptoGames.HMAC.keyToBytes32 k) = k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simpa [CryptoGames.HMAC.keyToBytes32, CryptoGames.HKDF.bytesToKey32, show i < 8 * 32 from hi]
    using foldr_extractLsb'_getLsbD k 32 0 i hi

theorem crypto_eq_cryptoOf'_of_modelAgree {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) :
    P.C = cryptoOf' interp P.C.E P.C.D := by
  obtain ⟨hF, _, _, hX, hpub, _⟩ := hagree
  rcases hC : P.C with ⟨F, E, D, X, pub⟩
  rw [hC] at hF hX hpub; dsimp only [cryptoOf'] at hF hX hpub ⊢; subst hF
  have hX' : X = fun sec pub' => vec32 ((interp x25519AgreementSymbol [sec.toList, pub'.toList]).getD []) := by
    funext sec pub'; rw [hX sec pub', Option.getD_some]; exact (bytesToVec_toList _).symm
  have hpub' : pub = fun sec => vec32 ((interp x25519PublicKeySymbol [sec.toList]).getD []) := by
    funext sec; rw [hpub sec, Option.getD_some]; exact (bytesToVec_toList _).symm
  rw [hX', hpub']

theorem interpW_eq_cbcW_of_modelAgree {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) :
    interpW interp = cbcW P.C := by
  obtain ⟨_, henc, hdec, _⟩ := hagree
  unfold interpW cbcW; congr 1
  · funext k iv pt
    rw [henc pt _ _ (by simp [CryptoGames.HMAC.keyToBytes32]) (by simp [CryptoGames.CBC.blockToBytesLE]),
        Option.getD_some, bytesToKey32_keyToBytes32, bytesToBlock_blockToBytesLE]
  · funext k iv ct
    rw [hdec ct _ _ (by simp [CryptoGames.HMAC.keyToBytes32]) (by simp [CryptoGames.CBC.blockToBytesLE]),
        bytesToKey32_keyToBytes32, bytesToBlock_blockToBytesLE]

theorem modelHookBridge_interpOfParams {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) :
    ModelHookBridge (interpOfParams interp P) P := by
  have hagree' : ModelAgree (interpOfParams interp P) P := (modelAgree_interpOfParams interp P).mpr hagree
  exact { crypto := crypto_eq_cryptoOf'_of_modelAgree hagree',
          aesCbc := interpW_eq_cbcW_of_modelAgree hagree',
          spqrModel := (spqrModelOf_interpOfParams hagree).symm }

end Symbolic.Swarm.CREF.Cli
