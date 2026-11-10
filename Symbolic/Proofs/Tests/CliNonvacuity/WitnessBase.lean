/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Refinement.Cli.ExternWitness
public import Symbolic.Proofs.Tests.Refinement.Cli.RecvWhisperNonVacuityBase
public import Symbolic.Proofs.Swarm.CREF.Cli.HooksBridge
import Symbolic.Proofs.Swarm.CREF.Sem -- shake: keep
import Symbolic.Proofs.Tests.CliNonvacuity.Defs -- shake: keep
import Symbolic.Tests.Nonvacuity.SetupTrace -- shake: keep

/-!
# Collision-Free Witness Primitives, `CliHooks`, and `ExternInterpretation`

Defines the keyed involutive `xorBlock` AES-256-CBC cipher, collision-free SHA-256 mixer and
Kyber-1024 witness primitives, concrete `myBaseInterp`, `myHooks`, `myParams`, and `myInterp`
witnesses, and `myInterp_total : ExternInterpretationTotalOnUsedSymbols myInterp`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.WitnessBase

open DY
open CryptoProofLib.Refinement (ByteString ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement
  (ExternCryptoLawsHold sha256CompressFunction sha256CompressSymbol x25519AgreementSymbol
   x25519PublicKeySymbol x25519TorsionSymbol aesCbcEncryptSymbol aesCbcDecryptSymbol torsionShift)
open DY.Libsignal.PQXDH.Refinement
  (kyberEncapsSymbol kyberDecapsSymbol sha512CompressSymbol toEdwardsSymbol edwardsCompressSymbol
   edwardsNegSymbol torsionFreeSymbol doubleScalarMulSymbol scalarModOrderSymbol
   scalarModOrderWideSymbol mlkem768FromSeedSymbol mlkem768ValidatePkSymbol
   mlkem768Encaps1Symbol mlkem768Encaps2Symbol mlkem768DecapsSymbol libcruxHmacSymbol)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost GhostAndSemMatchSetup MatchesEvents
   ExternInterpretationTotalOnUsedSymbols ReturnsLength ProtocolSetupWF
   PreKeyFields KyberMismatch kyberKey kyberEncapsBytes kyberDecapsBytes
   gamma gamma' concretizeAll concretizeRandom concretizeLit concretizeConcat
   concretizeKemPk concretizeSign node ofByteArray
   setupRandomsAt setupPublic slice randTerm)
open DY.Libsignal.Composed.Refinement.Cli
  (ExternContractsHoldCli HooksMatchInterpretation ModelAgree CliTurn initDirs CliTraces
   runFnToRelation)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.SignalSession (CliRun CliHooks CliSpecPqxdh)
open Symbolic.Tests.Nonvacuity (keySetupTrace)
open Symbolic.Proofs.Tests.CliNonvacuity.Defs
  (CliTraceReachableProof modelRunWF_nil invertsGuarded_of_noInverts)
open Symbolic.Proofs.Tests.Refinement.Cli
  (cliWitnessInterp cliWitnessInterp_total cliWitnessInterp_contracts
   cliWitnessHooks cliWitnessHooks_agree)
open Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers (nvMlKem)
open Symbolic.Proofs.Swarm.WIT.Pure
  (exampleAgreement exampleBasepoint length_exampleAgreement
   exampleInterpretation witnessInterpretation_of_none)
open Symbolic.Swarm.CREF
  (compSemOf b1_setupRandomsAt_eq b1_setupPublic_5 b1_setupPublic_6 b1_setupPublic_7)
open Symbolic.Swarm.CREF.Cli
  (isSpqrOrHmacSymbol interpOfParams interpOfParams_other
   externContractsHoldCli_interpOfParams modelAgree_interpOfParams hmacFnOf_interpOfParams)
open Symbolic.Swarm.TRREF.SpqrSemOf (bytesToVec)

/-! ## Keyed Involutive AES-256-CBC (`xorBlock`) -/

def xorKeyMask (k : CryptoGames.CBC.AesKey) : CryptoGames.CBC.Block :=
  k.extractLsb' 0 128 ^^^ k.extractLsb' 128 128

def xorBlock (k : CryptoGames.CBC.AesKey) (b : CryptoGames.CBC.Block) : CryptoGames.CBC.Block :=
  b ^^^ xorKeyMask k

theorem xorBlock_involutive (k : CryptoGames.CBC.AesKey) (b : CryptoGames.CBC.Block) :
    xorBlock k (xorBlock k b) = b := by
  unfold xorBlock
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

private theorem cbcEncrypt_eq (f : ByteSpecs.Block → ByteSpecs.Block) :
    ∀ (iv : ByteSpecs.Block) {n : Nat} (P : List.Vector ByteSpecs.Block n),
      CryptoGames.CBC.cbcEncrypt f iv P = ByteSpecs.cbcEncrypt f iv P
  | _, 0, _ => rfl
  | iv, _ + 1, P => by
    simp only [CryptoGames.CBC.cbcEncrypt, ByteSpecs.cbcEncrypt]
    rw [cbcEncrypt_eq f (f (P.head ^^^ iv)) P.tail]

private theorem cbcDecryptBlocks_eq (g : ByteSpecs.Block → ByteSpecs.Block)
    (iv : ByteSpecs.Block) :
    ∀ (cs : List ByteSpecs.Block),
      CryptoGames.CBC.cbcDecryptBlocks g iv cs = ByteSpecs.cbcDecryptBlocks g iv cs
  | [] => rfl
  | c :: cs => by
    simp only [CryptoGames.CBC.cbcDecryptBlocks, ByteSpecs.cbcDecryptBlocks]
    rw [cbcDecryptBlocks_eq g c cs]

theorem aesCbcEncrypt_eq_byteSpecs
    (E : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block)
    (k : CryptoGames.CBC.AesKey) (iv : CryptoGames.CBC.Block) (p : List (BitVec 8)) :
    CryptoGames.LibsignalSession.aesCbcEncrypt E k iv p =
      (ByteSpecs.cbcEncrypt (E k) iv
        (ByteSpecs.pkcs7Blocks (⟨p, rfl⟩ : ByteSpecs.Plain p.length))).toList.flatMap
        ByteSpecs.blockToBytesLE := by
  let vp : List.Vector (BitVec 8) p.length := ⟨p, rfl⟩
  change (CryptoGames.CBC.cbcEncrypt (E k) iv (CryptoGames.CBC.pkcs7Blocks vp)).toList.flatMap
      CryptoGames.CBC.blockToBytesLE =
    (ByteSpecs.cbcEncrypt (E k) iv (ByteSpecs.pkcs7Blocks vp)).toList.flatMap
      ByteSpecs.blockToBytesLE
  have hpk : CryptoGames.CBC.pkcs7Blocks vp = ByteSpecs.pkcs7Blocks vp := rfl
  have hbl : CryptoGames.CBC.blockToBytesLE = ByteSpecs.blockToBytesLE := rfl
  rw [hbl]
  exact congrArg (fun v => v.toList.flatMap ByteSpecs.blockToBytesLE)
    (hpk ▸ cbcEncrypt_eq (E k) iv (ByteSpecs.pkcs7Blocks vp))

theorem aesCbcDecrypt_eq_byteSpecs
    (D : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block)
    (k : CryptoGames.CBC.AesKey) (iv : CryptoGames.CBC.Block) (c : List (BitVec 8)) :
    CryptoGames.LibsignalSession.aesCbcDecrypt D k iv c = ByteSpecs.cbcDecRaw D k iv c := by
  unfold CryptoGames.LibsignalSession.aesCbcDecrypt CryptoGames.CBC.cbcDecRaw ByteSpecs.cbcDecRaw
  have hch : CryptoGames.CBC.chunks16 c = ByteSpecs.chunks16 c := rfl
  have hbl : CryptoGames.CBC.blockToBytesLE = ByteSpecs.blockToBytesLE := rfl
  have hunp : CryptoGames.CBC.pkcs7Unpad = ByteSpecs.pkcs7Unpad := rfl
  rw [hch, cbcDecryptBlocks_eq, hbl, hunp]

private theorem eq_replicate_of_all_beq :
    ∀ (l : List (BitVec 8)) (x : BitVec 8),
      l.all (· == x) = true → l = List.replicate l.length x
  | [], _, _ => rfl
  | y :: ys, x, h => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    have ih := eq_replicate_of_all_beq ys x h.2
    simp only [h.1, List.length_cons, List.replicate_succ, List.cons.injEq, true_and]
    exact ih

private theorem length_cbcDecryptBlocks (g : ByteSpecs.Block → ByteSpecs.Block) :
    ∀ (iv : ByteSpecs.Block) (cs : List ByteSpecs.Block),
      (ByteSpecs.cbcDecryptBlocks g iv cs).length = cs.length
  | _, [] => rfl
  | iv, c :: cs => by simp [ByteSpecs.cbcDecryptBlocks, length_cbcDecryptBlocks g c cs]

private theorem length_flatMap_blockToBytesLE :
    ∀ (cs : List ByteSpecs.Block),
      (cs.flatMap ByteSpecs.blockToBytesLE).length = 16 * cs.length
  | [] => rfl
  | c :: cs => by
    have h16 : (ByteSpecs.blockToBytesLE c).length = 16 := by simp [ByteSpecs.blockToBytesLE]
    simp only [List.flatMap_cons, List.length_append, h16, length_flatMap_blockToBytesLE cs,
      List.length_cons]
    omega

private def cbcEncryptListF (f : ByteSpecs.Block → ByteSpecs.Block) (iv : ByteSpecs.Block) :
    List ByteSpecs.Block → List ByteSpecs.Block
  | [] => []
  | b :: bs => f (b ^^^ iv) :: cbcEncryptListF f (f (b ^^^ iv)) bs

private theorem toList_cbcEncrypt_f (f : ByteSpecs.Block → ByteSpecs.Block) :
    ∀ (iv : ByteSpecs.Block) {n : Nat} (P : List.Vector ByteSpecs.Block n),
      (ByteSpecs.cbcEncrypt f iv P).toList = cbcEncryptListF f iv P.toList
  | _, 0, P => by
    cases P with
    | mk l hl =>
      cases l with
      | nil => rfl
      | cons _ _ => cases hl
  | iv, _ + 1, P => by
    simp only [ByteSpecs.cbcEncrypt, List.Vector.toList_cons]
    rw [toList_cbcEncrypt_f f (f (P.head ^^^ iv)) P.tail]
    cases P with
    | mk l hl =>
      cases l with
      | nil => cases hl
      | cons b bs => rfl

private theorem cbcEncryptListF_cbcDecryptBlocks (f : ByteSpecs.Block → ByteSpecs.Block)
    (hf : ∀ x, f (f x) = x) :
    ∀ (iv : ByteSpecs.Block) (cs : List ByteSpecs.Block),
      cbcEncryptListF f iv (ByteSpecs.cbcDecryptBlocks f iv cs) = cs
  | _, [] => rfl
  | iv, c :: cs => by
    have hxor : f ((f c ^^^ iv) ^^^ iv) = c := by
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, hf]
    simp only [ByteSpecs.cbcDecryptBlocks, cbcEncryptListF, hxor,
      cbcEncryptListF_cbcDecryptBlocks f hf c cs]

private theorem flatMap_ofFn_chunks16 (m : Nat) :
    ∀ (bs : List (BitVec 8)), bs.length = 16 * m →
      (List.ofFn fun i : Fin m =>
        ByteSpecs.bytesToBlock ((bs.drop (16 * i.val)).take 16)).flatMap
          ByteSpecs.blockToBytesLE = bs := by
  induction m with
  | zero =>
    intro bs h
    simp only [Nat.mul_zero, List.length_eq_zero_iff] at h
    subst h; rfl
  | succ m ih =>
    intro bs h
    rw [List.ofFn_succ, List.flatMap_cons]
    simp only [Fin.val_zero, Nat.mul_zero, List.drop_zero, Fin.val_succ]
    rw [ByteSpecs.blockToBytesLE_bytesToBlock (bs.take 16) (by rw [List.length_take, h]; omega)]
    have hrest : (List.ofFn fun i : Fin m =>
        ByteSpecs.bytesToBlock ((bs.drop (16 * (i.val + 1))).take 16)) =
      List.ofFn fun i : Fin m =>
        ByteSpecs.bytesToBlock (((bs.drop 16).drop (16 * i.val)).take 16) := by
      congr 1; ext i; rw [List.drop_drop]
      have : 16 * (i.val + 1) = 16 + 16 * i.val := by omega
      rw [this]
    rw [hrest, ih (bs.drop 16) (by simp [h]; omega), List.take_append_drop]

private theorem flatMap_chunks16 (ct : List (BitVec 8)) (h : ct.length % 16 = 0) :
    (ByteSpecs.chunks16 ct).flatMap ByteSpecs.blockToBytesLE = ct := by
  unfold ByteSpecs.chunks16
  exact flatMap_ofFn_chunks16 (ct.length / 16) ct (by omega)

private theorem chunks16_pkcs7Bytes (p : List (BitVec 8)) :
    ByteSpecs.chunks16 (ByteSpecs.pkcs7Bytes (⟨p, rfl⟩ : ByteSpecs.Plain p.length)) =
      (ByteSpecs.pkcs7Blocks (⟨p, rfl⟩ : ByteSpecs.Plain p.length)).toList := by
  unfold ByteSpecs.chunks16 ByteSpecs.pkcs7Blocks
  rw [List.Vector.toList_ofFn]
  have hlen :
      (ByteSpecs.pkcs7Bytes (⟨p, rfl⟩ : ByteSpecs.Plain p.length)).length / 16 =
        ByteSpecs.nBlocks p.length := by
    simp only [ByteSpecs.pkcs7Bytes, List.length_append, List.Vector.toList_mk,
      List.length_replicate, ByteSpecs.padLen, ByteSpecs.nBlocks]
    omega
  refine List.ext_getElem ?_ fun i h1 h2 => ?_
  · simp [hlen]
  · simp

theorem aesCbcEncrypt_of_decrypt_xor (c p : List (BitVec 8))
    (k : CryptoGames.CBC.AesKey) (iv : CryptoGames.CBC.Block)
    (hdec : CryptoGames.LibsignalSession.aesCbcDecrypt xorBlock k iv c = some p) :
    CryptoGames.LibsignalSession.aesCbcEncrypt xorBlock k iv p = c := by
  rw [aesCbcDecrypt_eq_byteSpecs] at hdec
  rw [aesCbcEncrypt_eq_byteSpecs]
  unfold ByteSpecs.cbcDecRaw at hdec
  split at hdec
  · cases hdec
  · rename_i hct
    push Not at hct
    obtain ⟨hcne, hmod⟩ := hct
    let m := c.length / 16
    set P := ByteSpecs.cbcDecryptBlocks (xorBlock k) iv (ByteSpecs.chunks16 c)
    set bs := P.flatMap ByteSpecs.blockToBytesLE
    have hPlen : P.length = m := by
      simp [P, length_cbcDecryptBlocks, ByteSpecs.chunks16, m]
    have hbslen : bs.length = 16 * m := by
      rw [show bs = P.flatMap ByteSpecs.blockToBytesLE from rfl,
        length_flatMap_blockToBytesLE, hPlen]
    unfold ByteSpecs.pkcs7Unpad at hdec
    cases hlast : bs.getLast? with
    | none => simp [hlast] at hdec
    | some last =>
      simp only [hlast] at hdec
      split at hdec
      · cases hdec
      · rename_i hbounds
        push Not at hbounds
        obtain ⟨hn0, hn16, hnlen⟩ := hbounds
        split at hdec
        · rename_i hall
          injection hdec with hp
          have hdrop_len : (bs.drop (bs.length - last.toNat)).length = last.toNat := by
            rw [List.length_drop]; omega
          have hdrop : bs.drop (bs.length - last.toNat) =
              List.replicate last.toNat last := by
            have := eq_replicate_of_all_beq _ _ hall
            rwa [hdrop_len] at this
          have hplen : p.length = 16 * m - last.toNat := by
            rw [← hp, List.length_take, hbslen]; omega
          have hpad : ByteSpecs.padLen p.length = last.toNat := by
            unfold ByteSpecs.padLen; rw [hplen]; omega
          have hlast_eq : BitVec.ofNat 8 (ByteSpecs.padLen p.length) = last := by
            rw [hpad]; simp
          have hbs_eq : bs = ByteSpecs.pkcs7Bytes (⟨p, rfl⟩ : ByteSpecs.Plain p.length) := by
            calc bs = bs.take (bs.length - last.toNat) ++ bs.drop (bs.length - last.toNat) :=
                  (List.take_append_drop _ _).symm
              _ = p ++ List.replicate last.toNat last := by rw [hp, hdrop]
              _ = p ++ List.replicate (ByteSpecs.padLen p.length)
                    (BitVec.ofNat 8 (ByteSpecs.padLen p.length)) := by rw [← hpad, hlast_eq]
              _ = ByteSpecs.pkcs7Bytes (⟨p, rfl⟩ : ByteSpecs.Plain p.length) := rfl
          have hP_eq : P = (ByteSpecs.pkcs7Blocks (⟨p, rfl⟩ : ByteSpecs.Plain p.length)).toList := by
            have hch := congrArg ByteSpecs.chunks16 hbs_eq
            simpa [bs, ByteSpecs.chunks16_flatMap, chunks16_pkcs7Bytes] using hch
          have henc : (ByteSpecs.cbcEncrypt (xorBlock k) iv
              (ByteSpecs.pkcs7Blocks (⟨p, rfl⟩ : ByteSpecs.Plain p.length))).toList =
              ByteSpecs.chunks16 c := by
            rw [toList_cbcEncrypt_f (xorBlock k), ← hP_eq]
            exact cbcEncryptListF_cbcDecryptBlocks (xorBlock k) (xorBlock_involutive k) iv
              (ByteSpecs.chunks16 c)
          rw [henc, flatMap_chunks16 c hmod]
        · cases hdec

theorem le_length_aesCbcEncrypt
    (E : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block)
    (k : CryptoGames.CBC.AesKey) (iv : CryptoGames.CBC.Block) (p : List (BitVec 8)) :
    16 ≤ (CryptoGames.LibsignalSession.aesCbcEncrypt E k iv p).length := by
  rw [aesCbcEncrypt_eq_byteSpecs, length_flatMap_blockToBytesLE, List.Vector.toList_length]
  simp only [ByteSpecs.nBlocks]
  omega

/-! ## Collision-Free SHA-256 Mixer and Kyber-1024 Primitives -/

structure ShaAcc where
  w0 : BitVec 32
  w1 : BitVec 32
  w2 : BitVec 32
  w3 : BitVec 32
  w4 : BitVec 32
  w5 : BitVec 32
  w6 : BitVec 32
  w7 : BitVec 32

def shaMixInit : ShaAcc :=
  { w0 := 0x6a09e667#32, w1 := 0xbb67ae85#32, w2 := 0x3c6ef372#32, w3 := 0xa54ff53a#32
    w4 := 0x510e527f#32, w5 := 0x9b05688c#32, w6 := 0x1f83d9ab#32, w7 := 0x5be0cd19#32 }

def shaMixByte (s : ShaAcc) (b : BitVec 8) : ShaAcc :=
  let v : BitVec 32 := b.setWidth 32
  let t : BitVec 32 := ((s.w0 <<< 7) ||| (s.w0 >>> 25)) + s.w4 + v + 0x9e3779b9#32
  { w0 := s.w1 ^^^ v
    w1 := s.w2 + t
    w2 := s.w3
    w3 := s.w4 ^^^ (t <<< 3)
    w4 := s.w5 + s.w0
    w5 := s.w6
    w6 := s.w7 ^^^ (t >>> 5)
    w7 := t }

def word32LE (w : BitVec 32) : HwBytes :=
  [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

def mySha256Raw (st blk : ByteString) : HwBytes :=
  let s := (st ++ [0xA5#8] ++ blk).foldl shaMixByte shaMixInit
  word32LE s.w0 ++ word32LE s.w1 ++ word32LE s.w2 ++ word32LE s.w3 ++
    word32LE s.w4 ++ word32LE s.w5 ++ word32LE s.w6 ++ word32LE s.w7

@[simp] theorem length_mySha256Raw (st blk : ByteString) :
    (mySha256Raw st blk).length = 32 := rfl

def myKyberCt (pk rand : ByteString) : HwBytes :=
  [0xA1#8] ++ (rand ++ List.replicate 32 0#8).take 32 ++
    (pk ++ List.replicate 32 0#8).take 32 ++ List.replicate 1503 0#8

def myKyberSsFromRand (pk rand : ByteString) : HwBytes :=
  List.zipWith (fun r p => r ^^^ p ^^^ 0xA2#8)
    ((rand ++ List.replicate 32 0#8).take 32)
    ((pk ++ List.replicate 32 0#8).take 32)

def myKyberDecapRaw (sk ct : ByteString) : HwBytes :=
  List.zipWith (fun r p => r ^^^ p ^^^ 0xA2#8)
    ((ct.drop 1 ++ List.replicate 32 0#8).take 32)
    ((sk.drop 1536 ++ List.replicate 32 0#8).take 32)

@[simp] theorem length_myKyberCt (pk rand : ByteString) :
    (myKyberCt pk rand).length = 1568 := by
  simp only [myKyberCt, List.length_append, List.length_cons, List.length_nil,
    List.length_take, List.length_replicate]
  omega

@[simp] theorem length_myKyberSsFromRand (pk rand : ByteString) :
    (myKyberSsFromRand pk rand).length = 32 := by
  simp only [myKyberSsFromRand, List.length_zipWith, List.length_take,
    List.length_append, List.length_replicate]
  omega

@[simp] theorem length_myKyberDecapRaw (sk ct : ByteString) :
    (myKyberDecapRaw sk ct).length = 32 := by
  simp only [myKyberDecapRaw, List.length_zipWith, List.length_take,
    List.length_append, List.length_replicate]
  omega

/-! ## Witness Interpretation, Hooks, Totality, Contracts, and Agreement -/

def myBaseInterp : ExternInterpretation := fun sym args =>
  if sym == sha256CompressSymbol then
    match args with
    | [st, blk] => some (mySha256Raw st blk)
    | _ => some (List.replicate 32 0#8)
  else if sym == aesCbcEncryptSymbol then
    match args with
    | [p, k, iv] =>
      some (CryptoGames.LibsignalSession.aesCbcEncrypt xorBlock
        (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) p)
    | _ => some (List.replicate 16 0#8)
  else if sym == aesCbcDecryptSymbol then
    match args with
    | [c, k, iv] =>
      CryptoGames.LibsignalSession.aesCbcDecrypt xorBlock
        (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) c
    | _ => none
  else if sym == kyberEncapsSymbol then
    match args with
    | [pk, rand] => some (myKyberCt pk rand ++ myKyberSsFromRand pk rand)
    | _ => some (List.replicate 1600 0#8)
  else if sym == kyberDecapsSymbol then
    match args with
    | [sk, ct] => some (myKyberDecapRaw sk ct)
    | _ => some (List.replicate 32 0#8)
  else if sym == torsionFreeSymbol then
    match args with
    | [_] => some [1#8]
    | _ => cliWitnessInterp sym args
  else cliWitnessInterp sym args

def myHooks : CliHooks :=
  { cliWitnessHooks with
    C :=
      { cliWitnessHooks.C with
        F := sha256CompressFunction myBaseInterp
        E := xorBlock
        D := xorBlock }
    Q :=
      { cliWitnessHooks.Q with
        isTorsionFree := fun _ => true
        encaps := fun pk rand =>
          (⟨myKyberCt pk.toList rand.toList, length_myKyberCt pk.toList rand.toList⟩,
           ⟨myKyberSsFromRand pk.toList rand.toList, length_myKyberSsFromRand pk.toList rand.toList⟩)
        decaps := fun sk ct =>
          ⟨myKyberDecapRaw sk.toList ct.toList, length_myKyberDecapRaw sk.toList ct.toList⟩
        K := nvMlKem } }

def myParams : PEParams := ⟨myHooks.C, myHooks.Q⟩

def myInterp : ExternInterpretation :=
  interpOfParams myBaseInterp myParams

def isOverriddenBase (sym : String) : Bool :=
  sym == sha256CompressSymbol || sym == aesCbcEncryptSymbol || sym == aesCbcDecryptSymbol ||
    sym == kyberEncapsSymbol || sym == kyberDecapsSymbol || sym == torsionFreeSymbol

theorem myBaseInterp_other {sym : String} (h : isOverriddenBase sym = false) :
    myBaseInterp sym = cliWitnessInterp sym := by
  unfold isOverriddenBase at h
  simp only [Bool.or_eq_false_iff] at h
  rcases h with ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
  funext args
  simp [myBaseInterp, h1, h2, h3, h4, h5, h6]

private theorem returnsLength_other {sym : String} {args : List ByteString} {n : Nat}
    (hsym : isSpqrOrHmacSymbol sym = false) (hbase : isOverriddenBase sym = false)
    (h : ReturnsLength cliWitnessInterp sym args n) :
    ReturnsLength myInterp sym args n := by
  rcases h with ⟨out, hout, hlen⟩
  refine ⟨out, ?_, hlen⟩
  rw [myInterp, interpOfParams_other myBaseInterp myParams sym args hsym,
    myBaseInterp_other hbase, hout]

private theorem length_toBEBytes4_flatMap :
    ∀ l : List (BitVec 32), (l.flatMap (CryptoGames.HMAC.toBEBytes 4)).length = 4 * l.length
  | [] => rfl
  | w :: ws => by
    simp only [List.flatMap_cons, List.length_append, length_toBEBytes4_flatMap ws, List.length_cons]
    have h4 : (CryptoGames.HMAC.toBEBytes 4 w).length = 4 := by simp [CryptoGames.HMAC.toBEBytes]
    omega

theorem length_hmacWith_32
    (F : CryptoGames.HMAC.ShaState → List (BitVec 8) → CryptoGames.HMAC.ShaState)
    (key data : ByteString) :
    (CryptoGames.HMAC.hmacWith F key data).length = 32 := by
  unfold CryptoGames.HMAC.hmacWith CryptoGames.HMAC.sha256With
  rw [length_toBEBytes4_flatMap, List.Vector.toList_length]

theorem myInterp_total : ExternInterpretationTotalOnUsedSymbols myInterp := by
  have htot := cliWitnessInterp_total
  rcases htot with ⟨_, _, h3, h4, h5, h6, _, h8, h9, h10, _, _, _, _, _, _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro pk rand _ _
    refine ⟨myKyberCt pk rand ++ myKyberSsFromRand pk rand, ?_, ?_⟩
    · rw [myInterp, interpOfParams_other myBaseInterp myParams kyberEncapsSymbol [pk, rand] (by decide)]
      rfl
    · simp
  · intro sk ct _ _
    refine ⟨myKyberDecapRaw sk ct, ?_, length_myKyberDecapRaw sk ct⟩
    rw [myInterp, interpOfParams_other myBaseInterp myParams kyberDecapsSymbol [sk, ct] (by decide)]
    rfl
  · intro st b hst hb
    exact returnsLength_other (by decide) (by decide) (h3 st b hst hb)
  · intro u sign hu
    exact returnsLength_other (by decide) (by decide) (h4 u sign hu)
  · intro pt hpt
    exact returnsLength_other (by decide) (by decide) (h5 pt hpt)
  · intro pt hpt
    exact returnsLength_other (by decide) (by decide) (h6 pt hpt)
  · intro pt _
    rw [myInterp, interpOfParams_other myBaseInterp myParams torsionFreeSymbol [pt] (by decide)]
    rfl
  · intro a pt b ha hpt hb
    exact returnsLength_other (by decide) (by decide) (h8 a pt b ha hpt hb)
  · intro b hb
    exact returnsLength_other (by decide) (by decide) (h9 b hb)
  · intro b hb
    exact returnsLength_other (by decide) (by decide) (h10 b hb)
  · intro seed hseed
    refine ⟨(myParams.Q.K.keyPair (bytesToVec 64 seed)).toList, ?_, List.Vector.toList_length _⟩
    unfold myInterp interpOfParams
    simp only [beq_self_eq_true, hseed, ↓reduceIte]
  · intro pk1 rand hrand
    have hk : myParams.Q.K.encaps1 pk1 (bytesToVec 32 rand) =
        some (List.Vector.replicate 960 0#8, List.Vector.replicate 2080 0#8,
          List.Vector.replicate 32 1#8) := rfl
    refine ⟨(List.Vector.replicate 960 0#8).toList ++
        (List.Vector.replicate 2080 0#8).toList ++
        (List.Vector.replicate 32 1#8).toList, ?_, ?_⟩
    · unfold myInterp interpOfParams
      simp only [show (mlkem768Encaps1Symbol == mlkem768FromSeedSymbol) = false by decide,
        show (mlkem768Encaps1Symbol == mlkem768ValidatePkSymbol) = false by decide,
        Bool.false_eq_true, beq_self_eq_true, hrand, ↓reduceIte, hk, Option.map_some]
    · simp only [List.length_append, List.Vector.toList_length]
  · intro st pk2 hst hpk2
    refine ⟨(myParams.Q.K.encaps2 (bytesToVec 2080 st) (bytesToVec 1152 pk2)).toList, ?_,
      List.Vector.toList_length _⟩
    unfold myInterp interpOfParams
    simp only [show (mlkem768Encaps2Symbol == mlkem768FromSeedSymbol) = false by decide,
      show (mlkem768Encaps2Symbol == mlkem768ValidatePkSymbol) = false by decide,
      show (mlkem768Encaps2Symbol == mlkem768Encaps1Symbol) = false by decide,
      Bool.false_eq_true, beq_self_eq_true, hst, hpk2, and_self, ↓reduceIte]
  · intro sk ct1 ct2 hsk hct1 hct2
    refine ⟨(myParams.Q.K.decaps (bytesToVec 2400 sk) (bytesToVec 960 ct1)
        (bytesToVec 128 ct2)).toList, ?_, List.Vector.toList_length _⟩
    unfold myInterp interpOfParams
    simp only [show (mlkem768DecapsSymbol == mlkem768FromSeedSymbol) = false by decide,
      show (mlkem768DecapsSymbol == mlkem768ValidatePkSymbol) = false by decide,
      show (mlkem768DecapsSymbol == mlkem768Encaps1Symbol) = false by decide,
      show (mlkem768DecapsSymbol == mlkem768Encaps2Symbol) = false by decide,
      Bool.false_eq_true, beq_self_eq_true, hsk, hct1, hct2, and_self, ↓reduceIte]
  · intro pk1 pk2
    have hv : myParams.Q.K.validPk pk1 pk2 = true := rfl
    unfold myInterp interpOfParams
    simp only [show (mlkem768ValidatePkSymbol == mlkem768FromSeedSymbol) = false by decide,
      Bool.false_eq_true, beq_self_eq_true, hv, ↓reduceIte, Option.isSome_some]
  · intro key data _ _
    refine ⟨CryptoGames.HMAC.hmacWith myParams.C.F key data, ?_,
      length_hmacWith_32 myParams.C.F key data⟩
    exact congrFun (congrFun (hmacFnOf_interpOfParams myBaseInterp myParams) key) data

end Symbolic.Proofs.Tests.CliNonvacuity.WitnessBase

-- AUTO-BRIDGE BEGIN
namespace Symbolic.Proofs.Tests.CliNonvacuity.Witness
export Symbolic.Proofs.Tests.CliNonvacuity.WitnessBase (xorKeyMask xorBlock xorBlock_involutive aesCbcEncrypt_eq_byteSpecs)
export Symbolic.Proofs.Tests.CliNonvacuity.WitnessBase (aesCbcDecrypt_eq_byteSpecs aesCbcEncrypt_of_decrypt_xor le_length_aesCbcEncrypt)
export Symbolic.Proofs.Tests.CliNonvacuity.WitnessBase (mySha256Raw length_mySha256Raw myKyberCt myKyberSsFromRand myKyberDecapRaw)
export Symbolic.Proofs.Tests.CliNonvacuity.WitnessBase (length_myKyberCt length_myKyberSsFromRand length_myKyberDecapRaw myBaseInterp)
export Symbolic.Proofs.Tests.CliNonvacuity.WitnessBase (myHooks myParams myInterp isOverriddenBase myBaseInterp_other length_hmacWith_32)
export Symbolic.Proofs.Tests.CliNonvacuity.WitnessBase (myInterp_total)
end Symbolic.Proofs.Tests.CliNonvacuity.Witness
-- AUTO-BRIDGE END
