/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Stage1Kyber -- shake: keep
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredTraceExplanation
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.Bytes.AttackerKnowledge
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
public import ProofLib.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Sem
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

/-!
# PQXDH and Triple Ratchet Concretization Lemmas

Proves concretization (`gamma`) commutation lemmas over `DY.Libsignal.Composed.Refinement.gamma` for
symmetric encryption, HMAC, Triple Ratchet message-key derivation, X25519 agreement, PQXDH and
Double Ratchet KDFs, KEM decapsulation, and Bob's initial pre-key salt/seed and MAC
(`bobSaltSeed_gamma`, `accept_macSound_of_post`).
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.TR

cref_open
open DY.DiffieHellman DY.Signature DY.PQKem DY.SymEnc
open DY.Concat DY.Literal DY.Trunc DY.KdfExtract
open DY.X25519 (leValue p25519)
open ByteSpecs (hmacWith sha256With toBEBytes)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.Refinement (x25519PublicKeySymbol x25519AgreementSymbol sha256CompressFunction
  ExternCryptoLawsHold)
open DY.Libsignal.PQXDH (HandshakeKeys pqxdhKdf pqxdhIkm agree errToOption serializedIk encodeEC
  pqxdhLabel discontinuity)
open DY.Libsignal.TripleRatchet (TRSignalMsg parseTrSignalMsg trMsgKeys spqrB2A)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
/-! ## Pure Byte-Level KDF, MAC, and Cipher Helpers -/

def dhAgreeBytes (interpretation : ExternInterpretation) (sk pk : HwBytes) : HwBytes :=
  (interpretation x25519AgreementSymbol [clamp sk, pk]).getD []

def discontinuityBytes : HwBytes := List.replicate 32 0xFF#8

def pqxdhLabelBytes : HwBytes :=
  ofByteArray "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024".toUTF8

def whisperRatchetBytes : HwBytes := ofByteArray "WhisperRatchet".toUTF8

def whisperMessageKeysBytes : HwBytes := ofByteArray "WhisperMessageKeys".toUTF8

def pqxdhIkmBytes (dh1 dh2 dh3 : HwBytes) (dh4 : Option HwBytes) (ss : HwBytes) : HwBytes :=
  discontinuityBytes ++ (dh1 ++ (dh2 ++ (dh3 ++ match dh4 with | some d => d ++ ss | none => ss)))

def hkdfBlock1Bytes (F : ByteSpecs.ShaState → HwBytes → ByteSpecs.ShaState)
    (prk info : HwBytes) : HwBytes :=
  hmacWith F prk (info ++ [1#8])

def hkdfBlock2Bytes (F : ByteSpecs.ShaState → HwBytes → ByteSpecs.ShaState)
    (prk info : HwBytes) : HwBytes :=
  hmacWith F prk (hkdfBlock1Bytes F prk info ++ (info ++ [2#8]))

def hkdfBlock3Bytes (F : ByteSpecs.ShaState → HwBytes → ByteSpecs.ShaState)
    (prk info : HwBytes) : HwBytes :=
  hmacWith F prk (hkdfBlock2Bytes F prk info ++ (info ++ [3#8]))

def pqxdhKdfBytes (F : ByteSpecs.ShaState → HwBytes → ByteSpecs.ShaState)
    (ikm : HwBytes) : HwBytes × HwBytes × HwBytes :=
  let prk := hmacWith F (List.replicate 32 0#8) ikm
  (hkdfBlock1Bytes F prk pqxdhLabelBytes,
   hkdfBlock2Bytes F prk pqxdhLabelBytes,
   hkdfBlock3Bytes F prk pqxdhLabelBytes)

def createChainKeyBytes (interpretation : ExternInterpretation)
    (rk theirPk ourSk : HwBytes) : HwBytes :=
  let F := sha256CompressFunction interpretation
  hkdfBlock2Bytes F (hmacWith F rk (dhAgreeBytes interpretation ourSk theirPk)) whisperRatchetBytes

def chainKeyAtBytes (F : ByteSpecs.ShaState → HwBytes → ByteSpecs.ShaState)
    (ck : HwBytes) : Nat → HwBytes
  | 0 => ck
  | n + 1 => chainKeyAtBytes F (hmacWith F ck [0x02#8]) n

def recvSeedBytes (F : ByteSpecs.ShaState → HwBytes → ByteSpecs.ShaState)
    (ck : HwBytes) (n : Nat) : HwBytes :=
  hmacWith F (chainKeyAtBytes F ck n) [0x01#8]

def spqrIdxBytes (idx : UInt32) : HwBytes :=
  ofByteArray ⟨#[idx.toUInt8, (idx >>> 8).toUInt8, (idx >>> 16).toUInt8, (idx >>> 24).toUInt8]⟩

def trMacKeyBytes (F : ByteSpecs.ShaState → HwBytes → ByteSpecs.ShaState)
    (salt seed : HwBytes) : HwBytes :=
  hkdfBlock2Bytes F (hmacWith F salt seed) whisperMessageKeysBytes

def computeMacBytes (F : ByteSpecs.ShaState → HwBytes → ByteSpecs.ShaState)
    (macKey ikA ikB wire : HwBytes) : HwBytes :=
  (hmacWith F macKey (ikA ++ (ikB ++ wire))).take 8

def trCipherKeyBytes (F : ByteSpecs.ShaState → HwBytes → ByteSpecs.ShaState)
    (salt seed : HwBytes) : HwBytes :=
  hkdfBlock1Bytes F (hmacWith F salt seed) whisperMessageKeysBytes

def trIvBytes (F : ByteSpecs.ShaState → HwBytes → ByteSpecs.ShaState)
    (salt seed : HwBytes) : HwBytes :=
  hkdfBlock3Bytes F (hmacWith F salt seed) whisperMessageKeysBytes

/-- Bob's PQXDH handshake keys for pre-key message `p` and representation `x`. -/
def bobKeys (r : ProtocolSetup) (p : PreKeyFields) (x : PreKeyRep) : Option HandshakeKeys := do
  let opk ← match p.preKeyId with
    | none => some none
    | some id => if r.withOpk && id == r.opkId then some (some (setupSecret r 6)) else none
  let ikA := setupPublic r 0
  let ikBsk := setupSecret r 1
  let spk := setupSecret r 2
  let pqsk := setupSecret r 4
  let ss := (errToOption (DY.PQKem.kemDecap pqsk x.ct)).getD
    (DY.PQKem.kemRejKey pqsk x.ct)
  pure (pqxdhKdf (pqxdhIkm (agree ikA spk) (agree x.ek ikBsk) (agree x.ek spk)
    (opk.map (agree x.ek ·)) ss))

/-- Bob's initial receiving chain for `msg` under handshake keys `keys`. -/
def bobChain (r : ProtocolSetup) (keys : HandshakeKeys) (msg : TRSignalMsg) : RecvChain :=
  { ratchetKey := msg.ratchetKey, chainKey := (createChain keys.rk msg.ratchetKey
      (setupSecret r 2)).2, index := 0, rIdx := 2 }

/-! ## `SubFunction` Instances and Basic `gamma` Unfolding Lemmas -/

unseal DY.Bytes in
instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeLit (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, litFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeConcat (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, concatFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeDhPk interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeDh interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKdf interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kdfFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSym interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, symFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeTrunc (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, truncFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeVariant interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, x25519Funs, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemPk S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemEncap interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemSS interpretation S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrChainKey S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem gamma_rand (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (t n : Nat) :
    gamma interpretation S g (({timestamp := t, size := n} : DY.Random.Random DY.Bytes).pack) =
      if n = 0 then [] else g.σ t n := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll interpretation S g)]
  unfold concretizeRandom node
  split <;> rfl

theorem gamma_lit (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (b : ByteArray) :
    gamma interpretation S g (DY.Literal.literalToBytes b) = ofByteArray b := by
  unfold gamma gamma' DY.Literal.literalToBytes
  show ((({lit := b} : DY.Literal.Literal.SubF DY.Bytes).pack).rec
    (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeLit (concretizeAll interpretation S g)]; rfl

theorem gamma_concat (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (l r : DY.Bytes) :
    gamma interpretation S g (DY.Concat.concat l r) =
      gamma interpretation S g l ++ gamma interpretation S g r := by
  unfold gamma gamma'
  show ((({lhs := l, rhs := r} : DY.Concat.Concat.SubF DY.Bytes).pack).rec
    (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeConcat (concretizeAll interpretation S g)]; rfl

theorem gamma_trunc8 (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (x : DY.Bytes) :
    gamma interpretation S g (DY.Trunc.trunc8 x) = (gamma interpretation S g x).take 8 := by
  unfold gamma gamma'
  show ((({input := x} : DY.Trunc.Trunc8.SubF DY.Bytes).pack).rec
    (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeTrunc (concretizeAll interpretation S g)]; rfl

theorem gamma_kdfExtract (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (salt ikm : DY.Bytes) :
    gamma interpretation S g (DY.KdfExtract.kdfExtract salt ikm) =
      hmacWith (sha256CompressFunction interpretation)
        (gamma interpretation S g salt) (gamma interpretation S g ikm) := by
  unfold gamma gamma'
  show ((({salt, ikm} : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec
    (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeKdf interpretation) (concretizeAll interpretation S g)]; rfl

theorem gamma_hmac (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (key msg : DY.Bytes) :
    gamma interpretation S g (DY.Libsignal.TripleRatchet.hmac key msg) =
      hmacWith (sha256CompressFunction interpretation)
        (gamma interpretation S g key) (gamma interpretation S g msg) :=
  gamma_kdfExtract interpretation S g key msg

theorem gamma_dhPk (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (sk : DY.Bytes) :
    gamma interpretation S g (DY.DiffieHellman.dhPk sk) =
      (interpretation x25519PublicKeySymbol [clamp (gamma interpretation S g sk)]).getD [] := by
  unfold gamma gamma'
  show ((({sk} : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack).rec (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeDhPk interpretation) (concretizeAll interpretation S g)]; rfl

theorem gamma_dh_raw (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (pk sk : DY.Bytes) :
    gamma interpretation S g (({pk, sk} : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) =
      (interpretation x25519AgreementSymbol
        [clamp (gamma interpretation S g sk), gamma interpretation S g pk]).getD [] := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeDh interpretation) (concretizeAll interpretation S g)]; rfl

theorem gamma_dh (interpretation : ExternInterpretation)
    (hEq : ExternCryptoLawsHold interpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (pk sk : DY.Bytes) :
    gamma interpretation S g (DY.DiffieHellman.dh pk sk) =
      (interpretation x25519AgreementSymbol
        [clamp (gamma interpretation S g sk), gamma interpretation S g pk]).getD [] := by
  have hv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF pk
  simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]
  split
  · rename_i sk2 heq
    rw [heq] at hv; simp only at hv; subst hv
    split
    · rw [gamma_dh_raw]
    · rw [gamma_dh_raw]
      show (interpretation x25519AgreementSymbol
          [clamp (gamma interpretation S g sk2), gamma interpretation S g (dhPk sk)]).getD [] =
        (interpretation x25519AgreementSymbol
          [clamp (gamma interpretation S g sk), gamma interpretation S g (dhPk sk2)]).getD []
      rw [gamma_dhPk, gamma_dhPk,
        hEq.x25519_agreement_commutes (clamp (gamma interpretation S g sk2))
          (clamp (gamma interpretation S g sk))]
  · rw [gamma_dh_raw]

theorem gamma_kemEncap_fst (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (pk e : DY.Bytes) :
    gamma interpretation S g (DY.PQKem.kemEncap pk e).1 =
      if (gamma interpretation S g e).length = 32 then
        ((interpretation kyberEncapsSymbol
          [gamma interpretation S g pk, gamma interpretation S g e]).getD []).take 1568
      else [] := by
  unfold gamma gamma'
  show ((({pk, entropy := e} : DY.PQKem.Encap.SubF DY.Bytes).pack).rec
    (concretizeAll interpretation S g)).bytes = _
  exact Symbolic.Swarm.CREF.Stage1Kyber.gamma_kemEncap_fst interpretation S g pk e

theorem gamma_kemEncap_snd (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (pk e : DY.Bytes) :
    gamma interpretation S g (DY.PQKem.kemEncap pk e).2 =
      if (gamma interpretation S g e).length = 32 then
        ((interpretation kyberEncapsSymbol
          [gamma interpretation S g pk, gamma interpretation S g e]).getD []).drop 1568
      else S.kemDecap (gamma interpretation S g pk) (gamma interpretation S g e) := by
  unfold gamma gamma'
  show ((({pk, entropy := e} : DY.PQKem.SharedSecret.SubF DY.Bytes).pack).rec
    (concretizeAll interpretation S g)).bytes = _
  exact Symbolic.Swarm.CREF.Stage1Kyber.gamma_kemEncap_snd interpretation S g pk e

theorem gamma_spqrChainKey (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (k p i : DY.Bytes) :
    gamma interpretation S g (DY.Spqr.spqrChainKey k p i) =
      spqrKeyBytes
        (S.chainKey (gamma interpretation S g k)
          (gamma interpretation S g p) (gamma interpretation S g i)) := by
  unfold gamma gamma'
  show ((({authKey := k, params := p, idx := i} : DY.Spqr.ChainKey.SubF DY.Bytes).pack).rec
    (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeSpqrChainKey S) (concretizeAll interpretation S g)]; rfl

theorem gamma_zeroKey (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    gamma interpretation S g DY.Spqr.zeroKey = List.replicate 32 0#8 := by
  unfold DY.Spqr.zeroKey
  rw [gamma_lit]
  decide

theorem gamma_litByte (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (b : UInt8) :
    gamma interpretation S g (DY.Libsignal.TripleRatchet.litByte b) = [b.toBitVec] := by
  unfold DY.Libsignal.TripleRatchet.litByte; rw [gamma_lit]; rfl

theorem gamma_serializedIk (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (pk : DY.Bytes) :
    gamma interpretation S g (serializedIk pk) = ecKey (gamma interpretation S g pk) := by
  unfold serializedIk encodeEC; rw [gamma_concat, gamma_litByte]; rfl

/-! ## Setup Trace, `setupSecret`, and `setupPublic` Under `gamma` -/

theorem setupRandomsAt_eq (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    setupRandomsAt r =
      [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] ++
        (if r.withOpk then [(22, 32)] else []) :=
  Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hNe

theorem secretBytes_eq (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    secretBytes r 0 = r.fresh 0 32 ∧
    secretBytes r 1 = r.fresh 5 32 ∧
    secretBytes r 2 = r.fresh 10 32 ∧
    secretBytes r 4 = r.fresh 16 64 ∧
    (r.withOpk = true → secretBytes r 6 = r.fresh 22 32) := by
  refine ⟨?_, ?_, ?_, ?_, fun hopk => ?_⟩
  · rw [secretBytes, setupRandomsAt_eq r hNe]; cases r.withOpk <;> rfl
  · rw [secretBytes, setupRandomsAt_eq r hNe]; cases r.withOpk <;> rfl
  · rw [secretBytes, setupRandomsAt_eq r hNe]; cases r.withOpk <;> rfl
  · rw [secretBytes, setupRandomsAt_eq r hNe]; cases r.withOpk <;> rfl
  · rw [secretBytes, setupRandomsAt_eq r hNe, hopk]; rfl

theorem setupSecret_eq (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    setupSecret r 0 = randTerm 0 32 ∧
    setupSecret r 1 = randTerm 5 32 ∧
    setupSecret r 2 = randTerm 10 32 ∧
    setupSecret r 4 = randTerm 16 64 ∧
    (r.withOpk = true → setupSecret r 6 = randTerm 22 32) := by
  refine ⟨?_, ?_, ?_, ?_, fun hopk => ?_⟩
  · rw [setupSecret, setupRandoms_eq r hNe]; cases r.withOpk <;> rfl
  · rw [setupSecret, setupRandoms_eq r hNe]; cases r.withOpk <;> rfl
  · rw [setupSecret, setupRandoms_eq r hNe]; cases r.withOpk <;> rfl
  · rw [setupSecret, setupRandoms_eq r hNe]; cases r.withOpk <;> rfl
  · rw [setupSecret, setupRandoms_eq r hNe, hopk]; rfl

theorem setupPublic_eq (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    setupPublic r 0 = DY.DiffieHellman.dhPk (setupSecret r 0) ∧
    setupPublic r 2 = DY.DiffieHellman.dhPk (setupSecret r 1) ∧
    setupPublic r 6 = DY.PQKem.kemPk (setupSecret r 4) := by
  obtain ⟨hs0, hs1, _, hs4, -⟩ := setupSecret_eq r hNe
  rw [hs0, hs1, hs4]
  have hlen4 : (setupTr4 r.alice r.bob).length = 22 := by
    simp only [setupTr4, setupTr3, setupTr2, setupTr1,
      Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hlen5 : (setupTr5 r.alice r.bob).length = 26 := by
    simp only [setupTr5, setupTr4, setupTr3, setupTr2, setupTr1,
      Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hr22 : List.range' 0 (22 - 0) =
      [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] := rfl
  have hr26 : List.range' 0 (26 - 0) =
      [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25] := rfl
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [setupPublic, setupSent, setupTrace_eq r hNe]
    cases r.withOpk
    · simp only [Bool.false_eq_true, ↓reduceIte, newIndices,
        Symbolic.DYBridge.DY.Trace.length_eq_1, hlen4, hr22,
        List.filterMap_cons, List.filterMap_nil]
      simp [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1,
        setupTr4, setupTr3, setupTr2, setupTr1,
        Symbolic.DYBridge.DY.Trace.append_eq_1,
        DY.Trace.at?, Symbolic.DYBridge.DY.Trace.at_eq_2,
        Symbolic.DYBridge.DY.Trace.length_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_2]
      rfl
    · simp only [↓reduceIte, newIndices,
        Symbolic.DYBridge.DY.Trace.length_eq_1, hlen5, hr26,
        List.filterMap_cons, List.filterMap_nil]
      simp [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1,
        setupTr5, setupTr4, setupTr3, setupTr2, setupTr1,
        Symbolic.DYBridge.DY.Trace.append_eq_1,
        DY.Trace.at?, Symbolic.DYBridge.DY.Trace.at_eq_2,
        Symbolic.DYBridge.DY.Trace.length_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_2]
      rfl

theorem gamma_setupSecret (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (hCompat : GhostAndSemMatchSetup interpretation r S g) (hNe : r.alice ≠ r.bob) :
    gamma interpretation S g (setupSecret r 0) = secretBytes r 0 ∧
    gamma interpretation S g (setupSecret r 1) = secretBytes r 1 ∧
    gamma interpretation S g (setupSecret r 2) = secretBytes r 2 ∧
    gamma interpretation S g (setupSecret r 4) = secretBytes r 4 ∧
    (r.withOpk = true → gamma interpretation S g (setupSecret r 6) = secretBytes r 6) := by
  obtain ⟨hs0, hs1, hs2, hs4, hs6⟩ := setupSecret_eq r hNe
  obtain ⟨hb0, hb1, hb2, hb4, hb6⟩ := secretBytes_eq r hNe
  have hm0 : (0, 32) ∈ setupRandomsAt r := by
    rw [setupRandomsAt_eq r hNe]; cases r.withOpk <;> simp
  have hm1 : (5, 32) ∈ setupRandomsAt r := by
    rw [setupRandomsAt_eq r hNe]; cases r.withOpk <;> simp
  have hm2 : (10, 32) ∈ setupRandomsAt r := by
    rw [setupRandomsAt_eq r hNe]; cases r.withOpk <;> simp
  have hm4 : (16, 64) ∈ setupRandomsAt r := by
    rw [setupRandomsAt_eq r hNe]; cases r.withOpk <;> simp
  refine ⟨?_, ?_, ?_, ?_, fun hopk => ?_⟩
  · rw [hs0, hb0, randTerm]
    exact (gamma_rand interpretation S g 0 32).trans (hCompat.1 (0, 32) hm0)
  · rw [hs1, hb1, randTerm]
    exact (gamma_rand interpretation S g 5 32).trans (hCompat.1 (5, 32) hm1)
  · rw [hs2, hb2, randTerm]
    exact (gamma_rand interpretation S g 10 32).trans (hCompat.1 (10, 32) hm2)
  · rw [hs4, hb4, randTerm]
    exact (gamma_rand interpretation S g 16 64).trans (hCompat.1 (16, 64) hm4)
  · have hm6 : (22, 32) ∈ setupRandomsAt r := by
      rw [setupRandomsAt_eq r hNe, hopk]; simp
    rw [hs6 hopk, hb6 hopk, randTerm]
    exact (gamma_rand interpretation S g 22 32).trans (hCompat.1 (22, 32) hm6)

theorem gamma_setupPublic_0_2_6 (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (hCompat : GhostAndSemMatchSetup interpretation r S g) (hNe : r.alice ≠ r.bob) :
    gamma interpretation S g (setupPublic r 0) = pubBytes interpretation (secretBytes r 0) ∧
    gamma interpretation S g (setupPublic r 2) = pubBytes interpretation (secretBytes r 1) ∧
    gamma interpretation S g (setupPublic r 6) = r.opaqueBytes (setupPublic r 6) := by
  obtain ⟨hp0, hp2, -⟩ := setupPublic_eq r hNe
  obtain ⟨hs0, hs1, -⟩ := gamma_setupSecret interpretation r S g hCompat hNe
  refine ⟨?_, ?_, hCompat.2.1 r.pqpkPubTerm (by simp)⟩
  · rw [hp0, gamma_dhPk, hs0]; rfl
  · rw [hp2, gamma_dhPk, hs1]; rfl

/-! ## Symmetric Encryption, HMAC, and Message-Key Concretization -/

theorem length_flatMap_toBEBytes_is5 :
    ∀ l : List (BitVec 32), (l.flatMap (toBEBytes 4)).length = 4 * l.length
  | [] => rfl
  | _ :: xs => by
    simp [List.flatMap_cons, toBEBytes, length_flatMap_toBEBytes_is5 xs]
    omega

theorem length_hmacWith (F : ByteSpecs.ShaState → List (BitVec 8) → ByteSpecs.ShaState)
    (k m : List (BitVec 8)) : (hmacWith F k m).length = 32 := by
  unfold hmacWith sha256With
  rw [length_flatMap_toBEBytes_is5]
  simp

theorem gamma_discontinuity (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    gamma interpretation S g discontinuity = discontinuityBytes := by
  unfold discontinuity discontinuityBytes; rw [gamma_lit]; decide

theorem gamma_zeroSalt (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    gamma interpretation S g zeroSalt = List.replicate 32 0#8 := by
  unfold zeroSalt; rw [gamma_lit]; decide

theorem gamma_pqxdhLabel (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    gamma interpretation S g pqxdhLabel = pqxdhLabelBytes := by
  unfold pqxdhLabel DY.Libsignal.TripleRatchet.lit pqxdhLabelBytes; rw [gamma_lit]

theorem gamma_whisperRatchet (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    gamma interpretation S g (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") =
      whisperRatchetBytes := by
  unfold DY.Libsignal.TripleRatchet.lit whisperRatchetBytes; rw [gamma_lit]

theorem gamma_whisperMessageKeys (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    gamma interpretation S g (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") =
      whisperMessageKeysBytes := by
  unfold DY.Libsignal.TripleRatchet.lit whisperMessageKeysBytes; rw [gamma_lit]

theorem gamma_hkdfBlock1 (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (prk info : DY.Bytes) :
    gamma interpretation S g (hkdfBlock1 prk info) =
      hkdfBlock1Bytes (sha256CompressFunction interpretation)
        (gamma interpretation S g prk) (gamma interpretation S g info) := by
  unfold hkdfBlock1 hkdfBlock1Bytes; rw [gamma_hmac, gamma_concat, gamma_litByte]; rfl

theorem gamma_hkdfBlock2 (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (prk info : DY.Bytes) :
    gamma interpretation S g (hkdfBlock2 prk info) =
      hkdfBlock2Bytes (sha256CompressFunction interpretation)
        (gamma interpretation S g prk) (gamma interpretation S g info) := by
  unfold hkdfBlock2 hkdfBlock2Bytes
  rw [gamma_hmac, gamma_concat, gamma_hkdfBlock1, gamma_concat, gamma_litByte]; rfl

theorem gamma_hkdfBlock3 (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (prk info : DY.Bytes) :
    gamma interpretation S g (hkdfBlock3 prk info) =
      hkdfBlock3Bytes (sha256CompressFunction interpretation)
        (gamma interpretation S g prk) (gamma interpretation S g info) := by
  unfold hkdfBlock3 hkdfBlock3Bytes
  rw [gamma_hmac, gamma_concat, gamma_hkdfBlock2, gamma_concat, gamma_litByte]; rfl

theorem gamma_trMsgKeys_cipherKey (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (salt seed : DY.Bytes) :
    gamma interpretation S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).cipherKey =
      trCipherKeyBytes (sha256CompressFunction interpretation)
        (gamma interpretation S g salt) (gamma interpretation S g seed) := by
  unfold DY.Libsignal.TripleRatchet.trMsgKeys trCipherKeyBytes
  rw [gamma_hkdfBlock1, gamma_hmac, gamma_whisperMessageKeys]

theorem gamma_trMsgKeys_iv (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (salt seed : DY.Bytes) :
    gamma interpretation S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).iv =
      trIvBytes (sha256CompressFunction interpretation)
        (gamma interpretation S g salt) (gamma interpretation S g seed) := by
  unfold DY.Libsignal.TripleRatchet.trMsgKeys trIvBytes
  rw [gamma_hkdfBlock3, gamma_hmac, gamma_whisperMessageKeys]

theorem gamma_trMsgKeys_macKey (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (salt seed : DY.Bytes) :
    gamma interpretation S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).macKey =
      trMacKeyBytes (sha256CompressFunction interpretation)
        (gamma interpretation S g salt) (gamma interpretation S g seed) := by
  unfold DY.Libsignal.TripleRatchet.trMsgKeys trMacKeyBytes
  rw [gamma_hkdfBlock2, gamma_hmac, gamma_whisperMessageKeys]

theorem gamma_computeMac (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (macKey ikA ikB wire : DY.Bytes) :
    gamma interpretation S g (DY.Libsignal.TripleRatchet.computeMac macKey ikA ikB wire) =
      computeMacBytes (sha256CompressFunction interpretation)
        (gamma interpretation S g macKey) (gamma interpretation S g ikA)
        (gamma interpretation S g ikB) (gamma interpretation S g wire) := by
  unfold DY.Libsignal.TripleRatchet.computeMac computeMacBytes
  rw [gamma_trunc8, gamma_hmac, gamma_concat, gamma_concat]

/-! ## DH Agreement and Key-Schedule Commutation -/

theorem length_leBytes : ∀ n w, (leBytes n w).length = n
  | 0, _ => rfl
  | n + 1, w => by simp [leBytes, length_leBytes n]

theorem leValue_leBytes : ∀ n w, leValue ((leBytes n w).map BitVec.toNat) = w % 256 ^ n
  | 0, w => by simp [leBytes, leValue, Nat.mod_one]
  | n + 1, w => by
    have h : w % 256 ^ (n + 1) = w % 256 + 256 * (w / 256 % 256 ^ n) := by
      rw [Nat.pow_succ', Nat.mod_mul]
    simp only [leBytes, List.map_cons, leValue, leValue_leBytes n, BitVec.toNat_ofNat]
    exact h.symm

theorem p25519_lt : p25519 < 2 ^ 255 := by unfold p25519; omega
theorem p25519_pos : 0 < p25519 := by unfold p25519; omega
theorem uOf_lt (b : HwBytes) : x25519UCoord b < p25519 := Nat.mod_lt _ p25519_pos

theorem uOf_leBytes (w : Nat) (hw : w < 2 ^ 256) :
    x25519UCoord (leBytes 32 w) = w % 2 ^ 255 % p25519 := by
  unfold x25519UCoord DY.X25519.uCoord
  have hpow : w < 256 ^ 32 := by omega
  rw [leValue_leBytes, Nat.mod_eq_of_lt hpow]

theorem variantBytes_spec (b : HwBytes) (hb : b.length = 32) (v : Fin 4) :
    (variantBytes b v).length = 32 ∧ x25519UCoord (variantBytes b v) = x25519UCoord b := by
  unfold variantBytes
  simp only [hb, ↓reduceIte]
  refine ⟨length_leBytes _ _, ?_⟩
  have hu := uOf_lt b
  have hp := p25519_lt
  generalize x25519UCoord b = u at hu ⊢
  have key : ∀ u', u' < 2 ^ 255 → u' % p25519 = u →
      x25519UCoord (leBytes 32 (if v.val % 2 = 1 then u' + 2 ^ 255 else u')) = u := by
    intro u' h1 h2
    split
    · rw [uOf_leBytes _ (by omega), Nat.add_mod_right, Nat.mod_eq_of_lt h1, h2]
    · rw [uOf_leBytes _ (by omega), Nat.mod_eq_of_lt h1, h2]
  apply key
  · split <;> omega
  · split
    · rw [Nat.add_mod_right, Nat.mod_eq_of_lt hu]
    · exact Nat.mod_eq_of_lt hu

theorem gamma_agree (interpretation : ExternInterpretation)
    (hEq : ExternCryptoLawsHold interpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (pk sk : DY.Bytes) :
    gamma interpretation S g (agree pk sk) =
      (interpretation x25519AgreementSymbol
        [clamp (gamma interpretation S g sk), gamma interpretation S g pk]).getD [] := by
  unfold agree
  rw [gamma_dh interpretation hEq]
  unfold DY.X25519.normalizeX25519Key
  cases hview : pk.view? DY.X25519.Variant.SubF with
  | none => rfl
  | some v =>
    dsimp only
    have hpack : v.pack = pk := by
      have hp := DY.Bytes.pack_view? DY.X25519.Variant.SubF pk
      simpa [hview] using hp
    have hgamma_pk : gamma interpretation S g pk =
        variantBytes (DY.Libsignal.Refinement.torsionShift interpretation
          (gamma interpretation S g v.key) v.torsion) v.variation := by
      rw [← hpack]; unfold gamma gamma'
      rw [DY.Bytes.rec_eq (concretizeVariant interpretation) (concretizeAll interpretation S g)]; rfl
    rw [hgamma_pk]
    have htl : (DY.Libsignal.Refinement.torsionShift interpretation
        (gamma interpretation S g v.key) v.torsion).length =
          (gamma interpretation S g v.key).length := by
      unfold DY.Libsignal.Refinement.torsionShift
      split
      · rfl
      · rename_i h
        have hlen : (gamma interpretation S g v.key).length = 32 := by revert h; simp
        split
        · split
          · rename_i q _ hq
            omega
          · rfl
        · rfl
    by_cases hlen : (gamma interpretation S g v.key).length = 32
    · have hlen' := htl.trans hlen
      have hspec := variantBytes_spec _ hlen' v.variation
      rw [← hEq.x25519_agreement_torsion_invariant (clamp (gamma interpretation S g sk))
          (gamma interpretation S g v.key) v.torsion,
        hEq.x25519_agreement_reads_u_coordinate
          (clamp (gamma interpretation S g sk))
          (DY.Libsignal.Refinement.torsionShift interpretation
            (gamma interpretation S g v.key) v.torsion)
          (variantBytes (DY.Libsignal.Refinement.torsionShift interpretation
            (gamma interpretation S g v.key) v.torsion) v.variation)
          hlen' hspec.1 hspec.2.symm]
    · have hts : DY.Libsignal.Refinement.torsionShift interpretation
          (gamma interpretation S g v.key) v.torsion = gamma interpretation S g v.key := by
        unfold DY.Libsignal.Refinement.torsionShift; simp [hlen]
      rw [hts]
      unfold variantBytes
      simp [hlen]

theorem gamma_pqxdhIkm (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (dh1 dh2 dh3 : DY.Bytes) (dh4 : Option DY.Bytes) (ss : DY.Bytes) :
    gamma interpretation S g (pqxdhIkm dh1 dh2 dh3 dh4 ss) =
      pqxdhIkmBytes (gamma interpretation S g dh1) (gamma interpretation S g dh2)
        (gamma interpretation S g dh3) (dh4.map (gamma interpretation S g))
        (gamma interpretation S g ss) := by
  unfold pqxdhIkm pqxdhIkmBytes
  cases dh4 <;> simp [gamma_concat, gamma_discontinuity]

theorem gamma_pqxdhKdf (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ikm : DY.Bytes) :
    let F := sha256CompressFunction interpretation
    let k := pqxdhKdf ikm
    let (rkB, ckB, pqrB) := pqxdhKdfBytes F (gamma interpretation S g ikm)
    gamma interpretation S g k.rk = rkB ∧
    gamma interpretation S g k.ck = ckB ∧
    gamma interpretation S g k.pqr = pqrB := by
  unfold pqxdhKdf pqxdhKdfBytes
  refine ⟨?_, ?_, ?_⟩
  · rw [gamma_hkdfBlock1, gamma_hmac, gamma_zeroSalt, gamma_pqxdhLabel]
  · rw [gamma_hkdfBlock2, gamma_hmac, gamma_zeroSalt, gamma_pqxdhLabel]
  · rw [gamma_hkdfBlock3, gamma_hmac, gamma_zeroSalt, gamma_pqxdhLabel]

theorem gamma_createChain_snd (interpretation : ExternInterpretation)
    (hEq : ExternCryptoLawsHold interpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (rk theirPk ourSk : DY.Bytes) :
    gamma interpretation S g (createChain rk theirPk ourSk).2 =
      createChainKeyBytes interpretation
        (gamma interpretation S g rk) (gamma interpretation S g theirPk)
        (gamma interpretation S g ourSk) := by
  have hcc : (createChain rk theirPk ourSk).2 =
      hkdfBlock2 (DY.Libsignal.TripleRatchet.hmac rk (agree theirPk ourSk))
        (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") := rfl
  rw [hcc, gamma_hkdfBlock2, gamma_hmac, gamma_agree interpretation hEq, gamma_whisperRatchet]; rfl

theorem gamma_kdfCk_fst (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ck : DY.Bytes) :
    gamma interpretation S g (kdfCk ck).1 =
      hmacWith (sha256CompressFunction interpretation) (gamma interpretation S g ck) [0x02#8] := by
  unfold kdfCk; rw [gamma_hmac, gamma_litByte]; rfl

theorem gamma_kdfCk_snd (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ck : DY.Bytes) :
    gamma interpretation S g (kdfCk ck).2 =
      hmacWith (sha256CompressFunction interpretation) (gamma interpretation S g ck) [0x01#8] := by
  unfold kdfCk; rw [gamma_hmac, gamma_litByte]; rfl

theorem gamma_chainKeyAt (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ck : DY.Bytes) (n : Nat) :
    gamma interpretation S g (chainKeyAt ck n) =
      chainKeyAtBytes (sha256CompressFunction interpretation) (gamma interpretation S g ck) n := by
  induction n generalizing ck with
  | zero => rfl
  | succ n ih => simp only [chainKeyAt, chainKeyAtBytes]; rw [ih, gamma_kdfCk_fst]

theorem consumeMessageKey_index_zero (rk ck : DY.Bytes) (counter : UInt32)
    (hle : counter.toNat ≤ maxForwardJumps) (rIdx : Nat := 0) :
    ∃ c' : RecvChain,
      consumeMessageKey { ratchetKey := rk, chainKey := ck, index := 0, rIdx := rIdx } counter =
        some ((kdfCk (chainKeyAt ck counter.toNat)).2, c') := by
  unfold consumeMessageKey
  have h1 : ¬ (counter < (0 : UInt32)) := fun hlt => Nat.not_lt_zero counter.toNat hlt
  have h2 : ¬ (counter.toNat - (0 : UInt32).toNat > maxForwardJumps) := by
    change ¬ (counter.toNat - 0 > maxForwardJumps); omega
  have h3 : counter ≠ u32Max := by
    rintro rfl
    have hm : u32Max.toNat = 4294967295 := rfl
    have hj : maxForwardJumps = 25000 := rfl
    omega
  simp only [h1, h2, h3, ↓reduceIte]; exact ⟨_, rfl⟩

theorem spqrEmptyMsg_false_of_gamma_ne_nil (interpretation : ExternInterpretation)
    (S : OpaqueSymbolSemantics) (g : Ghost) (pq : DY.Bytes) (hne : gamma interpretation S g pq ≠ []) :
    DY.Spqr.spqrEmptyMsg pq = false := by
  unfold DY.Spqr.spqrEmptyMsg
  cases hlit : DY.Literal.bytesToLiteral pq with
  | none => rfl
  | some ba =>
    dsimp only; rw [beq_eq_false_iff_ne]; intro hsz; apply hne
    have hpq : pq = DY.Literal.literalToBytes ba := by
      have hinv := DY.Literal.literalToBytes_bytesToLiteral pq; rw [hlit] at hinv; exact hinv
    rw [hpq, gamma_lit]; unfold ofByteArray
    simp [List.eq_nil_of_length_eq_zero hsz]

theorem gamma_spqrParams_a2b (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    gamma interpretation S g (DY.Spqr.encodeSpqrDirectionParams .a2b) = [0#8] := by
  unfold DY.Spqr.encodeSpqrDirectionParams; rw [gamma_lit]; decide

theorem gamma_spqrIdx (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (idx : UInt32) :
    gamma interpretation S g (DY.Spqr.encodeSpqrIndexTerm idx) = spqrIdxBytes idx := by
  unfold DY.Spqr.encodeSpqrIndexTerm spqrIdxBytes; rw [gamma_lit]

def spqrSaltBytes (S : OpaqueSymbolSemantics) (pqr : HwBytes) (idx : UInt32) : HwBytes :=
  if idx = 0 then List.replicate 32 0#8
  else spqrKeyBytes (S.chainKey pqr [0#8] (spqrIdxBytes idx))

theorem spqrRecv_init_b2a_of_gamma_ne_nil (interpretation : ExternInterpretation)
    (S : OpaqueSymbolSemantics) (g : Ghost) (pqr pq : DY.Bytes) (idx : UInt32)
    (hne : gamma interpretation S g pq ≠ []) :
    ∃ st' salt : DY.Bytes,
      DY.Spqr.spqrRecv (DY.Spqr.spqrInit pqr (DY.Spqr.encodeSpqrDirectionParams .b2a)) pq idx =
        some (st', salt) ∧
      gamma interpretation S g salt =
        spqrSaltBytes S (gamma interpretation S g pqr) idx := by
  have hempty := spqrEmptyMsg_false_of_gamma_ne_nil interpretation S g pq hne
  refine ⟨({st := DY.Spqr.spqrInit pqr (DY.Spqr.encodeSpqrDirectionParams .b2a), msg := pq} :
      DY.Spqr.RecvState.SubF DY.Bytes).pack,
    if idx = 0 then DY.Spqr.zeroKey
    else DY.Spqr.spqrChainKey pqr (DY.Spqr.encodeSpqrDirectionParams .a2b) (DY.Spqr.encodeSpqrIndexTerm idx), ?_, ?_⟩
  · unfold DY.Spqr.spqrRecv; rw [hempty]
    simp [DY.Spqr.spqrInit, BytesView.view_pack, DY.Spqr.Direction.flip]
  · unfold spqrSaltBytes; split
    · exact gamma_zeroKey interpretation S g
    · rw [gamma_spqrChainKey, gamma_spqrParams_a2b, gamma_spqrIdx]

/-! ## KEM Decapsulation Without Implicit Rejection or Mismatch -/

theorem kemDecap_eq_some_iff (sk cipher ss : DY.Bytes) :
    errToOption (DY.PQKem.kemDecap sk cipher) = some ss →
    ∃ e : DY.Bytes,
      cipher = (DY.PQKem.kemEncap (DY.PQKem.kemPk sk) e).1 ∧
      ss = (DY.PQKem.kemEncap (DY.PQKem.kemPk sk) e).2 := by
  intro h
  simp only [errToOption, DY.PQKem.kemDecap, DY.PQKem.CanPQKem.kemDecap] at h
  cases hview1 : cipher.view? DY.PQKem.Encap.SubF with
  | none => rw [hview1] at h; cases h
  | some enc =>
    rw [hview1] at h
    dsimp only at h
    cases hview2 : enc.pk.view? DY.PQKem.Pk.SubF with
    | none => rw [hview2] at h; cases h
    | some pkSub =>
      rw [hview2] at h
      dsimp only at h
      split at h
      · next hsk =>
        injection h with hss
        have hpack1 : enc.pack = cipher := by
          have hp := DY.Bytes.pack_view? DY.PQKem.Encap.SubF cipher
          simpa [hview1] using hp
        have hpack2 : pkSub.pack = enc.pk := by
          have hp := DY.Bytes.pack_view? DY.PQKem.Pk.SubF enc.pk
          simpa [hview2] using hp
        have hpk : enc.pk = DY.PQKem.kemPk sk := by
          rw [← hpack2, hsk]
          rfl
        refine ⟨enc.entropy, ?_, ?_⟩
        · rw [← hpack1, ← hpk]; rfl
        · rw [← hss, ← hpk]; rfl
      · cases h

theorem gamma_bobKemShare_of_preKey
    (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (p : PreKeyFields) (x : PreKeyRep) (ct_wire : HwBytes)
    (hCompat : GhostAndSemMatchSetup interpretation r S g) (hNe : r.alice ≠ r.bob)
    (hnk : ¬ KyberMismatch interpretation r p)
    (hct_p : p.kyberCiphertext = some (kyberKey ct_wire))
    (hct_len : ct_wire.length = 1568)
    (hct_x : gamma interpretation S g x.ct = ct_wire) :
    gamma interpretation S g
      ((errToOption (DY.PQKem.kemDecap (setupSecret r 4) x.ct)).getD
        (DY.PQKem.kemRejKey (setupSecret r 4) x.ct)) =
      (kyberDecapsBytes interpretation r ct_wire).getD [] := by
  have h := Symbolic.Swarm.CREF.Stage1Kyber.gamma_bobKemShare
    (ct := x.ct) hNe hCompat hnk (hct_x.symm ▸ hct_p) (hct_x.symm ▸ hct_len)
  rwa [hct_x] at h

theorem gamma_kemSS_of_not_implicitReject
    (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (p : PreKeyFields) (x : PreKeyRep) (ct_wire : HwBytes)
    (hCompat : GhostAndSemMatchSetup interpretation r S g) (hNe : r.alice ≠ r.bob)
    (hnk : ¬ KyberMismatch interpretation r p)
    (hct_p : p.kyberCiphertext = some (kyberKey ct_wire))
    (hct_len : ct_wire.length = 1568)
    (hct_x : gamma interpretation S g x.ct = ct_wire) :
    ∃ ss : DY.Bytes,
      (errToOption (DY.PQKem.kemDecap (setupSecret r 4) x.ct)).getD
        (DY.PQKem.kemRejKey (setupSecret r 4) x.ct) = ss ∧
      gamma interpretation S g ss = (kyberDecapsBytes interpretation r ct_wire).getD [] :=
  ⟨_, rfl, gamma_bobKemShare_of_preKey interpretation r S g p x ct_wire
    hCompat hNe hnk hct_p hct_len hct_x⟩

/-! ## Bob Pre-Key Salt, Seed, and MAC Soundness -/

def ekBytes (p : PreKeyFields) : HwBytes := (p.baseKey.drop 1).take 32

def bobExpectedMacBytes (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (p : PreKeyFields) (ct_wire : HwBytes) : HwBytes :=
  let F := sha256CompressFunction interpretation
  let ikABytes := pubBytes interpretation (secretBytes r 0)
  let ikBBytes := pubBytes interpretation (secretBytes r 1)
  let ikBskBytes := secretBytes r 1
  let spkBytes := secretBytes r 2
  let ek := ekBytes p
  let dh1 := dhAgreeBytes interpretation spkBytes ikABytes
  let dh2 := dhAgreeBytes interpretation ikBskBytes ek
  let dh3 := dhAgreeBytes interpretation spkBytes ek
  let dh4 := p.preKeyId.map (fun _ => dhAgreeBytes interpretation (secretBytes r 6) ek)
  let ss := (kyberDecapsBytes interpretation r ct_wire).getD []
  let (rk, _, pqr) := pqxdhKdfBytes F (pqxdhIkmBytes dh1 dh2 dh3 dh4 ss)
  let ck0 := createChainKeyBytes interpretation rk p.inner.senderRatchetKey.bytes.toList spkBytes
  let seed := recvSeedBytes F ck0 p.inner.counter.toNat
  let salt := spqrSaltBytes S pqr (preKeySpqrIndex p)
  let macKey := trMacKeyBytes F salt seed
  let wire := p.message.take (p.message.length - 8)
  computeMacBytes F macKey (ecKey ikABytes) (ecKey ikBBytes) wire

def bobSaltSeedBytes (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (p : PreKeyFields) (ct_wire : HwBytes) : HwBytes × HwBytes :=
  let F := sha256CompressFunction interpretation
  let ikABytes := pubBytes interpretation (secretBytes r 0)
  let ikBskBytes := secretBytes r 1
  let spkBytes := secretBytes r 2
  let ek := ekBytes p
  let dh1 := dhAgreeBytes interpretation spkBytes ikABytes
  let dh2 := dhAgreeBytes interpretation ikBskBytes ek
  let dh3 := dhAgreeBytes interpretation spkBytes ek
  let dh4 := p.preKeyId.map (fun _ => dhAgreeBytes interpretation (secretBytes r 6) ek)
  let ss := (kyberDecapsBytes interpretation r ct_wire).getD []
  let (rk, _, pqr) := pqxdhKdfBytes F (pqxdhIkmBytes dh1 dh2 dh3 dh4 ss)
  let ck0 := createChainKeyBytes interpretation rk p.inner.senderRatchetKey.bytes.toList spkBytes
  (spqrSaltBytes S pqr (preKeySpqrIndex p), recvSeedBytes F ck0 p.inner.counter.toNat)

/-- Bob's SPQR salt and message seed for the representation `x` of the pre-key message `p`
over composed types (`bobKeys`, `parseTrSignalMsg`, `bobChain`). -/
def bobSaltSeed (r : ProtocolSetup) (p : PreKeyFields) (x : PreKeyRep) :
    Option (DY.Bytes × DY.Bytes) := do
  let keys ← bobKeys r p x
  let msg ← parseTrSignalMsg x.msg
  let c := bobChain r keys msg
  let (seed, _) ← consumeMessageKey c msg.counter
  let (_, salt) ← DY.Spqr.spqrRecv (DY.Spqr.spqrInit keys.pqr spqrB2A) msg.pqRatchet (preKeySpqrIndex p)
  pure (salt, seed)

/-- Bob's expected MAC term for the representation `x` of the pre-key message `p`
over composed types (`bobKeys`, `parseTrSignalMsg`, `bobChain`). -/
def bobMac (r : ProtocolSetup) (p : PreKeyFields) (x : PreKeyRep) : Option DY.Bytes := do
  let keys ← bobKeys r p x
  let msg ← parseTrSignalMsg x.msg
  let c := bobChain r keys msg
  let (seed, _) ← consumeMessageKey c msg.counter
  let (_, salt) ← DY.Spqr.spqrRecv (DY.Spqr.spqrInit keys.pqr spqrB2A) msg.pqRatchet (preKeySpqrIndex p)
  let mk := trMsgKeys salt seed
  pure (computeMac mk.macKey (serializedIk (setupPublic r 0)) (serializedIk (setupPublic r 2))
    msg.wire)

theorem rep_ek_ct_gamma (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (ms' : List Move) (b : HwBytes) (p : PreKeyFields) (ct_wire : HwBytes)
    (x : PreKeyRep) (hp : parsePreKeyWire b = some p)
    (hct_p : p.kyberCiphertext = some (kyberKey ct_wire))
    (hx : x ∈ preKeyRepresentations interpretation r S g ms' b) :
    gamma interpretation S g x.ek = ekBytes p ∧
    gamma interpretation S g x.ct = ct_wire ∧
    FaithfulInner interpretation S g x.msg p := by
  rcases hx with ⟨_, _, _, ⟨p₁, hp₁, hbk₁, hct₁, _⟩, p₂, hp₂, hFaith⟩
  cases hp.symm.trans hp₁
  cases hp.symm.trans hp₂
  have hek : gamma interpretation S g x.ek = ekBytes p := by
    have hdrop := congrArg (List.drop 1) hbk₁
    rw [List.drop_take] at hdrop
    exact hdrop.symm
  have hct : gamma interpretation S g x.ct = ct_wire := by
    rw [hct_p] at hct₁
    unfold kyberKey at hct₁
    injection hct₁ with hct₁
    injection hct₁ with _ heq
    exact heq.symm
  exact ⟨hek, hct, hFaith⟩

/-- Concretization of `bobSaltSeed` matches the byte-level handshake and initial receiving-chain
key schedule. -/
theorem bobSaltSeed_gamma (interpretation : ExternInterpretation)
    (hEq : ExternCryptoLawsHold interpretation) (r : ProtocolSetup) (hwf : ProtocolSetupWF r)
    (S : OpaqueSymbolSemantics) (g : Ghost)
    (hCompat : GhostAndSemMatchSetup interpretation r S g) (used : Bool) (b : HwBytes) (p : PreKeyFields)
    (hp : parsePreKeyWire b = some p) (hnk : ¬ KyberMismatch interpretation r p)
    (ct_wire : HwBytes) (hct_p : p.kyberCiphertext = some (kyberKey ct_wire))
    (hct_len : ct_wire.length = 1568)
    (hopk : p.preKeyId = none ∨ (r.withOpk = true ∧ used = false ∧ p.preKeyId = some r.opkId))
    (hctr : p.inner.counter.toNat ≤ maxForwardJumps) (hpqne : p.inner.pqRatchet ≠ [])
    (ms' : List Move) (x : PreKeyRep)
    (hx : x ∈ preKeyRepresentations interpretation r S g ms' b)
    (msg : TRSignalMsg) (salt seed : DY.Bytes)
    (hparse0 : parseTrSignalMsg x.msg = some msg)
    (hss : bobSaltSeed r p x = some (salt, seed)) :
    gamma interpretation S g salt = (bobSaltSeedBytes interpretation r S p ct_wire).1 ∧
    gamma interpretation S g seed = (bobSaltSeedBytes interpretation r S p ct_wire).2 ∧
    gamma interpretation S g msg.ciphertext = p.inner.ciphertext := by
  have hNe : r.alice ≠ r.bob := hwf.1
  obtain ⟨hek_gamma, hct_gamma, hFaith⟩ :=
    rep_ek_ct_gamma interpretation r S g ms' b p ct_wire x hp hct_p hx
  rcases hFaith with ⟨msg₁, hparse, _, _, _, hcipher, hrk_gamma, hpq_gamma, hctr_eq, _⟩
  rw [hparse0] at hparse
  cases Option.some.inj hparse
  obtain ⟨ss, hdec, hss_gamma⟩ :=
    gamma_kemSS_of_not_implicitReject interpretation r S g p x ct_wire
      hCompat hNe hnk hct_p hct_len hct_gamma
  obtain ⟨_, hs1, hs2, _, hs6⟩ := gamma_setupSecret interpretation r S g hCompat hNe
  obtain ⟨hp0, _, _⟩ := gamma_setupPublic_0_2_6 interpretation r S g hCompat hNe
  let opk : Option DY.Bytes := p.preKeyId.map (fun _ => setupSecret r 6)
  have hopk_gamma :
      Option.map (gamma interpretation S g) (Option.map (agree x.ek ·) opk) =
        p.preKeyId.map (fun _ => dhAgreeBytes interpretation (secretBytes r 6) (ekBytes p)) := by
    rcases hopk with hnone | ⟨hw, _, hsome⟩
    · simp [opk, hnone]
    · simp [opk, hsome, gamma_agree interpretation hEq, hs6 hw, hek_gamma, dhAgreeBytes]
  set ikA := setupPublic r 0
  set ikBsk := setupSecret r 1
  set spk := setupSecret r 2
  set keys := pqxdhKdf (pqxdhIkm (agree ikA spk) (agree x.ek ikBsk) (agree x.ek spk)
    (opk.map (agree x.ek ·)) ss)
  have hbobKeys : bobKeys r p x = some keys := by
    unfold bobKeys
    rcases hopk with hnone | ⟨hw, _, hsome⟩
    · have hopk_none : (none : Option DY.Bytes) = opk := by simp [opk, hnone]
      simp only [hnone, Bind.bind, Option.bind, Pure.pure]
      rw [hopk_none, hdec]
    · have hid : (r.withOpk && r.opkId == r.opkId) = true := by simp [hw]
      have hopk_some : (some (setupSecret r 6) : Option DY.Bytes) = opk := by simp [opk, hsome]
      simp only [hsome, hid, ↓reduceIte, Bind.bind, Option.bind, Pure.pure]
      rw [hopk_some, hdec]
  have hctr_le : msg.counter.toNat ≤ maxForwardJumps := by
    rw [hctr_eq]; exact hctr
  obtain ⟨c', hcmk⟩ :=
    consumeMessageKey_index_zero msg.ratchetKey (createChain keys.rk msg.ratchetKey spk).2
      msg.counter hctr_le 2
  have hpq_ne : gamma interpretation S g msg.pqRatchet ≠ [] := by
    rw [hpq_gamma]; exact hpqne
  obtain ⟨st', salt₀, hspqr, hsalt_gamma⟩ :=
    spqrRecv_init_b2a_of_gamma_ne_nil interpretation S g keys.pqr msg.pqRatchet (preKeySpqrIndex p) hpq_ne
  set seed₀ := (kdfCk (chainKeyAt (createChain keys.rk msg.ratchetKey spk).2 msg.counter.toNat)).2
  have hbss : bobSaltSeed r p x = some (salt₀, seed₀) := by
    unfold bobSaltSeed
    simp only [hbobKeys, hparse0, Bind.bind, Option.bind, Pure.pure, bobChain]
    rw [hcmk]
    dsimp only
    rw [hspqr]
  rw [hbss] at hss
  obtain ⟨hsalt_eq, hseed_eq⟩ := Prod.mk.inj (Option.some.inj hss)
  rw [← hsalt_eq, ← hseed_eq]
  have hikm_gamma :
      gamma interpretation S g
        (pqxdhIkm (agree ikA spk) (agree x.ek ikBsk) (agree x.ek spk) (opk.map (agree x.ek ·)) ss) =
      pqxdhIkmBytes
        (dhAgreeBytes interpretation (secretBytes r 2) (pubBytes interpretation (secretBytes r 0)))
        (dhAgreeBytes interpretation (secretBytes r 1) (ekBytes p))
        (dhAgreeBytes interpretation (secretBytes r 2) (ekBytes p))
        (p.preKeyId.map (fun _ => dhAgreeBytes interpretation (secretBytes r 6) (ekBytes p)))
        ((kyberDecapsBytes interpretation r ct_wire).getD []) := by
    rw [gamma_pqxdhIkm, hopk_gamma,
      gamma_agree interpretation hEq _ _ ikA spk,
      gamma_agree interpretation hEq _ _ x.ek ikBsk,
      gamma_agree interpretation hEq _ _ x.ek spk,
      hp0, hs1, hs2, hek_gamma, hss_gamma]
    rfl
  have hkdf := gamma_pqxdhKdf interpretation S g
    (pqxdhIkm (agree ikA spk) (agree x.ek ikBsk) (agree x.ek spk) (opk.map (agree x.ek ·)) ss)
  dsimp only at hkdf
  rw [hikm_gamma] at hkdf
  obtain ⟨hrk_kdf, _, hpqr_kdf⟩ := hkdf
  have hck0_gamma :
      gamma interpretation S g (createChain keys.rk msg.ratchetKey spk).2 =
      createChainKeyBytes interpretation
        (pqxdhKdfBytes (sha256CompressFunction interpretation)
          (pqxdhIkmBytes
            (dhAgreeBytes interpretation (secretBytes r 2) (pubBytes interpretation (secretBytes r 0)))
            (dhAgreeBytes interpretation (secretBytes r 1) (ekBytes p))
            (dhAgreeBytes interpretation (secretBytes r 2) (ekBytes p))
            (p.preKeyId.map (fun _ => dhAgreeBytes interpretation (secretBytes r 6) (ekBytes p)))
            ((kyberDecapsBytes interpretation r ct_wire).getD []))).1
        p.inner.senderRatchetKey.bytes.toList
        (secretBytes r 2) := by
    rw [gamma_createChain_snd interpretation hEq, hrk_kdf, hrk_gamma, hs2]
  have hseed_gamma :
      gamma interpretation S g seed₀ =
      recvSeedBytes (sha256CompressFunction interpretation)
        (gamma interpretation S g (createChain keys.rk msg.ratchetKey spk).2)
        p.inner.counter.toNat := by
    dsimp only [seed₀, recvSeedBytes]
    rw [gamma_kdfCk_snd, gamma_chainKeyAt, hctr_eq]
  refine ⟨?_, ?_, hcipher⟩
  · rw [hsalt_gamma, hpqr_kdf]
    rfl
  · rw [hseed_gamma, hck0_gamma]
    rfl

end Symbolic.Swarm.CREF.TR
