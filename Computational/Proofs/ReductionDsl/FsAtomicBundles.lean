/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.FsAtomicOps
public import Computational.Proofs.ReductionDsl.PubRed
public import Computational.Proofs.ReductionDsl.FSAEAD.HybridCosted
public import Computational.Proofs.ReductionDsl.FSAEAD.SaltWire
public import Computational.Proofs.SessionCostedBase
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalBound

/-!
# Compiled atomic `FsCostedReds` bundles

Pure macro bundles, compiled atomic `CostedReduction` and `TwoStageCostedReduction` programs over
`ReductionDsl.atomicFsOps`, and the guarded `fsCostedRedsInst` instance.
-/

@[expose] public section

set_option autoImplicit false

open ReductionDsl (Sig Ty Var Env Expr Comp Samplers Ops Iface GameCodec CostedReduction
  TwoStageCostedReduction UniformSamplerTag OpsSizeHonest SampSizeHonest bits unifSamplers
  unifSamplers0 isGameQuery AtomicSort atomicSig AtomicBaseUnif atomicBaseSamplers atomicFsOps
  B U8 U32 U64 BV128 BV256 PK IdKey PlainT PtT
  fitBytesN salt32V salt32OfV wireSignalHdrT wireSignalHdrV wireSignalHdrOfV
  lpubT lpubV lpubOfV wireSaltCtT wireSaltCtV wireSaltCtOfV
  lctT lctV lctOfV fig8HdrT fig8PubAdT fig8PubAdV fig8PubAdOfV
  slotAdT slotAdV slotAdOfV fsSendStT fsSendStV fsSendStOfV
  fsRecvStT fsRecvStV fsRecvStOfV fsRrT fsRrEnc fsRrDec derivedMsgKeysT
  OTCCATag FSAEADTag coinOnlyBaseIface saltPrfTargetIface wireOtccaTargetIface
  slotOtccaTargetIface fsaeadPubTargetIface fsaeadPubCodec fsaeadRatchetCodec)

namespace Computational.Proofs.ReductionDsl.FsAtomicBundles

open OracleSpec OracleComp
open CryptoGames (Party AEADScheme MACScheme WireAEAD)
open CryptoGames.HKDF (DerivedMessageKeys)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalAead (SerializedIdentityKeys)
open CryptoGames.Ratchet (padOrTruncatePlain)
open CryptoGames.Ratchet.LibsignalInst (Salt32 LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart
  lIds lHeader lWire lAeadK lPubOf lChainPRG lAeadR lIdeal lSaltRed lWireRed slotSaltRed slotWireRed)
open CryptoGames.SM.Construction (Header)
open CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey SignalHeader
  SignalMessageProtoCodec maxForwardJumps)
open CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState ReceiveResult)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSession (LCt FsAdv fsSlotCount ratchetCostBudget
  fsRatchetCostBudget GRedBounded GTwoStageBounded FsCostedReds fsCostedBounds)
open Computational.Proofs.ReductionDsl.MacroLift (mapTy toVal dummyTwoStageRed guardTwoStageRed)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (PureMacroBundle compilePureRed
  compilePureTwoStageRed)
open Computational.Proofs.ReductionDsl.FsAtomicOps (clampedProtoSignalCodec
  lPubOfExpr chainGenExpr lIdsExpr lHeaderExpr eqWireSignalHdrExpr fitPlainExpr eqPlainExpr
  eqSaltExpr saltOfSlotAdExpr eqFig8PubAdExpr eqSlotAdExpr eqWireSaltCtExpr
  aeadKEncExpr aeadKDecExpr aeadREncExpr aeadRDecExpr sampleMsgKeyComp sampleIdealComp)

section BaseTypes

variable {Pt : Type} {ℓ : ℕ}

@[reducible] def pubBaseTy : CryptoGames.FSAEAD.Costed.FSort → Ty (atomicSig ℓ Pt)
  | .ss => fsSendStT
  | .rs => fsRecvStT
  | .ad => fig8HdrT
  | .pub => lpubT
  | .msg => PlainT
  | .ct => lctT

def pubToDen : (b : CryptoGames.FSAEAD.Costed.FSort) →
    (CryptoGames.FSAEAD.Costed.fsSig (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) LibsignalMsgPublicPart (Plain ℓ) (ℕ × LCt)).den b →
    (pubBaseTy (Pt := Pt) (ℓ := ℓ) b).denote
  | .ss => fsSendStV
  | .rs => fsRecvStV
  | .ad => id
  | .pub => lpubV
  | .msg => id
  | .ct => lctV

@[reducible] def hybBaseTy : CryptoGames.FSAEAD.Costed.FSort → Ty (atomicSig ℓ Pt)
  | .ss => BV256
  | .rs => BV256
  | .ad => fig8PubAdT
  | .pub => .unit
  | .msg => PlainT
  | .ct => wireSaltCtT

def hybToDen : (b : CryptoGames.FSAEAD.Costed.FSort) →
    (CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt).den b →
    (hybBaseTy (Pt := Pt) (ℓ := ℓ) b).denote
  | .ss => id
  | .rs => id
  | .ad => fig8PubAdV
  | .pub => id
  | .msg => id
  | .ct => wireSaltCtV

@[reducible] def swBaseTy : CryptoGames.AEAD.Costed.SaltWireSort → Ty (atomicSig ℓ Pt)
  | .seed => BV256
  | .msgKey => derivedMsgKeysT
  | .salt => BV256
  | .ad => fig8PubAdT
  | .plain => PlainT
  | .idKeys => B 66
  | .sigHdr => wireSignalHdrT
  | .rawBytes => B 32
  | .macTag => U64

def swToDen : (b : CryptoGames.AEAD.Costed.SaltWireSort) →
    (CryptoGames.AEAD.Costed.saltWireSig Pt ℓ).den b →
    (swBaseTy (Pt := Pt) (ℓ := ℓ) b).denote
  | .seed => id
  | .msgKey => id
  | .salt => salt32V
  | .ad => fig8PubAdV
  | .plain => id
  | .idKeys => fun v => v.toList
  | .sigHdr => wireSignalHdrV
  | .rawBytes => id
  | .macTag => id

end BaseTypes

section BundlesPart1

variable {Pt : Type} [DecidableEq Pt]
  (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicFsOps ℓ Pt C encT

omit [DecidableEq Pt] in
def pubMacroBundle :
    PureMacroBundle
      (CryptoGames.FSAEAD.Costed.fsOps (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        (Header Pt) LibsignalMsgPublicPart (Plain ℓ) (ℕ × LCt)
        (fun c : ℕ × LCt => lPubOf protoSignalCodec c.2) 1)
      AOps
      (CryptoGames.FSAEAD.Costed.fsaeadIface
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (AD := Header Pt) (Pub := LibsignalMsgPublicPart) (M := Plain ℓ) (C := ℕ × LCt)
        (.prod (.base .ad) (.base .pub)))
      (fsaeadPubTargetIface ℓ Pt) where
  baseTy := pubBaseTy
  toDen := pubToDen
  opMacro := fun _ => lPubOfExpr ℓ Pt C encT (.snd (.var .zero))
  sampMacro := fun s => nomatch s
  queryMacro
    | .tr => Comp.query (I := fsaeadPubTargetIface ℓ Pt) FSAEADTag.tr (.var .zero)
    | .ch => Comp.query (I := fsaeadPubTargetIface ℓ Pt) FSAEADTag.ch (.var .zero)
    | .cs => Comp.query (I := fsaeadPubTargetIface ℓ Pt) FSAEADTag.cs .unit
    | .cr => Comp.query (I := fsaeadPubTargetIface ℓ Pt) FSAEADTag.cr .unit
    | .dl => Comp.query (I := fsaeadPubTargetIface ℓ Pt) FSAEADTag.dl (.var .zero)
    | .ij => Comp.query (I := fsaeadPubTargetIface ℓ Pt) FSAEADTag.ij (.var .zero)

def hybOpMacro :
    (o : (Ops.sum
      (CryptoGames.PRG.Costed.prgOps
        (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
          (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
        (.prod .nat (.base .ss)) (.prod (.base .ss) (.base .rs))
        (fun pw => (lChainPRG C.F pw.1).gen pw.2) 1)
      (CryptoGames.OTCCA.Costed.otccaOps
        (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
          (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
        (.base .rs) (.prod .nat (.base .ad)) (.base .ad) (.base .msg) (.base .ct)
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf) 1 .unit (fun _ => ()))).Op) →
    Expr AOps
      [mapTy (hybBaseTy (Pt := Pt) (ℓ := ℓ))
        ((Ops.sum
          (CryptoGames.PRG.Costed.prgOps
            (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
              (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
            (.prod .nat (.base .ss)) (.prod (.base .ss) (.base .rs))
            (fun pw => (lChainPRG C.F pw.1).gen pw.2) 1)
          (CryptoGames.OTCCA.Costed.otccaOps
            (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
              (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
            (.base .rs) (.prod .nat (.base .ad)) (.base .ad) (.base .msg) (.base .ct)
            (lAeadR C clampedProtoSignalCodec ℓ encT idOf) 1 .unit (fun _ => ()))).dom o)]
      (mapTy (hybBaseTy (Pt := Pt) (ℓ := ℓ))
        ((Ops.sum
          (CryptoGames.PRG.Costed.prgOps
            (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
              (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
            (.prod .nat (.base .ss)) (.prod (.base .ss) (.base .rs))
            (fun pw => (lChainPRG C.F pw.1).gen pw.2) 1)
          (CryptoGames.OTCCA.Costed.otccaOps
            (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
              (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
            (.base .rs) (.prod .nat (.base .ad)) (.base .ad) (.base .msg) (.base .ct)
            (lAeadR C clampedProtoSignalCodec ℓ encT idOf) 1 .unit (fun _ => ()))).cod o))
  | .inl () => chainGenExpr ℓ Pt C encT (.snd (.var .zero))
  | .inr .enc => aeadREncExpr ℓ Pt C encT idOf
  | .inr .dec => aeadRDecExpr ℓ Pt C encT idOf
  | .inr .saltOf => .unit
  | .inr .eqAD => eqFig8PubAdExpr ℓ Pt C encT (.fst (.var .zero)) (.snd (.var .zero))
  | .inr .eqM => eqPlainExpr ℓ Pt C encT (.fst (.var .zero)) (.snd (.var .zero))
  | .inr .eqC => eqWireSaltCtExpr ℓ Pt C encT (.fst (.var .zero)) (.snd (.var .zero))
  | .inr .eqSalt => .bool true

def prgZeroMacroBundle :
    PureMacroBundle
      (Ops.sum
        (CryptoGames.PRG.Costed.prgOps
          (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
            (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
          (.prod .nat (.base .ss)) (.prod (.base .ss) (.base .rs))
          (fun pw => (lChainPRG C.F pw.1).gen pw.2) 1)
        (CryptoGames.OTCCA.Costed.otccaOps
          (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
            (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
          (.base .rs) (.prod .nat (.base .ad)) (.base .ad) (.base .msg) (.base .ct)
          (lAeadR C clampedProtoSignalCodec ℓ encT idOf) 1 .unit (fun _ => ())))
      AOps
      (Iface.withSamp
        (Iface.withSamp
          (CryptoGames.PRG.Costed.prgIface
            (CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
              (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt))
          (CryptoGames.OTCCA.Costed.idealSamplers (.prod .nat (.base .ad)) (.base .ct)
            (lIdeal C clampedProtoSignalCodec ℓ encT) 1))
        (unifSamplers CryptoGames.FSAEAD.Costed.fsStateSampleSort (fun _ => 1)))
      (coinOnlyBaseIface ℓ Pt) where
  baseTy := hybBaseTy
  toDen := hybToDen
  opMacro := hybOpMacro C ℓ encT idOf
  sampMacro
    | .inl (.inl e) => nomatch e
    | .inl (.inr ()) =>
      sampleIdealComp ℓ Pt C encT
        (fun b => Comp.sample (I := coinOnlyBaseIface ℓ Pt) (UniformSamplerTag.base b) .unit)
    | .inr .bool => Comp.sample (I := coinOnlyBaseIface ℓ Pt) UniformSamplerTag.bool .unit
    | .inr (.index N) => Comp.sample (I := coinOnlyBaseIface ℓ Pt) (UniformSamplerTag.index N) .unit
    | .inr (.base true) =>
      Comp.sample (I := coinOnlyBaseIface ℓ Pt) (UniformSamplerTag.base .bv256) .unit
    | .inr (.base false) =>
      Comp.sample (I := coinOnlyBaseIface ℓ Pt) (UniformSamplerTag.base .bv256) .unit
  queryMacro := fun g => nomatch g

def multiMacroBundle :
    PureMacroBundle
      (Ops.sum
        (CryptoGames.PRG.Costed.prgOps
          (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
            (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
          (.prod .nat (.base .ss)) (.prod (.base .ss) (.base .rs))
          (fun pw => (lChainPRG C.F pw.1).gen pw.2) 1)
        (CryptoGames.OTCCA.Costed.otccaOps
          (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
            (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
          (.base .rs) (.prod .nat (.base .ad)) (.base .ad) (.base .msg) (.base .ct)
          (lAeadR C clampedProtoSignalCodec ℓ encT idOf) 1 .unit (fun _ => ())))
      AOps
      (Iface.withSamp
        (CryptoGames.OTCCA.Costed.otccaIface
          (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
            (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
          (.prod .nat (.base .ad)) (.base .msg) (.base .ct)
          (lIdeal C clampedProtoSignalCodec ℓ encT) 1)
        (unifSamplers CryptoGames.FSAEAD.Costed.fsStateSampleSort (fun _ => 1)))
      (slotOtccaTargetIface ℓ Pt) where
  baseTy := hybBaseTy
  toDen := hybToDen
  opMacro := hybOpMacro C ℓ encT idOf
  sampMacro
    | .inl () =>
      sampleIdealComp ℓ Pt C encT
        (fun b => Comp.sample (I := slotOtccaTargetIface ℓ Pt) (UniformSamplerTag.base b) .unit)
    | .inr .bool => Comp.sample (I := slotOtccaTargetIface ℓ Pt) UniformSamplerTag.bool .unit
    | .inr (.index N) =>
      Comp.sample (I := slotOtccaTargetIface ℓ Pt) (UniformSamplerTag.index N) .unit
    | .inr (.base true) =>
      Comp.sample (I := slotOtccaTargetIface ℓ Pt) (UniformSamplerTag.base .bv256) .unit
    | .inr (.base false) =>
      Comp.sample (I := slotOtccaTargetIface ℓ Pt) (UniformSamplerTag.base .bv256) .unit
  queryMacro
    | .enc => Comp.query (I := slotOtccaTargetIface ℓ Pt) OTCCATag.enc (.var .zero)
    | .dec => Comp.query (I := slotOtccaTargetIface ℓ Pt) OTCCATag.dec (.var .zero)

end BundlesPart1

section BundlesPart2

variable {Pt : Type} [DecidableEq Pt]
  (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
  (encT : Pt → PublicKey) (idOf : Party → IdentityKey)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicFsOps ℓ Pt C encT
local notation "SWOps" => CryptoGames.AEAD.Costed.saltWireOps C clampedProtoSignalCodec ℓ encT idOf 1

def swOpMacro :
    (o : (SWOps).Op) →
    Expr AOps
      [mapTy (swBaseTy (Pt := Pt) (ℓ := ℓ)) ((SWOps).dom o)]
      (mapTy (swBaseTy (Pt := Pt) (ℓ := ℓ)) ((SWOps).cod o))
  | .inl .enc => aeadKEncExpr ℓ Pt C encT idOf
  | .inl .dec => aeadKDecExpr ℓ Pt C encT idOf
  | .inl .saltOf => saltOfSlotAdExpr ℓ Pt C encT (.var .zero)
  | .inl .eqAD => eqSlotAdExpr ℓ Pt C encT (.fst (.var .zero)) (.snd (.var .zero))
  | .inl .eqM => eqPlainExpr ℓ Pt C encT (.fst (.var .zero)) (.snd (.var .zero))
  | .inl .eqC => eqWireSaltCtExpr ℓ Pt C encT (.fst (.var .zero)) (.snd (.var .zero))
  | .inl .eqSalt => eqSaltExpr ℓ Pt C encT (.fst (.var .zero)) (.snd (.var .zero))
  | .inr (.inl .enc) => aeadREncExpr ℓ Pt C encT idOf
  | .inr (.inl .dec) => aeadRDecExpr ℓ Pt C encT idOf
  | .inr (.inl .saltOf) => saltOfSlotAdExpr ℓ Pt C encT (.var .zero)
  | .inr (.inl .eqAD) => eqSlotAdExpr ℓ Pt C encT (.fst (.var .zero)) (.snd (.var .zero))
  | .inr (.inl .eqM) => eqPlainExpr ℓ Pt C encT (.fst (.var .zero)) (.snd (.var .zero))
  | .inr (.inl .eqC) => eqWireSaltCtExpr ℓ Pt C encT (.fst (.var .zero)) (.snd (.var .zero))
  | .inr (.inl .eqSalt) => eqSaltExpr ℓ Pt C encT (.fst (.var .zero)) (.snd (.var .zero))
  | .inr (.inr .idsOf) => lIdsExpr ℓ Pt C encT idOf (.fst (.fst (.snd (.var .zero))))
  | .inr (.inr .hdrOf) => lHeaderExpr ℓ Pt C encT (.var .zero)
  | .inr (.inr .eqHdr) => eqWireSignalHdrExpr ℓ Pt C encT (.fst (.var .zero)) (.snd (.var .zero))
  | .inr (.inr .fitPlainOp) => fitPlainExpr ℓ Pt C encT (.var .zero)

def slotSwMacroBundle :
    PureMacroBundle SWOps AOps
      (CryptoGames.AEAD.Costed.slotOtccaIface C clampedProtoSignalCodec ℓ encT 1)
      (slotOtccaTargetIface ℓ Pt) where
  baseTy := swBaseTy
  toDen := swToDen
  opMacro := swOpMacro C ℓ encT idOf
  sampMacro
    | .inl () =>
      sampleIdealComp ℓ Pt C encT
        (fun b => Comp.sample (I := slotOtccaTargetIface ℓ Pt) (UniformSamplerTag.base b) .unit)
    | .inr .bool => Comp.sample (I := slotOtccaTargetIface ℓ Pt) UniformSamplerTag.bool .unit
    | .inr (.index N) =>
      Comp.sample (I := slotOtccaTargetIface ℓ Pt) (UniformSamplerTag.index N) .unit
    | .inr (.base true) =>
      Comp.sample (I := slotOtccaTargetIface ℓ Pt) (UniformSamplerTag.base .bv256) .unit
    | .inr (.base false) =>
      sampleMsgKeyComp ℓ Pt C encT
        (fun b => Comp.sample (I := slotOtccaTargetIface ℓ Pt) (UniformSamplerTag.base b) .unit)
  queryMacro
    | .enc => Comp.query (I := slotOtccaTargetIface ℓ Pt) OTCCATag.enc (.var .zero)
    | .dec => Comp.query (I := slotOtccaTargetIface ℓ Pt) OTCCATag.dec (.var .zero)

def lSaltMacroBundle :
    PureMacroBundle SWOps AOps
      (CryptoGames.AEAD.Costed.saltRedIface C clampedProtoSignalCodec ℓ encT 1)
      (saltPrfTargetIface ℓ Pt) where
  baseTy := swBaseTy
  toDen := swToDen
  opMacro := swOpMacro C ℓ encT idOf
  sampMacro
    | .inl (.inl e) => nomatch e
    | .inl (.inr ()) =>
      sampleIdealComp ℓ Pt C encT
        (fun b => Comp.sample (I := saltPrfTargetIface ℓ Pt) (UniformSamplerTag.base b) .unit)
    | .inr .bool => Comp.sample (I := saltPrfTargetIface ℓ Pt) UniformSamplerTag.bool .unit
    | .inr (.index N) =>
      Comp.sample (I := saltPrfTargetIface ℓ Pt) (UniformSamplerTag.index N) .unit
    | .inr (.base e) => nomatch e
  queryMacro := fun _ => Comp.query (I := saltPrfTargetIface ℓ Pt) () (.var .zero)

def lWireMacroBundle :
    PureMacroBundle SWOps AOps
      (CryptoGames.AEAD.Costed.wireRedIface Pt ℓ)
      (wireOtccaTargetIface ℓ Pt) where
  baseTy := swBaseTy
  toDen := swToDen
  opMacro := swOpMacro C ℓ encT idOf
  sampMacro
    | .inl e => nomatch e
    | .inr .bool => Comp.sample (I := wireOtccaTargetIface ℓ Pt) UniformSamplerTag.bool .unit
    | .inr (.index N) =>
      Comp.sample (I := wireOtccaTargetIface ℓ Pt) (UniformSamplerTag.index N) .unit
    | .inr (.base e) => nomatch e
  queryMacro
    | .enc => Comp.query (I := wireOtccaTargetIface ℓ Pt) OTCCATag.enc (.var .zero)
    | .dec => Comp.query (I := wireOtccaTargetIface ℓ Pt) OTCCATag.dec (.var .zero)

omit [DecidableEq Pt] in
def fsPubRedAtomic :=
  compilePureRed (fsaeadPubCodec ℓ Pt) (pubMacroBundle (Pt := Pt) C ℓ encT)
    (CryptoGames.FSAEAD.Costed.pubRedProg
      (SS := RatchetSenderState (BitVec 256))
      (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
      (AD := Header Pt) (M := Plain ℓ)
      (fun c : ℕ × LCt => lPubOf protoSignalCodec c.2) 1)

def fsPrgRedZeroAtomic (qR j : ℕ) :=
  compilePureTwoStageRed (fsaeadRatchetCodec ℓ Pt) (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf)
    (CryptoGames.FSAEAD.Thm5.Costed.prgRedZeroProg
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
      (lIdeal C clampedProtoSignalCodec ℓ encT) 1 qR maxForwardJumps j)

def fsMultiRedAtomic (qR : ℕ) (la : Bool) :=
  compilePureTwoStageRed (fsaeadRatchetCodec ℓ Pt) (multiMacroBundle (Pt := Pt) C ℓ encT idOf)
    (CryptoGames.FSAEAD.Thm5.Costed.multiRedProg
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
      (lIdeal C clampedProtoSignalCodec ℓ encT) 1
      qR maxForwardJumps (if la then qR + (maxForwardJumps + 1) else qR) la)

def fsPrgRedAuthAtomic (qR j : ℕ) :=
  compilePureTwoStageRed (fsaeadRatchetCodec ℓ Pt) (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf)
    (CryptoGames.FSAEAD.Thm5.Costed.prgRedAuthProg
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
      (lIdeal C clampedProtoSignalCodec ℓ encT) 1 qR maxForwardJumps j)

def fsMultiRedAuthAtomic (qR : ℕ) (la : Bool) :=
  compilePureTwoStageRed (fsaeadRatchetCodec ℓ Pt) (multiMacroBundle (Pt := Pt) C ℓ encT idOf)
    (CryptoGames.FSAEAD.Thm5.Costed.multiRedAuthProg
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
      (lIdeal C clampedProtoSignalCodec ℓ encT) 1
      qR maxForwardJumps (if la then qR + (maxForwardJumps + 1) else qR) la)

def fsSlotSaltRedAtomic (qR j : ℕ) :=
  compilePureRed (ReductionDsl.slotOtccaCodec ℓ Pt) (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
    (CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltRedProg
      C clampedProtoSignalCodec ℓ encT idOf 1 1
      (if CryptoGames.FSAEAD.Thm5.isLookaheadHop j then qR + (maxForwardJumps + 1) else qR)
      (j / 2) qR)

def fsLSaltRedAtomic :=
  compilePureRed (ReductionDsl.slotOtccaCodec ℓ Pt) (lSaltMacroBundle (Pt := Pt) C ℓ encT idOf)
    (CryptoGames.Ratchet.LibsignalInst.Costed.lSaltRedProg
      C clampedProtoSignalCodec ℓ encT idOf 1 1)

def fsSlotWireRedAtomic (qR j : ℕ) :=
  compilePureRed (ReductionDsl.slotOtccaCodec ℓ Pt) (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
    (CryptoGames.Ratchet.LibsignalInst.Costed.slotWireRedProg
      C clampedProtoSignalCodec ℓ encT idOf 1 1 (j / 2) qR)

def fsLWireRedAtomic (qR : ℕ) :=
  compilePureRed (ReductionDsl.slotOtccaCodec ℓ Pt) (lWireMacroBundle (Pt := Pt) C ℓ encT idOf)
    (CryptoGames.Ratchet.LibsignalInst.Costed.lWireRedProg
      C clampedProtoSignalCodec ℓ encT idOf 1 0 qR)

omit [DecidableEq Pt] in
def fsCostedRedsBoundedWitness : FsCostedReds C codec ℓ encT idOf where
  pubRed := ⟨.unit, .ret (.pair .unit .unit), .ret (.pair (.inl .none) .unit), .ret (.bool false)⟩
  prgRedZero _ := dummyTwoStageRed .unit (.inl .none) .unit (.bool false)
  multiRed _ := dummyTwoStageRed .unit (.inl .none) .unit (.bool false)
  slotSaltRed _ := ⟨.unit, .ret (.pair .unit .unit), .ret (.pair (.inl .none) .unit), .ret (.bool false)⟩
  lSaltRed := ⟨.unit, .ret (.pair .unit .unit), .ret (.pair (.inl .none) .unit), .ret (.bool false)⟩
  slotWireRed _ := ⟨.unit, .ret (.pair .unit .unit), .ret (.pair (.inl .none) .unit), .ret (.bool false)⟩
  lWireRed := ⟨.unit, .ret (.pair .unit .unit), .ret (.pair (.inl .none) .unit), .ret (.bool false)⟩

/-- Compiled atomic `FsCostedReds` bundle guarded by `ℓ < 10 ^ 6` and hop bounds for unconditional `fsCostedBounds`. -/
def fsCostedRedsInst (qR : ℕ) : FsCostedReds C codec ℓ encT idOf :=
  let fb := fsCostedRedsBoundedWitness C codec ℓ encT idOf
  { pubRed := if ℓ < 10 ^ 6 then fsPubRedAtomic C ℓ encT else fb.pubRed
    prgRedZero := fun j =>
      guardTwoStageRed (ℓ < 10 ^ 6 ∧ j ≤ 2 * (qR + maxForwardJumps + 1))
        (fsPrgRedZeroAtomic C ℓ encT idOf qR j) .unit (.inl .none) .unit (.bool false)
    multiRed := fun la =>
      guardTwoStageRed (ℓ < 10 ^ 6)
        (fsMultiRedAtomic C ℓ encT idOf qR la) .unit (.inl .none) .unit (.bool false)
    slotSaltRed := fun j =>
      if ℓ < 10 ^ 6 ∧ j ≤ 2 * (qR + maxForwardJumps + 1) then
        fsSlotSaltRedAtomic C ℓ encT idOf qR j
      else fb.slotSaltRed j
    lSaltRed := if ℓ < 10 ^ 6 then fsLSaltRedAtomic C ℓ encT idOf else fb.lSaltRed
    slotWireRed := fun j =>
      if ℓ < 10 ^ 6 ∧ j ≤ 2 * (qR + maxForwardJumps + 1) then
        fsSlotWireRedAtomic C ℓ encT idOf qR j
      else fb.slotWireRed j
    lWireRed := if ℓ < 10 ^ 6 then fsLWireRedAtomic C ℓ encT idOf qR else fb.lWireRed }

end BundlesPart2

end Computational.Proofs.ReductionDsl.FsAtomicBundles
