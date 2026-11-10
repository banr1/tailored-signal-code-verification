/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean
public import Computational.Specifications.Pqxdh.Security.HeadlineDelta
public import Computational.Specifications.Session.StatementSession
public import Computational.Specifications.Composition.StatementModel
public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Proofs.ReductionDsl.AtomicTablesHonest

/-!
# Unified Atomic Signature and Operator Guards for Headline Statements

Verifies that every `ReductionDsl` reduction reachable from the computational headline statements
uses the unified signature `atomicSig` (and its specialization `pqAtomicSig`), the pure operator set
`AtomicPureOp`, the cryptographic operator tables in `AtomicOps.lean`, and the game codecs in
`TargetCodecs.lean`, with no dependency on retired `*CostedTables` modules. The first namespace
checks definitional decompositions, `OpsSizeHonest` instances, and reduction-bundle types by kernel
elaboration; the second runs a `#eval` environment audit over the specification import graph and
headline constant closures alongside negative self-tests.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Guards.HeadlineAtomicOps

open ReductionDsl (Sig Ty Ops GameCodec CostedReduction TwoStageCostedReduction OpsSizeHonest
  atomicSig pqAtomicSig AtomicPureOp
  AtomicCurveCheckOp AtomicPtEncOp AtomicPtDecOp AtomicSymOp
  AtomicGroupOp AtomicSpqrKemOp AtomicPqxdhOp
  atomicPureOps pqAtomicOps atomicCurveCheckOps atomicPtEncOps atomicPtDecOps
  atomicSymOps atomicGroupOps atomicSpqrKemOps atomicPqxdhOps
  atomicAdapterOps atomicFsOps atomicFig8Ops atomicSessionOps atomicE2EOps
  atomicBaseSamplers pqAtomicSamplers
  atomicPureOps_sizeHonest pqAtomicOps_sizeHonest
  atomicAdapterOps_sizeHonest atomicFsOps_sizeHonest atomicFig8Ops_sizeHonest
  atomicSessionOps_sizeHonest atomicE2EOps_sizeHonest)
open CryptoGames CryptoGames.CKA CryptoGames.SM.Construction CryptoGames.LibsignalSession
  CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalSession (LCt FsCostedReds Fig8CostedReds)
open CryptoVerification.E2E (Bytes SpkLeakRedProg SpkLeakRedUProg SpkSwapPrgHybridProg
  SpkSwapPrfHybridProg SpkCostedReds SessionCostedReductions
  CompositionCostedReductions CliToModelAdapterProg
  bhGameSpec bhTargetGameSpec e2eBhAdapterIface e2eBhAdapterCodec e2eTargetGameCodec)

theorem pqAtomicSig_eq : pqAtomicSig = atomicSig 0 Empty := rfl

theorem pqAtomicOps_eq : pqAtomicOps = atomicPureOps 0 Empty := rfl

theorem pqAtomicSamplers_eq : pqAtomicSamplers = atomicBaseSamplers 0 Empty := rfl

theorem atomicPureOps_op_eq (ℓ : ℕ) (Pt : Type) :
    (atomicPureOps ℓ Pt).Op = AtomicPureOp := rfl

theorem atomicCurveCheckOps_op_eq (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (atomicCurveCheckOps ℓ decT encT).Op = AtomicCurveCheckOp := rfl

theorem atomicPtEncOps_op_eq (ℓ : ℕ) {Pt : Type} (encT : Pt → PublicKey) :
    (atomicPtEncOps ℓ encT).Op = AtomicPtEncOp := rfl

theorem atomicPtDecOps_op_eq (ℓ : ℕ) {Pt : Type} (decT : PublicKey → Option Pt) :
    (atomicPtDecOps ℓ decT).Op = AtomicPtDecOp := rfl

theorem atomicSymOps_op_eq (ℓ : ℕ) (Pt : Type) (C : Crypto) :
    (atomicSymOps ℓ Pt C).Op = AtomicSymOp := rfl

theorem atomicGroupOps_op_eq (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (lam : Pt) :
    (atomicGroupOps ℓ Pt C Dh encPt lam).Op = AtomicGroupOp := rfl

theorem atomicSpqrKemOps_op_eq (ℓ : ℕ) (Pt : Type) (C : Crypto) (K : MlKem) :
    (atomicSpqrKemOps ℓ Pt C K).Op = AtomicSpqrKemOp := rfl

theorem atomicPqxdhOps_op_eq (ℓ : ℕ) (Pt : Type) (P : SignalPqxdh.Primitives) :
    (atomicPqxdhOps ℓ Pt P).Op = AtomicPqxdhOp := rfl

theorem atomicAdapterOps_eq (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    atomicAdapterOps ℓ decT encT =
      Ops.sum (atomicPureOps ℓ Pt) (atomicCurveCheckOps ℓ decT encT) := rfl

theorem atomicFsOps_eq (ℓ : ℕ) (Pt : Type) (C : Crypto) (encT : Pt → PublicKey) :
    atomicFsOps ℓ Pt C encT =
      Ops.sum (atomicPureOps ℓ Pt) (Ops.sum (atomicPtEncOps ℓ encT) (atomicSymOps ℓ Pt C)) := rfl

theorem atomicFig8Ops_eq (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (lam : Pt) :
    atomicFig8Ops ℓ Pt C Dh encPt encT lam =
      Ops.sum (atomicFsOps ℓ Pt C encT) (atomicGroupOps ℓ Pt C Dh encPt lam) := rfl

theorem atomicSessionOps_eq (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    atomicSessionOps ℓ Pt C K Dh encPt encT decT lam =
      Ops.sum (Ops.sum (atomicFig8Ops ℓ Pt C Dh encPt encT lam)
          (Ops.sum (atomicPtDecOps ℓ decT) (atomicCurveCheckOps ℓ decT encT)))
        (atomicSpqrKemOps ℓ Pt C K) := rfl

theorem atomicE2EOps_eq (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    atomicE2EOps ℓ P C K decT encT =
      Ops.sum (atomicAdapterOps ℓ decT encT)
        (Ops.sum (Ops.sum (atomicPtEncOps ℓ encT) (atomicPtDecOps ℓ decT))
          (Ops.sum (atomicSymOps ℓ Pt C)
            (Ops.sum (atomicSpqrKemOps ℓ Pt C K) (atomicPqxdhOps ℓ Pt P)))) := rfl

theorem pqAtomicOps_opsSizeHonest : OpsSizeHonest pqAtomicOps :=
  pqAtomicOps_sizeHonest

theorem atomicPureOps_opsSizeHonest (ℓ : ℕ) (Pt : Type) :
    OpsSizeHonest (atomicPureOps ℓ Pt) :=
  atomicPureOps_sizeHonest ℓ Pt

theorem atomicFsOps_opsSizeHonest (ℓ : ℕ) (Pt : Type) (C : Crypto) (encT : Pt → PublicKey) :
    OpsSizeHonest (atomicFsOps ℓ Pt C encT) :=
  atomicFsOps_sizeHonest ℓ Pt C encT

theorem atomicFig8Ops_opsSizeHonest (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (lam : Pt) :
    OpsSizeHonest (atomicFig8Ops ℓ Pt C Dh encPt encT lam) :=
  atomicFig8Ops_sizeHonest ℓ Pt C Dh encPt encT lam

theorem atomicSessionOps_opsSizeHonest (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    OpsSizeHonest (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) :=
  atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam

def keyIndCostedSig {S : SignalPqxdh.Setup}
    (R : SignalPqxdh.Security.KeyIndCostedReductionFamily S) (b : SignalPqxdh.QueryBudget) :
    CostedReduction pqAtomicOps ReductionDsl.pqSigAndDdhIface
      (SignalPqxdh.keyIndSpec S) (ReductionDsl.pqKeyIndCodec S)
      (SignalPqxdh.Costed.PB 32) .unit .bool
      (.prod (SignalPqxdh.Costed.PB 1569) (SignalPqxdh.Costed.PB 64)) :=
  R.sig b

def keyIndCostedShcr {S : SignalPqxdh.Setup}
    (R : SignalPqxdh.Security.KeyIndCostedReductionFamily S) (b : SignalPqxdh.QueryBudget) :
    TwoStageCostedReduction pqAtomicOps ReductionDsl.pqPrimIface
      (SignalPqxdh.keyIndSpec S) (ReductionDsl.pqKeyIndCodec S)
      (.prod (SignalPqxdh.Costed.PB 1568) (SignalPqxdh.Costed.PB 3168)) .unit .bool
      (SignalPqxdh.Costed.PB 1568)
      (.prod (SignalPqxdh.Costed.PB 32) (SignalPqxdh.Costed.PB 1568))
      (SignalPqxdh.Costed.PB 1568) :=
  R.shcr b

def keyIndCostedGdh {S : SignalPqxdh.Setup}
    (R : SignalPqxdh.Security.KeyIndCostedReductionFamily S) (b : SignalPqxdh.QueryBudget) :
    CostedReduction pqAtomicOps ReductionDsl.pqSigAndDdhIface
      (SignalPqxdh.keyIndSpec S) (ReductionDsl.pqKeyIndCodec S)
      (.prod (SignalPqxdh.Costed.PB 32) (SignalPqxdh.Costed.PB 32)) .unit .bool
      (SignalPqxdh.Costed.PB 32) :=
  R.gdh b

def auth1KeyCostedSig {S : SignalPqxdh.Setup}
    (R : SignalPqxdh.Security.Auth1KeyCostedReductionFamily S) (b : SignalPqxdh.QueryBudget) :
    CostedReduction pqAtomicOps SignalPqxdh.Costed.pqAuthSigAndDdhIface
      (SignalPqxdh.authSpec S) (SignalPqxdh.Costed.authCodec S)
      (SignalPqxdh.Costed.PB 32) .unit .bool
      (.prod (SignalPqxdh.Costed.PB 1569) (SignalPqxdh.Costed.PB 64)) :=
  R.sig b

def auth1KeyCostedShcr {S : SignalPqxdh.Setup}
    (R : SignalPqxdh.Security.Auth1KeyCostedReductionFamily S) (b : SignalPqxdh.QueryBudget) :
    TwoStageCostedReduction pqAtomicOps SignalPqxdh.Costed.pqAuthPrimIface
      (SignalPqxdh.authSpec S) (SignalPqxdh.Costed.authCodec S)
      (.prod (SignalPqxdh.Costed.PB 1568) (SignalPqxdh.Costed.PB 3168)) .unit .bool
      (SignalPqxdh.Costed.PB 1568)
      (.prod (SignalPqxdh.Costed.PB 32) (SignalPqxdh.Costed.PB 1568))
      (SignalPqxdh.Costed.PB 1568) :=
  R.shcr b

def auth1KeyCostedGdh {S : SignalPqxdh.Setup}
    (R : SignalPqxdh.Security.Auth1KeyCostedReductionFamily S) (b : SignalPqxdh.QueryBudget) :
    CostedReduction pqAtomicOps SignalPqxdh.Costed.pqAuthSigAndDdhIface
      (SignalPqxdh.authSpec S) (SignalPqxdh.Costed.authCodec S)
      (.prod (SignalPqxdh.Costed.PB 32) (SignalPqxdh.Costed.PB 32)) .unit .bool
      (SignalPqxdh.Costed.PB 32) :=
  R.gdh b

def auth1KeyCostedCk {S : SignalPqxdh.Setup}
    (R : SignalPqxdh.Security.Auth1KeyCostedReductionFamily S) (b : SignalPqxdh.QueryBudget) :
    CostedReduction pqAtomicOps SignalPqxdh.Costed.pqAuthPrimIface
      (SignalPqxdh.authSpec S) (SignalPqxdh.Costed.authCodec S)
      (.prod (SignalPqxdh.Costed.PB 32) (SignalPqxdh.Costed.PB 32)) .unit .bool .bool :=
  R.ck b

def auth1KeyCostedMk {S : SignalPqxdh.Setup}
    (R : SignalPqxdh.Security.Auth1KeyCostedReductionFamily S) (b : SignalPqxdh.QueryBudget) :
    CostedReduction pqAtomicOps SignalPqxdh.Costed.pqPrfMkIface
      (SignalPqxdh.authSpec S) (SignalPqxdh.Costed.authCodec S)
      .unit .unit .bool .bool :=
  R.mk b

def auth1KeyCostedCpa {S : SignalPqxdh.Setup}
    (R : SignalPqxdh.Security.Auth1KeyCostedReductionFamily S) (b : SignalPqxdh.QueryBudget) :
    TwoStageCostedReduction pqAtomicOps SignalPqxdh.Costed.pqAuthPrimIface
      (SignalPqxdh.authSpec S) (SignalPqxdh.Costed.authCodec S)
      .unit .unit .bool
      (.prod (SignalPqxdh.Costed.PB 158)
        (.prod (SignalPqxdh.Costed.PB 32) (SignalPqxdh.Costed.PB 32)))
      (.opt (SignalPqxdh.Costed.PB 32)) .bool :=
  R.cpa b

def auth1KeyCostedInt {S : SignalPqxdh.Setup}
    (R : SignalPqxdh.Security.Auth1KeyCostedReductionFamily S) (b : SignalPqxdh.QueryBudget) :
    CostedReduction pqAtomicOps SignalPqxdh.Costed.pqPrfHmacIface
      (SignalPqxdh.authSpec S) (SignalPqxdh.Costed.authCodec S)
      .unit .unit .bool .bool :=
  R.int b

theorem spkLeakRedProg_eq (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    SpkLeakRedProg Pt ℓ C K Dh encPt encT decT lam =
      CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
        (ReductionDsl.extractPtPrfIface ℓ Pt)
        (SM.spec (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
        (ReductionDsl.e2eSessionCodec ℓ Pt)
        ReductionDsl.BV256 .unit .bool .bool := rfl

theorem spkLeakRedUProg_eq (Pt : Type) (ℓ : ℕ) :
    SpkLeakRedUProg Pt ℓ =
      CostedReduction (atomicPureOps ℓ Pt)
        (ReductionDsl.extractPtPrfBaseIface ℓ Pt)
        (CryptoGames.MACScheme.prfSpec Pt (BitVec 256))
        (ReductionDsl.extractPtPrfCodec ℓ Pt)
        .unit ReductionDsl.BV256 .bool .bool := rfl

theorem spkSwapPrgHybridProg_eq (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    SpkSwapPrgHybridProg Pt ℓ C K Dh encPt encT decT lam =
      CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
        (ReductionDsl.coinOnlyIface ℓ Pt)
        (SM.spec (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
        (ReductionDsl.e2eSessionCodec ℓ Pt)
        (.prod ReductionDsl.BV256 (.prod ReductionDsl.BV256 ReductionDsl.BV256))
        .unit .bool .bool := rfl

theorem spkSwapPrfHybridProg_eq (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    SpkSwapPrfHybridProg Pt ℓ C K Dh encPt encT decT lam =
      CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
        (ReductionDsl.extractPtPrfIface ℓ Pt)
        (SM.spec (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
        (ReductionDsl.e2eSessionCodec ℓ Pt)
        ReductionDsl.BV256 .unit .bool .bool := rfl

def fsCostedPrgRedZero {Pt : Type} [DecidableEq Pt] {C : Crypto} {codec : SignalMessageProtoCodec}
    {ℓ : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    (R : FsCostedReds C codec ℓ encT idOf) (j : ℕ) :
    TwoStageCostedReduction (atomicFsOps ℓ Pt C encT)
      (ReductionDsl.coinOnlyBaseIface ℓ Pt)
      (FSAEAD.spec
        (FSAEAD.RatchetSenderState (BitVec 256))
        (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (Header Pt × LibsignalMsgPublicPart) (CBC.Plain ℓ) (ℕ × LCt))
      (ReductionDsl.fsaeadRatchetCodec ℓ Pt)
      (.prod ReductionDsl.BV256 ReductionDsl.BV256) .unit .bool .unit .unit .bool :=
  R.prgRedZero j

def fsCostedMultiRed {Pt : Type} [DecidableEq Pt] {C : Crypto} {codec : SignalMessageProtoCodec}
    {ℓ : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    (R : FsCostedReds C codec ℓ encT idOf) (la : Bool) :
    TwoStageCostedReduction (atomicFsOps ℓ Pt C encT)
      (ReductionDsl.slotOtccaTargetIface ℓ Pt)
      (FSAEAD.spec
        (FSAEAD.RatchetSenderState (BitVec 256))
        (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (Header Pt × LibsignalMsgPublicPart) (CBC.Plain ℓ) (ℕ × LCt))
      (ReductionDsl.fsaeadRatchetCodec ℓ Pt) .unit .unit .bool .unit .unit .bool :=
  R.multiRed la

def fsCostedLWireRed {Pt : Type} [DecidableEq Pt] {C : Crypto} {codec : SignalMessageProtoCodec}
    {ℓ : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    (R : FsCostedReds C codec ℓ encT idOf) :
    CostedReduction (atomicFsOps ℓ Pt C encT)
      (ReductionDsl.wireOtccaTargetIface ℓ Pt)
      (AEADScheme.otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (CBC.Plain ℓ) LCt)
      (ReductionDsl.slotOtccaCodec ℓ Pt) .unit .unit .bool .bool :=
  R.lWireRed

def fig8CostedChallSim {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {ℓ : ℕ} {encT : Pt → PublicKey}
    {idOf : Party → IdentityKey} {lam : Pt}
    (R : Fig8CostedReds Dh encPt C codec ℓ encT idOf lam) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam)
      (ReductionDsl.fig8SmIface ℓ Pt)
      (SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ)
        (BitVec 256) (LibsignalSim.Fig8C Pt))
      (ReductionDsl.fig8SmCodec ℓ Pt) .unit .unit .bool .bool :=
  R.challSim

def sessionCostedSimFig8 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} {C : Crypto} {K : MlKem} {idA idB : IdentityKey}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    (R : SessionCostedReductions Pt ℓ C K idA idB Dh encPt encT decT lam) :
    CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (ReductionDsl.fig8SmIface ℓ Pt)
      (SM.spec (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
      (ReductionDsl.e2eSessionCodec ℓ Pt) .unit .unit .bool .bool :=
  R.simFig8

def compositionKindRed {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (R : CompositionCostedReductions S ℓ P C K qep decT encT) :
    CostedReduction (atomicE2EOps ℓ P C K decT encT)
      (ReductionDsl.e2eKeyIndTargetIface S ℓ Pt)
      (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ Pt)
      .unit .unit .bool .bool :=
  R.kindRed

def compositionPrefixRed {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (R : CompositionCostedReductions S ℓ P C K qep decT encT) (k : ℕ) :
    TwoStageCostedReduction (atomicE2EOps ℓ P C K decT encT)
      (ReductionDsl.e2eSessionTargetIface ℓ Pt)
      (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ Pt)
      .unit .unit .bool (ReductionDsl.prefixCtxT (ℓ := ℓ) (Pt := Pt)) .bool .bool :=
  R.prefixRed k

theorem cliAdapterProg_eq (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CliToModelAdapterProg S ℓ decT encT =
      CostedReduction (atomicAdapterOps ℓ decT encT)
        (e2eBhAdapterIface S ℓ Pt)
        (bhGameSpec S ℓ (BitVec 512)) (e2eBhAdapterCodec S ℓ Pt) .unit .unit .bool .bool := rfl

end CryptoVerification.E2E.Guards.HeadlineAtomicOps

namespace CryptoVerification.E2E.Guards.HeadlineAtomicOpsAudit

open ReductionDsl (Sig Ops GameCodec CostedReduction Comp Expr atomicSig pqAtomicSig
  atomicPureOps pqAtomicOps coinOnlyBaseIface atomicPrfCodec)

private def fixtureUnlistedSig : Sig where
  Base := Unit
  den := fun _ => Bool
  sz := fun _ _ => 1

private def fixtureStmtWithUnlistedSig : Prop :=
  fixtureUnlistedSig.Base = Unit

private def fixtureInlineSigCarrier : Type :=
  ({ Base := Unit, den := fun _ => Bool, sz := fun _ _ => 1 : Sig }).den ()

private def fixtureStmtWithInlineSigMk : Prop :=
  fixtureInlineSigCarrier = Bool

private def fixtureUnlistedOps : Ops pqAtomicSig :=
  Ops.sum pqAtomicOps pqAtomicOps

private def fixtureStmtWithUnlistedOps : Prop :=
  fixtureUnlistedOps.Op = (pqAtomicOps.Op ⊕ pqAtomicOps.Op)

private def fixtureInlineOpsCost : ℕ :=
  let o : Ops (atomicSig 0 Empty) := {
    Op := Unit
    dom := fun _ => .unit
    cod := fun _ => .bool
    eval := fun _ _ => false
    cost := fun _ => 1
  }
  o.cost ()

private def fixtureStmtWithInlineOpsMk : Prop :=
  fixtureInlineOpsCost = 1

private def fixtureUnlistedCodec :
    GameCodec (atomicSig 0 Empty) (CryptoGames.MACScheme.prfSpec Bool Bool) where
  Q := .bool
  R := .bool
  qenc := id
  rdec := fun _ r => r
  codecCost := 2

private def fixtureStmtWithUnlistedCodec : Prop :=
  fixtureUnlistedCodec.codecCost = 2

meta section

open Lean

def auditedSpecModuleRoots : Array Name := #[
  `Computational.Specifications.Pqxdh.Security.HeadlineDelta,
  `Computational.Specifications.Session.StatementSession,
  `Computational.Specifications.Composition.StatementModel,
  `Computational.Specifications.LibsignalCli.StatementPqElf
]

def auditedHeadlineRoots : Array Name := #[
  `SignalPqxdh.Security.PqxdhCorrectAndSecureδ,
  `CryptoVerification.E2E.SessionSecure,
  `CryptoVerification.E2E.ModelSecure,
  `CryptoVerification.SignalSession.CliPqxdhElfCorrectPlaced,
  `CryptoVerification.LibsignalCli.CliPqxdhElfSecurePlaced,
  `CryptoVerification.LibsignalCli.CliPqxdhBinaryCorrectAndSecurePlaced,
  `CryptoVerification.E2E.CliPqxdhSecurityFor
]

def allowedHeadlineSigs : Array Name := #[
  `ReductionDsl.atomicSig,
  `ReductionDsl.pqAtomicSig
]

def allowedSigMkCallers : Array Name := #[
  `ReductionDsl.atomicSig
]

def allowedHeadlineOps : Array Name := #[
  `ReductionDsl.Ops.sum,
  `ReductionDsl.atomicPureOps,
  `ReductionDsl.pqAtomicOps,
  `ReductionDsl.atomicCurveCheckOps,
  `ReductionDsl.atomicPtEncOps,
  `ReductionDsl.atomicPtDecOps,
  `ReductionDsl.atomicSymOps,
  `ReductionDsl.atomicGroupOps,
  `ReductionDsl.atomicSpqrKemOps,
  `ReductionDsl.atomicPqxdhOps,
  `ReductionDsl.atomicAdapterOps,
  `ReductionDsl.atomicFsOps,
  `ReductionDsl.atomicFig8Ops,
  `ReductionDsl.atomicSessionOps,
  `ReductionDsl.atomicE2EOps
]

def allowedOpsMkCallers : Array Name := #[
  `ReductionDsl.Ops.sum,
  `ReductionDsl.atomicPureOps,
  `ReductionDsl.atomicCurveCheckOps,
  `ReductionDsl.atomicPtEncOps,
  `ReductionDsl.atomicPtDecOps,
  `ReductionDsl.atomicSymOps,
  `ReductionDsl.atomicGroupOps,
  `ReductionDsl.atomicSpqrKemOps,
  `ReductionDsl.atomicPqxdhOps
]

def allowedHeadlineGameCodecs : Array Name := #[
  `ReductionDsl.atomicPrfCodec,
  `ReductionDsl.extractPtPrfCodec,
  `ReductionDsl.keyIndCodec,
  `ReductionDsl.pqKeyIndCodec,
  `SignalPqxdh.Costed.keyIndCodec,
  `SignalPqxdh.Costed.authCodec,
  `ReductionDsl.slotOtccaCodec,
  `ReductionDsl.fsaeadPubCodec,
  `ReductionDsl.fsaeadRatchetCodec,
  `ReductionDsl.fig8SmCodec,
  `ReductionDsl.fig8SmCodecDF,
  `ReductionDsl.e2eSessionCodec,
  `ReductionDsl.e2eGameCodec,
  `ReductionDsl.e2eAdapterCodec,
  `CryptoVerification.E2E.e2eTargetGameCodec,
  `CryptoVerification.E2E.e2eBhAdapterCodec
]

def requiredOperatorInductives : Array Name := #[
  `ReductionDsl.AtomicPureOp,
  `ReductionDsl.AtomicCurveCheckOp,
  `ReductionDsl.AtomicPtEncOp,
  `ReductionDsl.AtomicPtDecOp,
  `ReductionDsl.AtomicSymOp,
  `ReductionDsl.AtomicGroupOp,
  `ReductionDsl.AtomicSpqrKemOp,
  `ReductionDsl.AtomicPqxdhOp
]

def forbiddenLegacyPrefixes : Array Name := #[
  `SignalPqxdh.LegacyCosted,
  `CryptoVerification.E2E.Costed,
  `CryptoGames.PRF.Costed,
  `CryptoGames.PRG.Costed,
  `CryptoGames.OTCCA.Costed,
  `CryptoGames.AEAD.Costed,
  `CryptoGames.FSAEAD.Costed,
  `Computational.Proofs.SpecLemmas
]

def forbiddenLegacyCostedDecls : Array Name := #[
  `SignalPqxdh.Costed.PSort,
  `SignalPqxdh.Costed.pqSig,
  `SignalPqxdh.Costed.pqxdhOps,
  `CryptoGames.CKA.ckaSig,
  `CryptoGames.CKA.ckaOps,
  `CryptoGames.CKA.ckaCodec,
  `CryptoGames.CKA.ckaSMCodec,
  `CryptoGames.CKA.ckaSMCodecDF,
  `CryptoGames.PRFPRNG.prngOps,
  `CryptoGames.PRFPRNG.prngSMCodec,
  `CryptoGames.PRFPRNG.prngSMCodecDF,
  `CryptoGames.SM.smSig,
  `CryptoGames.SM.smOps,
  `CryptoGames.SM.smCodec,
  `CryptoGames.SM.smCodecDF,
  `CryptoGames.Ratchet.LibsignalSim.simSig,
  `CryptoGames.Ratchet.LibsignalSim.simOps,
  `CryptoGames.Ratchet.LibsignalSim.simCodec,
  `ReductionDsl.Ops.empty
]

partial def retHeadConst? : Expr → Option Name
  | .forallE _ _ b _ => retHeadConst? b
  | .letE _ _ _ b _  => retHeadConst? b
  | .mdata _ b       => retHeadConst? b
  | e                => e.getAppFn.constName?

partial def stripLambdas : Expr → Expr
  | .lam _ _ b _ => stripLambdas b
  | .mdata _ b   => stripLambdas b
  | e            => e

def isStructProjDef (env : Environment) (c : Name) (d : DefinitionVal) : Bool :=
  match stripLambdas d.value with
  | .proj indName _ (.bvar 0) =>
      c.getPrefix == indName &&
      match env.find? indName with
      | some (.inductInfo iv) => iv.ctors.length == 1
      | _ => false
  | _ => false

def isInternalAuxDecl (env : Environment) (c : Name) (ci : ConstantInfo) : Bool :=
  let user := (privateToUserName? c).getD c
  let genAux :=
    env.isProjectionFn c ||
    Lean.isAuxRecursor env c ||
    Lean.isNoConfusion env c ||
    Meta.isMatcherCore env c ||
    user.components.any fun p =>
      p.isInternalDetail || match p with | .str _ s => s.startsWith "_" | _ => false
  match ci with
  | .ctorInfo _ | .recInfo _ | .inductInfo _ | .quotInfo _ => true
  | .defnInfo d => isStructProjDef env c d || genAux
  | _ => genAux

def callsCtorConst (env : Environment) (ctorName : Name) (c : Name) : ConstantInfo → Bool
  | .defnInfo d =>
      d.value.getUsedConstantsAsSet.contains ctorName ||
      (!Lean.isAuxRecursor env c && !Lean.isNoConfusion env c &&
        d.type.getUsedConstantsAsSet.contains ctorName)
  | .opaqueInfo o => o.type.getUsedConstantsAsSet.contains ctorName
  | .axiomInfo a => a.type.getUsedConstantsAsSet.contains ctorName
  | _ => false

def stmtNodeDeps : ConstantInfo → NameSet
  | .thmInfo _    => {}
  | .defnInfo v   => v.type.getUsedConstantsAsSet.union v.value.getUsedConstantsAsSet
  | .opaqueInfo v => v.type.getUsedConstantsAsSet
  | .axiomInfo v  => v.type.getUsedConstantsAsSet
  | .ctorInfo v   => v.type.getUsedConstantsAsSet
  | .inductInfo v => v.ctors.foldl (fun s ct => s.insert ct) v.type.getUsedConstantsAsSet
  | .recInfo v    => v.type.getUsedConstantsAsSet
  | .quotInfo v   => v.type.getUsedConstantsAsSet

def moduleRootOfConst (env : Environment) (c : Name) : Name :=
  match env.getModuleIdxFor? c with
  | some idx => (env.header.moduleNames.getD idx.toNat Name.anonymous).getRoot
  | none     => env.mainModule.getRoot

def auditSpecModuleImports (env : Environment) (roots : Array Name)
    (forbiddenSubstrings : Array String := #["CostedTables"]) :
    CoreM (NameSet × Array String) := do
  let mut visited : NameSet := {}
  let mut queue : Array Name := #[]
  let mut violations : Array String := #[]
  for r in roots do
    if (env.getModuleIdx? r).isNone then
      throwError "HeadlineAtomicOpsGuard: missing specification module `{r}`"
    queue := queue.push r
  let mut idx := 0
  while idx < queue.size do
    let m := queue[idx]!
    idx := idx + 1
    if visited.contains m then continue
    visited := visited.insert m
    let mStr := m.toString
    for sub in forbiddenSubstrings do
      if (mStr.splitOn sub).length > 1 then
        violations := violations.push s!"FORBIDDEN-SPEC-IMPORT({sub}): {m}"
    if (`Computational.Proofs).isPrefixOf m || (`Computational.Tests).isPrefixOf m then
      violations := violations.push s!"NON-SPEC-IMPORT: {m}"
    if m.getRoot != `Computational then continue
    let some mIdx := env.getModuleIdx? m | continue
    let md := env.header.moduleData[mIdx.toNat]!
    for imp in md.imports do
      unless visited.contains imp.module do
        queue := queue.push imp.module
  return (visited, violations)

structure AtomicAuditResult where
  sigs : Array Name
  ops : Array Name
  codecs : Array Name
  opInductives : Array Name
  violations : Array String

def auditStmtRoot (env : Environment) (root : Name)
    (allowedSigs : Array Name := allowedHeadlineSigs)
    (allowedOps : Array Name := allowedHeadlineOps)
    (allowedCodecs : Array Name := allowedHeadlineGameCodecs)
    (forbiddenDecls : Array Name := forbiddenLegacyCostedDecls)
    (forbiddenPfxs : Array Name := forbiddenLegacyPrefixes) :
    CoreM AtomicAuditResult := do
  let some rootCi := env.find? root
    | throwError "HeadlineAtomicOpsGuard: missing audited root `{root}`"
  let mut visited : NameSet := {}
  let mut queue : Array Name :=
    match rootCi with
    | .thmInfo ti => ti.type.getUsedConstantsAsSet.toArray.qsort Name.lt
    | _ => #[root]
  let mut foundSigs : NameSet := {}
  let mut foundOps : NameSet := {}
  let mut foundCodecs : NameSet := {}
  let mut foundOpInds : NameSet := {}
  let mut violations : Array String := #[]
  let mut idx := 0
  while idx < queue.size do
    let c := queue[idx]!
    idx := idx + 1
    if visited.contains c then continue
    visited := visited.insert c
    let user := (privateToUserName? c).getD c
    if forbiddenDecls.contains c || forbiddenDecls.contains user ||
        forbiddenPfxs.any (fun p => p.isPrefixOf c || p.isPrefixOf user) then
      violations := violations.push s!"FORBIDDEN-LEGACY-COSTED({root}): {user}"
    if requiredOperatorInductives.contains user then
      foundOpInds := foundOpInds.insert user
    let some ci := env.find? c | continue
    let aux := isInternalAuxDecl env c ci

    let isSigDecl := retHeadConst? ci.type == some `ReductionDsl.Sig && !aux
    let isSigMk := callsCtorConst env `ReductionDsl.Sig.mk c ci
    if isSigDecl || isSigMk then
      if isSigDecl then foundSigs := foundSigs.insert user
      let okSig :=
        if isSigDecl then
          allowedSigs.contains c || allowedSigs.contains user
        else
          allowedSigMkCallers.contains c || allowedSigMkCallers.contains user ||
          (aux && allowedSigMkCallers.any fun a => a.isPrefixOf c || a.isPrefixOf user)
      unless okSig do
        violations := violations.push s!"UNLISTED-SIG({root}): {user}"

    let isOpsDecl := retHeadConst? ci.type == some `ReductionDsl.Ops && !aux
    let isOpsMk := callsCtorConst env `ReductionDsl.Ops.mk c ci
    if isOpsDecl || isOpsMk then
      if isOpsDecl then foundOps := foundOps.insert user
      let okOps :=
        if isOpsDecl then
          allowedOps.contains c || allowedOps.contains user
        else
          allowedOpsMkCallers.contains c || allowedOpsMkCallers.contains user ||
          (aux && allowedOpsMkCallers.any fun a => a.isPrefixOf c || a.isPrefixOf user)
      unless okOps do
        violations := violations.push s!"UNLISTED-OPS({root}): {user}"

    let isCodecDecl := retHeadConst? ci.type == some `ReductionDsl.GameCodec && !aux
    let isCodecMk := callsCtorConst env `ReductionDsl.GameCodec.mk c ci
    if isCodecDecl || isCodecMk then
      if isCodecDecl then foundCodecs := foundCodecs.insert user
      let okCodec :=
        allowedCodecs.contains c || allowedCodecs.contains user ||
        (aux && allowedCodecs.any fun a => a.isPrefixOf c || a.isPrefixOf user)
      unless okCodec do
        violations := violations.push s!"UNLISTED-CODEC({root}): {user}"

    if moduleRootOfConst env c != `Computational then
      continue
    for d in stmtNodeDeps ci do
      unless visited.contains d do
        queue := queue.push d
  return {
    sigs := foundSigs.toArray.qsort Name.lt
    ops := foundOps.toArray.qsort Name.lt
    codecs := foundCodecs.toArray.qsort Name.lt
    opInductives := foundOpInds.toArray.qsort Name.lt
    violations := violations
  }

def runHeadlineAtomicOpsAudit : CoreM Unit := do
  let env ← getEnv
  -- Negative self-tests
  let (_, negImportViolations) ← auditSpecModuleImports env auditedSpecModuleRoots
    (forbiddenSubstrings := #["CostedTables", "AtomicOps"])
  unless negImportViolations.any (·.startsWith "FORBIDDEN-SPEC-IMPORT(AtomicOps):") do
    throwError "HeadlineAtomicOpsGuard self-test failed: module-import walker missed AtomicOps"

  let negSig ← auditStmtRoot env ``fixtureStmtWithUnlistedSig
  unless negSig.violations.any (·.startsWith "UNLISTED-SIG(") do
    throwError "HeadlineAtomicOpsGuard self-test failed: unlisted Sig was not rejected"

  let negInlineSig ← auditStmtRoot env ``fixtureStmtWithInlineSigMk
  unless negInlineSig.violations.any (·.startsWith "UNLISTED-SIG(") do
    throwError "HeadlineAtomicOpsGuard self-test failed: inline Sig.mk was not rejected"

  let negOps ← auditStmtRoot env ``fixtureStmtWithUnlistedOps
  unless negOps.violations.any (·.startsWith "UNLISTED-OPS(") do
    throwError "HeadlineAtomicOpsGuard self-test failed: unlisted Ops was not rejected"

  let negInlineOps ← auditStmtRoot env ``fixtureStmtWithInlineOpsMk
  unless negInlineOps.violations.any (·.startsWith "UNLISTED-OPS(") do
    throwError "HeadlineAtomicOpsGuard self-test failed: inline Ops.mk was not rejected"

  let negCodec ← auditStmtRoot env ``fixtureStmtWithUnlistedCodec
  unless negCodec.violations.any (·.startsWith "UNLISTED-CODEC(") do
    throwError "HeadlineAtomicOpsGuard self-test failed: unlisted GameCodec was not rejected"

  let userUnlistedCodec := (privateToUserName? ``fixtureUnlistedCodec).getD ``fixtureUnlistedCodec
  let negLegacy ← auditStmtRoot env ``fixtureStmtWithUnlistedCodec
    (allowedCodecs := allowedHeadlineGameCodecs.push userUnlistedCodec)
    (forbiddenDecls := forbiddenLegacyCostedDecls.push userUnlistedCodec)
  unless negLegacy.violations.any (·.startsWith "FORBIDDEN-LEGACY-COSTED(") do
    throwError "HeadlineAtomicOpsGuard self-test failed: forbidden legacy declaration was not rejected"

  -- Specification module import-graph audit
  let (visitedSpecMods, specImportViolations) ← auditSpecModuleImports env auditedSpecModuleRoots
  let mut allViolations : Array String := specImportViolations
  unless visitedSpecMods.contains `Computational.Specifications.Reductions.ReductionDsl.AtomicOps do
    allViolations := allViolations.push
      "MISSING-SPEC-IMPORT: AtomicOps was not reached in specification import graph"
  unless visitedSpecMods.contains `Computational.Specifications.Reductions.ReductionDsl.TargetCodecs do
    allViolations := allViolations.push
      "MISSING-SPEC-IMPORT: TargetCodecs was not reached in specification import graph"

  -- Statement constant-closure audit
  let mut unionSigs : NameSet := {}
  let mut unionOps : NameSet := {}
  let mut unionOpInds : NameSet := {}
  let rootsRequiringAtomicOps : Array Name := #[
    `SignalPqxdh.Security.PqxdhCorrectAndSecureδ,
    `CryptoVerification.E2E.SessionSecure,
    `CryptoVerification.E2E.ModelSecure,
    `CryptoVerification.LibsignalCli.CliPqxdhElfSecurePlaced,
    `CryptoVerification.LibsignalCli.CliPqxdhBinaryCorrectAndSecurePlaced,
    `CryptoVerification.E2E.CliPqxdhSecurityFor
  ]
  for root in auditedHeadlineRoots do
    let res ← auditStmtRoot env root
    for s in res.sigs do unionSigs := unionSigs.insert s
    for o in res.ops do unionOps := unionOps.insert o
    for ind in res.opInductives do unionOpInds := unionOpInds.insert ind
    for v in res.violations do allViolations := allViolations.push v
    if rootsRequiringAtomicOps.contains root then
      unless res.sigs.contains `ReductionDsl.atomicSig do
        allViolations := allViolations.push
          s!"MISSING-ATOMIC-SIG({root}): closure did not reach ReductionDsl.atomicSig"
      unless res.opInductives.contains `ReductionDsl.AtomicPureOp do
        allViolations := allViolations.push
          s!"MISSING-ATOMIC-PURE-OP({root}): closure did not reach ReductionDsl.AtomicPureOp"

  for s in allowedHeadlineSigs do
    unless unionSigs.contains s do
      allViolations := allViolations.push
        s!"STALE-SIG-ALLOWLIST: {s} was not reached by any audited headline root"

  for o in allowedHeadlineOps do
    unless unionOps.contains o do
      allViolations := allViolations.push
        s!"STALE-OPS-ALLOWLIST: {o} was not reached by any audited headline root"

  for ind in requiredOperatorInductives do
    unless unionOpInds.contains ind do
      allViolations := allViolations.push
        s!"MISSING-OPERATOR-INDUCTIVE: {ind} was not reached by any audited headline root"

  unless allViolations.isEmpty do
    let joined := "\n  ".intercalate allViolations.toList
    throwError s!"HeadlineAtomicOpsGuard failed with {allViolations.size} violation(s):\n  {joined}"

#eval runHeadlineAtomicOpsAudit

end

end CryptoVerification.E2E.Guards.HeadlineAtomicOpsAudit
