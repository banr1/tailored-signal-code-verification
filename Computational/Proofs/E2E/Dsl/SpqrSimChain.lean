/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables
public import Computational.Proofs.E2E.Dsl.TablesHonest
public import Computational.Proofs.E2E.Dsl.ClampsLossless
public import Computational.Proofs.SpqrV1Sync.TopStateTight
import LibsignalBinary.Proofs.SpqrV1Sync.TopInSync
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbState
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidCodec
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopSend
import Computational.Proofs.E2E.ComposedBinaryLinkV1

/-!
# SPQR V1 `ReductionDsl` Primitives and Send-Chain Helpers

Provides `Comp` wrappers for SPQR V1 cryptographic operations, `TopStateTight` state split/join
and chain round-trip bridges, bounded list combinators (`listDropExpr`, `listGetExpr`,
`listSetExpr`), and `ReductionDsl` programs for chain resolution, `addEpoch`, and `Chain.sendKey`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.SpqrSimChain

open List Option Prod Sum BitVec OracleSpec OracleComp
open ReductionDsl (Ty Ops Var Expr Comp Iface Env bits)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (Crypto ShaCompress PublicKey)
open CryptoVerification.E2E (Bytes keyToBytes32_bytesToKey32)
open CryptoVerification.E2E.Costed (B U8 U32 U64 BV256 BV512 E2EPureOp E2ECryptoOp
  e2eSig e2ePureOps e2eCryptoOps e2eOps spqrParamsT spqrVnT spqrPrevEntryT spqrDirT
  spqrEpochLinkT spqrChainT spqrStatePartsT splitSpqrPrev spqrParamsToV spqrVnToV spqrVnOfV
  spqrDirToV spqrDirOfV spqrChainToV spqrChainOfV spqrSplitEval spqrJoinEval spqrMsgPayloadSuffix
  spqrBraidSendEval spqrBraidRecvEval spqrNegotiateInitEval spqrChainFromVnEval
  spqrChainAddEpochEval spqrChainNextKeyEval)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp e2eCryptoOp
  eval_e2ePureOp cost_e2ePureOp eval_e2eCryptoOp cost_e2eCryptoOp)
open Computational.Proofs.E2E.Dsl.ClampsLossless (spqrVn_roundtrip spqrChain_roundtrip
  spqrSplitJoin_topStateTight v1State_encodeRaw_take64000_of_bOkTight
  bSendClosed_encodeRaw_take64000 bRecvClosed_encodeRaw_take64000
  spqrChainNextKeyEval_take32_lossless spqrChainNextKeyRaw)
open CryptoVerification.LibsignalSpqrV1 (MlKem Direction Version ChainParamsPB EpochDirectionPB
  ChainEpochPB ChainPB VersionNegotiationPB V1State Chain ChainEpoch ChainEpochDirection
  EpochSecret States Message spqrPolyApi spqrAuthApi spqrDeps spqrHkdfWith coinBytes
  pbToPqRatchetState hkdfToVecUnchecked hkdfToSliceUnchecked chainFromVersionNegotiation
  chainFrom SpqrApiResult ChainResult)
open CryptoVerification.SpqrV1Sync.InSync (St)
open CryptoVerification.SpqrV1Sync.ChainSync (ChainOk length_seedAt)
open LibsignalBinary.Proofs.SpqrV1Sync.ChainSyncBase (length_nextAt)
open CryptoVerification.SpqrV1Sync.TopSync (topPb topBytes vnOf SendPrevNil chain_fromPb_intoPb)
open CryptoVerification.SpqrV1Sync.Codec (spqrDecodeState_encodeState decode_v1State)
open CryptoVerification.SpqrV1Sync.SendTotal (BOkTight RecvSmallTight TopWitness
  TopStateTight TopStateTightW topStateTightW_length_le st_bCodec chainCur_le_phiB)

/-! ## SPQR primitive wrappers -/

def spqrNegotiateInitC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (.prod U8 (.prod U32 (B 32)))) :
    Comp (e2eOps ℓ P C K decT encT) I Γ (.prod .bool (.opt (.opt (B 32)))) :=
  .ret (e2eCryptoOp .spqrNegotiateInit a)

def spqrBraidSendC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) BV512)) :
    Comp (e2eOps ℓ P C K decT encT) I Γ
      (.prod .bool (.opt (.prod (B 32) (.prod U64 (.prod (.opt (.prod U64 BV256)) (B 64)))))) :=
  .ret (e2eCryptoOp .spqrBraidSend a)

def spqrBraidRecvC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) (.prod U64 (B 32)))) :
    Comp (e2eOps ℓ P C K decT encT) I Γ
      (.prod .bool (.prod .bool (.opt (.prod (.opt (.prod U64 BV256)) (B 32))))) :=
  .ret (e2eCryptoOp .spqrBraidRecv a)

def spqrChainFromVnC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (a : Expr (e2eOps ℓ P C K decT encT) Γ spqrVnT) :
    Comp (e2eOps ℓ P C K decT encT) I Γ (.opt spqrChainT) :=
  .ret (e2eCryptoOp .spqrChainFromVn a)

def spqrChainAddEpochC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (.prod spqrChainT (.prod U64 BV256))) :
    Comp (e2eOps ℓ P C K decT encT) I Γ (.prod .bool (.opt spqrChainT)) :=
  .ret (e2eCryptoOp .spqrChainAddEpoch a)

def spqrChainNextKeyC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) U32)) :
    Comp (e2eOps ℓ P C K decT encT) I Γ (.prod .bool (.opt (.prod (B 32) (.prod U32 BV256)))) :=
  .ret (e2eCryptoOp .spqrChainNextKey a)

@[simp] theorem cost_spqrNegotiateInitC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (.prod U8 (.prod U32 (B 32)))) :
    (spqrNegotiateInitC I a).cost = a.cost + 1601 := rfl

@[simp] theorem cost_spqrBraidSendC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) BV512)) :
    (spqrBraidSendC I a).cost = a.cost + 3073 := rfl

@[simp] theorem cost_spqrBraidRecvC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) (.prod U64 (B 32)))) :
    (spqrBraidRecvC I a).cost = a.cost + 3073 := rfl

@[simp] theorem cost_spqrChainFromVnC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (a : Expr (e2eOps ℓ P C K decT encT) Γ spqrVnT) :
    (spqrChainFromVnC I a).cost = a.cost + 17 := rfl

@[simp] theorem cost_spqrChainAddEpochC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (.prod spqrChainT (.prod U64 BV256))) :
    (spqrChainAddEpochC I a).cost = a.cost + 25 := rfl

@[simp] theorem cost_spqrChainNextKeyC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) U32)) :
    (spqrChainNextKeyC I a).cost = a.cost + 13 := rfl

@[simp] theorem queries_spqrNegotiateInitC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (.prod U8 (.prod U32 (B 32)))) :
    (spqrNegotiateInitC I a).queries w ws = 0 := rfl

@[simp] theorem queries_spqrBraidSendC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) BV512)) :
    (spqrBraidSendC I a).queries w ws = 0 := rfl

@[simp] theorem queries_spqrBraidRecvC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) (.prod U64 (B 32)))) :
    (spqrBraidRecvC I a).queries w ws = 0 := rfl

@[simp] theorem queries_spqrChainFromVnC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ spqrVnT) :
    (spqrChainFromVnC I a).queries w ws = 0 := rfl

@[simp] theorem queries_spqrChainAddEpochC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (.prod spqrChainT (.prod U64 BV256))) :
    (spqrChainAddEpochC I a).queries w ws = 0 := rfl

@[simp] theorem queries_spqrChainNextKeyC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) U32)) :
    (spqrChainNextKeyC I a).queries w ws = 0 := rfl

@[simp] theorem eval_spqrNegotiateInitC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (.prod U8 (.prod U32 (B 32)))) (ρ : Env Γ) :
    (spqrNegotiateInitC I a).eval ρ =
      pure (spqrNegotiateInitEval C.F K (a.eval ρ).1 (a.eval ρ).2.1 (a.eval ρ).2.2) := rfl

@[simp] theorem eval_spqrBraidSendC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) BV512)) (ρ : Env Γ) :
    (spqrBraidSendC I a).eval ρ =
      pure (spqrBraidSendEval C.F K (a.eval ρ).1 (a.eval ρ).2) := rfl

@[simp] theorem eval_spqrBraidRecvC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) (.prod U64 (B 32)))) (ρ : Env Γ) :
    (spqrBraidRecvC I a).eval ρ =
      pure (spqrBraidRecvEval C.F K (a.eval ρ).1 (a.eval ρ).2.1 (a.eval ρ).2.2) := rfl

@[simp] theorem eval_spqrChainFromVnC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (a : Expr (e2eOps ℓ P C K decT encT) Γ spqrVnT) (ρ : Env Γ) :
    (spqrChainFromVnC I a).eval ρ = pure (spqrChainFromVnEval C.F (a.eval ρ)) := rfl

@[simp] theorem eval_spqrChainAddEpochC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (.prod spqrChainT (.prod U64 BV256))) (ρ : Env Γ) :
    (spqrChainAddEpochC I a).eval ρ =
      pure (spqrChainAddEpochEval C.F (a.eval ρ).1 (a.eval ρ).2.1 (a.eval ρ).2.2) := rfl

@[simp] theorem eval_spqrChainNextKeyC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) U32)) (ρ : Env Γ) :
    (spqrChainNextKeyC I a).eval ρ =
      pure (spqrChainNextKeyEval C.F (a.eval ρ).1 (a.eval ρ).2) := rfl

/-! ## `TopStateTight` split/join and chain bridges -/

theorem topBytes_ne_nil (F : ShaCompress) (K : MlKem) (st : St F)
    (vn? : Option VersionNegotiationPB) (ch? : Option Chain) :
    topBytes F K st vn? ch? ≠ [] := by
  intro hnil
  have hlen : 0 < (topBytes F K st vn? ch?).length := by
    have heq : topBytes F K st vn? ch? =
        CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
          VersionNegotiationPB.encodeRaw 1#32 vn? ++
        CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
          ChainPB.encodeRaw 2#32 (ch?.map Chain.intoPb) ++
        CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage
          V1State.encodeRaw 3#32 st.into_pb := rfl
    rw [heq]
    have hk : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 3#32 .lengthDelimited =
        [0x1a#8] := rfl
    simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, hk, List.length_append,
      List.length_singleton]
    omega
  rw [hnil] at hlen
  exact Nat.lt_irrefl 0 hlen

theorem spqrSplitEval_topStateTightW {ℓ : ℕ} (F : ShaCompress) (K : MlKem)
    {bytes : Bytes} {w : TopWitness F} (hw : TopStateTightW F K bytes w) :
    spqrSplitEval (ℓ := ℓ) bytes =
      some (some (V1State.encodeRaw w.st.into_pb),
        (w.vn?.map (spqrVnToV (ℓ := ℓ)),
         (w.ch?.map Chain.intoPb).map (spqrChainToV (ℓ := ℓ)))) := by
  have hlen : bytes.length ≤ 286196 := topStateTightW_length_le F K hw
  have hlt64 : bytes.length < 2 ^ 64 := by omega
  have henc : bytes =
      CryptoVerification.LibsignalSpqrV1.Proto.encodeState
        (pbToPqRatchetState (topPb w.st w.vn? w.ch?)) := hw.htop.hbytes
  have hdec :
      CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState bytes =
        .ok (pbToPqRatchetState (topPb w.st w.vn? w.ch?)) := by
    rw [henc]
    exact spqrDecodeState_encodeState _ (henc ▸ hlt64)
  unfold spqrSplitEval
  rw [hdec]
  dsimp only [pbToPqRatchetState, topPb, Option.map]
  rw [v1State_encodeRaw_take64000_of_bOkTight F K w.st hw.hbok]

theorem spqrJoinEval_topStateTightW {ℓ : ℕ} (F : ShaCompress) (K : MlKem)
    {bytes : Bytes} {w : TopWitness F} (hw : TopStateTightW F K bytes w) :
    spqrJoinEval (ℓ := ℓ)
      (some (V1State.encodeRaw w.st.into_pb),
        (w.vn?.map (spqrVnToV (ℓ := ℓ)),
         (w.ch?.map Chain.intoPb).map (spqrChainToV (ℓ := ℓ)))) = bytes := by
  obtain ⟨-, hrt⟩ := spqrSplitJoin_topStateTight (ℓ := ℓ) F K ⟨w, hw⟩
  rw [spqrSplitEval_topStateTightW (ℓ := ℓ) F K hw, Option.map_some, Option.some.injEq] at hrt
  exact hrt

theorem spqrChain_roundtrip_chainOk {ℓ : ℕ} (F : ShaCompress)
    (authKey : Bytes) (dir : Direction) (secret : ℕ → Bytes) (sendCtr : ℕ → ℕ)
    (recvSet : ℕ → Finset ℕ) (ch : Chain)
    (hok : ChainOk F authKey dir secret sendCtr recvSet ch)
    (hsp : SendPrevNil ch) (hsmall : RecvSmallTight ch)
    (hlen4 : ch.links.length ≤ 4) :
    spqrChainOfV (spqrChainToV (ℓ := ℓ) ch.intoPb) = ch.intoPb := by
  refine spqrChain_roundtrip ch.intoPb (by simpa [Chain.intoPb] using hlen4) ?_ ?_
  · dsimp only [Chain.intoPb]
    rw [hok.hroot]
    exact Nat.le_trans (List.length_take_le 32 _) (by decide)
  · intro lk hlk_mem
    dsimp only [Chain.intoPb] at hlk_mem
    rcases List.mem_map.mp hlk_mem with ⟨l, hl_mem, rfl⟩
    obtain ⟨i, hi_lt, hl_get⟩ := List.mem_iff_getElem.mp hl_mem
    have hl_opt : ch.links[i]? = some l := by simp [hi_lt, hl_get]
    let e := ch.sendEpoch.toNat - 1 + i
    have hlen := hok.hlen
    have hsend_le := hok.hsend_le
    have he_lo : ch.sendEpoch.toNat - 1 ≤ e := Nat.le_add_right _ _
    have he_hi : e ≤ ch.currentEpoch.toNat := by omega
    have he_idx : e - (ch.sendEpoch.toNat - 1) = i := Nat.add_sub_cancel_left _ _
    refine ⟨?_, ?_⟩
    · intro s hs
      simp only [Option.mem_def, Option.some.injEq] at hs
      subst hs
      dsimp only [ChainEpochDirection.intoPb]
      refine ⟨?_, ?_⟩
      · by_cases hold : i = 0 ∧ 1 ≤ ch.sendEpoch.toNat
        · rcases hold with ⟨rfl, hpos⟩
          rw [hok.hsendOld l hpos hl_opt]
          decide
        · have hse : ch.sendEpoch.toNat ≤ e := by omega
          obtain ⟨l', hl', hsok⟩ := hok.hsendDir e hse he_hi
          rw [he_idx, hl_opt] at hl'
          injection hl' with hl'_eq
          subst hl'_eq
          rw [hsok.hnext, length_nextAt F _ (length_seedAt F authKey secret dir e)]
          decide
      · rw [hsp l hl_mem]
        decide
    · intro r hr
      simp only [Option.mem_def, Option.some.injEq] at hr
      subst hr
      dsimp only [ChainEpochDirection.intoPb]
      refine ⟨?_, ?_⟩
      · obtain ⟨l', hl', hrok⟩ := hok.hrecvDir e he_lo he_hi
        rw [he_idx, hl_opt] at hl'
        injection hl' with hl'_eq
        subst hl'_eq
        rw [hrok.hnext, length_nextAt F _ (length_seedAt F authKey secret dir.switch e)]
        decide
      · exact Nat.le_trans (hsmall l hl_mem) (by decide)

theorem chainOk_send_next_le_64 (F : ShaCompress)
    (authKey : Bytes) (dir : Direction) (secret : ℕ → Bytes) (sendCtr : ℕ → ℕ)
    (recvSet : ℕ → Finset ℕ) (ch : Chain)
    (hok : ChainOk F authKey dir secret sendCtr recvSet ch) :
    ∀ l ∈ ch.links, l.send.next.length ≤ 64 := by
  intro l hl_mem
  obtain ⟨i, hi_lt, hl_get⟩ := List.mem_iff_getElem.mp hl_mem
  have hl_opt : ch.links[i]? = some l := by simp [hi_lt, hl_get]
  let e := ch.sendEpoch.toNat - 1 + i
  have hlen := hok.hlen
  have hsend_le := hok.hsend_le
  have he_hi : e ≤ ch.currentEpoch.toNat := by omega
  have he_idx : e - (ch.sendEpoch.toNat - 1) = i := Nat.add_sub_cancel_left _ _
  by_cases hold : i = 0 ∧ 1 ≤ ch.sendEpoch.toNat
  · rcases hold with ⟨rfl, hpos⟩
    rw [hok.hsendOld l hpos hl_opt]
    decide
  · have hse : ch.sendEpoch.toNat ≤ e := by omega
    obtain ⟨l', hl', hsok⟩ := hok.hsendDir e hse he_hi
    rw [he_idx, hl_opt] at hl'
    injection hl' with hl'_eq
    subst hl'_eq
    rw [hsok.hnext, length_nextAt F _ (length_seedAt F authKey secret dir e)]
    decide

theorem topStateTightW_links_le_three (F : ShaCompress) (K : MlKem)
    {bytes : Bytes} {w : TopWitness F} (hw : TopStateTightW F K bytes w) :
    w.chE.links.length ≤ 3 := by
  have hlen := hw.htop.hok.hlen
  have hcur := hw.htop.hcur
  have hsendEp := hw.htop.hsendEp
  have hcur_le := chainCur_le_phiB w.st
  have hphi := hw.hphi
  omega

private theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp_all [bind, Except.bind]

private theorem statesOfPanic_ok {α : Type}
    {x : Except CryptoVerification.LibsignalSpqrV1.StatesPanic α} {a : α}
    (h : CryptoVerification.LibsignalSpqrV1.StatesResult.ofPanic x = .ok a) : x = .ok a := by
  cases x <;> simp_all [CryptoVerification.LibsignalSpqrV1.StatesResult.ofPanic]

private theorem hkdfToVec32_spqrAuthApi (F : ShaCompress) (salt ikm info : Bytes) :
    (spqrAuthApi F).hkdf_to_vec salt ikm info 32 =
      .ok (hkdfToVecUnchecked F salt ikm info 32) := rfl

theorem states_send_secret_len (F : ShaCompress) (K : MlKem) {st st' : St F}
    {tape tape' : Bytes} {m : Message spqrPolyApi} {es : EpochSecret}
    (h : st.send K tape = .ok ({ msg := m, key := some es, state := st' }, tape')) :
    es.secret.length = 32 := by
  cases st with
  | keysUnsampled _ =>
    simp only [States.send] at h; obtain ⟨_, _, hret⟩ := except_bind_ok h; cases hret
  | keysSampled _ =>
    simp only [States.send] at h; obtain ⟨_, _, hret⟩ := except_bind_ok h; cases hret
  | headerSent _ =>
    simp only [States.send] at h; obtain ⟨_, _, hret⟩ := except_bind_ok h; cases hret
  | ct1Received _ =>
    simp only [States.send] at h; obtain ⟨_, _, hret⟩ := except_bind_ok h; cases hret
  | ekSentCt1Received _ =>
    simp only [States.send] at h; cases h
  | noHeaderReceived _ =>
    simp only [States.send] at h; cases h
  | headerReceived state =>
    simp only [States.send] at h
    obtain ⟨⟨state', chunk, es0, tape1⟩, hp, hret⟩ := except_bind_ok h
    cases hret
    have hs := statesOfPanic_ok hp
    unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.HeaderReceived.send_ct1_chunk at hs
    obtain ⟨⟨uc, ct1, es1, tape2⟩, huc, hs2⟩ := except_bind_ok hs
    obtain ⟨_, _, hs3⟩ := except_bind_ok hs2
    obtain ⟨_, _, hs4⟩ := except_bind_ok hs3
    cases hs4
    unfold CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.HeaderReceived.send_ct1 at huc
    obtain ⟨_, _, huc2⟩ := except_bind_ok huc
    obtain ⟨sec1, hsec1, huc3⟩ := except_bind_ok huc2
    obtain ⟨_, _, huc4⟩ := except_bind_ok huc3
    cases huc4
    rw [hkdfToVec32_spqrAuthApi] at hsec1
    cases hsec1
    simp [hkdfToVecUnchecked, hkdfToSliceUnchecked]
  | ct1Sampled _ =>
    simp only [States.send] at h; obtain ⟨_, _, hret⟩ := except_bind_ok h; cases hret
  | ekReceivedCt1Sampled _ =>
    simp only [States.send] at h; obtain ⟨_, _, hret⟩ := except_bind_ok h; cases hret
  | ct1Acknowledged _ =>
    simp only [States.send] at h; cases h
  | ct2Sampled _ =>
    simp only [States.send] at h; obtain ⟨_, _, hret⟩ := except_bind_ok h; cases hret

theorem states_recv_secret_len (F : ShaCompress) (K : MlKem) {st st' : St F}
    {m : Message spqrPolyApi} {es : EpochSecret}
    (h : st.recv K m = .ok { key := some es, state := st' }) :
    es.secret.length = 32 := by
  cases st with
  | keysUnsampled _ =>
    simp only [States.recv] at h; split at h <;> cases h
  | keysSampled _ =>
    simp only [States.recv] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases hp : m.payload <;> rw [hp] at h <;> try cases h
        obtain ⟨_, _, hret⟩ := except_bind_ok h; cases hret
  | headerSent _ =>
    simp only [States.recv] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases hp : m.payload <;> rw [hp] at h <;> try cases h
        obtain ⟨res, _, hret⟩ := except_bind_ok h; cases res <;> cases hret
  | ct1Received _ =>
    simp only [States.recv] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases hp : m.payload <;> rw [hp] at h <;> try cases h
        obtain ⟨_, _, hret⟩ := except_bind_ok h; cases hret
  | ekSentCt1Received state =>
    simp only [States.recv] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases hp : m.payload with
        | ct2 chunk =>
          rw [hp] at h
          obtain ⟨res, hres, hret⟩ := except_bind_ok h
          cases res with
          | stillReceiving _ => cases hret
          | done p =>
            rcases p with ⟨s1, sec⟩
            cases hret
            unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk
              at hres
            split at hres
            · cases hres
            · obtain ⟨_, _, hres2⟩ := except_bind_ok hres
              obtain ⟨dec?, _, hres3⟩ := except_bind_ok hres2
              cases dec? with
              | none => cases hres3
              | some _ =>
                dsimp only at hres3
                split at hres3
                · cases hres3
                · obtain ⟨⟨uc', sec'⟩, huc, hres4⟩ := except_bind_ok hres3
                  obtain ⟨_, _, hres5⟩ := except_bind_ok hres4
                  cases hres5
                  unfold CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.recv_ct2
                    at huc
                  obtain ⟨_, _, huc2⟩ := except_bind_ok huc
                  obtain ⟨ss1, hss1, huc3⟩ := except_bind_ok huc2
                  obtain ⟨_, _, huc4⟩ := except_bind_ok huc3
                  obtain ⟨vres, _, huc5⟩ := except_bind_ok huc4
                  cases vres with
                  | error _ => cases huc5
                  | ok _ =>
                    dsimp only at huc5
                    split at huc5
                    · cases huc5
                    · cases huc5
                      rw [hkdfToVec32_spqrAuthApi] at hss1
                      cases hss1
                      simp [hkdfToVecUnchecked, hkdfToSliceUnchecked]
        | _ =>
          rw [hp] at h
          cases h
  | noHeaderReceived _ =>
    simp only [States.recv] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases hp : m.payload <;> rw [hp] at h <;> try cases h
        obtain ⟨res, _, hret⟩ := except_bind_ok h; cases res <;> cases hret
  | headerReceived _ =>
    simp only [States.recv] at h; split at h <;> cases h
  | ct1Sampled _ =>
    simp only [States.recv] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases hp : m.payload <;> rw [hp] at h <;> dsimp only at h <;> try cases h
        all_goals
          obtain ⟨res, _, hret⟩ := except_bind_ok h
          cases res <;> cases hret
  | ekReceivedCt1Sampled _ =>
    simp only [States.recv] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases hp : m.payload with
        | ct1Ack b =>
          cases b <;> rw [hp] at h <;> simp only [↓reduceIte, Bool.false_eq_true] at h
          · cases h
          · obtain ⟨_, _, hret⟩ := except_bind_ok h; cases hret
        | ekCt1Ack _ =>
          rw [hp] at h; simp only [↓reduceIte] at h
          obtain ⟨_, _, hret⟩ := except_bind_ok h; cases hret
        | none | hdr _ | ek _ | ct1 _ | ct2 _ =>
          rw [hp] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h; cases h
  | ct1Acknowledged _ =>
    simp only [States.recv] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases hp : m.payload <;> rw [hp] at h <;> dsimp only at h <;> try cases h
        all_goals
          obtain ⟨res, _, hret⟩ := except_bind_ok h
          cases res <;> cases hret
  | ct2Sampled _ =>
    simp only [States.recv] at h
    split at h
    · split at h
      · obtain ⟨_, _, hret⟩ := except_bind_ok h
        cases hret
      · cases h
    · cases h

theorem decode_v1State_of_bOkTight (F : ShaCompress) (K : MlKem) (st : St F)
    (hbok : BOkTight st) :
    V1State.decode (V1State.encodeRaw st.into_pb) = .ok st.into_pb := by
  have htk := v1State_encodeRaw_take64000_of_bOkTight F K st hbok
  have hle : (V1State.encodeRaw st.into_pb).length ≤ 64000 := by
    rw [← htk]
    exact List.length_take_le 64000 _
  exact decode_v1State st.into_pb (Nat.lt_of_le_of_lt hle (by decide))

theorem spqrBraidSendEval_of_bOkTight {ℓ : ℕ} (F : ShaCompress) (K : MlKem)
    (st : St F) (hbok : BOkTight st) (coins : BitVec 512) :
    spqrBraidSendEval (ℓ := ℓ) F K (V1State.encodeRaw st.into_pb) coins =
      match st.send K (coinBytes coins) with
      | .error (.panic _) => (true, none)
      | .error (.err _) => (false, none)
      | .ok (sOut, _) =>
        (false, some (V1State.encodeRaw sOut.state.into_pb,
          (sOut.msg.epoch,
           (sOut.key.map (fun es => (es.epoch, bytesToKey32 es.secret)),
            spqrMsgPayloadSuffix sOut.msg)))) := by
  unfold spqrBraidSendEval
  rw [decode_v1State_of_bOkTight F K st hbok]
  dsimp only
  rw [st_bCodec F st hbok.1]
  dsimp only
  cases hs : st.send K (coinBytes coins) with
  | error err =>
    cases err <;> rfl
  | ok p =>
    rcases p with ⟨⟨m, key, st'⟩, tape'⟩
    dsimp only
    rw [bSendClosed_encodeRaw_take64000 F K hbok hs]

theorem spqrBraidRecvEval_of_bOkTight {ℓ : ℕ} (F : ShaCompress) (K : MlKem)
    (st : St F) (hbok : BOkTight st) (msgEpoch : BitVec 64) (remaining : Bytes) :
    spqrBraidRecvEval (ℓ := ℓ) F K (V1State.encodeRaw st.into_pb) msgEpoch remaining =
      match Message.deserialize spqrPolyApi msgEpoch remaining with
      | .error e => (false, e.isStateDecode, none)
      | .ok sckaMsg =>
        match st.recv K sckaMsg with
        | .error (.panic _) => (true, false, none)
        | .error (.err e) => (false, e.isStateDecode, none)
        | .ok rOut =>
          (false, false, some (rOut.key.map (fun es => (es.epoch, bytesToKey32 es.secret)),
            V1State.encodeRaw rOut.state.into_pb)) := by
  unfold spqrBraidRecvEval
  cases hd : Message.deserialize spqrPolyApi msgEpoch remaining with
  | error e => rfl
  | ok sckaMsg =>
    dsimp only
    rw [decode_v1State_of_bOkTight F K st hbok]
    dsimp only
    rw [st_bCodec F st hbok.1]
    dsimp only
    cases hr : st.recv K sckaMsg with
    | error err =>
      cases err <;> rfl
    | ok rOut =>
      rcases rOut with ⟨key, st'⟩
      dsimp only
      rw [bRecvClosed_encodeRaw_take64000 F K hbok hr]

/-! ## Bounded list combinators -/

private theorem foldr_drop_aux {α : Type} (n : ℕ) :
    ∀ (ys : List α) (off : ℕ),
      ys.foldr (fun y (p : ℕ × List α) =>
        (p.1 - 1, if n ≤ p.1 - 1 then y :: p.2 else p.2)) (off + ys.length, []) =
        (off, ys.drop (n - off))
  | [], off => by simp
  | y :: rest, off => by
    have hlen : off + (y :: rest).length = (off + 1) + rest.length := by
      simp only [List.length_cons]; omega
    simp only [List.foldr_cons, hlen, foldr_drop_aux n rest (off + 1)]
    have hsub1 : (off + 1) - 1 = off := Nat.add_sub_cancel off 1
    rw [hsub1]
    by_cases hle : n ≤ off
    · have h0 : n - off = 0 := Nat.sub_eq_zero_of_le hle
      have h0' : n - (off + 1) = 0 := Nat.sub_eq_zero_of_le (by omega)
      simp [hle, h0, h0']
    · have hgt : n - off = (n - (off + 1)) + 1 := by omega
      simp [hle, hgt]

private theorem foldr_get_aux {α : Type} (idx : ℕ) :
    ∀ (ys : List α) (off : ℕ),
      ys.foldr (fun y (p : ℕ × Option α) =>
        (p.1 - 1, if p.1 - 1 = idx then some y else p.2)) (off + ys.length, none) =
        (off, if off ≤ idx then ys[idx - off]? else none)
  | [], off => by simp
  | y :: rest, off => by
    have hlen : off + (y :: rest).length = (off + 1) + rest.length := by
      simp only [List.length_cons]; omega
    simp only [List.foldr_cons, hlen, foldr_get_aux idx rest (off + 1)]
    have hsub1 : (off + 1) - 1 = off := Nat.add_sub_cancel off 1
    rw [hsub1]
    by_cases heq : off = idx
    · subst heq
      simp
    · by_cases hle : off ≤ idx
      · have hle' : off + 1 ≤ idx := by omega
        have hidx : idx - off = (idx - (off + 1)) + 1 := by omega
        simp [heq, hle, hle', hidx]
      · have hle' : ¬ (off + 1 ≤ idx) := by omega
        simp [heq, hle, hle']

private theorem foldr_set_aux {α : Type} (idx : ℕ) (val : α) :
    ∀ (ys : List α) (off : ℕ),
      ys.foldr (fun y (p : ℕ × List α) =>
        (p.1 - 1, (if p.1 - 1 = idx then val else y) :: p.2)) (off + ys.length, []) =
        (off, if off ≤ idx then ys.set (idx - off) val else ys)
  | [], off => by simp
  | y :: rest, off => by
    have hlen : off + (y :: rest).length = (off + 1) + rest.length := by
      simp only [List.length_cons]; omega
    simp only [List.foldr_cons, hlen, foldr_set_aux idx val rest (off + 1)]
    have hsub1 : (off + 1) - 1 = off := Nat.add_sub_cancel off 1
    rw [hsub1]
    by_cases heq : off = idx
    · subst heq
      have hle' : ¬ (off + 1 ≤ off) := by omega
      simp [hle']
    · by_cases hle : off ≤ idx
      · have hle' : off + 1 ≤ idx := by omega
        have hidx : idx - off = (idx - (off + 1)) + 1 := by omega
        simp [heq, hle, hle', hidx]
      · have hle' : ¬ (off + 1 ≤ idx) := by omega
        simp [heq, hle, hle']

/-- Computes `l.drop n` in `Expr` on lists of length at most `K`. -/
def listDropExpr {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {t : Ty (e2eSig ℓ)} (K : ℕ) (n : Expr O Γ .nat) (l : Expr O Γ (.list t)) :
    Expr O Γ (.list t) :=
  .letE (.pair n l)
    (.snd (.foldrB K (.snd .v0)
      (.pair (.len (.take (.nat K) (.snd .v0))) .nil)
      (.letE (.sub (.fst .v1) (.nat 1))
        (.pair .v0 (.ite (.not (.lt .v0 (.fst .v3))) (.cons .v1 (.snd .v2)) (.snd .v2))))))

theorem eval_listDropExpr {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {t : Ty (e2eSig ℓ)} (K : ℕ) (n : Expr O Γ .nat) (l : Expr O Γ (.list t)) (ρ : Env Γ)
    (hlen : (l.eval ρ).length ≤ K) :
    (listDropExpr K n l).eval ρ = (l.eval ρ).drop (n.eval ρ) := by
  simp only [listDropExpr, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Env.get,
    List.take_of_length_le hlen]
  have h := foldr_drop_aux (n.eval ρ) (l.eval ρ) 0
  rw [Nat.zero_add, Nat.sub_zero] at h
  have hcongr :
      (l.eval ρ).foldr
        (fun x acc =>
          (acc.1 - 1, if (!decide (acc.1 - 1 < n.eval ρ)) = true then x :: acc.2 else acc.2))
        ((l.eval ρ).length, []) =
      (l.eval ρ).foldr
        (fun y (p : ℕ × List t.denote) =>
          (p.1 - 1, if n.eval ρ ≤ p.1 - 1 then y :: p.2 else p.2))
        ((l.eval ρ).length, []) := by
    congr 1
    funext y p
    have hb : ((!decide (p.1 - 1 < n.eval ρ)) = true) ↔ n.eval ρ ≤ p.1 - 1 := by
      simp
    by_cases hc : n.eval ρ ≤ p.1 - 1 <;> simp [hb, hc]
  rw [hcongr, h]

/-- Computes `l[idx]?` in `Expr` on lists of length at most `K`. -/
def listGetExpr {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {t : Ty (e2eSig ℓ)} (K : ℕ) (idx : Expr O Γ .nat) (l : Expr O Γ (.list t)) :
    Expr O Γ (.opt t) :=
  .letE (.pair idx l)
    (.snd (.foldrB K (.snd .v0)
      (.pair (.len (.take (.nat K) (.snd .v0))) .none)
      (.letE (.sub (.fst .v1) (.nat 1))
        (.pair .v0 (.ite (.eqN .v0 (.fst .v3)) (.some .v1) (.snd .v2))))))

theorem eval_listGetExpr {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {t : Ty (e2eSig ℓ)} (K : ℕ) (idx : Expr O Γ .nat) (l : Expr O Γ (.list t)) (ρ : Env Γ)
    (hlen : (l.eval ρ).length ≤ K) :
    (listGetExpr K idx l).eval ρ = (l.eval ρ)[idx.eval ρ]? := by
  simp only [listGetExpr, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Env.get,
    List.take_of_length_le hlen]
  have h := foldr_get_aux (idx.eval ρ) (l.eval ρ) 0
  simp only [Nat.zero_add, Nat.zero_le, ↓reduceIte, Nat.sub_zero] at h
  have hcongr :
      (l.eval ρ).foldr
        (fun x acc =>
          (acc.1 - 1, if decide (acc.1 - 1 = idx.eval ρ) = true then some x else acc.2))
        ((l.eval ρ).length, none) =
      (l.eval ρ).foldr
        (fun y (p : ℕ × Option t.denote) =>
          (p.1 - 1, if p.1 - 1 = idx.eval ρ then some y else p.2))
        ((l.eval ρ).length, none) := by
    congr 1
    funext y p
    by_cases hc : p.1 - 1 = idx.eval ρ <;> simp [hc]
  rw [hcongr, h]

/-- Computes `l.set idx val` in `Expr` on lists of length at most `K`. -/
def listSetExpr {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {t : Ty (e2eSig ℓ)} (K : ℕ) (idx : Expr O Γ .nat) (val : Expr O Γ t)
    (l : Expr O Γ (.list t)) : Expr O Γ (.list t) :=
  .letE (.pair idx (.pair val l))
    (.snd (.foldrB K (.snd (.snd .v0))
      (.pair (.len (.take (.nat K) (.snd (.snd .v0)))) .nil)
      (.letE (.sub (.fst .v1) (.nat 1))
        (.pair .v0 (.cons (.ite (.eqN .v0 (.fst .v3)) (.fst (.snd .v3)) .v1) (.snd .v2))))))

theorem eval_listSetExpr {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {t : Ty (e2eSig ℓ)} (K : ℕ) (idx : Expr O Γ .nat) (val : Expr O Γ t)
    (l : Expr O Γ (.list t)) (ρ : Env Γ)
    (hlen : (l.eval ρ).length ≤ K) :
    (listSetExpr K idx val l).eval ρ = (l.eval ρ).set (idx.eval ρ) (val.eval ρ) := by
  simp only [listSetExpr, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Env.get,
    List.take_of_length_le hlen]
  have h := foldr_set_aux (idx.eval ρ) (val.eval ρ) (l.eval ρ) 0
  simp only [Nat.zero_add, Nat.zero_le, ↓reduceIte, Nat.sub_zero] at h
  have hcongr :
      (l.eval ρ).foldr
        (fun x acc =>
          (acc.1 - 1,
            (if decide (acc.1 - 1 = idx.eval ρ) = true then val.eval ρ else x) :: acc.2))
        ((l.eval ρ).length, []) =
      (l.eval ρ).foldr
        (fun y (p : ℕ × List t.denote) =>
          (p.1 - 1, (if p.1 - 1 = idx.eval ρ then val.eval ρ else y) :: p.2))
        ((l.eval ρ).length, []) := by
    congr 1
    funext y p
    by_cases hc : p.1 - 1 = idx.eval ρ <;> simp [hc]
  rw [hcongr, h]

/-! ## Chain resolution, `addEpoch`, and `Chain.sendKey` -/

def spqrEpochIdxExpr {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (curEp : Expr (e2eOps ℓ P C K decT encT) Γ U64)
    (linksLen : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (epoch : Expr (e2eOps ℓ P C K decT encT) Γ U64) :
    Expr (e2eOps ℓ P C K decT encT) Γ (.opt .nat) :=
  .letE (.pair curEp (.pair linksLen epoch))
    (.ite (e2ePureOp .u64Lt (.pair (.fst .v0) (.snd (.snd .v0))))
      .none
      (.letE (e2ePureOp .u64ToNat (e2ePureOp .u64Sub (.pair (.fst .v0) (.snd (.snd .v0)))))
        (.ite (.lt .v0 (.fst (.snd .v1)))
          (.some (.sub (.sub (.fst (.snd .v1)) (.nat 1)) .v0))
          .none)))

theorem eval_spqrEpochIdxExpr {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (curEp : Expr (e2eOps ℓ P C K decT encT) Γ U64)
    (linksLen : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (epoch : Expr (e2eOps ℓ P C K decT encT) Γ U64)
    (ρ : Env Γ) (ch : Chain)
    (hcur : curEp.eval ρ = ch.currentEpoch)
    (hlen : linksLen.eval ρ = ch.links.length) :
    (spqrEpochIdxExpr curEp linksLen epoch).eval ρ =
      (ch.epochIdx (epoch.eval ρ)).toOption := by
  simp only [spqrEpochIdxExpr, Expr.eval, eval_e2ePureOp, E2EPureOp.eval,
    Expr.v0, Expr.v1, Env.get, hcur, hlen, Chain.epochIdx, gt_iff_lt]
  by_cases hgt : ch.currentEpoch < epoch.eval ρ
  · simp [hgt, Except.toOption]
  · simp only [hgt, decide_false, Bool.false_eq_true, ↓reduceIte]
    by_cases hlt : (ch.currentEpoch - epoch.eval ρ).toNat < ch.links.length
    · have hge : ¬ ((ch.currentEpoch - epoch.eval ρ).toNat ≥ ch.links.length) := by omega
      simp only [hlt, decide_true, ↓reduceIte, hge, Except.toOption]
    · have hge : (ch.currentEpoch - epoch.eval ρ).toNat ≥ ch.links.length := by omega
      simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte, hge, Except.toOption]

def spqrResolveChainComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (vn? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt spqrVnT))
    (ch? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt spqrChainT)) :
    Comp (e2eOps ℓ P C K decT encT) I Γ (.opt spqrChainT) :=
  .caseOpt ch?
    (.caseOpt vn? (.ret .none) (spqrChainFromVnC I .v0))
    (.ret (.some .v0))

theorem queries_spqrResolveChainComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (vn? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt spqrVnT))
    (ch? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt spqrChainT)) :
    (spqrResolveChainComp I vn? ch?).queries w ws = 0 := by
  simp [spqrResolveChainComp, Comp.queries]

theorem eval_spqrResolveChainComp_topStateTightW {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (vnExpr : Expr (e2eOps ℓ P C K decT encT) Γ (.opt spqrVnT))
    (chExpr : Expr (e2eOps ℓ P C K decT encT) Γ (.opt spqrChainT))
    (ρ : Env Γ) {bytes : Bytes} {w : TopWitness C.F} (hw : TopStateTightW C.F K bytes w)
    (hvn : vnExpr.eval ρ = w.vn?.map (spqrVnToV (ℓ := ℓ)))
    (hch : chExpr.eval ρ = (w.ch?.map Chain.intoPb).map (spqrChainToV (ℓ := ℓ))) :
    (spqrResolveChainComp I vnExpr chExpr).eval ρ =
      pure (some (spqrChainToV (ℓ := ℓ) w.chE.intoPb)) := by
  simp only [spqrResolveChainComp]
  rcases hw.htop.hch with hch_some | ⟨hch_none, hvn_some, hcf⟩
  · simp only [Comp.eval, hch, hch_some, Option.map_some, Expr.eval, Expr.v0, Env.get]
  · simp only [Comp.eval, hch, hch_none, Option.map_none, hvn, hvn_some, Option.map_some,
      eval_spqrChainFromVnC, Expr.eval, Expr.v0, Env.get, spqrChainFromVnEval]
    have hrt : spqrVnOfV (spqrVnToV (ℓ := ℓ) (vnOf w.dir w.authKey)) = vnOf w.dir w.authKey := by
      apply spqrVn_roundtrip
      simp [vnOf, hw.hauth]
    rw [hrt, hcf]

def spqrAddEpochOptComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (ch : Expr (e2eOps ℓ P C K decT encT) Γ spqrChainT)
    (epSec? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (.prod U64 BV256))) :
    Comp (e2eOps ℓ P C K decT encT) I Γ (.opt spqrChainT) :=
  .bind (.ret (.pair ch epSec?))
    (.caseOpt (.snd .v0)
      (.ret (.some (.fst .v0)))
      (.bind (spqrChainAddEpochC I (.pair (.fst .v1) .v0))
        (.ret (.snd .v0))))

theorem queries_spqrAddEpochOptComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (ch : Expr (e2eOps ℓ P C K decT encT) Γ spqrChainT)
    (epSec? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (.prod U64 BV256))) :
    (spqrAddEpochOptComp I ch epSec?).queries w ws = 0 := by
  simp [spqrAddEpochOptComp, Comp.queries]

theorem eval_spqrAddEpochOptComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (chExpr : Expr (e2eOps ℓ P C K decT encT) Γ spqrChainT)
    (epSecExpr : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (.prod U64 BV256)))
    (ρ : Env Γ) (authKey : Bytes) (dir : Direction) (secret : ℕ → Bytes) (sendCtr : ℕ → ℕ)
    (recvSet : ℕ → Finset ℕ) (chE : Chain) (key : Option EpochSecret)
    (hok : ChainOk C.F authKey dir secret sendCtr recvSet chE)
    (hsp : SendPrevNil chE) (hsmall : RecvSmallTight chE)
    (hlen3 : chE.links.length ≤ 3)
    (hch : chExpr.eval ρ = spqrChainToV (ℓ := ℓ) chE.intoPb)
    (hkey : epSecExpr.eval ρ = key.map (fun es => (es.epoch, bytesToKey32 es.secret)))
    (hsec_len : ∀ es, key = some es → es.secret.length = 32) :
    (spqrAddEpochOptComp I chExpr epSecExpr).eval ρ =
      pure (match key with
        | none => some (spqrChainToV (ℓ := ℓ) chE.intoPb)
        | some es =>
          match chE.addEpoch (spqrHkdfWith C.F) es with
          | .ok ch1 => some (spqrChainToV (ℓ := ℓ) ch1.intoPb)
          | .error _ => none) := by
  simp only [spqrAddEpochOptComp]
  cases key with
  | none =>
    simp [Comp.eval, Expr.eval, Expr.v0, Env.get, hkey, hch]
  | some es =>
    have hes32 : es.secret.length = 32 := hsec_len es rfl
    have hrt : spqrChainOfV (spqrChainToV (ℓ := ℓ) chE.intoPb) = chE.intoPb :=
      spqrChain_roundtrip_chainOk C.F authKey dir secret sendCtr recvSet chE hok hsp hsmall
        (by omega)
    have hfpb := chain_fromPb_intoPb C.F authKey dir secret sendCtr recvSet chE hok
    simp only [Comp.eval, hkey, Option.map_some, eval_spqrChainAddEpochC, Expr.eval,
      Expr.v0, Expr.v1, Env.get, hch, pure_bind, spqrChainAddEpochEval, hrt, hfpb,
      keyToBytes32_bytesToKey32 es.secret hes32]
    cases es
    cases chE.addEpoch (spqrHkdfWith C.F) _ <;> rfl

def clearLinkSendNext {ℓ : ℕ} (lk : (spqrEpochLinkT (ℓ := ℓ)).denote) :
    (spqrEpochLinkT (ℓ := ℓ)).denote :=
  (lk.1.map (fun s => (s.1, ([], s.2.2))), lk.2)

def clearLinkSendNextExpr {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (lk : Expr (e2eOps ℓ P C K decT encT) Γ spqrEpochLinkT) :
    Expr (e2eOps ℓ P C K decT encT) Γ spqrEpochLinkT :=
  .letE lk
    (.pair
      (.caseOpt (.fst .v0)
        .none
        (.some (.pair (.fst .v0) (.pair (e2ePureOp (.bytesLit 32 []) .unit) (.snd (.snd .v0))))))
      (.snd .v0))

theorem eval_clearLinkSendNextExpr {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (lk : Expr (e2eOps ℓ P C K decT encT) Γ spqrEpochLinkT) (ρ : Env Γ) :
    (clearLinkSendNextExpr lk).eval ρ = clearLinkSendNext (lk.eval ρ) := by
  rcases h : lk.eval ρ with ⟨s?, r?⟩
  cases s? <;> simp [clearLinkSendNextExpr, clearLinkSendNext, h, Expr.eval, eval_e2ePureOp,
    E2EPureOp.eval, Expr.v0, Env.get]

def clearSendPrefixV {ℓ : ℕ} :
    ℕ → List (spqrEpochLinkT (ℓ := ℓ)).denote → List (spqrEpochLinkT (ℓ := ℓ)).denote
  | 0, xs => xs
  | _ + 1, [] => []
  | n + 1, x :: xs => clearLinkSendNext x :: clearSendPrefixV n xs

private theorem foldr_clearSendPrefix_aux {ℓ : ℕ} (n : ℕ) :
    ∀ (ys : List (spqrEpochLinkT (ℓ := ℓ)).denote) (off : ℕ),
      ys.foldr (fun y (p : ℕ × List (spqrEpochLinkT (ℓ := ℓ)).denote) =>
        (p.1 - 1, (if p.1 - 1 < n then clearLinkSendNext y else y) :: p.2))
        (off + ys.length, []) =
        (off, clearSendPrefixV (n - off) ys)
  | [], off => by
    cases hn : n - off <;> simp [clearSendPrefixV]
  | y :: rest, off => by
    have hlen : off + (y :: rest).length = (off + 1) + rest.length := by
      simp only [List.length_cons]; omega
    simp only [List.foldr_cons, hlen, foldr_clearSendPrefix_aux n rest (off + 1)]
    have hsub1 : (off + 1) - 1 = off := Nat.add_sub_cancel off 1
    rw [hsub1]
    by_cases hlt : off < n
    · have hn : n - off = (n - (off + 1)) + 1 := by omega
      simp [hlt, hn, clearSendPrefixV]
    · have hn0 : n - off = 0 := by omega
      have hn0' : n - (off + 1) = 0 := by omega
      simp [hlt, hn0, hn0', clearSendPrefixV]

def linksClearSendPrefixExpr {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (n : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (links : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrEpochLinkT)) :
    Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrEpochLinkT) :=
  .letE (.pair n links)
    (.snd (.foldrB 4 (.snd .v0)
      (.pair (.len (.take (.nat 4) (.snd .v0))) .nil)
      (.letE (.sub (.fst .v1) (.nat 1))
        (.pair .v0
          (.cons (.ite (.lt .v0 (.fst .v3)) (clearLinkSendNextExpr .v1) .v1) (.snd .v2))))))

private theorem clearSendPrefixV_map_intoPb {ℓ : ℕ} :
    ∀ (n : ℕ) (lks : List ChainEpoch),
      clearSendPrefixV n
        (lks.map (fun lk =>
          (some (spqrDirToV (ℓ := ℓ) lk.send.intoPb),
           some (spqrDirToV (ℓ := ℓ) lk.recv.intoPb)))) =
      (Chain.clearSendNextPrefix n lks).map (fun lk =>
        (some (spqrDirToV (ℓ := ℓ) lk.send.intoPb),
         some (spqrDirToV (ℓ := ℓ) lk.recv.intoPb)))
  | 0, lks => rfl
  | _ + 1, [] => rfl
  | n + 1, lk :: rest => by
    simp only [List.map_cons, Chain.clearSendNextPrefix, clearSendPrefixV,
      clearSendPrefixV_map_intoPb n rest, List.cons.injEq, and_true]
    simp [clearLinkSendNext, ChainEpochDirection.clearNext, ChainEpochDirection.intoPb, spqrDirToV]

theorem eval_linksClearSendPrefixExpr {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (n : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (links : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrEpochLinkT))
    (ρ : Env Γ) (hlen : (links.eval ρ).length ≤ 4) :
    (linksClearSendPrefixExpr n links).eval ρ =
      clearSendPrefixV (n.eval ρ) (links.eval ρ) := by
  simp only [linksClearSendPrefixExpr, Expr.eval, eval_clearLinkSendNextExpr,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Env.get, List.take_of_length_le hlen]
  have h := foldr_clearSendPrefix_aux (ℓ := ℓ) (n.eval ρ) (links.eval ρ) 0
  rw [Nat.zero_add, Nat.sub_zero] at h
  have hcongr :
      (links.eval ρ).foldr
        (fun x acc =>
          (acc.1 - 1,
            (if decide (acc.1 - 1 < n.eval ρ) = true then clearLinkSendNext x else x) :: acc.2))
        ((links.eval ρ).length, []) =
      (links.eval ρ).foldr
        (fun y (p : ℕ × List (spqrEpochLinkT (ℓ := ℓ)).denote) =>
          (p.1 - 1, (if p.1 - 1 < n.eval ρ then clearLinkSendNext y else y) :: p.2))
        ((links.eval ρ).length, []) := by
    congr 1
    funext y p
    by_cases hc : p.1 - 1 < n.eval ρ <;> simp [hc]
  rw [hcongr, h]

/-- Simulates `Chain.sendKey` on `(ch, epoch)` in `ReductionDsl`. -/
def spqrChainSendKeyComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (ch : Expr (e2eOps ℓ P C K decT encT) Γ spqrChainT)
    (epoch : Expr (e2eOps ℓ P C K decT encT) Γ U64) :
    Comp (e2eOps ℓ P C K decT encT) I Γ
      (.opt (.prod spqrChainT (.prod U32 BV256))) :=
  .bind (.ret (.pair ch epoch))
    (.ite (e2ePureOp .u64Lt
        (.pair (.snd .v0) (.fst (.snd (.snd (.snd (.snd (.fst .v0))))))))
      (.ret .none)
      (.caseOpt
        (spqrEpochIdxExpr
          (.fst (.snd (.fst .v0)))
          (.len (.fst (.snd (.snd (.fst .v0)))))
          (.snd .v0))
        (.ret .none)
        (.bind (.ret
          (.ite (e2ePureOp .u64Eq
              (.pair (.fst (.snd (.snd (.snd (.snd (.fst .v1)))))) (.snd .v1)))
            (.pair (.fst (.snd (.snd (.snd (.snd (.fst .v1))))))
              (.pair (.fst (.snd (.snd (.fst .v1)))) .v0))
            (.letE (.sub .v0 (.nat 1))
              (.letE (.sub .v1 .v0)
                (.pair (.snd .v3)
                  (.pair
                    (linksClearSendPrefixExpr .v0
                      (listDropExpr 4 .v1 (.fst (.snd (.snd (.fst .v3))))))
                    .v0))))))
          (.caseOpt (listGetExpr 4 (.snd (.snd .v0)) (.fst (.snd .v0)))
            (.ret .none)
            (.caseOpt (.fst .v0)
              (.ret .none)
              (.bind (spqrChainNextKeyC I (.pair (.fst (.snd .v0)) (.fst .v0)))
                (.caseOpt (.snd .v0)
                  (.ret .none)
                  (.ret (.some (.pair
                    (.pair (.fst (.fst .v6))
                      (.pair (.fst (.snd (.fst .v6)))
                        (.pair
                          (listSetExpr 4 (.snd (.snd .v4))
                            (.pair (.some (.pair (.fst (.snd .v0))
                              (.pair (.fst .v0) (.snd (.snd .v2)))))
                              (.snd .v3))
                            (.fst (.snd .v4)))
                          (.pair (.fst (.snd (.snd (.snd (.fst .v6)))))
                            (.pair (.fst .v4)
                              (.snd (.snd (.snd (.snd (.snd (.fst .v6)))))))))))
                    (.snd .v0)))))))))))

theorem queries_spqrChainSendKeyComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (ch : Expr (e2eOps ℓ P C K decT encT) Γ spqrChainT)
    (epoch : Expr (e2eOps ℓ P C K decT encT) Γ U64) :
    (spqrChainSendKeyComp I ch epoch).queries w ws = 0 := by
  simp [spqrChainSendKeyComp, Comp.queries]

private theorem spqrChainToV_links_eq {ℓ : ℕ} (ch : Chain) (hlen4 : ch.links.length ≤ 4) :
    (spqrChainToV (ℓ := ℓ) ch.intoPb).2.2.1 =
      ch.links.map (fun lk =>
        (some (spqrDirToV (ℓ := ℓ) lk.send.intoPb),
         some (spqrDirToV (ℓ := ℓ) lk.recv.intoPb))) := by
  dsimp only [spqrChainToV, Chain.intoPb]
  rw [List.take_of_length_le (by simpa using hlen4), List.map_map]
  rfl

private theorem clearSendNextPrefix_length :
    ∀ (m : ℕ) (xs : List ChainEpoch),
      (Chain.clearSendNextPrefix m xs).length = xs.length
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | m + 1, _ :: xs => by
    simp [Chain.clearSendNextPrefix, clearSendNextPrefix_length m xs]

private theorem clearSendNextPrefix_next_le :
    ∀ (m : ℕ) (xs : List ChainEpoch),
      (∀ x ∈ xs, x.send.next.length ≤ 64) →
      ∀ x ∈ Chain.clearSendNextPrefix m xs, x.send.next.length ≤ 64
  | 0, _, hx => hx
  | _ + 1, [], _ => by intro x hx; cases hx
  | m + 1, _ :: ys, hy => by
    intro x hx
    simp only [Chain.clearSendNextPrefix, List.mem_cons] at hx
    rcases hx with rfl | hx_tail
    · simp [ChainEpochDirection.clearNext]
    · exact clearSendNextPrefix_next_le m ys (fun z hz => hy z (List.mem_cons_of_mem _ hz)) x hx_tail

private def sendKeyPrep (self : Chain) (epoch : BitVec 64) (epochIndex0 : ℕ) : Chain × ℕ :=
  if self.sendEpoch != epoch then
    let dropCount := epochIndex0 - CryptoVerification.LibsignalSpqrV1.EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH
    let epochIndex' := epochIndex0 - dropCount
    let links1 := self.links.drop dropCount
    let links2 := Chain.clearSendNextPrefix epochIndex' links1
    ({ self with sendEpoch := epoch, links := links2 }, epochIndex')
  else
    (self, epochIndex0)

private theorem chain_sendKey_option_eq {ℓ : ℕ} (hkdf : CryptoVerification.LibsignalSpqrV1.HkdfFn)
    (self : Chain) (epoch : BitVec 64) :
    (match self.sendKey hkdf epoch with
      | .ok (ch', (idx, mkBytes)) =>
        some (spqrChainToV (ℓ := ℓ) ch'.intoPb, (idx, bytesToKey32 mkBytes))
      | .error _ => none) =
    if epoch < self.sendEpoch then
      none
    else
      match self.epochIdx epoch with
      | .error _ => none
      | .ok epochIndex0 =>
        let prep := sendKeyPrep self epoch epochIndex0
        match prep.1.links[prep.2]? with
        | none => none
        | some link =>
          match link.send.nextKey hkdf with
          | .error _ => none
          | .ok (send', (idx, mkBytes)) =>
            some (spqrChainToV (ℓ := ℓ)
              ({ prep.1 with links := prep.1.links.set prep.2 { link with send := send' } } : Chain).intoPb,
              (idx, bytesToKey32 mkBytes)) := by
  unfold Chain.sendKey sendKeyPrep
  by_cases hlt : epoch < self.sendEpoch
  · simp [hlt]
  · simp only [hlt, ↓reduceIte]
    cases self.epochIdx epoch with
    | error _ => rfl
    | ok epochIndex0 =>
      dsimp only [ChainResult.ofError, Bind.bind, Except.bind]
      let dc := epochIndex0 - CryptoVerification.LibsignalSpqrV1.EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH
      let ei' := epochIndex0 - dc
      by_cases hne : self.sendEpoch != epoch <;> simp only [hne, ↓reduceIte, Bool.false_eq_true]
      · cases (Chain.clearSendNextPrefix ei' (self.links.drop dc))[ei']? with
        | none => rfl
        | some link =>
          dsimp only
          rcases link.send.nextKey hkdf with _ | ⟨_, _, _⟩ <;> rfl
      · cases self.links[epochIndex0]? with
        | none => rfl
        | some link =>
          dsimp only
          rcases link.send.nextKey hkdf with _ | ⟨_, _, _⟩ <;> rfl

theorem eval_spqrChainSendKeyComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (chExpr : Expr (e2eOps ℓ P C K decT encT) Γ spqrChainT)
    (epExpr : Expr (e2eOps ℓ P C K decT encT) Γ U64)
    (ρ : Env Γ) (ch : Chain)
    (hlen4 : ch.links.length ≤ 4)
    (hnext : ∀ lk ∈ ch.links, lk.send.next.length ≤ 64)
    (hch : chExpr.eval ρ = spqrChainToV (ℓ := ℓ) ch.intoPb) :
    (spqrChainSendKeyComp I chExpr epExpr).eval ρ =
      pure (match ch.sendKey (spqrHkdfWith C.F) (epExpr.eval ρ) with
        | .ok (ch', (idx, mkBytes)) =>
          some (spqrChainToV (ℓ := ℓ) ch'.intoPb, (idx, bytesToKey32 mkBytes))
        | .error _ => none) := by
  have hlks_eq := spqrChainToV_links_eq (ℓ := ℓ) ch hlen4
  have hcur_eq : (spqrChainToV (ℓ := ℓ) ch.intoPb).2.1 = ch.currentEpoch := rfl
  have hsend_eq : (spqrChainToV (ℓ := ℓ) ch.intoPb).2.2.2.2.1 = ch.sendEpoch := rfl
  have hdir_eq : (spqrChainToV (ℓ := ℓ) ch.intoPb).1 = ch.dir.toI32 := rfl
  have hroot_eq : (spqrChainToV (ℓ := ℓ) ch.intoPb).2.2.2.1 = ch.nextRoot.take 64 := rfl
  have hpar_eq : (spqrChainToV (ℓ := ℓ) ch.intoPb).2.2.2.2.2 =
      some (spqrParamsToV ch.params) := rfl
  simp only [spqrChainSendKeyComp, Comp.eval, Expr.eval, eval_e2ePureOp, E2EPureOp.eval,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v6, Env.get, hch, pure_bind,
    hsend_eq]
  generalize epExpr.eval ρ = ep
  refine Eq.trans ?_
    (congrArg pure (chain_sendKey_option_eq (ℓ := ℓ) (spqrHkdfWith C.F) ch ep)).symm
  by_cases hlt : ep < ch.sendEpoch
  · simp [hlt]
  · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hlks_len : ((spqrChainToV (ℓ := ℓ) ch.intoPb).2.2.1).length = ch.links.length := by
      rw [hlks_eq, List.length_map]
    have heidx :
        (spqrEpochIdxExpr (Pt := Pt) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
          (.fst (.snd (.fst (Expr.var Var.zero))))
          (.len (.fst (.snd (.snd (.fst (Expr.var Var.zero))))))
          (.snd (Expr.var Var.zero))).eval
            (Env.cons (t := .prod spqrChainT U64) (spqrChainToV (ℓ := ℓ) ch.intoPb, ep) ρ) =
          (ch.epochIdx ep).toOption := by
      apply eval_spqrEpochIdxExpr
      · exact hcur_eq
      · simpa [Expr.eval, Env.get] using hlks_len
    rw [heidx]
    cases hepIdx : ch.epochIdx ep with
    | error _ =>
      simp [Except.toOption]
    | ok epochIndex0 =>
      dsimp only [Except.toOption]
      have hlks_le4 : ((spqrChainToV (ℓ := ℓ) ch.intoPb).2.2.1).length ≤ 4 := by
        rw [hlks_len]; exact hlen4
      let fLink : ChainEpoch → (spqrEpochLinkT (ℓ := ℓ)).denote := fun lk =>
        (some (spqrDirToV (ℓ := ℓ) lk.send.intoPb),
         some (spqrDirToV (ℓ := ℓ) lk.recv.intoPb))
      let ρBase : Env (.prod spqrChainT U64 :: Γ) :=
        Env.cons (t := .prod spqrChainT U64) (spqrChainToV (ℓ := ℓ) ch.intoPb, ep) ρ
      let ρEp0 : Env (.nat :: .prod spqrChainT U64 :: Γ) :=
        Env.cons (t := .nat) epochIndex0 ρBase
      let self1 := (sendKeyPrep ch ep epochIndex0).1
      let epochIndex := (sendKeyPrep ch ep epochIndex0).2
      have hprep_props :
          self1.dir = ch.dir ∧
          self1.currentEpoch = ch.currentEpoch ∧
          self1.nextRoot = ch.nextRoot ∧
          self1.params = ch.params ∧
          self1.links.length ≤ 4 ∧
          (∀ lk ∈ self1.links, lk.send.next.length ≤ 64) ∧
          (if (ch.sendEpoch == ep) = true then
            (ch.sendEpoch, ((spqrChainToV (ℓ := ℓ) ch.intoPb).2.2.1, epochIndex0))
          else
            (ep,
             ((linksClearSendPrefixExpr (Pt := Pt) (P := P) (C := C) (K := K)
                (decT := decT) (encT := encT) (Expr.var Var.zero)
                (listDropExpr 4 (Expr.var Var.zero.succ)
                  (.fst (.snd (.snd (.fst (Expr.var Var.zero.succ.succ.succ))))))).eval
                (Env.cons (t := .nat) (epochIndex0 - (epochIndex0 - 1))
                  (Env.cons (t := .nat) (epochIndex0 - 1) ρEp0)),
              epochIndex0 - (epochIndex0 - 1)))) =
            (self1.sendEpoch, (self1.links.map fLink, epochIndex)) := by
        dsimp only [self1, epochIndex, sendKeyPrep]
        by_cases heq_ep : ch.sendEpoch == ep
        · have hne_ep : (ch.sendEpoch != ep) = false := by
            cases h : ch.sendEpoch == ep <;> simp_all
          simp only [hne_ep, heq_ep, Bool.false_eq_true, ↓reduceIte, true_and]
          exact ⟨hlen4, hnext, by rw [hlks_eq]⟩
        · have hne_ep : (ch.sendEpoch != ep) = true := by
            cases h : ch.sendEpoch == ep <;> simp_all
          let dropCount := epochIndex0 - 1
          let epochIndex' := epochIndex0 - dropCount
          let links1 := ch.links.drop dropCount
          let links2 := Chain.clearSendNextPrefix epochIndex' links1
          have hlen1 : links1.length ≤ 4 := by
            simp only [links1, List.length_drop]
            omega
          have hlen2 : links2.length ≤ 4 := by
            dsimp only [links2]
            rw [clearSendNextPrefix_length]
            exact hlen1
          have hnext2 : ∀ lk ∈ links2, lk.send.next.length ≤ 64 :=
            clearSendNextPrefix_next_le epochIndex' links1
              (fun z hz => hnext z (List.mem_of_mem_drop hz))
          simp only [hne_ep, heq_ep, Bool.false_eq_true, ↓reduceIte,
            CryptoVerification.LibsignalSpqrV1.EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH]
          refine ⟨trivial, trivial, trivial, trivial, hlen2, hnext2, ?_⟩
          let ρClr : Env (.nat :: .nat :: .nat :: .prod spqrChainT U64 :: Γ) :=
            Env.cons (t := .nat) epochIndex' (Env.cons (t := .nat) dropCount ρEp0)
          have hdrop_eval :
              (listDropExpr (O := e2eOps ℓ P C K decT encT) 4 (Expr.var Var.zero.succ)
                (.fst (.snd (.snd (.fst (Expr.var Var.zero.succ.succ.succ)))))).eval ρClr =
                links1.map fLink := by
            rw [eval_listDropExpr (O := e2eOps ℓ P C K decT encT) 4 _ _ ρClr
              (by simpa [ρClr, ρEp0, ρBase, Expr.eval, Env.get] using hlks_le4)]
            simp only [ρClr, ρEp0, ρBase, Expr.eval, Env.get, hlks_eq, ← List.map_drop]
            rfl
          have hclr_eval :
              (linksClearSendPrefixExpr (Pt := Pt) (P := P) (C := C) (K := K)
                (decT := decT) (encT := encT) (Expr.var Var.zero)
                (listDropExpr 4 (Expr.var Var.zero.succ)
                  (.fst (.snd (.snd (.fst (Expr.var Var.zero.succ.succ.succ))))))).eval ρClr =
                links2.map fLink := by
            rw [eval_linksClearSendPrefixExpr _ _ ρClr
              (by rw [hdrop_eval, List.length_map]; exact hlen1)]
            rw [hdrop_eval]
            simpa [ρClr, Expr.eval, Env.get, fLink] using
              clearSendPrefixV_map_intoPb (ℓ := ℓ) epochIndex' links1
          exact congrArg (fun l => (ep, (l, epochIndex'))) hclr_eval
      obtain ⟨hdir1, hcur1, hroot1, hpar1, hlen_self1, hnext_self1, hval1⟩ := hprep_props
      dsimp only [ρEp0, ρBase] at hval1
      rw [hval1]
      let ρMid : Env (.prod U64 (.prod (.list spqrEpochLinkT) .nat) ::
          .nat :: .prod spqrChainT U64 :: Γ) :=
        Env.cons (t := .prod U64 (.prod (.list spqrEpochLinkT) .nat))
          (self1.sendEpoch, (self1.links.map fLink, epochIndex)) ρEp0
      have hget_eval :
          (listGetExpr (O := e2eOps ℓ P C K decT encT) 4
            (.snd (.snd (Expr.var Var.zero)))
            (.fst (.snd (Expr.var Var.zero)))).eval ρMid =
            (self1.links[epochIndex]?).map fLink := by
        rw [eval_listGetExpr (O := e2eOps ℓ P C K decT encT) 4 _ _ ρMid
          (by simp only [ρMid, Expr.eval, Env.get, List.length_map]; exact hlen_self1)]
        simp [ρMid, Expr.eval, Env.get, List.getElem?_map]
      dsimp only [ρMid, ρEp0, ρBase] at hget_eval
      rw [hget_eval]
      change _ = pure (match self1.links[epochIndex]? with
        | none => none
        | some link =>
          match link.send.nextKey (spqrHkdfWith C.F) with
          | .error _ => none
          | .ok (send', (idx, mkBytes)) =>
            some (spqrChainToV (ℓ := ℓ)
              ({ self1 with links := self1.links.set epochIndex { link with send := send' } } : Chain).intoPb,
              (idx, bytesToKey32 mkBytes)))
      cases hlk : self1.links[epochIndex]? with
      | none => rfl
      | some link =>
        have hlk_mem : link ∈ self1.links := List.mem_of_getElem? hlk
        have hlk_next64 : link.send.next.length ≤ 64 := hnext_self1 link hlk_mem
        have hnext_take : link.send.next.take 64 = link.send.next :=
          List.take_of_length_le hlk_next64
        dsimp only [Option.map]
        have hflk1 : (fLink link).1 =
            some (link.send.ctr, (link.send.next, splitSpqrPrev 2201 link.send.prev.data)) := by
          simp [fLink, ChainEpochDirection.intoPb, spqrDirToV, hnext_take]
        have hflk_eq : fLink link =
            (some (link.send.ctr, (link.send.next, splitSpqrPrev 2201 link.send.prev.data)),
             some (spqrDirToV (ℓ := ℓ) link.recv.intoPb)) := by
          simp [fLink, ChainEpochDirection.intoPb, spqrDirToV, hnext_take]
        rw [hflk_eq]
        dsimp only
        rw [eval_spqrChainNextKeyC]
        simp only [Expr.eval, Env.get, spqrChainNextKeyEval_take32_lossless,
          spqrChainNextKeyRaw, ChainEpochDirection.nextKey]
        cases hnk : ChainEpochDirection.nextKeyInternal (spqrHkdfWith C.F) link.send.next
            link.send.ctr with
        | error p =>
          simp only [Bind.bind, Except.bind]
          rfl
        | ok nkOut =>
          rcases nkOut with ⟨next', ctr', idx, mkBytes⟩
          have hnext'32 : next'.length ≤ 64 := by
            unfold ChainEpochDirection.nextKeyInternal at hnk
            split_ifs at hnk
            injection hnk with hnk'
            rcases Prod.mk.inj hnk' with ⟨rfl, _⟩
            exact Nat.le_trans (List.length_take_le 32 _) (by decide)
          simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
          dsimp only [PFunctor.FreeM.bind]
          apply congrArg PFunctor.FreeM.pure
          apply congrArg some
          refine Prod.ext ?_ rfl
          let ρEnd : Env (.prod (B 32) (.prod U32 BV256) ::
              .prod .bool (.opt (.prod (B 32) (.prod U32 BV256))) ::
              spqrDirT :: spqrEpochLinkT ::
              .prod U64 (.prod (.list spqrEpochLinkT) .nat) ::
              .nat :: .prod spqrChainT U64 :: Γ) :=
            Env.cons (t := .prod (B 32) (.prod U32 BV256))
              (next', (idx, bytesToKey32 mkBytes))
              (Env.cons (t := .prod .bool (.opt (.prod (B 32) (.prod U32 BV256))))
                (false, some (next', (idx, bytesToKey32 mkBytes)))
                (Env.cons (t := spqrDirT)
                  (link.send.ctr, (link.send.next, splitSpqrPrev 2201 link.send.prev.data))
                  (Env.cons (t := spqrEpochLinkT)
                    (some (link.send.ctr, (link.send.next, splitSpqrPrev 2201 link.send.prev.data)),
                     some (spqrDirToV (ℓ := ℓ) link.recv.intoPb))
                    ρMid)))
          have hset_eval :
              (listSetExpr (O := e2eOps ℓ P C K decT encT) 4
                (.snd (.snd (Expr.var Var.zero.succ.succ.succ.succ)))
                (.pair (.some (.pair (.fst (.snd (Expr.var Var.zero)))
                  (.pair (.fst (Expr.var Var.zero)) (.snd (.snd (Expr.var Var.zero.succ.succ))))))
                  (.snd (Expr.var Var.zero.succ.succ.succ)))
                (.fst (.snd (Expr.var Var.zero.succ.succ.succ.succ)))).eval ρEnd =
                (self1.links.set epochIndex { link with send := { link.send with next := next', ctr := ctr' } }).map
                  fLink := by
            rw [eval_listSetExpr (O := e2eOps ℓ P C K decT encT) 4 _ _ _ ρEnd
              (by dsimp only [ρEnd, ρMid]; simp only [Expr.eval, Env.get, List.length_map]; exact hlen_self1)]
            have hctr_eq : ctr' = idx := by
              unfold ChainEpochDirection.nextKeyInternal at hnk
              split_ifs at hnk
              injection hnk with hnk'
              rcases Prod.mk.inj hnk' with ⟨_, h2⟩
              rcases Prod.mk.inj h2 with ⟨rfl, h3⟩
              injection h3
            subst hctr_eq
            dsimp only [ρEnd, ρMid]
            simp only [Expr.eval, Env.get, List.map_set]
            congr 2
            dsimp only [fLink]
            simp [ChainEpochDirection.intoPb, spqrDirToV,
              List.take_of_length_le hnext'32]
          dsimp only [ρEnd, ρMid, ρEp0, ρBase] at hset_eval
          rw [hset_eval]
          let linksOut := self1.links.set epochIndex
            { link with send := { link.send with next := next', ctr := ctr' } }
          have hlen_set : linksOut.length ≤ 4 := by
            dsimp only [linksOut]
            rw [List.length_set]
            exact hlen_self1
          have hlks_out :=
            spqrChainToV_links_eq (ℓ := ℓ) { self1 with links := linksOut } hlen_set
          refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))))
          · exact hdir_eq.trans (congrArg Direction.toI32 hdir1.symm)
          · exact hcur_eq.trans hcur1.symm
          · exact hlks_out.symm
          · exact hroot_eq.trans (congrArg (·.take 64) hroot1.symm)
          · rfl
          · exact hpar_eq.trans (congrArg (fun p => some (spqrParamsToV p)) hpar1.symm)

/-! ## Cost bounds -/

theorem cost_listDropExpr {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {t : Ty (e2eSig ℓ)} (K : ℕ) (n : Expr O Γ .nat) (l : Expr O Γ (.list t)) :
    (listDropExpr K n l).cost ≤ n.cost + l.cost + 24 * K + bits K + 15 := by
  have hb1 : bits 1 = 1 := by decide
  have hm : max 4 2 = 4 := rfl
  simp only [listDropExpr, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, hb1,
    Nat.reduceAdd, hm]
  omega

theorem cost_listGetExpr {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {t : Ty (e2eSig ℓ)} (K : ℕ) (idx : Expr O Γ .nat) (l : Expr O Γ (.list t)) :
    (listGetExpr K idx l).cost ≤ idx.cost + l.cost + 20 * K + bits K + 15 := by
  have hb1 : bits 1 = 1 := by decide
  have hm : max 2 2 = 2 := rfl
  simp only [listGetExpr, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, hb1,
    Nat.reduceAdd, hm]
  omega

theorem cost_listSetExpr {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {t : Ty (e2eSig ℓ)} (K : ℕ) (idx : Expr O Γ .nat) (val : Expr O Γ t)
    (l : Expr O Γ (.list t)) :
    (listSetExpr K idx val l).cost ≤ idx.cost + val.cost + l.cost + 22 * K + bits K + 20 := by
  have hb1 : bits 1 = 1 := by decide
  have hm : max 3 1 = 3 := rfl
  simp only [listSetExpr, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, hb1,
    Nat.reduceAdd, hm]
  omega

theorem cost_spqrEpochIdxExpr {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (curEp : Expr (e2eOps ℓ P C K decT encT) Γ U64)
    (linksLen : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (epoch : Expr (e2eOps ℓ P C K decT encT) Γ U64) :
    (spqrEpochIdxExpr curEp linksLen epoch).cost ≤
      curEp.cost + linksLen.cost + epoch.cost + 100 := by
  have hb1 : bits 1 = 1 := by decide
  simp only [spqrEpochIdxExpr, Expr.cost, cost_e2ePureOp, E2EPureOp.cost, Expr.v0, Expr.v1, hb1]
  omega

theorem cost_spqrResolveChainComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (vn? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt spqrVnT))
    (ch? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt spqrChainT)) :
    (spqrResolveChainComp I vn? ch?).cost ≤ vn?.cost + ch?.cost + 25 := by
  simp only [spqrResolveChainComp, Comp.cost, cost_spqrChainFromVnC, Expr.cost, Expr.v0]
  omega

theorem cost_spqrAddEpochOptComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (ch : Expr (e2eOps ℓ P C K decT encT) Γ spqrChainT)
    (epSec? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (.prod U64 BV256))) :
    (spqrAddEpochOptComp I ch epSec?).cost ≤ ch.cost + epSec?.cost + 40 := by
  simp only [spqrAddEpochOptComp, Comp.cost, cost_spqrChainAddEpochC, Expr.cost, Expr.v0, Expr.v1]
  omega

theorem cost_spqrChainSendKeyComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (ch : Expr (e2eOps ℓ P C K decT encT) Γ spqrChainT)
    (epoch : Expr (e2eOps ℓ P C K decT encT) Γ U64) :
    (spqrChainSendKeyComp I ch epoch).cost ≤ ch.cost + epoch.cost + 1200 := by
  have hb1 : bits 1 = 1 := by decide
  have hb4 : bits 4 = 3 := by decide
  have hp32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hmax : ∀ a b : ℕ, max a b = if a ≤ b then b else a := fun _ _ => rfl
  simp only [spqrChainSendKeyComp, linksClearSendPrefixExpr, clearLinkSendNextExpr,
    listDropExpr, listGetExpr, listSetExpr, spqrEpochIdxExpr, Comp.cost, cost_spqrChainNextKeyC,
    Expr.cost, cost_e2ePureOp, E2EPureOp.cost, hp32, List.length_nil, Expr.v0, Expr.v1, Expr.v2,
    Expr.v3, Expr.v4, Expr.v6, hb1, hb4, hmax, Nat.reduceLeDiff, ↓reduceIte,
    Nat.reduceAdd, Nat.reduceMul]
  omega

end Computational.Proofs.E2E.Dsl.SpqrSimChain
