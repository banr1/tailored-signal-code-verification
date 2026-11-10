/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.AtomicOps
public import Computational.Specifications.Assumptions.Assumptions
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction
public import Computational.Specifications.Session.ACD19.SM.Theorem8And12Statements

/-!
# Shared target oracle interfaces and game codecs

**Trusted in part.** Every `ReductionDsl` reduction in `Computational/Specifications/` accesses
target challenger oracles and source security games through the op-free `Iface` and `GameCodec`
projections in this file over `atomicSig` (`AtomicOps.lean`) and coin-only uniform samplers
(`Samplers.lean`). Three leaf primitive interfaces (`aes256PrfIface`, `hmacPrfIface`, and
`leafSigAndDdhIface`) are staged for Phase 1B leaf-assumption wiring; see
`Computational/docs/TRUSTED_BASE.md`.

Adapted in part from earlier leaf challenger interface definitions by Charles Sutton, paired here
with concrete `ReductionDsl` syntactic step, query, and 32-byte block-size budgets.
-/

@[expose] public section

set_option autoImplicit false

namespace ReductionDsl

open OracleSpec OracleComp
open CryptoVerification CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoGames
open Ratchet LibsignalInst LibsignalSession LibsignalSessionApi HMAC HKDF CBC LibsignalAead
  MACScheme SM CKA FSAEAD PRFPRNG WireAEAD AEADScheme

/-! ## Leaf challenger interfaces and PRF codecs -/

/-- Coin-only target interface on `unifSpec` with `atomicBaseSamplers ℓ Pt` (`Tag = Empty`). -/
@[reducible] def coinOnlyBaseIface (ℓ : ℕ) (Pt : Type := Empty) :
    Iface (atomicSig ℓ Pt) unifSpec where
  fwdU n := query (spec := unifSpec) n
  uCost := 1
  Tag := Empty
  dom := Empty.elim
  cod := Empty.elim
  enc g := g.elim
  dec g := g.elim
  qCost := Empty.elim
  smp := atomicBaseSamplers ℓ Pt

/-- Coin-only target interface on `unifSpec` with `atomicSamplers ℓ Pt` (`Tag = Empty`). -/
@[reducible] def coinOnlyIface (ℓ : ℕ) (Pt : Type) [SampleableType Pt] :
    Iface (atomicSig ℓ Pt) unifSpec where
  fwdU n := query (spec := unifSpec) n
  uCost := 1
  Tag := Empty
  dom := Empty.elim
  cod := Empty.elim
  enc g := g.elim
  dec g := g.elim
  qCost := Empty.elim
  smp := atomicSamplers ℓ Pt

/-- Generic PRF target interface on `unifSpec + MACScheme.prfSpec inpT.denote tagT.denote`. -/
@[reducible] def atomicPrfIface {ℓ : ℕ} {Pt : Type}
    (inpT tagT : Ty (atomicSig ℓ Pt)) (qCost : ℕ) (smp : Samplers (atomicSig ℓ Pt)) :
    Iface (atomicSig ℓ Pt) (unifSpec + MACScheme.prfSpec inpT.denote tagT.denote) where
  fwdU n := query (spec := unifSpec + MACScheme.prfSpec inpT.denote tagT.denote) (.inl n)
  uCost := 1
  Tag := Unit
  dom _ := inpT
  cod _ := tagT
  enc _ x := .inr x
  dec _ _ u := u
  qCost _ := qCost
  smp := smp

/-- Source game codec for `MACScheme.prfSpec inpT.denote tagT.denote` (`codecCost = 2`). -/
@[reducible] def atomicPrfCodec {ℓ : ℕ} {Pt : Type} (inpT tagT : Ty (atomicSig ℓ Pt)) :
    GameCodec (atomicSig ℓ Pt) (MACScheme.prfSpec inpT.denote tagT.denote) where
  Q := inpT
  R := tagT
  qenc x := x
  rdec _ r := r
  codecCost := 2

/-- Leaf AES-256 block PRF target interface (`BitVec 128 -> BitVec 128`, `qCost = 2`). -/
@[reducible] def aes256PrfIface (ℓ : ℕ) (Pt : Type := Empty) :
    Iface (atomicSig ℓ Pt) (unifSpec + MACScheme.prfSpec (BitVec 128) (BitVec 128)) :=
  atomicPrfIface (ℓ := ℓ) (Pt := Pt) BV128 BV128 2 (atomicBaseSamplers ℓ Pt)

/-- Leaf HMAC-SHA256 byte-domain PRF target interface at nominal width `w`
(`qCost = (w + 31) / 32 + 2`). -/
@[reducible] def hmacPrfIface (ℓ : ℕ) (Pt : Type := Empty) (w : ℕ+) :
    Iface (atomicSig ℓ Pt) (unifSpec + MACScheme.prfSpec Bytes (BitVec 256)) :=
  atomicPrfIface (ℓ := ℓ) (Pt := Pt) (B w) BV256 ((w.val + 31) / 32 + 2)
    (atomicBaseSamplers ℓ Pt)

/-- Point-domain HKDF-Extract PRF target interface (`Pt -> BitVec 256`, `qCost = 3`) with
`atomicBaseSamplers ℓ Pt` (no `[SampleableType Pt]` required). -/
@[reducible] def extractPtPrfBaseIface (ℓ : ℕ) (Pt : Type) :
    Iface (atomicSig ℓ Pt) (unifSpec + MACScheme.prfSpec Pt (BitVec 256)) :=
  atomicPrfIface (ℓ := ℓ) (Pt := Pt) PtT BV256 3 (atomicBaseSamplers ℓ Pt)

/-- Point-domain HKDF-Extract PRF target interface (`Pt -> BitVec 256`, `qCost = 3`) with
`atomicSamplers ℓ Pt`. -/
@[reducible] def extractPtPrfIface (ℓ : ℕ) (Pt : Type) [SampleableType Pt] :
    Iface (atomicSig ℓ Pt) (unifSpec + MACScheme.prfSpec Pt (BitVec 256)) :=
  atomicPrfIface (ℓ := ℓ) (Pt := Pt) PtT BV256 3 (atomicSamplers ℓ Pt)

/-- Source game codec for `MACScheme.prfSpec Pt (BitVec 256)` (`codecCost = 2`). -/
@[reducible] def extractPtPrfCodec (ℓ : ℕ) (Pt : Type) :
    GameCodec (atomicSig ℓ Pt) (MACScheme.prfSpec Pt (BitVec 256)) :=
  atomicPrfCodec (ℓ := ℓ) (Pt := Pt) PtT BV256

/-- Leaf challenger interface on `unifSpec + SignalPqxdh.sigAndDdhSpec`: `.inl m` queries XEdDSA
signing at nominal message width `m` (`qCost = 65 + m`), and `.inr ()` queries X25519 DDH
(`qCost = 97`). -/
@[reducible] def leafSigAndDdhIface (ℓ : ℕ := 0) (Pt : Type := Empty) :
    Iface (atomicSig ℓ Pt) (unifSpec + SignalPqxdh.sigAndDdhSpec) where
  fwdU n := query (spec := unifSpec + SignalPqxdh.sigAndDdhSpec) (.inl n)
  uCost := 1
  Tag := ℕ+ ⊕ Unit
  dom | .inl m => PB m | .inr () => .prod (PB 32) (.prod (PB 32) (PB 32))
  cod | .inl _ => PB 64 | .inr () => .bool
  enc | .inl _, msg => .inr (.inl (.sign msg)) | .inr (), x => .inr (.inr x)
  dec | .inl _, _, r => r | .inr (), _, r => r
  qCost | .inl m => 65 + m.val | .inr () => 97
  smp := atomicBaseSamplers ℓ Pt

/-! ## `KeyInd` value tuples and game codec -/

/-- `ReductionDsl` tuple type for `SignalPqxdh.PreKeyBundleInput`. -/
@[reducible] def bundleT {ℓ : ℕ} {Pt : Type} : Ty (atomicSig ℓ Pt) :=
  .prod (PB 32) (.prod PU32 (.prod (PB 32) (.prod (PB 64)
    (.prod (.opt (.prod PU32 (PB 32))) (.prod PU32 (.prod (PB 1568) (PB 64)))))))

def bundleV {ℓ : ℕ} {Pt : Type} (b : SignalPqxdh.PreKeyBundleInput) :
    (bundleT (ℓ := ℓ) (Pt := Pt)).denote :=
  (b.ikB, (b.spkId, (b.spkB, (b.spkSig, (b.opkB?, (b.pqspkId, (b.pqspkB, b.pqspkSig)))))))

def bundleOfV {ℓ : ℕ} {Pt : Type} (v : (bundleT (ℓ := ℓ) (Pt := Pt)).denote) :
    SignalPqxdh.PreKeyBundleInput :=
  ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2⟩

/-- `ReductionDsl` sum-of-products type for `SignalPqxdh.SessionId S`. -/
@[reducible] def sidT {ℓ : ℕ} {Pt : Type} (S : SignalPqxdh.Setup) : Ty (atomicSig ℓ Pt) :=
  .sum (.prod (FinT S.N_id) (FinT S.N_send_opk))
    (.sum (.prod (FinT S.N_id) (FinT S.N_send_no_opk))
      (.sum (.prod (FinT S.N_id) (.prod (FinT S.N_recv) (FinT S.N_opk)))
            (.prod (FinT S.N_id) (.prod (FinT S.N_recv) (FinT S.N_no_opk)))))

def sidV {ℓ : ℕ} {Pt : Type} {S : SignalPqxdh.Setup} :
    SignalPqxdh.SessionId S → (sidT (ℓ := ℓ) (Pt := Pt) S).denote
  | .sendOPK u i => .inl (u, i)
  | .sendNoOPK u i => .inr (.inl (u, i))
  | .recvOPK k j o => .inr (.inr (.inl (k, (j, o))))
  | .recvNoOPK k j l => .inr (.inr (.inr (k, (j, l))))

def sidOfV {ℓ : ℕ} {Pt : Type} {S : SignalPqxdh.Setup} :
    (sidT (ℓ := ℓ) (Pt := Pt) S).denote → SignalPqxdh.SessionId S
  | .inl (u, i) => .sendOPK u i
  | .inr (.inl (u, i)) => .sendNoOPK u i
  | .inr (.inr (.inl (k, (j, o)))) => .recvOPK k j o
  | .inr (.inr (.inr (k, (j, l)))) => .recvNoOPK k j l

/-- Four secret-key lists carried by `KeyIndResponse.dhSecretsResp`. -/
@[reducible] def dhSecretsT {ℓ : ℕ} {Pt : Type} : Ty (atomicSig ℓ Pt) :=
  .prod (.list (PB 32)) (.prod (.list (PB 32)) (.prod (.list (PB 32)) (.list (PB 32))))

/-- `ReductionDsl` sum type for `SignalPqxdh.KeyIndQuery S`. -/
@[reducible] def keyIndQT {ℓ : ℕ} {Pt : Type} (S : SignalPqxdh.Setup) : Ty (atomicSig ℓ Pt) :=
  .sum (FinT S.N_id) (.sum (FinT S.N_id)
  (.sum (.prod (FinT S.N_id) (FinT S.N_recv))
  (.sum (.prod (FinT S.N_id) (.prod (FinT S.N_recv) (FinT S.N_opk)))
  (.sum (.prod (FinT S.N_id) (.prod (FinT S.N_send_opk) bundleT))
  (.sum (.prod (FinT S.N_id) (.prod (FinT S.N_send_no_opk) bundleT))
  (.sum (.prod (FinT S.N_id) (.prod (FinT S.N_recv) (.prod (FinT S.N_opk) hdrT)))
  (.sum (.prod (FinT S.N_id) (.prod (FinT S.N_recv) (.prod (FinT S.N_no_opk) hdrT)))
  (.sum (sidT S) (.sum (PB 192) (.sum .unit
  (.sum (sidT S) (.sum (PB 32) (.prod (FinT S.N_id) (FinT S.N_recv))))))))))))))

def keyIndQenc {ℓ : ℕ} {Pt : Type} {S : SignalPqxdh.Setup} :
    SignalPqxdh.KeyIndQuery S → (keyIndQT (ℓ := ℓ) (Pt := Pt) S).denote
  | .initPrin u => .inl u
  | .corruptIK u => .inr (.inl u)
  | .genSPK u j => .inr (.inr (.inl (u, j)))
  | .genOPK u j o => .inr (.inr (.inr (.inl (u, (j, o)))))
  | .initiateOPK u i b => .inr (.inr (.inr (.inr (.inl (u, (i, bundleV b))))))
  | .initiateNoOPK u i b => .inr (.inr (.inr (.inr (.inr (.inl (u, (i, bundleV b)))))))
  | .acceptOPK k j o h => .inr (.inr (.inr (.inr (.inr (.inr (.inl (k, (j, (o, hdrV h)))))))))
  | .acceptNoOPK k j l h =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (k, (j, (l, hdrV h))))))))))
  | .testSession sid => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (sidV sid)))))))))
  | .roQuery sec => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl sec)))))))))
  | .revealDhSecrets => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))))))
  | .revealSessionKey sid =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (sidV sid))))))))))))
  | .registerKey sk =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl sk))))))))))))
  | .revealSpkSk u j =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (u, j)))))))))))))

def keyIndQdec {ℓ : ℕ} {Pt : Type} {S : SignalPqxdh.Setup} :
    (keyIndQT (ℓ := ℓ) (Pt := Pt) S).denote → SignalPqxdh.KeyIndQuery S
  | .inl u => .initPrin u
  | .inr (.inl u) => .corruptIK u
  | .inr (.inr (.inl (u, j))) => .genSPK u j
  | .inr (.inr (.inr (.inl (u, (j, o))))) => .genOPK u j o
  | .inr (.inr (.inr (.inr (.inl (u, (i, b)))))) => .initiateOPK u i (bundleOfV b)
  | .inr (.inr (.inr (.inr (.inr (.inl (u, (i, b))))))) => .initiateNoOPK u i (bundleOfV b)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl (k, (j, (o, h))))))))) =>
    .acceptOPK k j o (hdrOfV h)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (k, (j, (l, h)))))))))) =>
    .acceptNoOPK k j l (hdrOfV h)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl sid)))))))) => .testSession (sidOfV sid)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl sec))))))))) => .roQuery sec
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ())))))))))) => .revealDhSecrets
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl sid))))))))))) =>
    .revealSessionKey (sidOfV sid)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl sk)))))))))))) =>
    .registerKey sk
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (u, j))))))))))))) =>
    .revealSpkSk u j

/-- `ReductionDsl` sum type for `SignalPqxdh.KeyIndResponse`. -/
@[reducible] def keyIndRT {ℓ : ℕ} {Pt : Type} : Ty (atomicSig ℓ Pt) :=
  .sum .unit (.sum (.prod (PB 32) (PB 32)) (.sum (PB 32) (.sum (.prod (PB 32) (PB 32))
  (.sum bundleT (.sum hdrT (.sum (.prod drKeyT hdrT)
  (.sum .unit (.sum drKeyT (.sum dhSecretsT (PB 32))))))))))

def keyIndRenc {ℓ : ℕ} {Pt : Type} :
    SignalPqxdh.KeyIndResponse → (keyIndRT (ℓ := ℓ) (Pt := Pt)).denote
  | .noneResp => .inl ()
  | .initPrinResp ik s => .inr (.inl (ik, s))
  | .pkResp pk => .inr (.inr (.inl pk))
  | .corrResp ik s => .inr (.inr (.inr (.inl (ik, s))))
  | .bundleResp b => .inr (.inr (.inr (.inr (.inl (bundleV b)))))
  | .hdrResp h => .inr (.inr (.inr (.inr (.inr (.inl (hdrV h))))))
  | .initUnfreshResp dk h => .inr (.inr (.inr (.inr (.inr (.inr (.inl (drKeyV dk, hdrV h)))))))
  | .acceptFreshResp => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ())))))))
  | .drKeyResp dk => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (drKeyV dk)))))))))
  | .dhSecretsResp l1 l2 l3 l4 =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (l1, (l2, (l3, l4))))))))))))
  | .spkSkResp sk => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr sk)))))))))

def keyIndRdec {ℓ : ℕ} {Pt : Type} :
    (keyIndRT (ℓ := ℓ) (Pt := Pt)).denote → SignalPqxdh.KeyIndResponse
  | .inl () => .noneResp
  | .inr (.inl (ik, s)) => .initPrinResp ik s
  | .inr (.inr (.inl pk)) => .pkResp pk
  | .inr (.inr (.inr (.inl (ik, s)))) => .corrResp ik s
  | .inr (.inr (.inr (.inr (.inl b)))) => .bundleResp (bundleOfV b)
  | .inr (.inr (.inr (.inr (.inr (.inl h))))) => .hdrResp (hdrOfV h)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl (dk, h))))))) =>
    .initUnfreshResp (drKeyOfV dk) (hdrOfV h)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))) => .acceptFreshResp
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl dk)))))))) => .drKeyResp (drKeyOfV dk)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (l1, (l2, (l3, l4)))))))))))) =>
    .dhSecretsResp l1 l2 l3 l4
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr sk))))))))) => .spkSkResp sk

/-- Shared `GameCodec` for `SignalPqxdh.keyIndSpec S` (`codecCost = 64`). -/
@[reducible] def keyIndCodec {ℓ : ℕ} {Pt : Type} (S : SignalPqxdh.Setup) :
    GameCodec (atomicSig ℓ Pt) (SignalPqxdh.keyIndSpec S) where
  Q := keyIndQT S
  R := keyIndRT
  qenc := keyIndQenc (ℓ := ℓ) (Pt := Pt)
  rdec _ r := keyIndRdec (ℓ := ℓ) (Pt := Pt) r
  codecCost := 64

/-! ## PQXDH handshake primitive tags and interfaces -/

@[reducible] def pqAtomicSig : Sig := atomicSig 0 Empty
@[reducible] def pqAtomicOps : Ops pqAtomicSig := atomicPureOps 0 Empty
@[reducible] def pqAtomicSamplers : Samplers pqAtomicSig := atomicBaseSamplers 0 Empty

/-- Typed tags for the 11 handshake primitive queries in `SignalPqxdh.PrimQuery`. -/
inductive PTag where
  | x25519 | x25519Base | isCanonical | pow8 | sigPkGen
  | sigSign (m : ℕ+) | sigVerify (m : ℕ+)
  | kemKeyGen | kemEncaps | kemDecaps | hkdfDerive96 (w : ℕ+)
  deriving DecidableEq

@[reducible] def PTag.dom {ℓ : ℕ} {Pt : Type} : PTag → Ty (atomicSig ℓ Pt)
  | .x25519 => .prod (PB 32) (PB 32)
  | .x25519Base | .isCanonical | .pow8 | .sigPkGen => PB 32
  | .sigSign m | .sigVerify m => .prod (PB 32) (.prod (PB m) (PB 64))
  | .kemKeyGen => PB 64
  | .kemEncaps => .prod (PB 1568) (PB 32)
  | .kemDecaps => .prod (PB 3168) (PB 1568)
  | .hkdfDerive96 w => PB w

@[reducible] def PTag.cod {ℓ : ℕ} {Pt : Type} : PTag → Ty (atomicSig ℓ Pt)
  | .x25519 | .x25519Base | .pow8 | .sigPkGen => PB 32
  | .isCanonical | .sigVerify _ => .bool
  | .sigSign _ => PB 64
  | .kemKeyGen => .prod (PB 1568) (PB 3168)
  | .kemEncaps => .opt (.prod (PB 32) (PB 1568))
  | .kemDecaps => .opt (PB 32)
  | .hkdfDerive96 _ => drKeyT

def PTag.enc {ℓ : ℕ} {Pt : Type} :
    (t : PTag) → (t.dom (ℓ := ℓ) (Pt := Pt)).denote → SignalPqxdh.PrimQuery
  | .x25519, (sk, pk) => .x25519 sk pk
  | .x25519Base, sk => .x25519Base sk
  | .isCanonical, pk => .isCanonical pk
  | .pow8, pk => .pow8 pk
  | .sigPkGen, sk => .sigPkGen sk
  | .sigSign _, (sk, m, r) => .sigSign sk m r
  | .sigVerify _, (pk, m, s) => .sigVerify pk m s
  | .kemKeyGen, seed => .kemKeyGen seed
  | .kemEncaps, (pk, r) => .kemEncaps pk r
  | .kemDecaps, (sk, ct) => .kemDecaps sk ct
  | .hkdfDerive96 _, ikm => .hkdfDerive96 ikm

def PTag.dec {ℓ : ℕ} {Pt : Type} :
    (t : PTag) → (x : (t.dom (ℓ := ℓ) (Pt := Pt)).denote) →
      SignalPqxdh.primSpec (t.enc (ℓ := ℓ) (Pt := Pt) x) → (t.cod (ℓ := ℓ) (Pt := Pt)).denote
  | .x25519, _, r => r
  | .x25519Base, _, r => r
  | .isCanonical, _, r => r
  | .pow8, _, r => r
  | .sigPkGen, _, r => r
  | .sigSign _, _, r => r
  | .sigVerify _, _, r => r
  | .kemKeyGen, _, r => r
  | .kemEncaps, _, r => r
  | .kemDecaps, _, r => r
  | .hkdfDerive96 _, _, r => drKeyV r

/-- Nominal byte-width query cost `1 + wd(dom) + wd(cod)` of each handshake primitive tag. -/
def PTag.qCost : PTag → ℕ
  | .x25519 => 97
  | .x25519Base | .pow8 | .sigPkGen => 65
  | .isCanonical => 33
  | .sigSign m => 161 + m.val
  | .sigVerify m => 97 + m.val
  | .kemKeyGen => 4801
  | .kemEncaps => 3201
  | .kemDecaps => 4769
  | .hkdfDerive96 w => 97 + w.val

/-- Target oracle interface on `SignalPqxdh.PrimBaseSpec` (`KemShCr` reductions). -/
@[reducible] def pqPrimIface : Iface pqAtomicSig SignalPqxdh.PrimBaseSpec where
  fwdU n := query (spec := SignalPqxdh.PrimBaseSpec) (.inl n)
  uCost := 1
  Tag := PTag
  dom t := t.dom (ℓ := 0) (Pt := Empty)
  cod t := t.cod (ℓ := 0) (Pt := Empty)
  enc t x := .inr (t.enc (ℓ := 0) (Pt := Empty) x)
  dec t x r := t.dec (ℓ := 0) (Pt := Empty) x r
  qCost := PTag.qCost
  smp := pqAtomicSamplers

/-- Target oracle interface on `SignalPqxdh.PrimBaseSpec + SignalPqxdh.sigAndDdhSpec`
(`GapSigEufCma` and `GapDhWithSign` reductions). -/
@[reducible] def pqSigAndDdhIface :
    Iface pqAtomicSig (SignalPqxdh.PrimBaseSpec + SignalPqxdh.sigAndDdhSpec) where
  fwdU n := query (spec := SignalPqxdh.PrimBaseSpec + SignalPqxdh.sigAndDdhSpec) (.inl (.inl n))
  uCost := 1
  Tag := PTag ⊕ (ℕ+ ⊕ Unit)
  dom
    | .inl t => t.dom (ℓ := 0) (Pt := Empty)
    | .inr (.inl m) => PB (ℓ := 0) (Pt := Empty) m
    | .inr (.inr ()) =>
      .prod (PB (ℓ := 0) (Pt := Empty) 32)
        (.prod (PB (ℓ := 0) (Pt := Empty) 32) (PB (ℓ := 0) (Pt := Empty) 32))
  cod
    | .inl t => t.cod (ℓ := 0) (Pt := Empty)
    | .inr (.inl _) => PB (ℓ := 0) (Pt := Empty) 64
    | .inr (.inr ()) => .bool
  enc
    | .inl t, x => .inl (.inr (t.enc (ℓ := 0) (Pt := Empty) x))
    | .inr (.inl _), msg => .inr (.inl (.sign msg))
    | .inr (.inr ()), x => .inr (.inr x)
  dec
    | .inl t, x, r => t.dec (ℓ := 0) (Pt := Empty) x r
    | .inr (.inl _), _, r => r
    | .inr (.inr ()), _, r => r
  qCost | .inl t => t.qCost | .inr (.inl m) => 65 + m.val | .inr (.inr ()) => 97
  smp := pqAtomicSamplers

@[reducible] def pqKeyIndCodec (S : SignalPqxdh.Setup) :
    GameCodec pqAtomicSig (SignalPqxdh.keyIndSpec S) :=
  keyIndCodec (ℓ := 0) (Pt := Empty) S

/-! ## Symmetric-ratchet and FS-AEAD interfaces and codecs -/

section L2SymAndFsCodecs

variable {ℓ : ℕ} {Pt : Type}

def salt32V (s : Salt32) : BitVec 256 := HKDF.bytesToKey32 s.toList
def salt32OfV (x : BitVec 256) : Salt32 := Ratchet.keyToBytesVec32 x

@[reducible] def derivedMsgKeysT : Ty (atomicSig ℓ Pt) := .prod (.prod BV256 BV128) BV256

@[reducible] def wireSignalHdrT : Ty (atomicSig ℓ Pt) :=
  .prod (signalHdrT (ℓ := ℓ) (Pt := Pt)) (.prod (B 32) (.opt (B 32)))
def wireSignalHdrV (h : SignalHeader) : (wireSignalHdrT (ℓ := ℓ) (Pt := Pt)).denote :=
  ((h.messageVersion, (h.senderRatchetKey, (h.counter, h.previousCounter))),
   (h.pqRatchet, h.addresses))
def wireSignalHdrOfV (v : (wireSignalHdrT (ℓ := ℓ) (Pt := Pt)).denote) : SignalHeader :=
  let ((ver, (rk, (ctr, pctr))), (pq, addrs)) := v
  ⟨ver, rk, ctr, pctr, pq, addrs⟩

@[reducible] def lpubT : Ty (atomicSig ℓ Pt) := .prod U32 (.prod (B 32) (.prod BV256 (.opt (B 32))))
def lpubV (p : LibsignalMsgPublicPart) : (lpubT (ℓ := ℓ) (Pt := Pt)).denote :=
  (p.pn, (p.pqmsg, (salt32V p.salt, p.addrs)))
def lpubOfV (v : (lpubT (ℓ := ℓ) (Pt := Pt)).denote) : LibsignalMsgPublicPart :=
  let (pn, (pqmsg, (sv, addrs))) := v
  ⟨pn, pqmsg, salt32OfV sv, addrs⟩

@[reducible] def wireSaltCtT : Ty (atomicSig ℓ Pt) := .prod (.prod (B 32) U64) BV256
def wireSaltCtV (c : LibsignalCiphertextWithSalt32) : (wireSaltCtT (ℓ := ℓ) (Pt := Pt)).denote :=
  (c.1, salt32V c.2)
def wireSaltCtOfV (v : (wireSaltCtT (ℓ := ℓ) (Pt := Pt)).denote) : LibsignalCiphertextWithSalt32 :=
  (v.1, salt32OfV v.2)

@[reducible] def lctT : Ty (atomicSig ℓ Pt) := .prod .nat (wireSaltCtT (ℓ := ℓ) (Pt := Pt))
def lctV (c : ℕ × LibsignalCiphertextWithSalt32) : (lctT (ℓ := ℓ) (Pt := Pt)).denote :=
  (c.1, wireSaltCtV c.2)
def lctOfV (v : (lctT (ℓ := ℓ) (Pt := Pt)).denote) : ℕ × LibsignalCiphertextWithSalt32 :=
  (v.1, wireSaltCtOfV v.2)

@[reducible] def fig8HdrT : Ty (atomicSig ℓ Pt) := .prod .nat (.opt PtT)

@[reducible] def fig8PubAdT : Ty (atomicSig ℓ Pt) :=
  .prod (fig8HdrT (ℓ := ℓ) (Pt := Pt)) (lpubT (ℓ := ℓ) (Pt := Pt))
def fig8PubAdV (a : SM.Construction.Header Pt × LibsignalMsgPublicPart) :
    (fig8PubAdT (ℓ := ℓ) (Pt := Pt)).denote := (a.1, lpubV a.2)
def fig8PubAdOfV (v : (fig8PubAdT (ℓ := ℓ) (Pt := Pt)).denote) :
    SM.Construction.Header Pt × LibsignalMsgPublicPart := (v.1, lpubOfV v.2)

@[reducible] def slotAdT : Ty (atomicSig ℓ Pt) := .prod .nat (fig8PubAdT (ℓ := ℓ) (Pt := Pt))
def slotAdV (a : ℕ × (SM.Construction.Header Pt × LibsignalMsgPublicPart)) :
    (slotAdT (ℓ := ℓ) (Pt := Pt)).denote := (a.1, fig8PubAdV a.2)
def slotAdOfV (v : (slotAdT (ℓ := ℓ) (Pt := Pt)).denote) :
    ℕ × (SM.Construction.Header Pt × LibsignalMsgPublicPart) := (v.1, fig8PubAdOfV v.2)

@[reducible] def fsSendStT : Ty (atomicSig ℓ Pt) := .prod BV256 .nat
def fsSendStV (s : RatchetSenderState (BitVec 256)) : (fsSendStT (ℓ := ℓ) (Pt := Pt)).denote :=
  (s.chainKey, s.lastIndex)
def fsSendStOfV (v : (fsSendStT (ℓ := ℓ) (Pt := Pt)).denote) : RatchetSenderState (BitVec 256) :=
  ⟨v.1, v.2⟩

@[reducible] def fsRecvStT : Ty (atomicSig ℓ Pt) :=
  .prod BV256 (.prod .nat (.list (.prod .nat BV256)))
def fsRecvStV (r : RatchetReceiverState (BitVec 256) (BitVec 256)) :
    (fsRecvStT (ℓ := ℓ) (Pt := Pt)).denote := (r.chainKey, (r.lastIndex, r.skippedKeys))
def fsRecvStOfV (v : (fsRecvStT (ℓ := ℓ) (Pt := Pt)).denote) :
    RatchetReceiverState (BitVec 256) (BitVec 256) :=
  let (ck, (idx, sk)) := v
  ⟨ck, idx, sk⟩

@[reducible] def fsRrT (msgT : Ty (atomicSig ℓ Pt)) : Ty (atomicSig ℓ Pt) :=
  .sum .unit (.prod .nat (.opt msgT))
def fsRrEnc {M : Type} {msgT : Ty (atomicSig ℓ Pt)} (encM : M → msgT.denote) :
    FSAEAD.ReceiveResult M → (fsRrT (ℓ := ℓ) (Pt := Pt) msgT).denote
  | .rejected => .inl ()
  | .accepted i m => .inr (i, m.map encM)
def fsRrDec {M : Type} {msgT : Ty (atomicSig ℓ Pt)} (decM : msgT.denote → M) :
    (fsRrT (ℓ := ℓ) (Pt := Pt) msgT).denote → FSAEAD.ReceiveResult M
  | .inl () => .rejected
  | .inr (i, m) => .accepted i (m.map decM)

inductive OTCCATag where | enc | dec deriving DecidableEq, Repr
inductive FSAEADTag where | tr | ch | cs | cr | dl | ij deriving DecidableEq, Repr

/-- Salt-PRF target interface (`unifSpec + MACScheme.prfSpec Salt32 DerivedMessageKeys`, `qCost = 5`). -/
@[reducible] def saltPrfTargetIface (ℓ : ℕ) (Pt : Type := Empty) :
    Iface (atomicSig ℓ Pt) (unifSpec + MACScheme.prfSpec Salt32 DerivedMessageKeys) where
  fwdU n := query (spec := unifSpec + MACScheme.prfSpec Salt32 DerivedMessageKeys) (.inl n)
  uCost := 1
  Tag := Unit
  dom _ := BV256
  cod _ := derivedMsgKeysT
  enc _ x := .inr (salt32OfV x)
  dec _ _ r := r
  qCost _ := 5
  smp := atomicBaseSamplers ℓ Pt

/-- Wire OT-CCA target interface (`LibsignalWireOracleSpec ℓ`, `qCost = 2 * (ℓ / 32) + 24`). -/
@[reducible] def wireOtccaTargetIface (ℓ : ℕ) (Pt : Type := Empty) :
    Iface (atomicSig ℓ Pt) (LibsignalWireOracleSpec ℓ) where
  fwdU n := query (spec := LibsignalWireOracleSpec ℓ) (.inl n)
  uCost := 1
  Tag := OTCCATag
  dom | .enc => .prod (B 66) (.prod wireSignalHdrT PlainT) | .dec => .prod (B 66) (.prod (B 32) U64)
  cod | .enc => .opt (.prod (B 32) U64) | .dec => .opt (.prod wireSignalHdrT (B 32))
  enc
    | .enc, (ad, (h, m)) => .inr (.inl (fitBytesN 66 ad, wireSignalHdrOfV h, m))
    | .dec, (ad, (w, tag)) => .inr (.inr (fitBytesN 66 ad, (w, tag)))
  dec | .enc, _, r => r | .dec, _, r => r.map fun (h, m') => (wireSignalHdrV h, m')
  qCost | .enc | .dec => 2 * (ℓ / 32) + 24
  smp := atomicBaseSamplers ℓ Pt

/-- Per-slot indexed OT-CCA target interface (`FSAEAD.Thm5.IndexedOtccaSpec`,
`qCost = 2 * (ℓ / 32) + 24`). -/
@[reducible] def slotOtccaTargetIface (ℓ : ℕ) (Pt : Type) :
    Iface (atomicSig ℓ Pt)
      (FSAEAD.Thm5.IndexedOtccaSpec (SM.Construction.Header Pt × LibsignalMsgPublicPart) (Plain ℓ)
        LibsignalCiphertextWithSalt32) where
  fwdU n := query
    (spec := FSAEAD.Thm5.IndexedOtccaSpec (SM.Construction.Header Pt × LibsignalMsgPublicPart)
      (Plain ℓ) LibsignalCiphertextWithSalt32) (.inl n)
  uCost := 1
  Tag := OTCCATag
  dom | .enc => .prod slotAdT PlainT | .dec => .prod slotAdT wireSaltCtT
  cod | .enc => .opt wireSaltCtT | .dec => .opt PlainT
  enc
    | .enc, (a, m) => .inr (.inl (slotAdOfV a, m))
    | .dec, (a, c) => .inr (.inr (slotAdOfV a, wireSaltCtOfV c))
  dec | .enc, _, r => r.map wireSaltCtV | .dec, _, r => r
  qCost | .enc | .dec => 2 * (ℓ / 32) + 24
  smp := atomicBaseSamplers ℓ Pt

/-- Source game codec for per-slot OT-CCA (`AEADScheme.otccaSpec`, `codecCost = 16`). -/
@[reducible] def slotOtccaCodec (ℓ : ℕ) (Pt : Type) :
    GameCodec (atomicSig ℓ Pt)
      (AEADScheme.otccaSpec (ℕ × (SM.Construction.Header Pt × LibsignalMsgPublicPart)) (Plain ℓ)
        LibsignalCiphertextWithSalt32) where
  Q := .sum (.prod slotAdT PlainT) (.prod slotAdT wireSaltCtT)
  R := .sum (.opt wireSaltCtT) (.opt PlainT)
  qenc | .inl (a, m) => .inl (slotAdV a, m) | .inr (a, c) => .inr (slotAdV a, wireSaltCtV c)
  rdec
    | .inl _, .inl r => r.map wireSaltCtOfV
    | .inl _, .inr _ => none
    | .inr _, .inr r => r
    | .inr _, .inl _ => none
  codecCost := 16

/-- Target FS-AEAD interface after `movePubPartToAD` (`qCost .cr = 50016` covers up to
`maxForwardJumps = 25000` skipped message keys in `RatchetReceiverState`). -/
@[reducible] def fsaeadPubTargetIface (ℓ : ℕ) (Pt : Type) :
    Iface (atomicSig ℓ Pt)
      (unifSpec + FSAEAD.spec (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        (SM.Construction.Header Pt × LibsignalMsgPublicPart) (Plain ℓ)
        (ℕ × LibsignalCiphertextWithSalt32)) where
  fwdU n := query
    (spec := unifSpec + FSAEAD.spec (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (SM.Construction.Header Pt × LibsignalMsgPublicPart) (Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32)) (.inl n)
  uCost := 1
  Tag := FSAEADTag
  dom
    | .tr => .prod fig8PubAdT PlainT
    | .ch => .prod fig8PubAdT (.prod PlainT PlainT)
    | .cs | .cr => .unit
    | .dl | .ij => .prod fig8PubAdT lctT
  cod
    | .tr | .ch => .opt lctT
    | .cs => .opt fsSendStT
    | .cr => .opt (.prod fsSendStT fsRecvStT)
    | .dl | .ij => .opt (fsRrT PlainT)
  enc
    | .tr, (a, m) => .inr (.inl (.inl (.inl (.inl (.inl (fig8PubAdOfV a, m))))))
    | .ch, (a, (m0, m1)) => .inr (.inl (.inl (.inl (.inl (.inr (fig8PubAdOfV a, (m0, m1)))))))
    | .cs, () => .inr (.inl (.inl (.inl (.inr ()))))
    | .cr, () => .inr (.inl (.inl (.inr ())))
    | .dl, (a, c) => .inr (.inl (.inr (fig8PubAdOfV a, lctOfV c)))
    | .ij, (a, c) => .inr (.inr (fig8PubAdOfV a, lctOfV c))
  dec
    | .tr, _, r => r.map lctV
    | .ch, _, r => r.map lctV
    | .cs, _, r => r.map fsSendStV
    | .cr, _, r => r.map fun (ss, rs) => (fsSendStV ss, fsRecvStV rs)
    | .dl, _, r => r.map (fsRrEnc id)
    | .ij, _, r => r.map (fsRrEnc id)
  qCost
    | .tr | .dl | .ij => 2 * (ℓ / 32) + 24
    | .ch => 3 * (ℓ / 32) + 24
    | .cs => 4
    | .cr => 50016
  smp := atomicBaseSamplers ℓ Pt

/-- Source FS-AEAD game codec before `movePubPartToAD` (`codecCost = 16`). -/
@[reducible] def fsaeadPubCodec (ℓ : ℕ) (Pt : Type) :
    GameCodec (atomicSig ℓ Pt)
      (FSAEAD.spec (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        (SM.Construction.Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
        (ℕ × LibsignalCiphertextWithSalt32)) where
  Q := .sum (.prod fig8HdrT (.prod lpubT PlainT))
    (.sum (.prod fig8HdrT (.prod (.prod lpubT PlainT) (.prod lpubT PlainT)))
    (.sum .unit (.sum .unit (.sum (.prod fig8HdrT lctT) (.prod fig8HdrT lctT)))))
  R := .sum (.opt lctT) (.sum (.opt fsSendStT)
    (.sum (.opt (.prod fsSendStT fsRecvStT)) (.opt (fsRrT (.prod lpubT PlainT)))))
  qenc
    | .inl (.inl (.inl (.inl (.inl (h, (p, m)))))) => .inl (h, (lpubV p, m))
    | .inl (.inl (.inl (.inl (.inr (h, ((p0, m0), (p1, m1))))))) =>
      .inr (.inl (h, ((lpubV p0, m0), (lpubV p1, m1))))
    | .inl (.inl (.inl (.inr ()))) => .inr (.inr (.inl ()))
    | .inl (.inl (.inr ())) => .inr (.inr (.inr (.inl ())))
    | .inl (.inr (h, c)) => .inr (.inr (.inr (.inr (.inl (h, lctV c)))))
    | .inr (h, c) => .inr (.inr (.inr (.inr (.inr (h, lctV c)))))
  rdec
    | .inl (.inl (.inl (.inl (.inl _)))), .inl r => r.map lctOfV
    | .inl (.inl (.inl (.inl (.inl _)))), _ => none
    | .inl (.inl (.inl (.inl (.inr _)))), .inl r => r.map lctOfV
    | .inl (.inl (.inl (.inl (.inr _)))), _ => none
    | .inl (.inl (.inl (.inr _))), .inr (.inl r) => r.map fsSendStOfV
    | .inl (.inl (.inl (.inr _))), _ => none
    | .inl (.inl (.inr _)), .inr (.inr (.inl r)) =>
      r.map fun (ss, rs) => (fsSendStOfV ss, fsRecvStOfV rs)
    | .inl (.inl (.inr _)), _ => none
    | .inl (.inr _), .inr (.inr (.inr r)) =>
      r.map (fsRrDec (msgT := .prod lpubT PlainT) fun (pv, m) => (lpubOfV pv, m))
    | .inl (.inr _), _ => none
    | .inr _, .inr (.inr (.inr r)) =>
      r.map (fsRrDec (msgT := .prod lpubT PlainT) fun (pv, m) => (lpubOfV pv, m))
    | .inr _, _ => none
  codecCost := 16

/-- Source FS-AEAD game codec after `movePubPartToAD` (`codecCost = 16`). -/
@[reducible] def fsaeadRatchetCodec (ℓ : ℕ) (Pt : Type) :
    GameCodec (atomicSig ℓ Pt)
      (FSAEAD.spec (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        (SM.Construction.Header Pt × LibsignalMsgPublicPart) (Plain ℓ)
        (ℕ × LibsignalCiphertextWithSalt32)) where
  Q := .sum (.prod fig8PubAdT PlainT)
    (.sum (.prod fig8PubAdT (.prod PlainT PlainT))
    (.sum .unit (.sum .unit (.sum (.prod fig8PubAdT lctT) (.prod fig8PubAdT lctT)))))
  R := .sum (.opt lctT) (.sum (.opt fsSendStT)
    (.sum (.opt (.prod fsSendStT fsRecvStT)) (.opt (fsRrT PlainT))))
  qenc
    | .inl (.inl (.inl (.inl (.inl (a, m))))) => .inl (fig8PubAdV a, m)
    | .inl (.inl (.inl (.inl (.inr (a, (m0, m1)))))) => .inr (.inl (fig8PubAdV a, (m0, m1)))
    | .inl (.inl (.inl (.inr ()))) => .inr (.inr (.inl ()))
    | .inl (.inl (.inr ())) => .inr (.inr (.inr (.inl ())))
    | .inl (.inr (a, c)) => .inr (.inr (.inr (.inr (.inl (fig8PubAdV a, lctV c)))))
    | .inr (a, c) => .inr (.inr (.inr (.inr (.inr (fig8PubAdV a, lctV c)))))
  rdec
    | .inl (.inl (.inl (.inl (.inl _)))), .inl r => r.map lctOfV
    | .inl (.inl (.inl (.inl (.inl _)))), _ => none
    | .inl (.inl (.inl (.inl (.inr _)))), .inl r => r.map lctOfV
    | .inl (.inl (.inl (.inl (.inr _)))), _ => none
    | .inl (.inl (.inl (.inr _))), .inr (.inl r) => r.map fsSendStOfV
    | .inl (.inl (.inl (.inr _))), _ => none
    | .inl (.inl (.inr _)), .inr (.inr (.inl r)) =>
      r.map fun (ss, rs) => (fsSendStOfV ss, fsRecvStOfV rs)
    | .inl (.inl (.inr _)), _ => none
    | .inl (.inr _), .inr (.inr (.inr r)) => r.map (fsRrDec id)
    | .inl (.inr _), _ => none
    | .inr _, .inr (.inr (.inr r)) => r.map (fsRrDec id)
    | .inr _, _ => none
  codecCost := 16

end L2SymAndFsCodecs

/-! ## Fig. 8, CKA, PRF-PRNG, and single-session SM interfaces and codecs -/

section L2Fig8AndSessionCodecs

variable {ℓ : ℕ} {Pt : Type}

@[reducible] def ckaStT : Ty (atomicSig ℓ Pt) := .sum PtT BV256
def ckaStV : CKA.DDH.State (BitVec 256) Pt → (ckaStT (ℓ := ℓ) (Pt := Pt)).denote
  | .pub h => .inl h | .exp x => .inr x
def ckaStOfV : (ckaStT (ℓ := ℓ) (Pt := Pt)).denote → CKA.DDH.State (BitVec 256) Pt
  | .inl h => .pub h | .inr x => .exp x

@[reducible] def fig8CtT : Ty (atomicSig ℓ Pt) :=
  .prod (fig8HdrT (ℓ := ℓ) (Pt := Pt)) (lctT (ℓ := ℓ) (Pt := Pt))
def fig8CtV (c : SM.Construction.Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) :
    (fig8CtT (ℓ := ℓ) (Pt := Pt)).denote := (c.1, lctV c.2)
def fig8CtOfV (v : (fig8CtT (ℓ := ℓ) (Pt := Pt)).denote) :
    SM.Construction.Header Pt × (ℕ × LibsignalCiphertextWithSalt32) := (v.1, lctOfV v.2)

@[reducible] def fig8StT : Ty (atomicSig ℓ Pt) :=
  .prod .bool (.prod BV256 (.prod (.opt (fsSendStT (ℓ := ℓ) (Pt := Pt)))
    (.prod (.tbl (.opt (fsRecvStT (ℓ := ℓ) (Pt := Pt))))
      (.prod (ckaStT (ℓ := ℓ) (Pt := Pt)) (.prod (.opt PtT) .nat)))))
def fig8StV
    (s : SM.Construction.PartyState (CKA.DDH.State (BitVec 256) Pt) Pt Ratchet.RootKey
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))) :
    (fig8StT (ℓ := ℓ) (Pt := Pt)).denote :=
  (partyToBool s.id, (s.root, (s.vS.map fsSendStV,
    (fun t => (s.vR t).map fsRecvStV, (ckaStV s.γ, (s.curCkaMsg, s.tcur))))))
def fig8StOfV (v : (fig8StT (ℓ := ℓ) (Pt := Pt)).denote) :
    SM.Construction.PartyState (CKA.DDH.State (BitVec 256) Pt) Pt Ratchet.RootKey
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256)) :=
  let (p, (rk, (vs?, (vrTbl, (γv, (cur?, tc)))))) := v
  ⟨boolToParty p, rk, vs?.map fsSendStOfV, fun t => (vrTbl t).map fsRecvStOfV, ckaStOfV γv, cur?, tc⟩

@[reducible] def smRrT (msgT : Ty (atomicSig ℓ Pt)) : Ty (atomicSig ℓ Pt) :=
  .sum .unit (.prod .nat (.prod .nat (.opt msgT)))
def smRrEnc {M : Type} {msgT : Ty (atomicSig ℓ Pt)} (encM : M → msgT.denote) :
    SM.RecvResult M → (smRrT (ℓ := ℓ) (Pt := Pt) msgT).denote
  | .rejected => .inl () | .accepted t i m => .inr (t, (i, m.map encM))
def smRrDec {M : Type} {msgT : Ty (atomicSig ℓ Pt)} (decM : msgT.denote → M) :
    (smRrT (ℓ := ℓ) (Pt := Pt) msgT).denote → SM.RecvResult M
  | .inl () => .rejected | .inr (t, (i, m)) => .accepted t i (m.map decM)

inductive CKATag where | send | sendBad | chall | receive | corr deriving DecidableEq, Repr
inductive PRNGTag where | process | challPrng | challPrf | corr deriving DecidableEq, Repr
inductive SMTag where | tr | ch | dl | ij | cr deriving DecidableEq, Repr
inductive SMTagDF where | tr | ch | dl | ij | cr | df deriving DecidableEq, Repr

/-- Target CKA challenger interface (`unifSpec + CKA.spec`). -/
@[reducible] def ckaTargetIface (ℓ : ℕ) (Pt : Type) [SampleableType Pt] :
    Iface (atomicSig ℓ Pt)
      (unifSpec + CKA.spec (CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt) where
  fwdU n := query
    (spec := unifSpec + CKA.spec (CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt) (.inl n)
  uCost := 1
  Tag := CKATag
  dom | .send | .chall | .receive | .corr => .bool | .sendBad => .prod .bool BV256
  cod
    | .send | .sendBad | .chall => .opt (.prod PtT PtT)
    | .receive => .opt .unit
    | .corr => .opt ckaStT
  enc
    | .send, p => .inr (.inl (.inl (.inl (.inl (boolToParty p)))))
    | .sendBad, (p, r) => .inr (.inl (.inl (.inl (.inr (boolToParty p, r)))))
    | .chall, p => .inr (.inl (.inl (.inr (boolToParty p))))
    | .receive, p => .inr (.inl (.inr (boolToParty p)))
    | .corr, p => .inr (.inr (boolToParty p))
  dec
    | .send, _, r => r
    | .sendBad, _, r => r
    | .chall, _, r => r
    | .receive, _, r => r
    | .corr, _, r => r.map ckaStV
  qCost | .send | .chall => 4 | .sendBad => 5 | .receive => 2 | .corr => 3
  smp := atomicSamplers ℓ Pt

/-- Target PRF-PRNG challenger interface (`unifSpec + PRFPRNG.spec`). -/
@[reducible] def prngTargetIface (ℓ : ℕ) (Pt : Type) [SampleableType Pt] :
    Iface (atomicSig ℓ Pt) (unifSpec + PRFPRNG.spec (BitVec 256) Pt (BitVec 256)) where
  fwdU n := query (spec := unifSpec + PRFPRNG.spec (BitVec 256) Pt (BitVec 256)) (.inl n)
  uCost := 1
  Tag := PRNGTag
  dom | .process | .challPrng => .opt PtT | .challPrf => PtT | .corr => .unit
  cod
    | .process | .challPrng => .opt BV256
    | .challPrf => .opt (.prod BV256 BV256)
    | .corr => .opt BV256
  enc
    | .process, i => .inr (.inl (.inl (.inl i)))
    | .challPrng, i => .inr (.inl (.inl (.inr i)))
    | .challPrf, i => .inr (.inl (.inr i))
    | .corr, () => .inr (.inr ())
  dec | .process, _, r => r | .challPrng, _, r => r | .challPrf, _, r => r | .corr, _, r => r
  qCost | .process | .challPrng => 3 | .challPrf => 4 | .corr => 2
  smp := atomicSamplers ℓ Pt

/-- Target FS-AEAD challenger interface with associated data `Header Pt` and messages
`LibsignalMsgPublicPart × Plain ℓ` (`redFSAuth`, `redFSPriv`, `redFSPrivCoin`, `B_fs`). -/
@[reducible] def fsaeadHeaderIface (ℓ : ℕ) (Pt : Type) [SampleableType Pt] :
    Iface (atomicSig ℓ Pt)
      (unifSpec + FSAEAD.spec (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        (SM.Construction.Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
        (ℕ × LibsignalCiphertextWithSalt32)) where
  fwdU n := query
    (spec := unifSpec + FSAEAD.spec (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (SM.Construction.Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32)) (.inl n)
  uCost := 1
  Tag := FSAEADTag
  dom
    | .tr => .prod fig8HdrT (.prod lpubT PlainT)
    | .ch => .prod fig8HdrT (.prod (.prod lpubT PlainT) (.prod lpubT PlainT))
    | .cs | .cr => .unit
    | .dl | .ij => .prod fig8HdrT lctT
  cod
    | .tr | .ch => .opt lctT
    | .cs => .opt fsSendStT
    | .cr => .opt (.prod fsSendStT fsRecvStT)
    | .dl | .ij => .opt (fsRrT (.prod lpubT PlainT))
  enc
    | .tr, (h, (pv, m)) => .inr (.inl (.inl (.inl (.inl (.inl (h, (lpubOfV pv, m)))))))
    | .ch, (h, ((pv0, m0), (pv1, m1))) =>
      .inr (.inl (.inl (.inl (.inl (.inr (h, ((lpubOfV pv0, m0), (lpubOfV pv1, m1))))))))
    | .cs, () => .inr (.inl (.inl (.inl (.inr ()))))
    | .cr, () => .inr (.inl (.inl (.inr ())))
    | .dl, (h, cv) => .inr (.inl (.inr (h, lctOfV cv)))
    | .ij, (h, cv) => .inr (.inr (h, lctOfV cv))
  dec
    | .tr, _, r => r.map lctV
    | .ch, _, r => r.map lctV
    | .cs, _, r => r.map fsSendStV
    | .cr, _, r => r.map fun (ss, rs) => (fsSendStV ss, fsRecvStV rs)
    | .dl, _, r => r.map (fsRrEnc fun (p, m) => (lpubV p, m))
    | .ij, _, r => r.map (fsRrEnc fun (p, m) => (lpubV p, m))
  qCost
    | .tr | .dl | .ij => 2 * (ℓ / 32) + 24
    | .ch => 3 * (ℓ / 32) + 32
    | .cs => 4
    | .cr => 50016
  smp := atomicSamplers ℓ Pt

/-- Target 5-oracle Fig. 8 SM challenger interface (`simFig8`, `challSim`, `privRedB`).
`qCost .cr = 50032` covers `PartyState` up to `maxForwardJumps = 25000` skipped keys. -/
@[reducible] def fig8SmIface (ℓ : ℕ) (Pt : Type) [SampleableType Pt] :
    Iface (atomicSig ℓ Pt)
      (unifSpec + SM.spec
        (SM.Construction.PartyState (CKA.DDH.State (BitVec 256) Pt) Pt Ratchet.RootKey
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256)))
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
        (SM.Construction.Header Pt × (ℕ × LibsignalCiphertextWithSalt32))) where
  fwdU n := query
    (spec := unifSpec + SM.spec
      (SM.Construction.PartyState (CKA.DDH.State (BitVec 256) Pt) Pt Ratchet.RootKey
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (SM.Construction.Header Pt × (ℕ × LibsignalCiphertextWithSalt32))) (.inl n)
  uCost := 1
  Tag := SMTag
  dom
    | .tr => .prod .bool (.prod (.prod lpubT PlainT) (.opt BV256))
    | .ch => .prod .bool (.prod (.prod lpubT PlainT) (.prod (.prod lpubT PlainT) (.opt BV256)))
    | .dl | .ij => .prod .bool fig8CtT
    | .cr => .bool
  cod
    | .tr | .ch => .opt fig8CtT
    | .dl | .ij => .opt (smRrT (.prod lpubT PlainT))
    | .cr => .opt fig8StT
  enc
    | .tr, (p, ((pv, m), r)) =>
      .inr (.inl (.inl (.inl (.inl (boolToParty p, (lpubOfV pv, m), r)))))
    | .ch, (p, ((pv0, m0), ((pv1, m1), r))) =>
      .inr (.inl (.inl (.inl (.inr (boolToParty p, (lpubOfV pv0, m0), (lpubOfV pv1, m1), r)))))
    | .dl, (p, cv) => .inr (.inl (.inl (.inr (boolToParty p, fig8CtOfV cv))))
    | .ij, (p, cv) => .inr (.inl (.inr (boolToParty p, fig8CtOfV cv)))
    | .cr, p => .inr (.inr (boolToParty p))
  dec
    | .tr, _, r => r.map fig8CtV
    | .ch, _, r => r.map fig8CtV
    | .dl, _, r => r.map (smRrEnc fun (pub, m) => (lpubV pub, m))
    | .ij, _, r => r.map (smRrEnc fun (pub, m) => (lpubV pub, m))
    | .cr, _, r => r.map fig8StV
  qCost
    | .tr => 2 * (ℓ / 32) + 26
    | .ch => 3 * (ℓ / 32) + 34
    | .dl | .ij => 2 * (ℓ / 32) + 24
    | .cr => 50032
  smp := atomicSamplers ℓ Pt

/-- Target 6-oracle Fig. 8 `DeliverForge` challenger interface (`simDeliverForge`, `challSimDF`). -/
@[reducible] def fig8SmIfaceDF (ℓ : ℕ) (Pt : Type) [SampleableType Pt] :
    Iface (atomicSig ℓ Pt)
      (unifSpec + SM.specDF
        (SM.Construction.PartyState (CKA.DDH.State (BitVec 256) Pt) Pt Ratchet.RootKey
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256)))
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
        (SM.Construction.Header Pt × (ℕ × LibsignalCiphertextWithSalt32))) where
  fwdU n := query
    (spec := unifSpec + SM.specDF
      (SM.Construction.PartyState (CKA.DDH.State (BitVec 256) Pt) Pt Ratchet.RootKey
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (SM.Construction.Header Pt × (ℕ × LibsignalCiphertextWithSalt32))) (.inl n)
  uCost := 1
  Tag := SMTagDF
  dom
    | .tr => .prod .bool (.prod (.prod lpubT PlainT) (.opt BV256))
    | .ch => .prod .bool (.prod (.prod lpubT PlainT) (.prod (.prod lpubT PlainT) (.opt BV256)))
    | .dl | .ij => .prod .bool fig8CtT
    | .cr => .bool
    | .df => .prod .bool (.prod fig8CtT fig8CtT)
  cod
    | .tr | .ch => .opt fig8CtT
    | .dl | .ij | .df => .opt (smRrT (.prod lpubT PlainT))
    | .cr => .opt fig8StT
  enc
    | .tr, (p, ((pv, m), r)) =>
      .inr (.inl (.inl (.inl (.inl (.inl (boolToParty p, (lpubOfV pv, m), r))))))
    | .ch, (p, ((pv0, m0), ((pv1, m1), r))) =>
      .inr (.inl (.inl (.inl (.inl (.inr
        (boolToParty p, (lpubOfV pv0, m0), (lpubOfV pv1, m1), r))))))
    | .dl, (p, cv) => .inr (.inl (.inl (.inl (.inr (boolToParty p, fig8CtOfV cv)))))
    | .ij, (p, cv) => .inr (.inl (.inl (.inr (boolToParty p, fig8CtOfV cv))))
    | .cr, p => .inr (.inl (.inr (boolToParty p)))
    | .df, (p, (cv1, cv2)) => .inr (.inr (boolToParty p, fig8CtOfV cv1, fig8CtOfV cv2))
  dec
    | .tr, _, r => r.map fig8CtV
    | .ch, _, r => r.map fig8CtV
    | .dl, _, r => r.map (smRrEnc fun (pub, m) => (lpubV pub, m))
    | .ij, _, r => r.map (smRrEnc fun (pub, m) => (lpubV pub, m))
    | .cr, _, r => r.map fig8StV
    | .df, _, r => r.map (smRrEnc fun (pub, m) => (lpubV pub, m))
  qCost
    | .tr => 2 * (ℓ / 32) + 26
    | .ch => 3 * (ℓ / 32) + 34
    | .dl | .ij => 2 * (ℓ / 32) + 24
    | .cr => 50032
    | .df => 3 * (ℓ / 32) + 36
  smp := atomicSamplers ℓ Pt

/-- Source 5-oracle Fig. 8 SM game codec (`codecCost = 32`). -/
@[reducible] def fig8SmCodec (ℓ : ℕ) (Pt : Type) :
    GameCodec (atomicSig ℓ Pt)
      (SM.spec
        (SM.Construction.PartyState (CKA.DDH.State (BitVec 256) Pt) Pt Ratchet.RootKey
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256)))
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
        (SM.Construction.Header Pt × (ℕ × LibsignalCiphertextWithSalt32))) where
  Q := .sum (.prod .bool (.prod (.prod lpubT PlainT) (.opt BV256)))
    (.sum (.prod .bool (.prod (.prod lpubT PlainT) (.prod (.prod lpubT PlainT) (.opt BV256))))
    (.sum (.prod .bool fig8CtT) (.sum (.prod .bool fig8CtT) .bool)))
  R := .sum (.opt fig8CtT) (.sum (.opt (smRrT (.prod lpubT PlainT))) (.opt fig8StT))
  qenc
    | .inl (.inl (.inl (.inl (p, (pub, m), r)))) => .inl (partyToBool p, ((lpubV pub, m), r))
    | .inl (.inl (.inl (.inr (p, (pub0, m0), (pub1, m1), r)))) =>
      .inr (.inl (partyToBool p, ((lpubV pub0, m0), ((lpubV pub1, m1), r))))
    | .inl (.inl (.inr (p, c))) => .inr (.inr (.inl (partyToBool p, fig8CtV c)))
    | .inl (.inr (p, c)) => .inr (.inr (.inr (.inl (partyToBool p, fig8CtV c))))
    | .inr p => .inr (.inr (.inr (.inr (partyToBool p))))
  rdec
    | .inl (.inl (.inl (.inl _))), .inl r => r.map fig8CtOfV
    | .inl (.inl (.inl (.inl _))), _ => none
    | .inl (.inl (.inl (.inr _))), .inl r => r.map fig8CtOfV
    | .inl (.inl (.inl (.inr _))), _ => none
    | .inl (.inl (.inr _)), .inr (.inl r) =>
      r.map (smRrDec (msgT := .prod lpubT PlainT) fun (pv, m) => (lpubOfV pv, m))
    | .inl (.inl (.inr _)), _ => none
    | .inl (.inr _), .inr (.inl r) =>
      r.map (smRrDec (msgT := .prod lpubT PlainT) fun (pv, m) => (lpubOfV pv, m))
    | .inl (.inr _), _ => none
    | .inr _, .inr (.inr r) => r.map fig8StOfV
    | .inr _, _ => none
  codecCost := 32

/-- Source 6-oracle Fig. 8 `DeliverForge` SM game codec (`codecCost = 32`). -/
@[reducible] def fig8SmCodecDF (ℓ : ℕ) (Pt : Type) :
    GameCodec (atomicSig ℓ Pt)
      (SM.specDF
        (SM.Construction.PartyState (CKA.DDH.State (BitVec 256) Pt) Pt Ratchet.RootKey
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256)))
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
        (SM.Construction.Header Pt × (ℕ × LibsignalCiphertextWithSalt32))) where
  Q := .sum (.prod .bool (.prod (.prod lpubT PlainT) (.opt BV256)))
    (.sum (.prod .bool (.prod (.prod lpubT PlainT) (.prod (.prod lpubT PlainT) (.opt BV256))))
    (.sum (.prod .bool fig8CtT) (.sum (.prod .bool fig8CtT)
      (.sum .bool (.prod .bool (.prod fig8CtT fig8CtT))))))
  R := .sum (.opt fig8CtT) (.sum (.opt (smRrT (.prod lpubT PlainT))) (.opt fig8StT))
  qenc
    | .inl (.inl (.inl (.inl (.inl (p, (pub, m), r))))) =>
      .inl (partyToBool p, ((lpubV pub, m), r))
    | .inl (.inl (.inl (.inl (.inr (p, (pub0, m0), (pub1, m1), r))))) =>
      .inr (.inl (partyToBool p, ((lpubV pub0, m0), ((lpubV pub1, m1), r))))
    | .inl (.inl (.inl (.inr (p, c)))) => .inr (.inr (.inl (partyToBool p, fig8CtV c)))
    | .inl (.inl (.inr (p, c))) => .inr (.inr (.inr (.inl (partyToBool p, fig8CtV c))))
    | .inl (.inr p) => .inr (.inr (.inr (.inr (.inl (partyToBool p)))))
    | .inr (p, c1, c2) => .inr (.inr (.inr (.inr (.inr (partyToBool p, (fig8CtV c1, fig8CtV c2))))))
  rdec
    | .inl (.inl (.inl (.inl (.inl _)))), .inl r => r.map fig8CtOfV
    | .inl (.inl (.inl (.inl (.inl _)))), _ => none
    | .inl (.inl (.inl (.inl (.inr _)))), .inl r => r.map fig8CtOfV
    | .inl (.inl (.inl (.inl (.inr _)))), _ => none
    | .inl (.inl (.inl (.inr _))), .inr (.inl r) =>
      r.map (smRrDec (msgT := .prod lpubT PlainT) fun (pv, m) => (lpubOfV pv, m))
    | .inl (.inl (.inl (.inr _))), _ => none
    | .inl (.inl (.inr _)), .inr (.inl r) =>
      r.map (smRrDec (msgT := .prod lpubT PlainT) fun (pv, m) => (lpubOfV pv, m))
    | .inl (.inl (.inr _)), _ => none
    | .inl (.inr _), .inr (.inr r) => r.map fig8StOfV
    | .inl (.inr _), _ => none
    | .inr _, .inr (.inl r) =>
      r.map (smRrDec (msgT := .prod lpubT PlainT) fun (pv, m) => (lpubOfV pv, m))
    | .inr _, _ => none
  codecCost := 32

@[reducible] def recvResultT : Ty (atomicSig ℓ Pt) := .sum .unit (.prod .nat (.prod .nat (.opt PlainT)))
def recvResultEnc : SM.RecvResult (Plain ℓ) → (recvResultT (ℓ := ℓ) (Pt := Pt)).denote
  | .rejected => .inl () | .accepted t i m => .inr (t, (i, m))
def recvResultDec : (recvResultT (ℓ := ℓ) (Pt := Pt)).denote → SM.RecvResult (Plain ℓ)
  | .inl () => .rejected | .inr (t, (i, m)) => .accepted t i m

@[reducible] def smQT : Ty (atomicSig ℓ Pt) :=
  .sum (.prod .bool (.prod PlainT (.opt BV512)))
  (.sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
  (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool)))

def smQenc {St : Type} :
    (SM.spec St (Plain ℓ) (BitVec 512) Bytes).Domain → (smQT (ℓ := ℓ) (Pt := Pt)).denote
  | .inl (.inl (.inl (.inl (p, m, r)))) => .inl (partyToBool p, (m, r))
  | .inl (.inl (.inl (.inr (p, m0, m1, r)))) => .inr (.inl (partyToBool p, (m0, (m1, r))))
  | .inl (.inl (.inr (p, c))) => .inr (.inr (.inl (partyToBool p, c)))
  | .inl (.inr (p, c)) => .inr (.inr (.inr (.inl (partyToBool p, c))))
  | .inr p => .inr (.inr (.inr (.inr (partyToBool p))))

@[reducible] def smRT (stT : Ty (atomicSig ℓ Pt)) : Ty (atomicSig ℓ Pt) :=
  .prod (.opt (B 32)) (.prod (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))) (.opt stT))

def smRdec {St : Type} {stT : Ty (atomicSig ℓ Pt)} (ofSt : stT.denote → St) :
    (q : (SM.spec St (Plain ℓ) (BitVec 512) Bytes).Domain) →
    (smRT (ℓ := ℓ) (Pt := Pt) stT).denote →
    (SM.spec St (Plain ℓ) (BitVec 512) Bytes).Range q
  | .inl (.inl (.inl (.inl _))), (w, _) => w
  | .inl (.inl (.inl (.inr _))), (w, _) => w
  | .inl (.inl (.inr _)), (_, (rr, _)) => rr.map recvResultDec
  | .inl (.inr _), (_, (rr, _)) => rr.map recvResultDec
  | .inr _, (_, (_, st?)) => st?.map ofSt

/-- Source SM game codec for a single libsignal session (`GhostState Bytes`, `codecCost = 16`). -/
@[reducible] def e2eSessionCodec (ℓ : ℕ) (Pt : Type := Empty) :
    GameCodec (atomicSig ℓ Pt) (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) where
  Q := smQT (ℓ := ℓ) (Pt := Pt)
  R := smRT (ℓ := ℓ) (Pt := Pt) GhostStT
  qenc := smQenc (St := GhostState Bytes)
  rdec := smRdec (stT := GhostStT) id
  codecCost := 16

end L2Fig8AndSessionCodecs

/-! ## Multi-session composition and binary-harness adapter interfaces and codecs -/

section L3CompositionAndAdapterCodecs

/-- Stage-1 to stage-2 prefix context `(idA, (idB, spkCoins))` for `prefixRed`. -/
@[reducible] def prefixCtxT {ℓ : ℕ} {Pt : Type} : Ty (atomicSig ℓ Pt) :=
  .prod IdKey (.prod IdKey BV256)

inductive E2EKeyIndTag where | keyInd deriving DecidableEq, Repr
inductive E2ESessionTag where | tr | ch | dl | ij | cr deriving DecidableEq, Repr
inductive E2EAdapterTag where | ki | ctl | tr | ch | dl | ij | cr deriving DecidableEq, Repr

/-- Target `KeyInd` oracle interface for `R_e2e.kindRed` (`qCost = 128`). -/
@[reducible] def e2eKeyIndTargetIface (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type := Empty) :
    Iface (atomicSig ℓ Pt) (unifSpec + SignalPqxdh.keyIndSpec S) where
  fwdU n := query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inl n)
  uCost := 1
  Tag := E2EKeyIndTag
  dom | .keyInd => keyIndQT (ℓ := ℓ) (Pt := Pt) S
  cod | .keyInd => keyIndRT (ℓ := ℓ) (Pt := Pt)
  enc | .keyInd, q => .inr (keyIndQdec (ℓ := ℓ) (Pt := Pt) q)
  dec | .keyInd, _, r => keyIndRenc (ℓ := ℓ) (Pt := Pt) r
  qCost | .keyInd => 128
  smp := atomicBaseSamplers ℓ Pt

/-- Target single-session SM oracle interface for `R_e2e.prefixRed` (`qCost .cr = 32000` covers
unpacked `ghostPartsT` leaf-blocks under the `11000`-block PQ clamp). -/
@[reducible] def e2eSessionTargetIface (ℓ : ℕ) (Pt : Type := Empty) :
    Iface (atomicSig ℓ Pt)
      (unifSpec + SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) where
  fwdU n := query (spec := unifSpec + SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (.inl n)
  uCost := 1
  Tag := E2ESessionTag
  dom
    | .tr => .prod .bool (.prod PlainT (.opt BV512))
    | .ch => .prod .bool (.prod PlainT (.prod PlainT (.opt BV512)))
    | .dl | .ij => .prod .bool (B 32)
    | .cr => .bool
  cod
    | .tr | .ch => .opt (B 32)
    | .dl | .ij => .opt (recvResultT (ℓ := ℓ) (Pt := Pt))
    | .cr => .opt GhostStT
  enc
    | .tr, (p, (m, r)) => .inr (.inl (.inl (.inl (.inl (boolToParty p, m, r)))))
    | .ch, (p, (m0, (m1, r))) => .inr (.inl (.inl (.inl (.inr (boolToParty p, m0, m1, r)))))
    | .dl, (p, c) => .inr (.inl (.inl (.inr (boolToParty p, c))))
    | .ij, (p, c) => .inr (.inl (.inr (boolToParty p, c)))
    | .cr, p => .inr (.inr (boolToParty p))
  dec
    | .tr, _, r => r
    | .ch, _, r => r
    | .dl, _, r => r.map recvResultEnc
    | .ij, _, r => r.map recvResultEnc
    | .cr, _, r => r
  qCost
    | .tr | .dl | .ij => ℓ / 32 + 16
    | .ch => 2 * (ℓ / 32) + 18
    | .cr => 32000
  smp := atomicBaseSamplers ℓ Pt

@[reducible] def e2eCtlSpec (Ctl : Type) : OracleSpec Ctl := fun _ => Option ℕ
@[reducible] def e2eDrSpec (St : Type) (ℓ : ℕ) :
    OracleSpec (ℕ × (SM.spec St (Plain ℓ) (BitVec 512) Bytes).Domain) :=
  fun x => (SM.spec St (Plain ℓ) (BitVec 512) Bytes).Range x.2

/-- Composed non-coin game specification summing `keyIndSpec`, session-start control, and indexed SM
sessions. -/
@[reducible] def e2eComposedGameSpec (S : SignalPqxdh.Setup) (Ctl St : Type) (ℓ : ℕ) :=
  SignalPqxdh.keyIndSpec S + e2eCtlSpec Ctl + e2eDrSpec St ℓ

/-- Target oracle interface for `L_bh` (`unifSpec + e2eComposedGameSpec S Ctl (GhostState Bytes) ℓ`),
parameterized by `mkStart : SessionId S → Ctl` (`qCost .cr = 32000`). -/
@[reducible] def e2eAdapterIface (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type := Empty) {Ctl : Type}
    (mkStart : SignalPqxdh.SessionId S → Ctl) :
    Iface (atomicSig ℓ Pt) (unifSpec + e2eComposedGameSpec S Ctl (GhostState Bytes) ℓ) where
  fwdU n := query (spec := unifSpec + e2eComposedGameSpec S Ctl (GhostState Bytes) ℓ) (.inl n)
  uCost := 1
  Tag := E2EAdapterTag
  dom
    | .ki => keyIndQT (ℓ := ℓ) (Pt := Pt) S
    | .ctl => sidT (ℓ := ℓ) (Pt := Pt) S
    | .tr => .prod .nat (.prod .bool (.prod PlainT (.opt BV512)))
    | .ch => .prod .nat (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
    | .dl | .ij => .prod .nat (.prod .bool (B 32))
    | .cr => .prod .nat .bool
  cod
    | .ki => keyIndRT (ℓ := ℓ) (Pt := Pt)
    | .ctl => .opt .nat
    | .tr | .ch => .opt (B 32)
    | .dl | .ij => .opt (recvResultT (ℓ := ℓ) (Pt := Pt))
    | .cr => .opt GhostStT
  enc
    | .ki, kq => .inr (.inl (.inl (keyIndQdec (ℓ := ℓ) (Pt := Pt) kq)))
    | .ctl, sid => .inr (.inl (.inr (mkStart (sidOfV (ℓ := ℓ) (Pt := Pt) sid))))
    | .tr, (i, (p, (m, r))) => .inr (.inr ⟨i, .inl (.inl (.inl (.inl (boolToParty p, m, r))))⟩)
    | .ch, (i, (p, (m0, (m1, r)))) =>
      .inr (.inr ⟨i, .inl (.inl (.inl (.inr (boolToParty p, m0, m1, r))))⟩)
    | .dl, (i, (p, c)) => .inr (.inr ⟨i, .inl (.inl (.inr (boolToParty p, c)))⟩)
    | .ij, (i, (p, c)) => .inr (.inr ⟨i, .inl (.inr (boolToParty p, c))⟩)
    | .cr, (i, p) => .inr (.inr ⟨i, .inr (boolToParty p)⟩)
  dec
    | .ki, _, r => keyIndRenc (ℓ := ℓ) (Pt := Pt) r
    | .ctl, _, r => r
    | .tr, _, r => r
    | .ch, _, r => r
    | .dl, _, r => r.map recvResultEnc
    | .ij, _, r => r.map recvResultEnc
    | .cr, _, r => r
  qCost
    | .ki => 128
    | .ctl => 4
    | .tr | .dl | .ij => ℓ / 32 + 16
    | .ch => 2 * (ℓ / 32) + 18
    | .cr => 32000
  smp := atomicBaseSamplers ℓ Pt

/-- Source game codec for `R_e2e` (`e2eComposedGameSpec S Ctl (GhostState Bytes) ℓ`,
`codecCost = 64`). -/
@[reducible] def e2eGameCodec (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type := Empty) {Ctl : Type}
    (unStart : Ctl → SignalPqxdh.SessionId S) :
    GameCodec (atomicSig ℓ Pt) (e2eComposedGameSpec S Ctl (GhostState Bytes) ℓ) where
  Q := .sum (.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S))
    (.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)))
  R := .sum (.sum (keyIndRT (ℓ := ℓ) (Pt := Pt)) (.opt .nat)) (smRT (ℓ := ℓ) (Pt := Pt) GhostStT)
  qenc
    | .inl (.inl kq) => .inl (.inl (keyIndQenc (ℓ := ℓ) (Pt := Pt) kq))
    | .inl (.inr cq) => .inl (.inr (sidV (ℓ := ℓ) (Pt := Pt) (unStart cq)))
    | .inr ⟨i, sq⟩ => .inr (i, smQenc (ℓ := ℓ) (Pt := Pt) sq)
  rdec
    | .inl (.inl _), .inl (.inl r) => keyIndRdec (ℓ := ℓ) (Pt := Pt) r
    | .inl (.inl _), _ => .noneResp
    | .inl (.inr _), .inl (.inr r) => r
    | .inl (.inr _), _ => none
    | .inr ⟨_, sq⟩, .inr sr => smRdec (ℓ := ℓ) (Pt := Pt) (stT := GhostStT) id sq sr
    | .inr ⟨_, sq⟩, .inl _ =>
      smRdec (ℓ := ℓ) (Pt := Pt) (stT := GhostStT) id sq (none, (none, none))
  codecCost := 64

/-- Source game codec for `L_bh` (`e2eComposedGameSpec S Ctl BinState ℓ`, `codecCost = 64`). -/
@[reducible] def e2eAdapterCodec (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type := Empty) {Ctl : Type}
    (unStart : Ctl → SignalPqxdh.SessionId S) :
    GameCodec (atomicSig ℓ Pt) (e2eComposedGameSpec S Ctl BinState ℓ) where
  Q := .sum (.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S))
    (.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)))
  R := .sum (.sum (keyIndRT (ℓ := ℓ) (Pt := Pt)) (.opt .nat)) (smRT (ℓ := ℓ) (Pt := Pt) BinStT)
  qenc
    | .inl (.inl kq) => .inl (.inl (keyIndQenc (ℓ := ℓ) (Pt := Pt) kq))
    | .inl (.inr cq) => .inl (.inr (sidV (ℓ := ℓ) (Pt := Pt) (unStart cq)))
    | .inr ⟨i, sq⟩ => .inr (i, smQenc (ℓ := ℓ) (Pt := Pt) sq)
  rdec
    | .inl (.inl _), .inl (.inl r) => keyIndRdec (ℓ := ℓ) (Pt := Pt) r
    | .inl (.inl _), _ => .noneResp
    | .inl (.inr _), .inl (.inr r) => r
    | .inl (.inr _), _ => none
    | .inr ⟨_, sq⟩, .inr sr => smRdec (ℓ := ℓ) (Pt := Pt) (stT := BinStT) id sq sr
    | .inr ⟨_, sq⟩, .inl _ =>
      smRdec (ℓ := ℓ) (Pt := Pt) (stT := BinStT) id sq (none, (none, none))
  codecCost := 64

end L3CompositionAndAdapterCodecs
end ReductionDsl

namespace SignalPqxdh.Costed

export _root_.ReductionDsl (
  pqAtomicSig pqAtomicOps pqAtomicSamplers
  PTag pqPrimIface pqSigAndDdhIface pqKeyIndCodec
)

@[reducible] def PB (w : ℕ+) : _root_.ReductionDsl.Ty pqAtomicSig :=
  _root_.ReductionDsl.PB (ℓ := 0) (Pt := Empty) w

@[reducible] def PU32 : _root_.ReductionDsl.Ty pqAtomicSig :=
  _root_.ReductionDsl.PU32 (ℓ := 0) (Pt := Empty)

@[reducible] def keyIndCodec (S : Setup) :
    _root_.ReductionDsl.GameCodec pqAtomicSig (keyIndSpec S) :=
  pqKeyIndCodec S

end SignalPqxdh.Costed
