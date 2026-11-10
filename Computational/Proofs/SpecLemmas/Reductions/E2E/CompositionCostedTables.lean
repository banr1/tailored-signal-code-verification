/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementComposed
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhSessionModel
public import Computational.Specifications.Assumptions.KeyInd1KeyReal
public import Computational.Specifications.Reductions.ReductionDsl.Samplers
public import Computational.Proofs.SpecLemmas.Session.ACD19.SM.CostedTables

/-!
# Shared ReductionDsl tables, interfaces, and game codecs for E2E composition

**Checked by Lean.** Defines the shared `e2eSig` sort signature, coin-only uniform sampler table,
pure/curve-check/cryptographic operation tables, target oracle interfaces, and game codecs for the
end-to-end composition reductions (`R_e2e`) and binary-harness wire/state adapter (`L_bh`).
-/
@[expose] public section

set_option autoImplicit false

open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto GhostState IdentityKey MessageKeyGenerator PublicKey ReceiverChain SenderChain ShaCompress aesCbcDecrypt aesCbcEncrypt currentVersion versionByte)
open CryptoGames.Ratchet.LibsignalInst (ratchetKeyAdmissible)
open CryptoVerification.E2E (BinState Bytes PreKeyMessageFields RecordExtras binStateOfUnderExtras kyberKey ofU8 shortCiphertext toU8 u32 u8Vec vecU8 wirePrekey wireWhisper)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open ReductionDsl (GameCodec Iface Ops Samplers Sig Ty bits)

namespace Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables

open OracleSpec OracleComp

/-! ## Base sorts and block-size signature -/

/-- Base sorts of the shared E2E `ReductionDsl` signature `e2eSig ℓ`. -/
inductive E2ESort where
  | pbytes (w : ℕ+)
  | pu32
  | bytes (w : ℕ+)
  | u8
  | u32
  | u64
  | bv128
  | bv256
  | bv512
  | fin (n : ℕ)
  | pk
  | idKey
  | plain
  | ghostSt
  | binSt
  deriving DecidableEq

@[reducible] def E2ESort.den (ℓ : ℕ) : E2ESort → Type
  | .pbytes _ => SignalPqxdh.Bytes
  | .pu32 => UInt32
  | .bytes _ => Bytes
  | .u8 => BitVec 8
  | .u32 => BitVec 32
  | .u64 => BitVec 64
  | .bv128 => BitVec 128
  | .bv256 => BitVec 256
  | .bv512 => BitVec 512
  | .fin n => Fin n
  | .pk => PublicKey
  | .idKey => IdentityKey
  | .plain => Plain ℓ
  | .ghostSt => GhostState Bytes
  | .binSt => BinState

/-- Leaf-maximum 32-byte block count of a model `GhostState Bytes`. -/
def ghostStBlocks (g : GhostState Bytes) : ℕ :=
  let pqBlk := (g.session.pqRatchetState.length + 31) / 32
  let rcBlk := g.session.receiverChains.foldr
    (fun rc acc => max acc (rc.messageKeys.foldr
      (fun mk m => max m ((mk.seed.length + 31) / 32)) rc.messageKeys.length))
    g.session.receiverChains.length
  let ceBlk := g.chainEpochs.foldr (fun e acc => max acc (bits e)) g.chainEpochs.length
  max 1 (max pqBlk (max rcBlk (max ceBlk (bits g.epoch))))

/-- Leaf-maximum 32-byte block count of a binary `BinState`. -/
def binStBlocks (bs : BinState) : ℕ :=
  let bBlk := (bs.bytes.length + 31) / 32
  let chBlk := bs.epochs.chains.foldr (fun p acc => max acc (bits p.2)) bs.epochs.chains.length
  max 1 (max bBlk (max chBlk (bits bs.epochs.epoch)))

def E2ESort.blocks (ℓ : ℕ) : (s : E2ESort) → s.den ℓ → ℕ
  | .pbytes w, x => (x.length + w - 1) / w
  | .pu32, _ => 1
  | .bytes w, x => (x.length + w - 1) / w
  | .u8, _ | .u32, _ | .u64, _ | .bv128, _ | .bv256, _ => 1
  | .plain, _ => ℓ / 32 + 1
  | .bv512, _ | .pk, _ | .idKey, _ => 2
  | .fin _, k => max 1 (bits k.val)
  | .ghostSt, g => ghostStBlocks g
  | .binSt, bs => binStBlocks bs

/-- Shared E2E `ReductionDsl` signature at plaintext byte length `ℓ`. -/
@[reducible] def e2eSig (ℓ : ℕ) : Sig where
  Base := E2ESort
  den := E2ESort.den ℓ
  sz := E2ESort.blocks ℓ

section TyAbbrevs

variable {ℓ : ℕ}

@[reducible] def PB (w : ℕ+) : Ty (e2eSig ℓ) := .base (.pbytes w)
@[reducible] def PU32 : Ty (e2eSig ℓ) := .base .pu32
@[reducible] def B (w : ℕ+) : Ty (e2eSig ℓ) := .base (.bytes w)
@[reducible] def U8 : Ty (e2eSig ℓ) := .base .u8
@[reducible] def U32 : Ty (e2eSig ℓ) := .base .u32
@[reducible] def U64 : Ty (e2eSig ℓ) := .base .u64
@[reducible] def BV128 : Ty (e2eSig ℓ) := .base .bv128
@[reducible] def BV256 : Ty (e2eSig ℓ) := .base .bv256
@[reducible] def BV512 : Ty (e2eSig ℓ) := .base .bv512
@[reducible] def FinT (n : ℕ) : Ty (e2eSig ℓ) := .base (.fin n)
@[reducible] def PK : Ty (e2eSig ℓ) := .base .pk
@[reducible] def IdKey : Ty (e2eSig ℓ) := .base .idKey
@[reducible] def PlainT : Ty (e2eSig ℓ) := .base .plain
@[reducible] def GhostStT : Ty (e2eSig ℓ) := .base .ghostSt
@[reducible] def BinStT : Ty (e2eSig ℓ) := .base .binSt

@[reducible] def drKeyT : Ty (e2eSig ℓ) := .prod (PB 32) (.prod (PB 32) (PB 32))

def drKeyV (k : SignalPqxdh.DRKey) : (drKeyT (ℓ := ℓ)).denote := (k.rootKey, (k.chainKey, k.pqrKey))
def drKeyOfV (v : (drKeyT (ℓ := ℓ)).denote) : SignalPqxdh.DRKey := ⟨v.1, v.2.1, v.2.2⟩

@[reducible] def bundleT : Ty (e2eSig ℓ) :=
  .prod (PB 32) (.prod PU32 (.prod (PB 32) (.prod (PB 64)
    (.prod (.opt (.prod PU32 (PB 32))) (.prod PU32 (.prod (PB 1568) (PB 64)))))))

def bundleV (b : SignalPqxdh.PreKeyBundleInput) : (bundleT (ℓ := ℓ)).denote :=
  (b.ikB, (b.spkId, (b.spkB, (b.spkSig, (b.opkB?, (b.pqspkId, (b.pqspkB, b.pqspkSig)))))))
def bundleOfV (v : (bundleT (ℓ := ℓ)).denote) : SignalPqxdh.PreKeyBundleInput :=
  ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2⟩

@[reducible] def hdrT : Ty (e2eSig ℓ) :=
  .prod (PB 32) (.prod (PB 32) (.prod PU32 (.prod (.opt PU32) (.prod PU32 (PB 1568)))))

def hdrV (h : SignalPqxdh.HandshakeHdr) : (hdrT (ℓ := ℓ)).denote :=
  (h.ikAPk, (h.ekAPk, (h.spkId, (h.opkId?, (h.pqspkId, h.kemCt)))))
def hdrOfV (v : (hdrT (ℓ := ℓ)).denote) : SignalPqxdh.HandshakeHdr :=
  ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩

@[reducible] def sidT (S : SignalPqxdh.Setup) : Ty (e2eSig ℓ) :=
  .sum (.prod (FinT S.N_id) (FinT S.N_send_opk))
    (.sum (.prod (FinT S.N_id) (FinT S.N_send_no_opk))
      (.sum (.prod (FinT S.N_id) (.prod (FinT S.N_recv) (FinT S.N_opk)))
            (.prod (FinT S.N_id) (.prod (FinT S.N_recv) (FinT S.N_no_opk)))))

def sidV {S : SignalPqxdh.Setup} : SignalPqxdh.SessionId S → (sidT (ℓ := ℓ) S).denote
  | .sendOPK u i => .inl (u, i)
  | .sendNoOPK u i => .inr (.inl (u, i))
  | .recvOPK k j o => .inr (.inr (.inl (k, (j, o))))
  | .recvNoOPK k j l => .inr (.inr (.inr (k, (j, l))))

def sidOfV {S : SignalPqxdh.Setup} : (sidT (ℓ := ℓ) S).denote → SignalPqxdh.SessionId S
  | .inl (u, i) => .sendOPK u i
  | .inr (.inl (u, i)) => .sendNoOPK u i
  | .inr (.inr (.inl (k, (j, o)))) => .recvOPK k j o
  | .inr (.inr (.inr (k, (j, l)))) => .recvNoOPK k j l

@[reducible] def dhSecretsT : Ty (e2eSig ℓ) :=
  .prod (.list (PB 32)) (.prod (.list (PB 32)) (.prod (.list (PB 32)) (.list (PB 32))))

@[reducible] def keyIndQT (S : SignalPqxdh.Setup) : Ty (e2eSig ℓ) :=
  .sum (FinT S.N_id)
  (.sum (FinT S.N_id)
  (.sum (.prod (FinT S.N_id) (FinT S.N_recv))
  (.sum (.prod (FinT S.N_id) (.prod (FinT S.N_recv) (FinT S.N_opk)))
  (.sum (.prod (FinT S.N_id) (.prod (FinT S.N_send_opk) bundleT))
  (.sum (.prod (FinT S.N_id) (.prod (FinT S.N_send_no_opk) bundleT))
  (.sum (.prod (FinT S.N_id) (.prod (FinT S.N_recv) (.prod (FinT S.N_opk) hdrT)))
  (.sum (.prod (FinT S.N_id) (.prod (FinT S.N_recv) (.prod (FinT S.N_no_opk) hdrT)))
  (.sum (sidT S)
  (.sum (PB 192)
  (.sum .unit
  (.sum (sidT S)
  (.sum (PB 32)
        (.prod (FinT S.N_id) (FinT S.N_recv))))))))))))))

def keyIndQenc {S : SignalPqxdh.Setup} :
    SignalPqxdh.KeyIndQuery S → (keyIndQT (ℓ := ℓ) S).denote
  | .initPrin u => .inl u
  | .corruptIK u => .inr (.inl u)
  | .genSPK u j => .inr (.inr (.inl (u, j)))
  | .genOPK u j o => .inr (.inr (.inr (.inl (u, (j, o)))))
  | .initiateOPK u i b => .inr (.inr (.inr (.inr (.inl (u, (i, bundleV b))))))
  | .initiateNoOPK u i b => .inr (.inr (.inr (.inr (.inr (.inl (u, (i, bundleV b)))))))
  | .acceptOPK k j o h => .inr (.inr (.inr (.inr (.inr (.inr (.inl (k, (j, (o, hdrV h)))))))))
  | .acceptNoOPK k j l h =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (k, (j, (l, hdrV h))))))))))
  | .testSession sid =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (sidV sid)))))))))
  | .roQuery sec =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl sec)))))))))
  | .revealDhSecrets =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))))))
  | .revealSessionKey sid =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (sidV sid))))))))))))
  | .registerKey sk =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl sk))))))))))))
  | .revealSpkSk u j =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (u, j)))))))))))))

def keyIndQdec {S : SignalPqxdh.Setup} :
    (keyIndQT (ℓ := ℓ) S).denote → SignalPqxdh.KeyIndQuery S
  | .inl u => .initPrin u
  | .inr (.inl u) => .corruptIK u
  | .inr (.inr (.inl (u, j))) => .genSPK u j
  | .inr (.inr (.inr (.inl (u, (j, o))))) => .genOPK u j o
  | .inr (.inr (.inr (.inr (.inl (u, (i, b)))))) => .initiateOPK u i (bundleOfV b)
  | .inr (.inr (.inr (.inr (.inr (.inl (u, (i, b))))))) => .initiateNoOPK u i (bundleOfV b)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl (k, (j, (o, h))))))))) => .acceptOPK k j o (hdrOfV h)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (k, (j, (l, h)))))))))) =>
    .acceptNoOPK k j l (hdrOfV h)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl sid)))))))) =>
    .testSession (sidOfV sid)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl sec))))))))) => .roQuery sec
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ())))))))))) =>
    .revealDhSecrets
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl sid))))))))))) =>
    .revealSessionKey (sidOfV sid)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl sk)))))))))))) =>
    .registerKey sk
  | .inr (.inr (.inr (.inr (.inr (.inr
      (.inr (.inr (.inr (.inr (.inr (.inr (.inr (u, j))))))))))))) =>
    .revealSpkSk u j

@[reducible] def keyIndRT : Ty (e2eSig ℓ) :=
  .sum .unit (.sum (.prod (PB 32) (PB 32)) (.sum (PB 32) (.sum (.prod (PB 32) (PB 32))
  (.sum bundleT (.sum hdrT (.sum (.prod drKeyT hdrT)
  (.sum .unit (.sum drKeyT (.sum dhSecretsT (PB 32))))))))))

def keyIndRenc : SignalPqxdh.KeyIndResponse → (keyIndRT (ℓ := ℓ)).denote
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

def keyIndRdec : (keyIndRT (ℓ := ℓ)).denote → SignalPqxdh.KeyIndResponse
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

@[reducible] def prefixCtxT : Ty (e2eSig ℓ) := .prod IdKey (.prod IdKey BV256)

@[reducible] def spqrParamsT : Ty (e2eSig ℓ) := .prod U32 U32
@[reducible] def spqrVnT : Ty (e2eSig ℓ) := .prod (B 32) (.prod U32 (.prod U32 (.opt spqrParamsT)))
@[reducible] def spqrPrevEntryT : Ty (e2eSig ℓ) := .prod U32 BV256
/-- Value representation `(ctr, next, prevEntries, prevUnalignedTail)` of `LibsignalSpqrV1.EpochDirectionPB`. -/
@[reducible] def spqrDirT : Ty (e2eSig ℓ) :=
  .prod U32 (.prod (B 32) (.prod (.list spqrPrevEntryT) (B 35)))
@[reducible] def spqrEpochLinkT : Ty (e2eSig ℓ) := .prod (.opt spqrDirT) (.opt spqrDirT)
/-- Value representation `(direction, currentEpoch, links, nextRoot, sendEpoch, params)` of `LibsignalSpqrV1.ChainPB`. -/
@[reducible] def spqrChainT : Ty (e2eSig ℓ) :=
  .prod U32 (.prod U64 (.prod (.list spqrEpochLinkT) (.prod (B 32) (.prod U64 (.opt spqrParamsT)))))
@[reducible] def spqrStatePartsT : Ty (e2eSig ℓ) :=
  .prod (.opt (B 32)) (.prod (.opt spqrVnT) (.opt spqrChainT))

@[reducible] def drSenderChainT : Ty (e2eSig ℓ) := .prod (.prod PK BV256) (.prod BV256 U32)
@[reducible] def drRecvChainT : Ty (e2eSig ℓ) :=
  .prod PK (.prod (.opt (.prod BV256 U32)) (.list (.prod BV256 U32)))
/-- Decomposed `GhostState Bytes` tuple `(isBob, sessionVersion, localId, remoteId?, rootKey, prevCounter, pendingPreKey, epoch, chainEpochs, senderChain?, recvChains, pqRatchetState)`. -/
@[reducible] def ghostPartsT : Ty (e2eSig ℓ) :=
  .prod .bool (.prod U32 (.prod IdKey (.prod (.opt IdKey) (.prod BV256 (.prod U32
    (.prod .bool (.prod .nat (.prod (.list .nat)
      (.prod (.opt drSenderChainT) (.prod (.list drRecvChainT) (B 32)))))))))))

@[reducible] def signalHdrT : Ty (e2eSig ℓ) := .prod U8 (.prod PK (.prod U32 U32))
@[reducible] def signalParsedT : Ty (e2eSig ℓ) :=
  .prod signalHdrT (.prod (B 32) (.prod (B 32) (.opt (B 32))))

@[reducible] def recvResultT : Ty (e2eSig ℓ) :=
  .sum .unit (.prod .nat (.prod .nat (.opt PlainT)))

def recvResultEnc : CryptoGames.SM.RecvResult (Plain ℓ) → (recvResultT (ℓ := ℓ)).denote
  | .rejected => .inl ()
  | .accepted t i m => .inr (t, (i, m))

def recvResultDec : (recvResultT (ℓ := ℓ)).denote → CryptoGames.SM.RecvResult (Plain ℓ)
  | .inl () => .rejected
  | .inr (t, (i, m)) => .accepted t i m

def partyToBool : Party → Bool
  | .A => false
  | .B => true

def boolToParty : Bool → Party
  | false => .A
  | true => .B

@[reducible] def smQT : Ty (e2eSig ℓ) :=
  .sum (.prod .bool (.prod PlainT (.opt BV512)))
  (.sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
  (.sum (.prod .bool (B 32))
  (.sum (.prod .bool (B 32))
        .bool)))

def smQenc {St : Type} :
    (CryptoGames.SM.spec St (Plain ℓ) (BitVec 512) Bytes).Domain → (smQT (ℓ := ℓ)).denote
  | .inl (.inl (.inl (.inl (p, m, r)))) => .inl (partyToBool p, (m, r))
  | .inl (.inl (.inl (.inr (p, m0, m1, r)))) => .inr (.inl (partyToBool p, (m0, (m1, r))))
  | .inl (.inl (.inr (p, c))) => .inr (.inr (.inl (partyToBool p, c)))
  | .inl (.inr (p, c)) => .inr (.inr (.inr (.inl (partyToBool p, c))))
  | .inr p => .inr (.inr (.inr (.inr (partyToBool p))))

/-- Packed `SM.spec` response `(optWire, optRecvResult, optPartyState)`. -/
@[reducible] def smRT (stT : Ty (e2eSig ℓ)) : Ty (e2eSig ℓ) :=
  .prod (.opt (B 32)) (.prod (.opt recvResultT) (.opt stT))

def smRdec {St : Type} {stT : Ty (e2eSig ℓ)} (ofSt : stT.denote → St) :
    (q : (CryptoGames.SM.spec St (Plain ℓ) (BitVec 512) Bytes).Domain) →
    (smRT (ℓ := ℓ) stT).denote →
    (CryptoGames.SM.spec St (Plain ℓ) (BitVec 512) Bytes).Range q
  | .inl (.inl (.inl (.inl _))), (w, _) => w
  | .inl (.inl (.inl (.inr _))), (w, _) => w
  | .inl (.inl (.inr _)), (_, (rr, _)) => rr.map recvResultDec
  | .inl (.inr _), (_, (rr, _)) => rr.map recvResultDec
  | .inr _, (_, (_, st?)) => st?.map ofSt

end TyAbbrevs

/-! ## Coin-only sampler table -/

inductive E2EUnifBase where
  | bv256
  | bv512
  deriving DecidableEq, Repr

def E2EUnifBase.sort : E2EUnifBase → E2ESort
  | .bv256 => .bv256
  | .bv512 => .bv512

def E2EUnifBase.cost : E2EUnifBase → ℕ
  | .bv256 => 1
  | .bv512 => 2

instance (ℓ : ℕ) (b : E2EUnifBase) : SampleableType ((e2eSig ℓ).den b.sort) := by
  cases b <;> dsimp [e2eSig, E2EUnifBase.sort] <;> exact inferInstance

/-- Coin-only uniform sampler table (`BitVec 256` and `BitVec 512`) for E2E reductions and adapters. -/
@[reducible] def e2eSamplers (ℓ : ℕ) : Samplers (e2eSig ℓ) :=
  ReductionDsl.unifSamplers (S := e2eSig ℓ) E2EUnifBase.sort E2EUnifBase.cost

/-! ## Wire, SPQR state, and SessionRecord helpers -/

section PureHelpers

def e2eReadProstVarint : List (BitVec 8) → Option (ℕ × List (BitVec 8))
  | [] => none
  | b :: rest =>
    if b.toNat < 128 then some (b.toNat, rest)
    else (e2eReadProstVarint rest).map (fun (hi, rest') => (b.toNat - 128 + 128 * hi, rest'))

def e2eParseOptPreKeyId : List (BitVec 8) → Option (Option UInt32 × List (BitVec 8))
  | [] => some (none, [])
  | b :: rest =>
    if b == 0x08#8 then (e2eReadProstVarint rest).map (fun (n, r) => (some (UInt32.ofNat n), r))
    else some (none, b :: rest)

def e2eParseUint32Field (keyByte : BitVec 8) :
    List (BitVec 8) → Option (UInt32 × List (BitVec 8))
  | k :: rest =>
    if k == keyByte then (e2eReadProstVarint rest).map (fun (n, r) => (UInt32.ofNat n, r))
    else none
  | [] => none

def e2eParseDjbKeyField (keyByte : BitVec 8) :
    List (BitVec 8) → Option (List (BitVec 8) × List (BitVec 8))
  | k :: 0x21#8 :: 0x05#8 :: rest =>
    if k == keyByte && decide (32 ≤ rest.length) then some (rest.take 32, rest.drop 32) else none
  | _ => none

def e2eParseInnerMsgField : List (BitVec 8) → Option (List (BitVec 8) × List (BitVec 8))
  | 0x22#8 :: rest =>
    (e2eReadProstVarint rest).bind (fun (len, afterLen) =>
      if decide (len ≤ afterLen.length) then some (afterLen.take len, afterLen.drop len) else none)
  | _ => none

def e2eParseKyberCtField : List (BitVec 8) → Option (List (BitVec 8))
  | 0x42#8 :: 0xa1#8 :: 0x0c#8 :: 0x08#8 :: rest =>
    if decide (1568 ≤ rest.length) then some (rest.take 1568) else none
  | _ => none

def e2eDecodePreKeyRaw : Bytes → Option PreKeyMessageFields
  | t :: v :: proto =>
    if t == wirePrekey && v == versionByte currentVersion then
      (e2eParseOptPreKeyId proto).bind fun (opkId?, after1) =>
      (e2eParseDjbKeyField 0x12#8 after1).bind fun (bkBytes, after2) =>
      (e2eParseDjbKeyField 0x1a#8 after2).bind fun (idBytes, after3) =>
      (e2eParseInnerMsgField after3).bind fun (inner, after4) =>
      (e2eParseUint32Field 0x28#8 after4).bind fun (regId, after5) =>
      (e2eParseUint32Field 0x30#8 after5).bind fun (spkId, after6) =>
      (e2eParseUint32Field 0x38#8 after6).bind fun (pqspkId, after7) =>
      (e2eParseKyberCtField after7).bind fun kemCtBytes =>
      if hbk : bkBytes.length = 32 then if hid : idBytes.length = 32 then
        if hct : kemCtBytes.length = 1568 then
          some { regId := regId.toBitVec, opkId := opkId?.map UInt32.toBitVec,
                 spkId := spkId.toBitVec, kpkId := pqspkId.toBitVec, kyberCt := ⟨kemCtBytes, hct⟩,
                 baseKey := ⟨bkBytes, hbk⟩, idPub := ⟨idBytes, hid⟩, inner := inner }
        else none
      else none else none
    else none
  | _ => none

/-- Parse a canonical tag-3 `PreKeySignalMessage` wire buffer (`c == wirePrekey :: m.bytes`). -/
def e2eDecodePreKeyMsg (c : Bytes) : Option PreKeyMessageFields :=
  match e2eDecodePreKeyRaw c with
  | some m => if c == wirePrekey :: m.bytes then some m else none
  | none => none

def e2eHdrOfPreKeyMsg (m : PreKeyMessageFields) : SignalPqxdh.HandshakeHdr :=
  { ikAPk := vecU8 m.idPub, ekAPk := vecU8 m.baseKey, spkId := u32 m.spkId,
    opkId? := m.opkId.map u32, pqspkId := u32 m.kpkId, kemCt := vecU8 m.kyberCt }

def e2eExpectedPreKeyMsg (regIdA : BitVec 32) (hdr : SignalPqxdh.HandshakeHdr)
    (inner : Bytes) : PreKeyMessageFields :=
  { regId := regIdA, opkId := hdr.opkId?.map (fun id => BitVec.ofNat 32 id.toNat),
    spkId := BitVec.ofNat 32 hdr.spkId.toNat, kpkId := BitVec.ofNat 32 hdr.pqspkId.toNat,
    kyberCt := u8Vec 1568 hdr.kemCt, baseKey := u8Vec 32 hdr.ekAPk,
    idPub := u8Vec 32 hdr.ikAPk, inner := inner }

/-- Extract the inner `SignalMessage` slice from a canonical tag-3 or tag-2 wire. -/
def e2eWireInnerBytes (c : Bytes) : Option Bytes :=
  match e2eDecodePreKeyMsg c with
  | some m => some (m.inner.take c.length)
  | none =>
    match c with
    | t :: body => if t == wireWhisper then some body else none
    | [] => none

/-- Extract the inner `SignalMessage` slice from a Bob-partnered wire. -/
def e2ePartneredInnerBytes (bobAccepted : Bool) (regIdA : BitVec 32)
    (sessionHdr : SignalPqxdh.HandshakeHdr) (c : Bytes) : Option Bytes :=
  if !bobAccepted then
    match e2eDecodePreKeyMsg c with
    | some m =>
      if c == wirePrekey :: (e2eExpectedPreKeyMsg regIdA sessionHdr m.inner).bytes then
        some (m.inner.take c.length)
      else none
    | none => none
  else
    match e2eDecodePreKeyMsg c with
    | some m =>
      if e2eHdrOfPreKeyMsg m == sessionHdr then some (m.inner.take c.length) else none
    | none =>
      match c with
      | t :: body => if t == wireWhisper then some body else none
      | [] => none

def e2eReadU32BE : Bytes → BitVec 32
  | b0 :: b1 :: b2 :: b3 :: _ =>
    (b0.zeroExtend 32 <<< 24) ||| (b1.zeroExtend 32 <<< 16) |||
      (b2.zeroExtend 32 <<< 8) ||| b3.zeroExtend 32
  | _ => 0#32

/-- Split up to `fuel` 36-byte `(index, key)` entries from SPQR `KeyHistory` bytes. -/
def splitSpqrPrev : ℕ → Bytes → List (BitVec 32 × BitVec 256) × Bytes
  | 0, bs => ([], bs.take 35)
  | fuel + 1, bs =>
    if bs.length < 36 then ([], bs)
    else
      let idx := e2eReadU32BE (bs.take 4)
      let key := CryptoGames.HKDF.bytesToKey32 ((bs.drop 4).take 32)
      let (rest, tail) := splitSpqrPrev fuel (bs.drop 36)
      ((idx, key) :: rest, tail)

def joinSpqrPrev (entries : List (BitVec 32 × BitVec 256)) (tail : Bytes) : Bytes :=
  (entries.flatMap fun (idx, key) => CryptoGames.HMAC.toBEBytes 4 idx ++ CryptoGames.HMAC.keyToBytes32 key) ++
    tail.take 35

def spqrParamsToV {ℓ : ℕ} (p : CryptoVerification.LibsignalSpqrV1.ChainParamsPB) : (spqrParamsT (ℓ := ℓ)).denote :=
  (p.maxJump, p.maxOooKeys)

def spqrParamsOfV {ℓ : ℕ} (v : (spqrParamsT (ℓ := ℓ)).denote) : CryptoVerification.LibsignalSpqrV1.ChainParamsPB :=
  { maxJump := v.1, maxOooKeys := v.2 }

def spqrVnToV {ℓ : ℕ} (vn : CryptoVerification.LibsignalSpqrV1.VersionNegotiationPB) : (spqrVnT (ℓ := ℓ)).denote :=
  (vn.authKey.take 64, (vn.direction, (vn.minVersion, vn.chainParams.map spqrParamsToV)))

def spqrVnOfV {ℓ : ℕ} (v : (spqrVnT (ℓ := ℓ)).denote) : CryptoVerification.LibsignalSpqrV1.VersionNegotiationPB :=
  { authKey := v.1, direction := v.2.1, minVersion := v.2.2.1,
    chainParams := v.2.2.2.map spqrParamsOfV }

/-- Decompose `EpochDirectionPB` into `spqrDirT`, splitting up to `2201` `KeyHistory` entries and clamping `next` to 64 bytes. -/
def spqrDirToV {ℓ : ℕ} (d : CryptoVerification.LibsignalSpqrV1.EpochDirectionPB) : (spqrDirT (ℓ := ℓ)).denote :=
  let (entries, tail) := splitSpqrPrev 2201 d.prev
  (d.ctr, (d.next.take 64, (entries, tail)))

def spqrDirOfV {ℓ : ℕ} (v : (spqrDirT (ℓ := ℓ)).denote) : CryptoVerification.LibsignalSpqrV1.EpochDirectionPB :=
  { ctr := v.1, next := v.2.1, prev := joinSpqrPrev v.2.2.1 v.2.2.2 }

def spqrChainToV {ℓ : ℕ} (c : CryptoVerification.LibsignalSpqrV1.ChainPB) : (spqrChainT (ℓ := ℓ)).denote :=
  let links := (c.links.take 4).map fun lk => (lk.send.map spqrDirToV, lk.recv.map spqrDirToV)
  (c.direction, (c.currentEpoch, (links, (c.nextRoot.take 64, (c.sendEpoch,
    c.params.map spqrParamsToV)))))

def spqrChainOfV {ℓ : ℕ} (v : (spqrChainT (ℓ := ℓ)).denote) : CryptoVerification.LibsignalSpqrV1.ChainPB :=
  let links := v.2.2.1.map fun (s?, r?) =>
    ({ send := s?.map spqrDirOfV, recv := r?.map spqrDirOfV } : CryptoVerification.LibsignalSpqrV1.ChainEpochPB)
  { direction := v.1, currentEpoch := v.2.1, links := links,
    nextRoot := v.2.2.2.1, sendEpoch := v.2.2.2.2.1,
    params := v.2.2.2.2.2.map spqrParamsOfV }

/-- Decode serialized `PqRatchetState` bytes into `(v1Raw?, vn?, chain?)` with `V1State` clamped to `64,000` bytes. -/
def spqrSplitEval {ℓ : ℕ} (bs : Bytes) : Option (spqrStatePartsT (ℓ := ℓ)).denote :=
  match CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState bs with
  | .error _ => none
  | .ok st =>
    let v1? := st.inner.map fun (.v1 v) => (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw v).take 64000
    some (v1?, (st.versionNegotiation.map spqrVnToV, st.chain.map spqrChainToV))

/-- Re-encode `(v1Raw?, vn?, chain?)` into `PqRatchetState` bytes clamped to `352,000` bytes. -/
def spqrJoinEval {ℓ : ℕ} (parts : (spqrStatePartsT (ℓ := ℓ)).denote) : Bytes :=
  let (v1?, (vn?, ch?)) := parts
  let raw :=
    CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      CryptoVerification.LibsignalSpqrV1.VersionNegotiationPB.encodeRaw 1#32 (vn?.map spqrVnOfV) ++
    CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      CryptoVerification.LibsignalSpqrV1.ChainPB.encodeRaw 2#32 (ch?.map spqrChainOfV) ++
    match v1? with
    | none => []
    | some v1Raw => CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage id 3#32 v1Raw
  raw.take (32 * 11000)

def ghostSplitEval {ℓ : ℕ} (g : GhostState Bytes) : (ghostPartsT (ℓ := ℓ)).denote :=
  let st := g.session
  let sc? := st.senderChain.map fun sc =>
    ((sc.ratchetKey.publicKey, CryptoGames.HKDF.bytesToKey32 sc.ratchetKey.privateKey.bytes.toList),
     (sc.chainKey.key, sc.chainKey.index))
  let rcs := (st.receiverChains.take 5).map fun rc =>
    (rc.senderRatchetKey,
     (rc.chainKey.map (fun ck => (ck.key, ck.index)),
      rc.messageKeys.map (fun mk => (CryptoGames.HKDF.bytesToKey32 mk.seed, mk.counter))))
  (partyToBool g.party,
   (st.sessionVersion,
    (st.localIdentity,
     (st.remoteIdentity,
      (st.rootKey,
       (st.previousCounter,
        (st.pendingPreKey,
         (g.epoch,
          (g.chainEpochs,
           (sc?, (rcs, st.pqRatchetState)))))))))))

def ghostJoinEval {ℓ : ℕ} (p : (ghostPartsT (ℓ := ℓ)).denote) : GhostState Bytes :=
  let (isB, (ver, (locId, (remId?, (rk, (prevCtr, (pend, (ep, (cEps, (sc?, (rcs, pqSt))))))))))) := p
  let sc := sc?.map fun ((pub, priv), (ck, idx)) =>
    ({ ratchetKey := { publicKey := pub, privateKey := ⟨CryptoGames.Ratchet.keyToBytesVec32 priv⟩ },
       chainKey := { key := ck, index := idx } } : SenderChain)
  let rcList := (rcs.take 5).map fun (srk, (ck?, mks)) =>
    ({ senderRatchetKey := srk,
       chainKey := ck?.map fun (ck, idx) =>
         ({ key := ck, index := idx } : CryptoGames.LibsignalSession.ChainKey),
       messageKeys := mks.map fun (sd, ctr) =>
         ({ seed := CryptoGames.HMAC.keyToBytes32 sd, counter := ctr } : MessageKeyGenerator) } : ReceiverChain)
  { party := boolToParty isB
    session :=
      { sessionVersion := ver
        localIdentity := locId
        remoteIdentity := remId?
        rootKey := rk
        previousCounter := prevCtr
        senderChain := sc
        receiverChains := rcList
        pendingPreKey := pend
        pqRatchetState := pqSt }
    epoch := ep
    chainEpochs := cEps }

def e2eRecordExtras (regIdA regIdB bobRemoteRegId : BitVec 32)
    (hdr : SignalPqxdh.HandshakeHdr) : Party → RecordExtras
  | .A =>
    let base : PublicKey := ⟨u8Vec 32 hdr.ekAPk⟩
    { pending := { preKeyId := hdr.opkId?.map (fun id => BitVec.ofNat 32 id.toNat)
                   signedPreKeyId := BitVec.ofNat 32 hdr.spkId.toNat
                   baseKey := base
                   timestamp := 0#64 }
      kyber := some { preKeyId := BitVec.ofNat 32 hdr.pqspkId.toNat
                      ciphertext := kyberKey (u8Vec 1568 hdr.kemCt) }
      remoteRegistrationId := regIdB
      localRegistrationId := regIdA
      aliceBaseKey := base.serialize }
  | .B =>
    let base : PublicKey := ⟨u8Vec 32 hdr.ekAPk⟩
    { pending := { preKeyId := none, signedPreKeyId := 0#32, baseKey := base, timestamp := 0#64 }
      kyber := none
      remoteRegistrationId := bobRemoteRegId
      localRegistrationId := regIdB
      aliceBaseKey := base.serialize }

/-- Serialize `(extrasMeta, g)` to `BinState` with `SessionRecord` bytes clamped to `768,000` bytes. -/
def e2eEncodeSessionRecord {ℓ : ℕ}
    (inp : ((U32 (ℓ := ℓ)).denote × (U32 (ℓ := ℓ)).denote ×
      (U32 (ℓ := ℓ)).denote × (hdrT (ℓ := ℓ)).denote) × GhostState Bytes) : BinState :=
  let ((regIdA, (regIdB, (bobRemoteRegId, hdrV0))), g) := inp
  let bs := binStateOfUnderExtras (e2eRecordExtras regIdA regIdB bobRemoteRegId (hdrOfV hdrV0)) g
  { bs with bytes := bs.bytes.take (32 * 24000) }

end PureHelpers

/-! ## Pure operations -/

/-- Pure (`P`/`C`/`K`/`Pt`-independent) operations shared by `L_bh` and `R_e2e`. -/
inductive E2EPureOp where
  | pbytesLit (w : ℕ+) (v : SignalPqxdh.Bytes)
  | pbytesCat (m n : ℕ+)
  | pbytesCons (b : UInt8) (w : ℕ+)
  | pbytesWiden (w d : ℕ+)
  | pbytesTakeK (w k : ℕ+)
  | pbytesTake (w : ℕ+)
  | pbytesDrop (w : ℕ+)
  | pbytesLen (w : ℕ+)
  | pbytesEq (m n : ℕ+)
  | bytesLit (w : ℕ+) (v : Bytes)
  | bytesCat (m n : ℕ+)
  | bytesCons (b : BitVec 8) (w : ℕ+)
  | bytesWiden (w d : ℕ+)
  | bytesTakeK (w k : ℕ+)
  | bytesTake (w : ℕ+)
  | bytesDrop (w : ℕ+)
  | bytesLen (w : ℕ+)
  | bytesEq (m n : ℕ+)
  | bytesLtOp (m n : ℕ+)
  | pbytesToBytes (w : ℕ+)
  | bytesToPbytes (w : ℕ+)
  | pu32Lit (k : UInt32)
  | pu32OfNat
  | pu32ToNat
  | pu32Eq
  | pu32ToU32
  | u32ToPu32
  | u8Lit (v : BitVec 8)
  | u8OfNat
  | u8ToNat
  | u8Eq
  | u8Lt
  | u32Lit (v : BitVec 32)
  | u32OfNat
  | u32ToNat
  | u32Eq
  | u32Lt
  | u32Add
  | u32Sub
  | u32BeBytes
  | u64Lit (v : BitVec 64)
  | u64OfNat
  | u64ToNat
  | u64Eq
  | u64Lt
  | u64Add
  | u64Sub
  | u64Trunc8
  | finVal (n : ℕ)
  | finEq (n : ℕ)
  | bv128Eq
  | bv256Lit (v : BitVec 256)
  | bv256Eq
  | bv256ToPbytes32
  | pbytesToBv256
  | bv256ToBytes32
  | bytesToBv256
  | bv512Lit (v : BitVec 512)
  | bv512ToBytes64
  | idKeyOfPbytes
  | idKeySerialize
  | idKeyEq
  | pkOfPbytes
  | pkDeserialize
  | pkSerialize
  | pkEq
  | plainDefault
  | plainToBytes
  | bytesToPlain
  | plainEq
  | checkShortCiphertext
  | parsePreKeyWire
  | partneredInnerBytes
  | wireInnerBytes
  | splitWhisperWire
  | isValidSignalWire
  | signalMsgParse
  | wrapWhisperWire
  | wrapPreKeyWire
  | spqrParsePreamble
  | spqrAssembleMsg
  | spqrStateSplit
  | spqrStateJoin
  | ghostStateSplit
  | ghostStateJoin
  | encodeSessionRecord

@[reducible] def E2EPureOp.dom (ℓ : ℕ) : E2EPureOp → Ty (e2eSig ℓ)
  | .pbytesLit _ _ | .bytesLit _ _ | .pu32Lit _ | .u8Lit _ | .u32Lit _ | .u64Lit _
  | .bv256Lit _ | .bv512Lit _ | .plainDefault => .unit
  | .pbytesCat m n | .pbytesEq m n => .prod (PB m) (PB n)
  | .pbytesCons _ w | .pbytesWiden w _ | .pbytesTakeK w _ | .pbytesLen w | .pbytesToBytes w => PB w
  | .pbytesTake w | .pbytesDrop w => .prod .nat (PB w)
  | .bytesCat m n | .bytesEq m n | .bytesLtOp m n => .prod (B m) (B n)
  | .bytesCons _ w | .bytesWiden w _ | .bytesTakeK w _ | .bytesLen w | .bytesToPbytes w => B w
  | .bytesTake w | .bytesDrop w => .prod .nat (B w)
  | .pu32OfNat | .u8OfNat | .u32OfNat | .u64OfNat => .nat
  | .pu32ToNat | .pu32ToU32 => PU32
  | .pu32Eq => .prod PU32 PU32
  | .u32ToPu32 | .u32ToNat | .u32BeBytes => U32
  | .u8ToNat => U8
  | .u8Eq | .u8Lt => .prod U8 U8
  | .u32Eq | .u32Lt | .u32Add | .u32Sub => .prod U32 U32
  | .u64ToNat | .u64Trunc8 => U64
  | .u64Eq | .u64Lt | .u64Add | .u64Sub => .prod U64 U64
  | .finVal n => FinT n
  | .finEq n => .prod (FinT n) (FinT n)
  | .bv128Eq => .prod BV128 BV128
  | .bv256Eq => .prod BV256 BV256
  | .bv256ToPbytes32 | .bv256ToBytes32 => BV256
  | .pbytesToBv256 | .idKeyOfPbytes | .pkOfPbytes => PB 32
  | .bytesToBv256 => B 32
  | .bv512ToBytes64 => BV512
  | .idKeySerialize => IdKey
  | .idKeyEq => .prod IdKey IdKey
  | .pkDeserialize => B 33
  | .pkSerialize => PK
  | .pkEq => .prod PK PK
  | .plainToBytes => PlainT
  | .bytesToPlain => B 32
  | .plainEq => .prod PlainT PlainT
  | .checkShortCiphertext => .prod (B 32) (.opt (B 32))
  | .parsePreKeyWire | .wireInnerBytes | .splitWhisperWire | .isValidSignalWire
  | .signalMsgParse | .wrapWhisperWire | .spqrParsePreamble | .spqrStateSplit => B 32
  | .partneredInnerBytes => .prod .bool (.prod U32 (.prod hdrT (B 32)))
  | .wrapPreKeyWire => .prod U32 (.prod hdrT (B 32))
  | .spqrAssembleMsg => .prod U64 (.prod U32 (B 64))
  | .spqrStateJoin => spqrStatePartsT
  | .ghostStateSplit => GhostStT
  | .ghostStateJoin => ghostPartsT
  | .encodeSessionRecord => .prod (.prod U32 (.prod U32 (.prod U32 hdrT))) GhostStT

@[reducible] def E2EPureOp.cod (ℓ : ℕ) : E2EPureOp → Ty (e2eSig ℓ)
  | .pbytesLit w _ | .pbytesTake w | .pbytesDrop w | .bytesToPbytes w => PB w
  | .pbytesCat m n => PB (m + n)
  | .pbytesCons _ w => PB (w + 1)
  | .pbytesWiden w d => PB (w + d)
  | .pbytesTakeK _ k => PB k
  | .pbytesLen _ | .bytesLen _ | .pu32ToNat | .u8ToNat | .u32ToNat | .u64ToNat | .finVal _ => .nat
  | .pbytesEq _ _ | .bytesEq _ _ | .bytesLtOp _ _ | .pu32Eq | .u8Eq | .u8Lt | .u32Eq | .u32Lt
  | .u64Eq | .u64Lt | .finEq _ | .bv128Eq | .bv256Eq | .idKeyEq | .pkEq | .plainEq
  | .checkShortCiphertext | .isValidSignalWire => .bool
  | .bytesLit w _ | .bytesTake w | .bytesDrop w | .pbytesToBytes w => B w
  | .bytesCat m n => B (m + n)
  | .bytesCons _ w => B (w + 1)
  | .bytesWiden w d => B (w + d)
  | .bytesTakeK _ k => B k
  | .pu32Lit _ | .pu32OfNat | .u32ToPu32 => PU32
  | .u8Lit _ | .u8OfNat | .u64Trunc8 => U8
  | .u32Lit _ | .u32OfNat | .pu32ToU32 | .u32Add | .u32Sub => U32
  | .u32BeBytes => B 4
  | .u64Lit _ | .u64OfNat | .u64Add | .u64Sub => U64
  | .bv256Lit _ | .pbytesToBv256 | .bytesToBv256 => BV256
  | .bv256ToPbytes32 => PB 32
  | .bv256ToBytes32 | .plainToBytes | .wrapWhisperWire | .wrapPreKeyWire
  | .spqrAssembleMsg | .spqrStateJoin => B 32
  | .bv512Lit _ => BV512
  | .bv512ToBytes64 => B 64
  | .idKeyOfPbytes => IdKey
  | .idKeySerialize | .pkSerialize => B 33
  | .pkOfPbytes => PK
  | .pkDeserialize => .opt PK
  | .plainDefault => PlainT
  | .bytesToPlain => .opt PlainT
  | .parsePreKeyWire => .opt (.prod U32 (.prod hdrT (B 32)))
  | .partneredInnerBytes | .wireInnerBytes | .splitWhisperWire => .opt (B 32)
  | .signalMsgParse => .opt signalParsedT
  | .spqrParsePreamble => .opt (.prod U8 (.prod U64 (.prod U32 (B 32))))
  | .spqrStateSplit => .opt spqrStatePartsT
  | .ghostStateSplit => ghostPartsT
  | .ghostStateJoin => GhostStT
  | .encodeSessionRecord => BinStT

def E2EPureOp.eval (ℓ : ℕ) : (o : E2EPureOp) → (o.dom ℓ).denote → (o.cod ℓ).denote
  | .pbytesLit _ v, _ => v
  | .pbytesCat _ _, (x, y) => x ++ y
  | .pbytesCons b _, x => b :: x
  | .pbytesWiden _ _, x => x
  | .pbytesTakeK _ k, x => x.take k
  | .pbytesTake _, (n, x) => x.take n
  | .pbytesDrop _, (n, x) => x.drop n
  | .pbytesLen _, x => x.length
  | .pbytesEq _ _, (x, y) => x == y
  | .bytesLit _ v, _ => v
  | .bytesCat _ _, (x, y) => x ++ y
  | .bytesCons b _, x => b :: x
  | .bytesWiden _ _, x => x
  | .bytesTakeK _ k, x => x.take k
  | .bytesTake _, (n, x) => x.take n
  | .bytesDrop _, (n, x) => x.drop n
  | .bytesLen _, x => x.length
  | .bytesEq _ _, (x, y) => x == y
  | .bytesLtOp _ _, (x, y) => CryptoVerification.LibsignalSpqrV1.bytesLt x y
  | .pbytesToBytes _, x => ofU8 x
  | .bytesToPbytes _, x => toU8 x
  | .pu32Lit k, _ => k
  | .pu32OfNat, n => UInt32.ofNat n
  | .pu32ToNat, k => k.toNat
  | .pu32Eq, (a, b) => a == b
  | .pu32ToU32, k => k.toBitVec
  | .u32ToPu32, v => UInt32.ofBitVec v
  | .u8Lit v, _ => v
  | .u8OfNat, n => BitVec.ofNat 8 n
  | .u8ToNat, v => v.toNat
  | .u8Eq, (a, b) => a == b
  | .u8Lt, (a, b) => decide (a < b)
  | .u32Lit v, _ => v
  | .u32OfNat, n => BitVec.ofNat 32 n
  | .u32ToNat, v => v.toNat
  | .u32Eq, (a, b) => a == b
  | .u32Lt, (a, b) => decide (a < b)
  | .u32Add, (a, b) => a + b
  | .u32Sub, (a, b) => a - b
  | .u32BeBytes, v => CryptoGames.HMAC.toBEBytes 4 v
  | .u64Lit v, _ => v
  | .u64OfNat, n => BitVec.ofNat 64 n
  | .u64ToNat, v => v.toNat
  | .u64Eq, (a, b) => a == b
  | .u64Lt, (a, b) => decide (a < b)
  | .u64Add, (a, b) => a + b
  | .u64Sub, (a, b) => a - b
  | .u64Trunc8, v => v.truncate 8
  | .finVal _, k => k.val
  | .finEq _, (a, b) => a == b
  | .bv128Eq, (a, b) => a == b
  | .bv256Lit v, _ => v
  | .bv256Eq, (a, b) => a == b
  | .bv256ToPbytes32, v => SignalPqxdh.word256ToBytes v
  | .pbytesToBv256, bs => CryptoGames.HKDF.bytesToKey32 (ofU8 bs)
  | .bv256ToBytes32, v => CryptoGames.HMAC.keyToBytes32 v
  | .bytesToBv256, bs => CryptoGames.HKDF.bytesToKey32 bs
  | .bv512Lit v, _ => v
  | .bv512ToBytes64, v => CryptoVerification.LibsignalSpqrV1.coinBytes v
  | .idKeyOfPbytes, bs => ⟨⟨u8Vec 32 bs⟩⟩
  | .idKeySerialize, k => k.serialize
  | .idKeyEq, (a, b) => a == b
  | .pkOfPbytes, bs => ⟨u8Vec 32 bs⟩
  | .pkDeserialize, bs => (CryptoGames.LibsignalSession.PublicKey.deserialize bs).toOption
  | .pkSerialize, k => k.serialize
  | .pkEq, (a, b) => a == b
  | .plainDefault, _ => List.Vector.replicate ℓ 0#8
  | .plainToBytes, m => m.toList
  | .bytesToPlain, bs =>
    if h : bs.length = ℓ then some ⟨bs, h⟩ else none
  | .plainEq, (a, b) => decide (a = b)
  | .checkShortCiphertext, (c, inner?) =>
    shortCiphertext c &&
      match inner? with | some i => decide (i.length + 2048 < 2 ^ 32) | none => true
  | .parsePreKeyWire, c =>
    (e2eDecodePreKeyMsg c).map fun m => (m.regId, (hdrV (e2eHdrOfPreKeyMsg m), m.inner.take c.length))
  | .partneredInnerBytes, (bobAcc, (regIdA, (hdr, c))) =>
    e2ePartneredInnerBytes bobAcc regIdA (hdrOfV hdr) c
  | .wireInnerBytes, c => e2eWireInnerBytes c
  | .splitWhisperWire, c =>
    match c with | t :: body => if t == wireWhisper then some body else none | [] => none
  | .isValidSignalWire, body => (CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec body).isOk
  | .signalMsgParse, body =>
    match CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec body with
    | .ok m =>
      some ((m.messageVersion, (m.senderRatchetKey, (m.counter, m.previousCounter))),
            (m.ciphertext.take body.length,
             (m.pqRatchet.take body.length, m.addresses.map (·.take body.length))))
    | .error _ => none
  | .wrapWhisperWire, ct =>
    if ct.isEmpty then [] else (wireWhisper :: ct).take (32 * (2 * (ℓ / 32) + 26))
  | .wrapPreKeyWire, (regIdA, (hdr, inner)) =>
    if inner.isEmpty then []
    else (wirePrekey :: (e2eExpectedPreKeyMsg regIdA (hdrOfV hdr) inner).bytes).take
      (32 * (2 * (ℓ / 32) + 84))
  | .spqrParsePreamble, msg =>
    match CryptoVerification.LibsignalSpqrV1.msgPreamble msg with
    | .ok p => some (p.version, (p.epoch, (p.index, p.remaining.take msg.length)))
    | .error _ => none
  | .spqrAssembleMsg, (ep, (idx, sfx)) =>
    (CryptoVerification.LibsignalSpqrV1.encode_varint (idx.zeroExtend 64)
      (CryptoVerification.LibsignalSpqrV1.encode_varint ep [1#8]) ++ sfx.take 64).take 96
  | .spqrStateSplit, bs => spqrSplitEval bs
  | .spqrStateJoin, parts => spqrJoinEval parts
  | .ghostStateSplit, g => ghostSplitEval g
  | .ghostStateJoin, parts => ghostJoinEval parts
  | .encodeSessionRecord, inp => e2eEncodeSessionRecord inp

def E2EPureOp.cost (ℓ : ℕ) : E2EPureOp → ℕ
  | .pbytesLit w v => w + v.length
  | .pbytesCat m n | .pbytesEq m n => m + n
  | .pbytesCons _ w | .pbytesTake w | .pbytesDrop w => w + 1
  | .pbytesWiden w d => w + d
  | .pbytesTakeK w k => w + k
  | .pbytesLen w => bits w + 1
  | .bytesLit w v => w + v.length
  | .bytesCat m n | .bytesEq m n | .bytesLtOp m n => m + n
  | .bytesCons _ w | .bytesTake w | .bytesDrop w => w + 1
  | .bytesWiden w d => w + d
  | .bytesTakeK w k => w + k
  | .bytesLen w => bits w + 1
  | .pbytesToBytes w | .bytesToPbytes w => w
  | .pu32Lit _ | .pu32OfNat | .pu32Eq | .pu32ToU32 | .u32ToPu32 => 1
  | .pu32ToNat | .u32ToNat => 32
  | .u8Lit _ | .u8OfNat | .u8Eq | .u8Lt | .u64Trunc8 => 1
  | .u8ToNat => 8
  | .u32Lit _ | .u32OfNat | .u32Eq | .u32Lt | .u32Add | .u32Sub => 1
  | .u32BeBytes => 4
  | .u64Lit _ | .u64OfNat | .u64Eq | .u64Lt | .u64Add | .u64Sub => 2
  | .u64ToNat => 64
  | .finVal _ => 1
  | .finEq _ | .bv128Eq | .bv256Lit _ | .bv256Eq | .idKeyEq | .pkEq => 2
  | .bv256ToPbytes32 | .pbytesToBv256 | .bv256ToBytes32 | .bytesToBv256 => 32
  | .bv512Lit _ => 3
  | .bv512ToBytes64 => 64
  | .idKeyOfPbytes | .idKeySerialize | .pkOfPbytes | .pkDeserialize | .pkSerialize => 33
  | .plainDefault | .plainToBytes | .bytesToPlain | .plainEq => ℓ / 32 + 2
  | .checkShortCiphertext => 4
  | .parsePreKeyWire | .wireInnerBytes => 96
  | .partneredInnerBytes => 128
  | .splitWhisperWire => 2
  | .isValidSignalWire | .signalMsgParse => ℓ / 32 + 18
  | .wrapWhisperWire => 2 * (ℓ / 32) + 28
  | .wrapPreKeyWire => 2 * (ℓ / 32) + 88
  | .spqrParsePreamble => 4
  | .spqrAssembleMsg => 6
  | .spqrStateSplit | .spqrStateJoin => 11200
  | .ghostStateSplit | .ghostStateJoin => 16
  | .encodeSessionRecord => 24576

@[reducible] def E2EPureOp.opSize : E2EPureOp → ℕ
  | .pbytesLit _ v | .bytesLit _ v => v.length
  | .u8Lit _ | .pbytesCons _ _ | .bytesCons _ _ => 1
  | .pu32Lit _ | .u32Lit _ => 4
  | .u64Lit _ => 8
  | .bv256Lit _ => 32
  | .bv512Lit _ => 64
  | _ => 0

/-- Pure `ReductionDsl` operation table shared by `L_bh` and `R_e2e`. -/
@[reducible] def e2ePureOps (ℓ : ℕ) : Ops (e2eSig ℓ) where
  Op := E2EPureOp
  dom := E2EPureOp.dom ℓ
  cod := E2EPureOp.cod ℓ
  eval := E2EPureOp.eval ℓ
  cost := E2EPureOp.cost ℓ
  opSize := E2EPureOp.opSize

/-! ## Curve admissibility operations -/

/-- Curve canonicality checks (`decT`/`encT`) shared by `L_bh` and `R_e2e`. -/
inductive E2ECurveCheckOp where
  | decEncCheck
  | checkRatchetKeyOnCurve
  deriving DecidableEq, Repr

/-- Operation table for `decT`/`encT` curve checks, independent of `(P, C, K)`. -/
@[reducible] def e2eCurveCheckOps (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) : Ops (e2eSig ℓ) where
  Op := E2ECurveCheckOp
  dom := fun
    | .decEncCheck => PK
    | .checkRatchetKeyOnCurve => B 32
  cod := fun
    | .decEncCheck | .checkRatchetKeyOnCurve => .bool
  eval := fun
    | .decEncCheck, pk =>
      match decT pk with
      | some T => decide (encT T = pk)
      | none => false
    | .checkRatchetKeyOnCurve, body =>
      ratchetKeyAdmissible protoSignalCodec decT encT body
  cost := fun
    | .decEncCheck => 8
    | .checkRatchetKeyOnCurve => ℓ / 32 + 24

/-! ## Cryptographic primitive operations -/

section CryptoHelpers

/-- Serialized payload suffix (`typeByte ‖ chunkBytes`) of an SPQR V1 message, clamped to 64 bytes. -/
def spqrMsgPayloadSuffix {P : CryptoVerification.LibsignalSpqrV1.PolyApi}
    (m : CryptoVerification.LibsignalSpqrV1.Message P) : Bytes :=
  let tByte := [(CryptoVerification.LibsignalSpqrV1.MessageType.from_payload m.payload).toU8]
  let body :=
    match m.payload with
    | .hdr c | .ek c | .ekCt1Ack c | .ct1 c | .ct2 c => CryptoVerification.LibsignalSpqrV1.encode_chunk c []
    | .none | .ct1Ack _ => []
  (tByte ++ body).take 64

/-- Single SPQR V1 braid `States.send` transition on serialized `V1State` bytes without symmetric-chain steps. -/
def spqrBraidSendEval {ℓ : ℕ} (F : ShaCompress) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (v1Raw : Bytes) (coins : BitVec 512) :
    Bool × Option ((B (ℓ := ℓ) 32).denote × BitVec 64 ×
      Option (BitVec 64 × BitVec 256) × (B (ℓ := ℓ) 64).denote) :=
  match CryptoVerification.LibsignalSpqrV1.V1State.decode v1Raw with
  | .error _ => (false, none)
  | .ok pb =>
    match CryptoVerification.LibsignalSpqrV1.States.from_pb CryptoVerification.LibsignalSpqrV1.spqrPolyApi
        (CryptoVerification.LibsignalSpqrV1.spqrAuthApi F) pb with
    | .error (.panic _) => (true, none)
    | .error (.err _) => (false, none)
    | .ok st0 =>
      match st0.send K (CryptoVerification.LibsignalSpqrV1.coinBytes coins) with
      | .error (.panic _) => (true, none)
      | .error (.err _) => (false, none)
      | .ok (sOut, _) =>
        let newV1 := (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw sOut.state.into_pb).take 64000
        let epSec? := sOut.key.map fun es => (es.epoch, CryptoGames.HKDF.bytesToKey32 es.secret)
        (false, some (newV1, (sOut.msg.epoch, (epSec?, spqrMsgPayloadSuffix sOut.msg))))

/-- Single SPQR V1 braid `States.recv` transition on serialized `V1State` bytes without symmetric-chain steps. -/
def spqrBraidRecvEval {ℓ : ℕ} (F : ShaCompress) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (v1Raw : Bytes) (msgEpoch : BitVec 64) (remaining : Bytes) :
    Bool × Bool × Option (Option (BitVec 64 × BitVec 256) × (B (ℓ := ℓ) 32).denote) :=
  match CryptoVerification.LibsignalSpqrV1.Message.deserialize CryptoVerification.LibsignalSpqrV1.spqrPolyApi msgEpoch remaining with
  | .error e => (false, e.isStateDecode, none)
  | .ok sckaMsg =>
    match CryptoVerification.LibsignalSpqrV1.V1State.decode v1Raw with
    | .error _ => (false, true, none)
    | .ok pb =>
      match CryptoVerification.LibsignalSpqrV1.States.from_pb CryptoVerification.LibsignalSpqrV1.spqrPolyApi
          (CryptoVerification.LibsignalSpqrV1.spqrAuthApi F) pb with
      | .error (.panic _) => (true, false, none)
      | .error (.err e) => (false, e.isStateDecode, none)
      | .ok st0 =>
        match st0.recv K sckaMsg with
        | .error (.panic _) => (true, false, none)
        | .error (.err e) => (false, e.isStateDecode, none)
        | .ok rOut =>
          let newV1 := (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw rOut.state.into_pb).take 64000
          let epSec? := rOut.key.map fun es => (es.epoch, CryptoGames.HKDF.bytesToKey32 es.secret)
          (false, false, some (epSec?, newV1))

/-- SPQR version-negotiation `initInner` transition with `V1State` clamped to `48,000` bytes. -/
def spqrNegotiateInitEval {ℓ : ℕ} (F : ShaCompress) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (verByte : BitVec 8) (dirI32 : BitVec 32) (authKey : Bytes) :
    Bool × Option (Option (B (ℓ := ℓ) 32).denote) :=
  match CryptoVerification.LibsignalSpqrV1.Version.fromU8? verByte with
  | none => (true, none)
  | some v =>
    match CryptoVerification.LibsignalSpqrV1.Direction.fromI32? dirI32 with
    | none => (false, none)
    | some dir =>
      match CryptoVerification.LibsignalSpqrV1.initInner (CryptoVerification.LibsignalSpqrV1.spqrDeps F K) v dir authKey with
      | .error _ => (true, none)
      | .ok pb? =>
        (false, some (pb?.map fun pb => (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw pb).take 48000))

def spqrChainFromVnEval {ℓ : ℕ} (F : ShaCompress)
    (vn : (spqrVnT (ℓ := ℓ)).denote) : Option (spqrChainT (ℓ := ℓ)).denote :=
  match CryptoVerification.LibsignalSpqrV1.chainFromVersionNegotiation
      (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F) (spqrVnOfV vn) with
  | .ok c => some (spqrChainToV c.intoPb)
  | .error _ => none

def spqrChainAddEpochEval {ℓ : ℕ} (F : ShaCompress)
    (ch : (spqrChainT (ℓ := ℓ)).denote) (ep : BitVec 64) (sec : BitVec 256) :
    Bool × Option (spqrChainT (ℓ := ℓ)).denote :=
  match CryptoVerification.LibsignalSpqrV1.Chain.fromPb (spqrChainOfV ch) with
  | .error _ => (false, none)
  | .ok c0 =>
    match c0.addEpoch (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F) ⟨ep, CryptoGames.HMAC.keyToBytes32 sec⟩ with
    | .error _ => (true, none)
    | .ok c1 => (false, some (spqrChainToV c1.intoPb))

def spqrChainNextKeyEval {ℓ : ℕ} (F : ShaCompress) (next : Bytes) (ctr : BitVec 32) :
    Bool × Option ((B (ℓ := ℓ) 32).denote × BitVec 32 × BitVec 256) :=
  match CryptoVerification.LibsignalSpqrV1.ChainEpochDirection.nextKeyInternal
      (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F) next ctr with
  | .error _ => (true, none)
  | .ok (next', _, (idx, mkBytes)) =>
    (false, some (next'.take 32, (idx, CryptoGames.HKDF.bytesToKey32 mkBytes)))

end CryptoHelpers

/-- Atomic cryptographic primitive operations parameterized by `(P, C, K)`. -/
inductive E2ECryptoOp where
  | x25519
  | x25519Base
  | pow8
  | isCanonical
  | sigSign
  | sigVerify
  | kemKeyGen
  | kemEncaps
  | kemDecaps
  | hkdfDerive96
  | sessionKeyPairGen
  | sessionRootCreateChain
  | chainStep
  | deriveMsgKeys
  | aes256CbcEnc
  /-- PKCS#7-padded AES-256-CBC decryption with `padOrTruncatePlain ℓ` (`DEV-LS27`). -/
  | aes256CbcDec
  | signalMsgEncode
  | signalMsgVerifyMac
  | spqrV1InitOp
  | spqrNegotiateInit
  | spqrBraidSend
  | spqrBraidRecv
  | spqrChainFromVn
  | spqrChainAddEpoch
  | spqrChainNextKey
  deriving DecidableEq, Repr

@[reducible] def E2ECryptoOp.dom (ℓ : ℕ) : E2ECryptoOp → Ty (e2eSig ℓ)
  | .x25519 => .prod (PB 32) (PB 32)
  | .x25519Base | .pow8 | .isCanonical => PB 32
  | .sigSign | .sigVerify => .prod (PB 32) (.prod (PB 1569) (PB 64))
  | .kemKeyGen => PB 64
  | .kemEncaps => .prod (PB 1568) (PB 32)
  | .kemDecaps => .prod (PB 3168) (PB 1568)
  | .hkdfDerive96 => PB 192
  | .sessionKeyPairGen => BV256
  | .sessionRootCreateChain => .prod BV256 (.prod PK BV256)
  | .chainStep => .prod BV256 U32
  | .deriveMsgKeys => .prod BV256 (.prod U32 (.opt BV256))
  | .aes256CbcEnc => .prod BV256 (.prod BV128 PlainT)
  | .aes256CbcDec => .prod BV256 (.prod BV128 (B 32))
  | .signalMsgEncode =>
    .prod signalHdrT (.prod (B 32) (.prod (B 32)
      (.prod (.opt (B 32)) (.prod IdKey (.prod IdKey BV256)))))
  | .signalMsgVerifyMac =>
    .prod (B 32) (.prod (.opt (B 32)) (.prod IdKey (.prod IdKey BV256)))
  | .spqrV1InitOp => .prod .bool BV256
  | .spqrNegotiateInit => .prod U8 (.prod U32 (B 32))
  | .spqrBraidSend => .prod (B 32) BV512
  | .spqrBraidRecv => .prod (B 32) (.prod U64 (B 32))
  | .spqrChainFromVn => spqrVnT
  | .spqrChainAddEpoch => .prod spqrChainT (.prod U64 BV256)
  | .spqrChainNextKey => .prod (B 32) U32

@[reducible] def E2ECryptoOp.cod (ℓ : ℕ) : E2ECryptoOp → Ty (e2eSig ℓ)
  | .x25519 | .x25519Base | .pow8 => PB 32
  | .isCanonical | .sigVerify | .signalMsgVerifyMac => .bool
  | .sigSign => PB 64
  | .kemKeyGen => .prod (PB 1568) (PB 3168)
  | .kemEncaps => .opt (.prod (PB 32) (PB 1568))
  | .kemDecaps => .opt (PB 32)
  | .hkdfDerive96 => drKeyT
  | .sessionKeyPairGen => .prod PK BV256
  | .sessionRootCreateChain => .opt (.prod BV256 BV256)
  | .chainStep => .opt (.prod (.prod BV256 U32) BV256)
  | .deriveMsgKeys => .prod BV256 (.prod BV256 (.prod BV128 U32))
  | .aes256CbcEnc | .signalMsgEncode | .spqrV1InitOp => B 32
  | .aes256CbcDec => .opt PlainT
  | .spqrNegotiateInit => .prod .bool (.opt (.opt (B 32)))
  | .spqrBraidSend =>
    .prod .bool (.opt (.prod (B 32) (.prod U64 (.prod (.opt (.prod U64 BV256)) (B 64)))))
  | .spqrBraidRecv =>
    .prod .bool (.prod .bool (.opt (.prod (.opt (.prod U64 BV256)) (B 32))))
  | .spqrChainFromVn => .opt spqrChainT
  | .spqrChainAddEpoch => .prod .bool (.opt spqrChainT)
  | .spqrChainNextKey => .prod .bool (.opt (.prod (B 32) (.prod U32 BV256)))

def E2ECryptoOp.eval (ℓ : ℕ) (P : SignalPqxdh.Primitives) (C : Crypto)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem) : (o : E2ECryptoOp) → (o.dom ℓ).denote → (o.cod ℓ).denote
  | .x25519, (sk, pk) => (P.x25519 sk pk).take 32
  | .x25519Base, sk => (P.x25519Base sk).take 32
  | .pow8, pk => (P.pow8 pk).take 32
  | .isCanonical, pk => P.isCanonical pk
  | .sigSign, (sk, (msg, rnd)) => (P.sigSign sk msg rnd).take 64
  | .sigVerify, (pk, (msg, sig)) => P.sigVerify pk msg sig
  | .kemKeyGen, seed =>
    let (pk, sk) := P.kemKeyGen seed
    (pk.take 1568, sk.take 3168)
  | .kemEncaps, (pk, coins) =>
    (P.kemEncaps pk coins).map fun (ss, ct) => (ss.take 32, ct.take 1568)
  | .kemDecaps, (sk, ct) => (P.kemDecaps sk ct).map (·.take 32)
  | .hkdfDerive96, ikm =>
    let dk := P.hkdfDerive96 ikm
    (dk.rootKey.take 32, (dk.chainKey.take 32, dk.pqrKey.take 32))
  | .sessionKeyPairGen, coins =>
    let kp := CryptoGames.LibsignalSession.KeyPair.generate C coins
    (kp.publicKey, CryptoGames.HKDF.bytesToKey32 kp.privateKey.bytes.toList)
  | .sessionRootCreateChain, (rk, (theirPk, ourPriv)) =>
    match CryptoGames.LibsignalSession.rootCreateChain C rk theirPk ⟨CryptoGames.Ratchet.keyToBytesVec32 ourPriv⟩ with
    | .ok (rk', ck) => some (rk', ck.key)
    | .error _ => none
  | .chainStep, (ck, idx) =>
    let ckObj : CryptoGames.LibsignalSession.ChainKey := { key := ck, index := idx }
    match CryptoGames.LibsignalSession.ChainKey.nextChainKey C.F ckObj with
    | .ok ckNext =>
      let mkGen := CryptoGames.LibsignalSession.ChainKey.messageKeys C.F ckObj
      some ((ckNext.key, ckNext.index), CryptoGames.HKDF.bytesToKey32 mkGen.seed)
    | .error _ => none
  | .deriveMsgKeys, (seed, (ctr, salt?)) =>
    let saltVec? : CryptoGames.HKDF.Salt := salt?.map CryptoGames.Ratchet.keyToBytesVec32
    let mks := CryptoGames.LibsignalSession.MessageKeyGenerator.generateKeys C.F ⟨CryptoGames.HMAC.keyToBytes32 seed, ctr⟩ saltVec?
    (mks.cipherKey, (mks.macKey, (mks.iv, mks.counter)))
  | .aes256CbcEnc, (k, (iv, pt)) =>
    (aesCbcEncrypt C.E k iv pt.toList).take (32 * (ℓ / 32 + 2))
  | .aes256CbcDec, (k, (iv, ct)) =>
    (aesCbcDecrypt C.D k iv ct).map (CryptoGames.Ratchet.padOrTruncatePlain ℓ)
  | .signalMsgEncode,
      ((msgVer, (senderRk, (ctr, prevCtr))), (ct, (pqMsg, (addr?, (idS, (idR, macKey)))))) =>
    (CryptoGames.LibsignalSession.SignalMessage.new C.F protoSignalCodec msgVer macKey addr? senderRk ctr prevCtr ct
      idS idR pqMsg).serialized.take (32 * (2 * (ℓ / 32) + 24))
  | .signalMsgVerifyMac, (body, (expectedAddr?, (idS, (idR, macKey)))) =>
    match CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec body with
    | .ok m => m.verifyMacWithAddresses C.F expectedAddr? idS idR macKey
    | .error _ => false
  | .spqrV1InitOp, (isAlice, pqrKey) =>
    (CryptoVerification.LibsignalSpqrV1.spqrV1Init C.F K (if isAlice then .a2b else .b2a) pqrKey).take 512
  | .spqrNegotiateInit, (verByte, (dirI32, authKey)) =>
    spqrNegotiateInitEval C.F K verByte dirI32 authKey
  | .spqrBraidSend, (v1Raw, coins) => spqrBraidSendEval C.F K v1Raw coins
  | .spqrBraidRecv, (v1Raw, (msgEpoch, rem)) => spqrBraidRecvEval C.F K v1Raw msgEpoch rem
  | .spqrChainFromVn, vn => spqrChainFromVnEval C.F vn
  | .spqrChainAddEpoch, (ch, (ep, sec)) => spqrChainAddEpochEval C.F ch ep sec
  | .spqrChainNextKey, (next, ctr) => spqrChainNextKeyEval C.F next ctr

def E2ECryptoOp.cost (ℓ : ℕ) : E2ECryptoOp → ℕ
  | .x25519 | .x25519Base | .pow8 | .sessionKeyPairGen | .chainStep => 8
  | .isCanonical => 2
  | .sigSign | .sigVerify => 60
  | .kemKeyGen | .kemEncaps | .kemDecaps => 160
  | .hkdfDerive96 | .sessionRootCreateChain | .spqrChainFromVn => 16
  | .deriveMsgKeys | .spqrChainNextKey => 12
  | .aes256CbcEnc => 2 * (ℓ / 16 + 2) + 4
  | .aes256CbcDec => 2 * (ℓ / 16 + 2) + (ℓ / 32 + 6)
  | .signalMsgEncode => 4 * (ℓ / 32 + 12) + 204
  | .signalMsgVerifyMac => 2 * (ℓ / 32 + 12) + 8
  | .spqrV1InitOp => 210
  | .spqrNegotiateInit => 1600
  | .spqrBraidSend | .spqrBraidRecv => 3072
  | .spqrChainAddEpoch => 24

/-- Cryptographic primitive operation table parameterized by `(P, C, K)`. -/
@[reducible] def e2eCryptoOps (ℓ : ℕ) (P : SignalPqxdh.Primitives) (C : Crypto)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem) : Ops (e2eSig ℓ) where
  Op := E2ECryptoOp
  dom := E2ECryptoOp.dom ℓ
  cod := E2ECryptoOp.cod ℓ
  eval := E2ECryptoOp.eval ℓ P C K
  cost := E2ECryptoOp.cost ℓ

@[reducible] def e2ePrimOps (ℓ : ℕ) {Pt : Type} (P : SignalPqxdh.Primitives) (C : Crypto)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    Ops (e2eSig ℓ) :=
  ReductionDsl.Ops.sum (e2eCurveCheckOps ℓ decT encT) (e2eCryptoOps ℓ P C K)

/-- Operation table for the binary-harness wire/state adapter `L_bh`, independent of `(P, C, K)`. -/
@[reducible] def e2eAdapterOps (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) : Ops (e2eSig ℓ) :=
  ReductionDsl.Ops.sum (e2ePureOps ℓ) (e2eCurveCheckOps ℓ decT encT)

/-- Complete operation table for the E2E composition reductions `R_e2e`. -/
@[reducible] def e2eOps (ℓ : ℕ) {Pt : Type} (P : SignalPqxdh.Primitives) (C : Crypto)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    Ops (e2eSig ℓ) :=
  ReductionDsl.Ops.sum (e2ePureOps ℓ) (e2ePrimOps ℓ P C K decT encT)

/-! ## Target oracle interfaces and game codecs -/

inductive E2EKeyIndTag where
  | keyInd
  deriving DecidableEq, Repr

/-- Target oracle interface for `R_e2e.kindRed` (`unifSpec + SignalPqxdh.keyIndSpec S`). -/
@[reducible] def e2eKeyIndTargetIface (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    Iface (e2eSig ℓ) (unifSpec + SignalPqxdh.keyIndSpec S) where
  fwdU n := query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inl n)
  uCost := 1
  Tag := E2EKeyIndTag
  dom := fun | .keyInd => keyIndQT S
  cod := fun | .keyInd => keyIndRT
  enc := fun | .keyInd, q => .inr (keyIndQdec q)
  dec := fun | .keyInd, _, r => keyIndRenc r
  qCost := fun | .keyInd => 128
  smp := e2eSamplers ℓ

inductive E2ESessionTag where
  | tr | ch | dl | ij | cr
  deriving DecidableEq, Repr

/-- Target oracle interface for `R_e2e.prefixRed` over single-session `SM.spec (GhostState Bytes)`. -/
@[reducible] def e2eSessionTargetIface (ℓ : ℕ) :
    Iface (e2eSig ℓ) (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) where
  fwdU n := query (spec := unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (.inl n)
  uCost := 1
  Tag := E2ESessionTag
  dom := fun
    | .tr => .prod .bool (.prod PlainT (.opt BV512))
    | .ch => .prod .bool (.prod PlainT (.prod PlainT (.opt BV512)))
    | .dl | .ij => .prod .bool (B 32)
    | .cr => .bool
  cod := fun
    | .tr | .ch => .opt (B 32)
    | .dl | .ij => .opt recvResultT
    | .cr => .opt GhostStT
  enc := fun
    | .tr, (p, (m, r)) => .inr (.inl (.inl (.inl (.inl (boolToParty p, m, r)))))
    | .ch, (p, (m0, (m1, r))) => .inr (.inl (.inl (.inl (.inr (boolToParty p, m0, m1, r)))))
    | .dl, (p, c) => .inr (.inl (.inl (.inr (boolToParty p, c))))
    | .ij, (p, c) => .inr (.inl (.inr (boolToParty p, c)))
    | .cr, p => .inr (.inr (boolToParty p))
  dec := fun
    | .tr, _, r => r
    | .ch, _, r => r
    | .dl, _, r => r.map recvResultEnc
    | .ij, _, r => r.map recvResultEnc
    | .cr, _, r => r
  qCost := fun
    | .tr => ℓ / 32 + 16
    | .ch => 2 * (ℓ / 32) + 18
    | .dl | .ij => ℓ / 32 + 16
    | .cr => 32000
  smp := e2eSamplers ℓ

inductive E2EAdapterTag where
  | ki | ctl | tr | ch | dl | ij | cr
  deriving DecidableEq, Repr

@[reducible] def e2eCtlSpec (Ctl : Type) : OracleSpec Ctl :=
  fun _ => Option ℕ

@[reducible] def e2eDrSpec (St : Type) (ℓ : ℕ) :
    OracleSpec (ℕ × (CryptoGames.SM.spec St (Plain ℓ) (BitVec 512) Bytes).Domain) :=
  fun x => (CryptoGames.SM.spec St (Plain ℓ) (BitVec 512) Bytes).Range x.2

@[reducible] def e2eComposedGameSpec (S : SignalPqxdh.Setup) (Ctl St : Type) (ℓ : ℕ) :=
  SignalPqxdh.keyIndSpec S + e2eCtlSpec Ctl + e2eDrSpec St ℓ

/-- Target oracle interface for `L_bh` over the composed model game `e2eComposedGameSpec`. -/
@[reducible] def e2eAdapterIface (S : SignalPqxdh.Setup) (ℓ : ℕ) {Ctl : Type}
    (mkStart : SignalPqxdh.SessionId S → Ctl) :
    Iface (e2eSig ℓ) (unifSpec + e2eComposedGameSpec S Ctl (GhostState Bytes) ℓ) where
  fwdU n := query (spec := unifSpec + e2eComposedGameSpec S Ctl (GhostState Bytes) ℓ) (.inl n)
  uCost := 1
  Tag := E2EAdapterTag
  dom := fun
    | .ki => keyIndQT S
    | .ctl => sidT S
    | .tr => .prod .nat (.prod .bool (.prod PlainT (.opt BV512)))
    | .ch => .prod .nat (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
    | .dl | .ij => .prod .nat (.prod .bool (B 32))
    | .cr => .prod .nat .bool
  cod := fun
    | .ki => keyIndRT
    | .ctl => .opt .nat
    | .tr | .ch => .opt (B 32)
    | .dl | .ij => .opt recvResultT
    | .cr => .opt GhostStT
  enc := fun
    | .ki, kq => .inr (.inl (.inl (keyIndQdec kq)))
    | .ctl, sid => .inr (.inl (.inr (mkStart (sidOfV sid))))
    | .tr, (i, (p, (m, r))) =>
      .inr (.inr ⟨i, .inl (.inl (.inl (.inl (boolToParty p, m, r))))⟩)
    | .ch, (i, (p, (m0, (m1, r)))) =>
      .inr (.inr ⟨i, .inl (.inl (.inl (.inr (boolToParty p, m0, m1, r))))⟩)
    | .dl, (i, (p, c)) => .inr (.inr ⟨i, .inl (.inl (.inr (boolToParty p, c)))⟩)
    | .ij, (i, (p, c)) => .inr (.inr ⟨i, .inl (.inr (boolToParty p, c))⟩)
    | .cr, (i, p) => .inr (.inr ⟨i, .inr (boolToParty p)⟩)
  dec := fun
    | .ki, _, r => keyIndRenc r
    | .ctl, _, r => r
    | .tr, _, r => r
    | .ch, _, r => r
    | .dl, _, r => r.map recvResultEnc
    | .ij, _, r => r.map recvResultEnc
    | .cr, _, r => r
  qCost := fun
    | .ki => 128
    | .ctl => 4
    | .tr => ℓ / 32 + 16
    | .ch => 2 * (ℓ / 32) + 18
    | .dl | .ij => ℓ / 32 + 16
    | .cr => 32000
  smp := e2eSamplers ℓ

/-- Source game codec for `R_e2e` over `GhostState Bytes`. -/
@[reducible] def e2eGameCodec (S : SignalPqxdh.Setup) (ℓ : ℕ) {Ctl : Type}
    (unStart : Ctl → SignalPqxdh.SessionId S) :
    GameCodec (e2eSig ℓ) (e2eComposedGameSpec S Ctl (GhostState Bytes) ℓ) where
  Q := .sum (.sum (keyIndQT S) (sidT S)) (.prod .nat smQT)
  R := .sum (.sum keyIndRT (.opt .nat)) (smRT GhostStT)
  qenc := fun
    | .inl (.inl kq) => .inl (.inl (keyIndQenc kq))
    | .inl (.inr cq) => .inl (.inr (sidV (unStart cq)))
    | .inr ⟨i, sq⟩ => .inr (i, smQenc sq)
  rdec := fun
    | .inl (.inl _), .inl (.inl r) => keyIndRdec r
    | .inl (.inl _), _ => .noneResp
    | .inl (.inr _), .inl (.inr r) => r
    | .inl (.inr _), _ => none
    | .inr ⟨_, sq⟩, .inr sr => smRdec (stT := GhostStT) id sq sr
    | .inr ⟨_, sq⟩, .inl _ => smRdec (stT := GhostStT) id sq (none, (none, none))
  codecCost := 64

/-- Source game codec for `L_bh` over `BinState`. -/
@[reducible] def e2eAdapterCodec (S : SignalPqxdh.Setup) (ℓ : ℕ) {Ctl : Type}
    (unStart : Ctl → SignalPqxdh.SessionId S) :
    GameCodec (e2eSig ℓ) (e2eComposedGameSpec S Ctl BinState ℓ) where
  Q := .sum (.sum (keyIndQT S) (sidT S)) (.prod .nat smQT)
  R := .sum (.sum keyIndRT (.opt .nat)) (smRT BinStT)
  qenc := fun
    | .inl (.inl kq) => .inl (.inl (keyIndQenc kq))
    | .inl (.inr cq) => .inl (.inr (sidV (unStart cq)))
    | .inr ⟨i, sq⟩ => .inr (i, smQenc sq)
  rdec := fun
    | .inl (.inl _), .inl (.inl r) => keyIndRdec r
    | .inl (.inl _), _ => .noneResp
    | .inl (.inr _), .inl (.inr r) => r
    | .inl (.inr _), _ => none
    | .inr ⟨_, sq⟩, .inr sr => smRdec (stT := BinStT) id sq sr
    | .inr ⟨_, sq⟩, .inl _ => smRdec (stT := BinStT) id sq (none, (none, none))
  codecCost := 64

end Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables

-- AUTO-BRIDGE BEGIN
namespace CryptoVerification.E2E.Costed
export Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables (
  B BV128 BV256 BV512 BinStT E2EAdapterTag E2ECryptoOp E2ECurveCheckOp E2EKeyIndTag E2EPureOp
  E2ESessionTag E2ESort E2EUnifBase FinT GhostStT IdKey PB PK PU32 PlainT U32 U64 U8 binStBlocks
  boolToParty bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV drRecvChainT
  drSenderChainT e2eAdapterCodec e2eAdapterIface e2eAdapterOps e2eComposedGameSpec e2eCryptoOps
  e2eCtlSpec e2eCurveCheckOps e2eDecodePreKeyMsg e2eDecodePreKeyRaw e2eDrSpec
  e2eEncodeSessionRecord e2eExpectedPreKeyMsg e2eGameCodec e2eHdrOfPreKeyMsg e2eKeyIndTargetIface
  e2eOps e2eParseDjbKeyField e2eParseInnerMsgField e2eParseKyberCtField e2eParseOptPreKeyId
  e2eParseUint32Field e2ePartneredInnerBytes e2ePrimOps e2ePureOps e2eReadProstVarint e2eReadU32BE
  e2eRecordExtras e2eSamplers e2eSessionTargetIface e2eSig e2eWireInnerBytes ghostJoinEval
  ghostPartsT ghostSplitEval ghostStBlocks hdrOfV hdrT hdrV joinSpqrPrev keyIndQT keyIndQdec
  keyIndQenc keyIndRT keyIndRdec keyIndRenc partyToBool prefixCtxT recvResultDec recvResultEnc
  recvResultT sidOfV sidT sidV signalHdrT signalParsedT smQT smQenc smRT smRdec splitSpqrPrev
  spqrBraidRecvEval spqrBraidSendEval spqrChainAddEpochEval spqrChainFromVnEval
  spqrChainNextKeyEval spqrChainOfV spqrChainT spqrChainToV spqrDirOfV spqrDirT spqrDirToV
  spqrEpochLinkT spqrJoinEval spqrMsgPayloadSuffix spqrNegotiateInitEval spqrParamsOfV spqrParamsT
  spqrParamsToV spqrPrevEntryT spqrSplitEval spqrStatePartsT spqrVnOfV spqrVnT spqrVnToV
)
end CryptoVerification.E2E.Costed
namespace CryptoVerification.E2E.Costed.E2ESort
export Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ESort (
  binSt blocks bv128 bv256 bv512 bytes den fin ghostSt idKey pbytes pk plain pu32 u32 u64 u8
)
end CryptoVerification.E2E.Costed.E2ESort
namespace CryptoVerification.E2E.Costed.E2EUnifBase
export Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EUnifBase (
  bv256 bv512 cost sort
)
end CryptoVerification.E2E.Costed.E2EUnifBase
namespace CryptoVerification.E2E.Costed.E2EPureOp
export Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp (
  bv128Eq bv256Eq bv256Lit bv256ToBytes32 bv256ToPbytes32 bv512Lit bv512ToBytes64 bytesCat
  bytesCons bytesDrop bytesEq bytesLen bytesLit bytesLtOp bytesTake bytesTakeK bytesToBv256
  bytesToPbytes bytesToPlain bytesWiden checkShortCiphertext cod cost dom encodeSessionRecord eval
  finEq finVal ghostStateJoin ghostStateSplit idKeyEq idKeyOfPbytes idKeySerialize
  isValidSignalWire opSize parsePreKeyWire partneredInnerBytes pbytesCat pbytesCons pbytesDrop pbytesEq
  pbytesLen pbytesLit pbytesTake pbytesTakeK pbytesToBv256 pbytesToBytes pbytesWiden pkDeserialize
  pkEq pkOfPbytes pkSerialize plainDefault plainEq plainToBytes pu32Eq pu32Lit pu32OfNat pu32ToNat
  pu32ToU32 signalMsgParse splitWhisperWire spqrAssembleMsg spqrParsePreamble spqrStateJoin
  spqrStateSplit u32Add u32BeBytes u32Eq u32Lit u32Lt u32OfNat u32Sub u32ToNat u32ToPu32 u64Add
  u64Eq u64Lit u64Lt u64OfNat u64Sub u64ToNat u64Trunc8 u8Eq u8Lit u8Lt u8OfNat u8ToNat
  wireInnerBytes wrapPreKeyWire wrapWhisperWire
)
end CryptoVerification.E2E.Costed.E2EPureOp
namespace CryptoVerification.E2E.Costed.E2ECurveCheckOp
export Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECurveCheckOp (
  checkRatchetKeyOnCurve decEncCheck
)
end CryptoVerification.E2E.Costed.E2ECurveCheckOp
namespace CryptoVerification.E2E.Costed.E2ECryptoOp
export Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp (
  aes256CbcDec aes256CbcEnc chainStep cod cost deriveMsgKeys dom eval hkdfDerive96 isCanonical
  kemDecaps kemEncaps kemKeyGen pow8 sessionKeyPairGen sessionRootCreateChain sigSign sigVerify
  signalMsgEncode signalMsgVerifyMac spqrBraidRecv spqrBraidSend spqrChainAddEpoch spqrChainFromVn
  spqrChainNextKey spqrNegotiateInit spqrV1InitOp x25519 x25519Base
)
end CryptoVerification.E2E.Costed.E2ECryptoOp
namespace CryptoVerification.E2E.Costed.E2EKeyIndTag
export Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EKeyIndTag (
  keyInd
)
end CryptoVerification.E2E.Costed.E2EKeyIndTag
namespace CryptoVerification.E2E.Costed.E2ESessionTag
export Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ESessionTag (
  ch cr dl ij tr
)
end CryptoVerification.E2E.Costed.E2ESessionTag
namespace CryptoVerification.E2E.Costed.E2EAdapterTag
export Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EAdapterTag (
  ch cr ctl dl ij ki tr
)
end CryptoVerification.E2E.Costed.E2EAdapterTag
-- AUTO-BRIDGE END
