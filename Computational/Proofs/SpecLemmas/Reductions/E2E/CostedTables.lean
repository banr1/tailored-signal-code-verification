/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.SpkHop2Red
public import Computational.Proofs.SpecLemmas.Session.ACD19.SM.CostedTables
public import Computational.Proofs.SpecLemmas.Reductions.Primitives.PRF.CostedTables
public import Computational.Proofs.SpecLemmas.Reductions.Primitives.PRG.CostedTables
public import Computational.Specifications.Reductions.ReductionDsl.Samplers

/-!
# Libsignal E2E pre-key reduction tables

**Checked by Lean.** Shared `ReductionDsl` signature, operation tables, target PRF/PRG interfaces,
and SM game codec for the Libsignal signed-pre-key reductions (`spkLeakRed`, `hop2PrgRedK`,
`hop2PrfRedK`) under `configRefuseEarlyBobCorr` (DEV-LS33, DEV-LS34). Abstract sorts have unit size
so costs count primitive calls, and `spkSc` exposes Bob's leaked signed-pre-key scalar `s` in
`sessionSchemeFixedSpk`.
-/

@[expose] public section

namespace Computational.Proofs.SpecLemmas.Reductions.E2E.CostedTables

open Computational.Proofs.SpecLemmas.Reductions.Primitives.PRF.CostedTables (prfIface)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSession (GhostState Params PublicKey currentVersion rootCreateChain)
open CryptoGames.PRG.Costed (prgIface)
open CryptoGames.Ratchet (expandPRG extractPRF padOrTruncatePlain)
open CryptoGames.Ratchet.LibsignalInst (ratchetKeyAdmissible)
open CryptoGames.SM (SMSort partyEnc smCodec smOps smSig)
open CryptoVerification.E2E (Bytes sessionSchemeU)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open ReductionDsl (GameCodec Iface Ops Sig bits unifSamplers)

open OracleSpec OracleComp

/-- Signature for Libsignal E2E reductions: `smSig` instantiated with points `Pt`,
`GhostState Bytes`, `CBC.Plain ℓ`, `PQC`, 256-bit keys/scalars, and wire `Bytes`. -/
@[reducible] def spkLeakSessionSig (Pt : Type) (ℓ : ℕ) (PQC : Type := Unit) : Sig :=
  smSig Pt (GhostState Bytes) Unit (CryptoGames.CBC.Plain ℓ) PQC (BitVec 256) Bytes

/-- SM operation table for `sessionSchemeU P ℓ` with
`injOK = ratchetKeyAdmissible protoSignalCodec decT encT`. -/
@[reducible] def spkLeakSessionSmOps {Pt PQC : Type} (P : Params Bytes PQC) (ℓ : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    Ops (spkLeakSessionSig Pt ℓ PQC) :=
  smOps
    (init := fun _ _ => none)
    (send := fun st m r => some ((sessionSchemeU P ℓ).send st m r))
    (receive := (sessionSchemeU P ℓ).receive)
    (eqMsg := (· == ·))
    (eqCt := (· == ·))
    (blank := id)
    (injOK := ratchetKeyAdmissible protoSignalCodec decT encT)
    (stOK := fun _ _ => true)
    (φ := fun _ => none)

def pkToBytes (pk : PublicKey) : Bytes :=
  pk.bytes.toList

def bytesToPk? (bs : Bytes) : Option PublicKey :=
  if h : bs.length = 32 then some ⟨⟨bs, h⟩⟩ else none

/-- Primitive group, KDF, public-key, and `GhostState` operations of the E2E pre-key reductions
beyond `SMOp`. -/
inductive E2EOp
  | basePt
  | dh
  | isZeroPt
  | eqPt
  | zeroBv
  | spkSc
  | rootExpand
  | extractTag
  | rootCreateChain
  | genPub
  | encT
  | decT
  | eqBytes
  | parseSenderKey
  | stParty
  | stEpoch (B : ℕ)
  | hasEpoch0Chain
  | hasSenderChain
  | hasRecvChain
  | newSession
  | setPendingPreKey
  | setRootKey
  | setSenderChain
  | addRecvChain
  | resetEpoch0
  | advancePrevCounter
  | pushRecvChain
  | tryDecryptWhisper (B : ℕ)
  deriving DecidableEq

/-- Operation table for `E2EOp` (unit cost, except `bits B` for clamped-index operations `stEpoch B`
and `tryDecryptWhisper B`), parameterized by the leaked scalar `s`. -/
@[reducible] def spkLeakOps {Pt PQC : Type} [DecidableEq Pt] [Zero Pt]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) :
    Ops (spkLeakSessionSig Pt ℓ PQC) where
  Op := E2EOp
  dom := fun
    | .basePt => .unit
    | .dh => .prod (.base .rcoins) (.base .key)
    | .isZeroPt => .base .key
    | .eqPt => .prod (.base .key) (.base .key)
    | .zeroBv => .unit
    | .spkSc => .unit
    | .rootExpand => .base .rcoins
    | .extractTag => .prod (.base .rcoins) (.base .key)
    | .rootCreateChain => .prod (.base .rcoins) (.prod (.base .ct) (.base .rcoins))
    | .genPub => .base .rcoins
    | .encT => .base .key
    | .decT => .base .ct
    | .eqBytes => .prod (.base .ct) (.base .ct)
    | .parseSenderKey => .base .ct
    | .stParty => .base .st
    | .stEpoch _ => .base .st
    | .hasEpoch0Chain => .base .st
    | .hasSenderChain => .base .st
    | .hasRecvChain => .prod (.base .st) (.base .ct)
    | .newSession => .prod .bool (.prod (.base .rcoins) (.base .rcoins))
    | .setPendingPreKey => .base .st
    | .setRootKey => .prod (.base .st) (.base .rcoins)
    | .setSenderChain => .prod (.base .st) (.prod (.base .rcoins) (.base .rcoins))
    | .addRecvChain => .prod (.base .st) (.prod (.base .ct) (.base .rcoins))
    | .resetEpoch0 => .base .st
    | .advancePrevCounter => .base .st
    | .pushRecvChain => .prod (.base .st) (.prod (.base .ct) (.base .rcoins))
    | .tryDecryptWhisper _ => .prod (.base .st) (.prod (.base .ct) (.base .rcoins))
  cod := fun
    | .basePt => .base .key
    | .dh => .base .key
    | .isZeroPt => .bool
    | .eqPt => .bool
    | .zeroBv => .base .rcoins
    | .spkSc => .base .rcoins
    | .rootExpand => .prod (.base .rcoins) (.base .rcoins)
    | .extractTag => .base .rcoins
    | .rootCreateChain => .opt (.prod (.base .rcoins) (.base .rcoins))
    | .genPub => .base .ct
    | .encT => .base .ct
    | .decT => .opt (.base .key)
    | .eqBytes => .bool
    | .parseSenderKey => .opt (.base .ct)
    | .stParty => .bool
    | .stEpoch _ => .nat
    | .hasEpoch0Chain => .bool
    | .hasSenderChain => .bool
    | .hasRecvChain => .bool
    | .newSession => .base .st
    | .setPendingPreKey => .base .st
    | .setRootKey => .base .st
    | .setSenderChain => .base .st
    | .addRecvChain => .base .st
    | .resetEpoch0 => .base .st
    | .advancePrevCounter => .base .st
    | .pushRecvChain => .base .st
    | .tryDecryptWhisper _ => .opt (.prod (.base .st) (.prod .nat (.prod .nat (.base .msg))))
  eval := fun
    | .basePt, () => Dh.base
    | .dh, (x, T) => Dh.dh x T
    | .isZeroPt, T => decide (T = 0)
    | .eqPt, (T₁, T₂) => T₁ == T₂
    | .zeroBv, () => 0
    | .spkSc, () => s
    | .rootExpand, prk => (expandPRG P.C.F).gen prk
    | .extractTag, (rk, T) => (extractPRF P.C.F encPt).tag rk T
    | .rootCreateChain, (rk, pkBytes, rc) =>
      match bytesToPk? pkBytes with
      | none => none
      | some pk =>
        match rootCreateChain P.C rk pk (CryptoGames.LibsignalSession.KeyPair.generate P.C rc).privateKey with
        | .error _ => none
        | .ok (rk', ck) => some (rk', ck.key)
    | .genPub, sc => pkToBytes (CryptoGames.LibsignalSession.KeyPair.generate P.C sc).publicKey
    | .encT, T => pkToBytes (encT T)
    | .decT, bs => (bytesToPk? bs).bind decT
    | .eqBytes, (a, b) => a == b
    | .parseSenderKey, c =>
      match CryptoGames.LibsignalSession.SignalMessage.tryFrom P.codec c with
      | .error _ => none
      | .ok msg => some (pkToBytes msg.senderRatchetKey)
    | .stParty, g => partyEnc g.party
    | .stEpoch B, g => min g.epoch B
    | .hasEpoch0Chain, g => g.chainEpochs.contains 0
    | .hasSenderChain, g => g.session.senderChain.isSome
    | .hasRecvChain, (g, pkBytes) =>
      match bytesToPk? pkBytes with
      | none => false
      | some pk => (g.session.receiverChains.findIdx? (·.senderRatchetKey == pk)).isSome
    | .newSession, (isB, rk, pqr) =>
      if isB then
        ⟨.B, CryptoGames.LibsignalSession.SessionState.new currentVersion P.idB P.idA rk (P.spqr.init .b2a pqr), 0, []⟩
      else
        ⟨.A, CryptoGames.LibsignalSession.SessionState.new currentVersion P.idA P.idB rk (P.spqr.init .a2b pqr), 0, []⟩
    | .setPendingPreKey, g =>
      { g with session := g.session.setUnacknowledgedPreKeyMessage }
    | .setRootKey, (g, rk) =>
      { g with session := { g.session with rootKey := rk } }
    | .setSenderChain, (g, sc, ck) =>
      { g with session := g.session.setSenderChain (CryptoGames.LibsignalSession.KeyPair.generate P.C sc) ⟨ck, 0⟩ }
    | .addRecvChain, (g, pkBytes, ck) =>
      match bytesToPk? pkBytes with
      | none => g
      | some pk =>
        { g with
          session := g.session.addReceiverChain pk ⟨ck, 0⟩
          chainEpochs := g.chainEpochs ++ [g.epoch] }
    | .resetEpoch0, g =>
      { g with
        session := { g.session with previousCounter := 0, receiverChains := [] }
        epoch := 0
        chainEpochs := [] }
    | .advancePrevCounter, g =>
      let prev := match g.session.senderChain with
        | none => g.session.previousCounter
        | some sc => if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
      { g with session := { g.session with previousCounter := prev } }
    | .pushRecvChain, (g, pkBytes, ck) =>
      match bytesToPk? pkBytes with
      | none => g
      | some pk =>
        { g with
          session :=
            { g.session with
              receiverChains := CryptoGames.LibsignalSession.RatchetState.evictReceiverChains
                (g.session.receiverChains ++ [⟨pk, some ⟨ck, 0⟩, []⟩]) }
          epoch := g.epoch + 1
          chainEpochs := g.chainEpochs ++ [g.epoch + 1] }
    | .tryDecryptWhisper B, (g, c, rc) =>
      match CryptoGames.LibsignalSession.SignalMessage.tryFrom P.codec c with
      | .error _ => none
      | .ok msg =>
        match CryptoGames.LibsignalSession.SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
            rc g.session with
        | (.error _, _) => none
        | (.ok m, s_out) =>
          let epochs := g.chainEpochs.drop (g.chainEpochs.length - s_out.receiverChains.length)
          some ({ g with session := s_out, chainEpochs := epochs },
            min g.epoch B, min (msg.counter.toNat + 1) B, padOrTruncatePlain ℓ m)
  cost := fun
    | .stEpoch B => bits B
    | .tryDecryptWhisper B => bits B
    | _ => 1

/-- Combined operation table summing `spkLeakSessionSmOps` and `spkLeakOps`. -/
@[reducible] def spkLeakSessionOps {Pt PQC : Type} [DecidableEq Pt] [Zero Pt]
    (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) :
    Ops (spkLeakSessionSig Pt ℓ PQC) :=
  ReductionDsl.Ops.sum (spkLeakSessionSmOps P ℓ decT encT) (spkLeakOps P ℓ Dh encPt encT decT s)

@[reducible] def e2eUnifSort : Bool → SMSort
  | false => .coins
  | true => .rcoins

instance (Pt : Type) (ℓ : ℕ) (PQC : Type) [SampleableType PQC] :
    ∀ b : Bool, SampleableType ((spkLeakSessionSig Pt ℓ PQC).den (e2eUnifSort b))
  | false => inferInstanceAs (SampleableType PQC)
  | true => inferInstanceAs (SampleableType (BitVec 256))

/-- Target PRF interface (`unifSpec + prfSpec Pt (BitVec 256)`) with uniform coin samplers for
`spkLeakRed` and `hop2PrfRedK`. -/
@[reducible] def e2ePrfIface (Pt : Type) (ℓ : ℕ) (PQC : Type := Unit) [SampleableType PQC] :
    Iface (spkLeakSessionSig Pt ℓ PQC) (unifSpec + CryptoGames.MACScheme.prfSpec Pt (BitVec 256)) :=
  (prfIface (S := spkLeakSessionSig Pt ℓ PQC) (.base .key) (.base .rcoins)).withSamp
    (unifSamplers (S := spkLeakSessionSig Pt ℓ PQC) e2eUnifSort (fun _ => 1))

/-- Target coin-only PRG interface (`unifSpec`) with uniform coin samplers for `hop2PrgRedK`. -/
@[reducible] def e2ePrgIface (Pt : Type) (ℓ : ℕ) (PQC : Type := Unit) [SampleableType PQC] :
    Iface (spkLeakSessionSig Pt ℓ PQC) unifSpec :=
  (prgIface (spkLeakSessionSig Pt ℓ PQC)).withSamp
    (unifSamplers (S := spkLeakSessionSig Pt ℓ PQC) e2eUnifSort (fun _ => 1))

/-- Source SM game codec for `spkLeakSessionSig` (`codecCost = 6`). -/
@[reducible] def e2eCodec (Pt : Type) (ℓ : ℕ) (PQC : Type := Unit) :
    GameCodec (spkLeakSessionSig Pt ℓ PQC) (CryptoGames.SM.spec (GhostState Bytes) (CryptoGames.CBC.Plain ℓ) PQC Bytes) :=
  smCodec Pt (GhostState Bytes) Unit (CryptoGames.CBC.Plain ℓ) PQC (BitVec 256) Bytes .st

end Computational.Proofs.SpecLemmas.Reductions.E2E.CostedTables

-- AUTO-BRIDGE BEGIN
namespace CryptoVerification.E2E.Costed
export Computational.Proofs.SpecLemmas.Reductions.E2E.CostedTables (
  E2EOp bytesToPk? e2eCodec e2ePrfIface e2ePrgIface e2eUnifSort
  pkToBytes spkLeakOps spkLeakSessionOps spkLeakSessionSig spkLeakSessionSmOps
)
end CryptoVerification.E2E.Costed
namespace CryptoVerification.E2E.Costed.E2EOp
export Computational.Proofs.SpecLemmas.Reductions.E2E.CostedTables.E2EOp (
  addRecvChain advancePrevCounter basePt decT dh encT
  eqBytes eqPt extractTag genPub hasEpoch0Chain hasRecvChain
  hasSenderChain isZeroPt newSession parseSenderKey pushRecvChain resetEpoch0
  rootCreateChain rootExpand setPendingPreKey setRootKey setSenderChain spkSc
  stEpoch stParty tryDecryptWhisper zeroBv
)
end CryptoVerification.E2E.Costed.E2EOp
-- AUTO-BRIDGE END
