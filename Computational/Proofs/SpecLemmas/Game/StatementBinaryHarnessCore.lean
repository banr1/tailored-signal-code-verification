/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.StatementBinaryHarnessCore
public import Computational.Specifications.Assumptions.KemCorrect

/-!
# Proof-side `modelPrims` assumption bundles and binary-harness adapter helpers

**Checked by Lean.** Companion assumption bundles on `modelPrims` and per-instance record, wire,
and state-projection helpers for the binary-harness adapter proofs.
-/

@[expose] public section

set_option autoImplicit false
open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1

namespace BH
end BH
open BH

/-- Bob's record extras for a session with header `hdr`. -/
def bhRecvExtrasOfHdr (meA meB : LocalIdentity) (hdr : SignalPqxdh.HandshakeHdr) : RecordExtras :=
  { pending := { preKeyId := none, signedPreKeyId := 0#32, baseKey := ⟨u8Vec 32 hdr.ekAPk⟩,
                 timestamp := 0#64 }
    kyber := none
    remoteRegistrationId := meA.regId
    localRegistrationId := meB.regId
    aliceBaseKey := djbKey (u8Vec 32 hdr.ekAPk) }

/-- Shared X25519, cofactor (`pow8`), and collision assumptions on `(X, W)`. -/
structure ModelPrimsSharedAssumptions (X : UnreachedPqxdhPrimitives) (W : PEParams) : Prop where
  x25519_zero_iff : ∀ a1 a2 pk : List UInt8, a1.length = 32 → a2.length = 32 → pk.length = 32 →
    ((modelPrims X W).x25519 a1 pk = List.replicate 32 0 ↔
      (modelPrims X W).x25519 a2 pk = List.replicate 32 0)
  canon_base : ∀ e : List UInt8, e.length = 32 →
    (modelPrims X W).isCanonical ((modelPrims X W).x25519Base e) = true
  canon_x25519 : ∀ a pk : List UInt8, a.length = 32 → (modelPrims X W).isCanonical pk = true →
    (modelPrims X W).isCanonical ((modelPrims X W).x25519 a pk) = true
  pow8_idemp : ∀ p : List UInt8, X.pow8 (X.pow8 p) = X.pow8 p
  isValidDhTriple_eq_ref : ∀ A B Z : List UInt8,
    X.isValidDhTriple A B Z = true ↔ SignalPqxdh.isValidDhTripleRef (modelPrims X W) A B Z
  x25519_pow8_congr : ∀ a pk1 pk2 : List UInt8, a.length = 32 → pk1.length = 32 → pk2.length = 32 →
    X.pow8 pk1 = X.pow8 pk2 → (modelPrims X W).x25519 a pk1 = (modelPrims X W).x25519 a pk2
  x25519_congr_of_base_eq : ∀ a1 a2 pk : List UInt8, a1.length = 32 → a2.length = 32 →
    (modelPrims X W).isCanonical pk = true →
    (modelPrims X W).x25519Base a1 = (modelPrims X W).x25519Base a2 →
    (modelPrims X W).x25519 a1 pk = (modelPrims X W).x25519 a2 pk
  canon_pow8_inj : ∀ pk1 pk2 : List UInt8, (modelPrims X W).isCanonical pk1 = true →
    (modelPrims X W).isCanonical pk2 = true → X.pow8 pk1 = X.pow8 pk2 → pk1 = pk2
  pow8_len : ∀ p : List UInt8, (X.pow8 p).length = 32
  ec_coll_bound : ∀ targetPk : List UInt8,
    (𝒟[do let sk ← SignalPqxdh.sampleScalar32
          pure (X.pow8 ((modelPrims X W).x25519Base sk) == X.pow8 targetPk)] {true}).toReal
      ≤ 1 / (2 : ℝ) ^ 250
  x25519_inj_pow8 : ∀ a pk1 pk2 : List UInt8, a.length = 32 → pk1.length = 32 → pk2.length = 32 →
    (modelPrims X W).x25519 a pk1 = (modelPrims X W).x25519 a pk2 → X.pow8 pk1 = X.pow8 pk2
  pow8_base_len : ∀ p e : List UInt8, e.length = 32 →
    X.pow8 p = X.pow8 ((modelPrims X W).x25519Base e) → p.length = 32

/-- External primitive, correctness, collision, and unreached helper-pinning (`DEV-C16`)
assumptions on `(X, W)` used to instantiate `SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W)`. -/
structure ModelPrimsCryptoAssumptions (X : UnreachedPqxdhPrimitives) (W : PEParams) : Prop extends
    ModelPrimsSharedAssumptions X W where
  sigPkGen_eq_x25519Base : X.sigPkGen = (modelPrims X W).x25519Base
  scalarMul_len : ∀ a b : List UInt8, (X.scalarMul a b).length = 32
  scalarAdd_len : ∀ a b : List UInt8, (X.scalarAdd a b).length = 32
  kemKeyGen_len : ∀ seed : List UInt8,
    (X.kemKeyGen seed).1.length = 1568 ∧ (X.kemKeyGen seed).2.length = 3168
  sig_corr : ∀ sk msg r : List UInt8,
    (modelPrims X W).sigVerify (X.sigPkGen sk) msg (X.sigSign sk msg r) = true
  kem_coll_bound : ∀ targetPk : List UInt8,
    (𝒟[do let (pk, _) ← SignalPqxdh.sampleKemKeyGen (modelPrims X W); pure (pk == targetPk)]
      {true}).toReal ≤ 1 / (2 : ℝ) ^ 255

/-- Local `startDR` promotion step on `BHE2EDrvState S ℓ` over `pqxdhKeyIndImpl`. -/
def bhE2ELocalStart {S : SignalPqxdh.Setup} {ℓ : ℕ} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (bMode? : Option Bool)
    (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S) :
    ProbComp (Option ℕ × BHE2EDrvState S ℓ) := do
  match bhE2EGuard σ sid with
  | none => return (none, σ)
  | some (_, _, (u, j)) =>
    let (kr1, st1) ← (SignalPqxdh.pqxdhKeyIndImpl true S P (.testSession sid)).run σ.st
    let (kr2, st2) ← (SignalPqxdh.pqxdhKeyIndImpl true S P (.revealSpkSk u j)).run st1
    let ac ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
    return bhE2EFinishStartSpk C K bMode? { σ with st := st2 } sid kr1 kr2 ac

/-- Per-instance transcript metadata tracked by the binary-harness adapter. -/
structure BHAdapterInstMeta (S : SignalPqxdh.Setup) where
  sid : SignalPqxdh.SessionId S
  u_resp : Fin S.N_id
  hdr : SignalPqxdh.HandshakeHdr
  idB : SignalPqxdh.Bytes
  aliceAcked : Bool := false
  bobAccepted : Bool := false
  bobRemoteRegId : BitVec 32 := 0#32
  deriving DecidableEq, Repr

/-- Alice's `PreKeyMessageFields` wrapper for an unacknowledged send. -/
def bhAlicePreKeyMsgE {S : SignalPqxdh.Setup} (inst : BHAdapterInstMeta S) (inner : Bytes) :
    PreKeyMessageFields :=
  bhExpectedPreKeyMsg (bhInitRegId inst.sid) inst.hdr inner

/-- Alice's reconstructed `RecordExtras` on promoted instance `inst` (`DEV-M2`). -/
def bhInstExtrasA {S : SignalPqxdh.Setup} (inst : BHAdapterInstMeta S) : RecordExtras :=
  let regIdA : BitVec 32 := bhInitRegId inst.sid
  let base : PublicKey := ⟨u8Vec 32 inst.hdr.ekAPk⟩
  { pending := { preKeyId := inst.hdr.opkId?.map (fun id => BitVec.ofNat 32 id.toNat),
                 signedPreKeyId := BitVec.ofNat 32 inst.hdr.spkId.toNat,
                 baseKey := base, timestamp := 0#64 },
    kyber := some { preKeyId := BitVec.ofNat 32 inst.hdr.pqspkId.toNat,
                    ciphertext := kyberKey (u8Vec SignalPqxdh.kyberCtLen inst.hdr.kemCt) },
    remoteRegistrationId := BitVec.ofNat 32 inst.u_resp.val,
    localRegistrationId := regIdA, aliceBaseKey := base.serialize }

/-- Bob's reconstructed `RecordExtras` on promoted instance `inst` (`DEV-M2`). -/
def bhInstExtrasB {S : SignalPqxdh.Setup} (inst : BHAdapterInstMeta S) : RecordExtras :=
  let base : PublicKey := ⟨u8Vec 32 inst.hdr.ekAPk⟩
  { pending := { preKeyId := none, signedPreKeyId := 0#32, baseKey := base, timestamp := 0#64 },
    kyber := none, remoteRegistrationId := inst.bobRemoteRegId,
    localRegistrationId := BitVec.ofNat 32 inst.u_resp.val, aliceBaseKey := base.serialize }

/-- Wrap a model send ciphertext into the binary-harness wire format. -/
def bhWrapSendOut {S : SignalPqxdh.Setup} (inst : BHAdapterInstMeta S) (p : Party) (ct : Bytes) :
    Bytes :=
  if ct.isEmpty then []
  else match p with
    | .A => if !inst.aliceAcked then wirePrekey :: (bhAlicePreKeyMsgE inst ct).bytes
            else wireWhisper :: ct
    | .B => wireWhisper :: ct

/-- Map a model `GhostState Bytes` to the binary-harness `BinState` (`DEV-M2`). -/
def bhBinStateOfParty {S : SignalPqxdh.Setup} (inst : BHAdapterInstMeta S)
    (g : GhostState Bytes) : BinState :=
  let x := match g.party with | .A => bhInstExtrasA inst | .B => bhInstExtrasB inst
  binStateOfUnderExtras (fun _ => x) g

/-- Public prefix context `(idA, idB, spkCoins)` for a promoted DR instance. -/
structure BHPrefixCtx where
  idA : IdentityKey
  idB : IdentityKey
  spkCoins : BitVec 256

end CryptoVerification.E2E
