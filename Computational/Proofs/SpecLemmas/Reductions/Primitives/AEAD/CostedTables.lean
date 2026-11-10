/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSMInstance
public import Computational.Proofs.SpecLemmas.Reductions.Primitives.OTCCA.CostedTables
public import Computational.Proofs.SpecLemmas.Reductions.Primitives.PRF.CostedTables
public import Computational.Specifications.Reductions.ReductionDsl.Samplers

/-!
# WireAEAD and salt/wire reduction tables

**Checked by Lean.** Shared `ReductionDsl` signature, operation tables, target interfaces, and
source OT-CCA game codec for `WireAEAD.wireSpec` and the Libsignal per-message salt-PRF and
wire-OT-CCA reductions (`lSaltRed`, `lWireRed`, `slotSaltRed`, `slotWireRed`).
-/

@[expose] public section

namespace Computational.Proofs.SpecLemmas.Reductions.Primitives.AEAD.CostedTables

open Computational.Proofs.SpecLemmas.Reductions.Primitives.OTCCA.CostedTables (idealSamplers otccaCodec otccaIface otccaOps)
open Computational.Proofs.SpecLemmas.Reductions.Primitives.PRF.CostedTables (prfIface)
open CryptoGames (AEADScheme Party)
open CryptoGames.CBC (Plain)
open CryptoGames.HKDF (DerivedMessageKeys)
open CryptoGames.LibsignalAead (SerializedIdentityKeys)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey SignalHeader SignalMessageProtoCodec)
open CryptoGames.Ratchet (padOrTruncatePlain)
open CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart LibsignalWireOracleSpec Salt32 lAeadK lAeadR lHeader lIdeal lIds)
open CryptoGames.SM.Construction (Header)
open ReductionDsl (GameCodec Iface Ops Sig Ty unifSamplers unifSamplers0)

open OracleSpec OracleComp

inductive WireTag
  | enc | dec
  deriving DecidableEq

/-- Target oracle interface for `WireAEAD.wireSpec` with wire byte codec `toBytes`/`ofBytes` and
unit query cost. -/
@[reducible] def wireIface {S : Sig} (adT hdrT msgT msg'T rawT tagT : Ty S)
    (toBytes : rawT.denote → List (BitVec 8))
    (ofBytes : List (BitVec 8) → rawT.denote) :
    Iface S (unifSpec +
      CryptoGames.WireAEAD.wireSpec adT.denote hdrT.denote msgT.denote msg'T.denote tagT.denote) where
  fwdU := fun n =>
    query (spec := unifSpec +
      CryptoGames.WireAEAD.wireSpec adT.denote hdrT.denote msgT.denote msg'T.denote tagT.denote) (.inl n)
  uCost := 1
  Tag := WireTag
  dom := fun
    | .enc => .prod adT (.prod hdrT msgT)
    | .dec => .prod adT (.prod rawT tagT)
  cod := fun
    | .enc => .opt (.prod rawT tagT)
    | .dec => .opt (.prod hdrT msg'T)
  enc := fun
    | .enc, x => .inr (.inl x)
    | .dec, (a, (w, τ)) => .inr (.inr (a, (toBytes w, τ)))
  dec := fun
    | .enc, _, u => u.map fun (w, τ) => (ofBytes w, τ)
    | .dec, _, u => u
  qCost := fun _ => 1
  smp := ReductionDsl.Samplers.empty

/-- Base value sorts of the Libsignal per-message salt/wire reductions. -/
inductive SaltWireSort
  | seed
  | msgKey
  | salt
  | ad
  | plain
  | idKeys
  | sigHdr
  | rawBytes
  | macTag
  deriving DecidableEq

@[reducible] def SaltWireSort.den (Pt : Type) (ℓ : ℕ) : SaltWireSort → Type
  | .seed => BitVec 256
  | .msgKey => DerivedMessageKeys
  | .salt => Salt32
  | .ad => Header Pt × LibsignalMsgPublicPart
  | .plain => Plain ℓ
  | .idKeys => SerializedIdentityKeys
  | .sigHdr => SignalHeader
  | .rawBytes => List (BitVec 8)
  | .macTag => BitVec 64

/-- Signature for the Libsignal salt/wire reductions, assigning unit size to every `SaltWireSort`. -/
@[reducible] def saltWireSig (Pt : Type) (ℓ : ℕ) : Sig where
  Base := SaltWireSort
  den := SaltWireSort.den Pt ℓ
  sz := fun _ _ => 1

@[reducible] def slotAdTy (Pt : Type) (ℓ : ℕ) : Ty (saltWireSig Pt ℓ) :=
  .prod .nat (.base .ad)

@[reducible] def wireTagTy (Pt : Type) (ℓ : ℕ) : Ty (saltWireSig Pt ℓ) :=
  .prod (.base .rawBytes) (.base .macTag)

@[reducible] def lctTy (Pt : Type) (ℓ : ℕ) : Ty (saltWireSig Pt ℓ) :=
  .prod (wireTagTy Pt ℓ) (.base .salt)

/-- `lAeadK` with associated data re-associated as `ℕ × (Header Pt × LibsignalMsgPublicPart)` to
match `lAeadR`. -/
def libsignalAeadKeyIndexedAd {Pt : Type} (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) :
    AEADScheme DerivedMessageKeys (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32 where
  enc mk a m := (lAeadK C codec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m
  dec mk a c := (lAeadK C codec ℓ encT idOf).dec mk ((a.1, a.2.1), a.2.2) c

inductive WireOp
  | idsOf
  | hdrOf
  | eqHdr
  | fitPlainOp
  deriving DecidableEq

/-- Wire header, identity-key, and plaintext-padding operation table for `lWireRed` at unit cost. -/
@[reducible] def wireOps {Pt : Type} (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) :
    Ops (saltWireSig Pt ℓ) where
  Op := WireOp
  dom := fun
    | .idsOf => slotAdTy Pt ℓ
    | .hdrOf => slotAdTy Pt ℓ
    | .eqHdr => .prod (.base .sigHdr) (.base .sigHdr)
    | .fitPlainOp => .base .rawBytes
  cod := fun
    | .idsOf => .base .idKeys
    | .hdrOf => .base .sigHdr
    | .eqHdr => .bool
    | .fitPlainOp => .base .plain
  eval := fun
    | .idsOf, a => lIds idOf a.2.1.1
    | .hdrOf, a => lHeader encT a.1 a.2.1 a.2.2
    | .eqHdr, (h₁, h₂) => h₁ == h₂
    | .fitPlainOp, m => padOrTruncatePlain ℓ m
  cost := fun _ => 1

/-- Combined operation table summing `otccaOps` for `libsignalAeadKeyIndexedAd`, `otccaOps` for
`lAeadR`, and `wireOps`. -/
@[reducible] def saltWireOps {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (kAEAD : ℕ) :
    Ops (saltWireSig Pt ℓ) :=
  ReductionDsl.Ops.sum
    (otccaOps (S := saltWireSig Pt ℓ) (.base .msgKey) (slotAdTy Pt ℓ) (slotAdTy Pt ℓ)
      (.base .plain) (lctTy Pt ℓ) (libsignalAeadKeyIndexedAd C codec ℓ encT idOf) kAEAD
      (.base .salt) (fun a => a.2.2.salt))
    (ReductionDsl.Ops.sum
      (otccaOps (S := saltWireSig Pt ℓ) (.base .seed) (slotAdTy Pt ℓ) (slotAdTy Pt ℓ)
        (.base .plain) (lctTy Pt ℓ) (lAeadR C codec ℓ encT idOf) kAEAD
        (.base .salt) (fun a => a.2.2.salt))
      (wireOps ℓ encT idOf))

def slotKeySort : Bool → SaltWireSort
  | true => .seed
  | false => .msgKey

instance instSampleableSlotKey {Pt : Type} {ℓ : ℕ} :
    (b : Bool) → SampleableType ((saltWireSig Pt ℓ).den (slotKeySort b))
  | true => inferInstanceAs (SampleableType (BitVec 256))
  | false => inferInstanceAs (SampleableType DerivedMessageKeys)

/-- Target PRF interface for `lSaltRed` with `lIdeal` ciphertext sampling (`kIdeal`) and uniform bit
sampling. -/
@[reducible] def saltRedIface {Pt : Type} (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (kIdeal : ℕ) :
    Iface (saltWireSig Pt ℓ) (unifSpec + CryptoGames.MACScheme.prfSpec Salt32 DerivedMessageKeys) :=
  ((prfIface (S := saltWireSig Pt ℓ) (.base .salt) (.base .msgKey)).withSamp
    (idealSamplers (S := saltWireSig Pt ℓ) (slotAdTy Pt ℓ) (lctTy Pt ℓ)
      (lIdeal C codec ℓ encT) kIdeal)).withSamp
    (unifSamplers0 (saltWireSig Pt ℓ))

/-- Target `WireAEAD` interface for `lWireRed` with uniform bit sampling. -/
@[reducible] def wireRedIface (Pt : Type) (ℓ : ℕ) :
    Iface (saltWireSig Pt ℓ) (LibsignalWireOracleSpec ℓ) :=
  (wireIface (S := saltWireSig Pt ℓ) (.base .idKeys) (.base .sigHdr) (.base .plain)
    (.base .rawBytes) (.base .rawBytes) (.base .macTag) id id).withSamp
    (unifSamplers0 (saltWireSig Pt ℓ))

/-- Target single-slot OT-CCA interface for `slotSaltRed` and `slotWireRed` with `lIdeal` and
uniform key samplers. -/
@[reducible] def slotOtccaIface {Pt : Type} (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (kIdeal : ℕ) :
    Iface (saltWireSig Pt ℓ)
      (CryptoGames.FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) :=
  (otccaIface (S := saltWireSig Pt ℓ) (slotAdTy Pt ℓ) (.base .plain) (lctTy Pt ℓ)
    (lIdeal C codec ℓ encT) kIdeal).withSamp
    (unifSamplers (S := saltWireSig Pt ℓ) slotKeySort (fun _ => 1))

/-- Source multi-slot OT-CCA game codec in `saltWireSig` (`codecCost = 2`). -/
@[reducible] def slotOtccaCodec (Pt : Type) (ℓ : ℕ) :
    GameCodec (saltWireSig Pt ℓ)
      (CryptoGames.AEADScheme.otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32) :=
  otccaCodec (S := saltWireSig Pt ℓ) (slotAdTy Pt ℓ) (.base .plain) (lctTy Pt ℓ)

end Computational.Proofs.SpecLemmas.Reductions.Primitives.AEAD.CostedTables

-- AUTO-BRIDGE BEGIN
namespace CryptoGames.AEAD.Costed
export Computational.Proofs.SpecLemmas.Reductions.Primitives.AEAD.CostedTables (
  SaltWireSort WireOp WireTag instSampleableSlotKey lctTy libsignalAeadKeyIndexedAd
  saltRedIface saltWireOps saltWireSig slotAdTy slotKeySort slotOtccaCodec
  slotOtccaIface wireIface wireOps wireRedIface wireTagTy
)
end CryptoGames.AEAD.Costed
namespace CryptoGames.AEAD.Costed.SaltWireSort
export Computational.Proofs.SpecLemmas.Reductions.Primitives.AEAD.CostedTables.SaltWireSort (
  ad den idKeys macTag msgKey plain
  rawBytes salt seed sigHdr
)
end CryptoGames.AEAD.Costed.SaltWireSort
namespace CryptoGames.AEAD.Costed.WireOp
export Computational.Proofs.SpecLemmas.Reductions.Primitives.AEAD.CostedTables.WireOp (
  eqHdr fitPlainOp hdrOf idsOf
)
end CryptoGames.AEAD.Costed.WireOp
namespace CryptoGames.AEAD.Costed.WireTag
export Computational.Proofs.SpecLemmas.Reductions.Primitives.AEAD.CostedTables.WireTag (
  dec enc
)
end CryptoGames.AEAD.Costed.WireTag
-- AUTO-BRIDGE END
