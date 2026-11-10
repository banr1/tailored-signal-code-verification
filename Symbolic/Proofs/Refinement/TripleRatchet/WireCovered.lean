/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Concretization
import DY.Bytes.Basic
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
public import Symbolic.Proofs.Refinement.EncodeWithSound
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Refinement.EncodeWithCovered
import VCVio.EvalDist.ProbabilityNotation

/-!
# Wire coverage for `SignalMessage` encodings

Proves that every byte sequence accepted by `SignalMessage.tryFrom` decomposes uniformly across
all `addresses` and `pq_ratchet` payloads as `trWireBytes addr v f pq ++ mac` for a
non-canonical sentinel variation `v` (`trWireBytes_covered_uniform`), characterizes the
canonical layout (`trWireBytes_canonical`), and unfolds `gamma` on literals and `trWireMsg`.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement

open CryptoGames.LibsignalSession CryptoVerification.LibsignalProtoCodec
open DY.Libsignal.Refinement DY.TrWire

/-- Prepends a zero-tag sentinel item to `v.fields`. -/
def withSentinel (v : EncodingVariation) : EncodingVariation :=
  { v with fields := .known 0 0 0 :: v.fields }

theorem withSentinel_ne_canonical (v : EncodingVariation) :
    withSentinel v ≠ canonicalVariation := by
  intro h
  have := congrArg EncodingVariation.fields h
  simp [withSentinel, canonicalVariation] at this

theorem encode_withFields (v : EncodingVariation) (fs : List FieldItem)
    (f : WireFields) (it : FieldItem) :
    it.encode { v with fields := fs } f = it.encode v f := by
  cases it with
  | known t kp vp =>
    simp only [FieldItem.encode]
    rcases t with _ | _ | _ | _ | _ | t <;> rfl
  | extra => rfl

theorem knownValue?_tag {v : EncodingVariation} {f : WireFields} {t : Nat} {x : PbValue}
    (h : knownValue? v f t = some x) : t ≠ 5 ∧ t ≠ 6 := by
  constructor <;> (rintro rfl; simp [knownValue?] at h)

theorem trItemEncode_of_itemWF (addr pq : HwBytes) (v : EncodingVariation) (fs : List FieldItem)
    (f : WireFields) (it : FieldItem) (h : ItemWF v f it) :
    trItemEncode addr { v with fields := fs } f pq it = it.encode v f := by
  cases it with
  | known t kp vp =>
    obtain ⟨x, hx, -⟩ := h
    obtain ⟨h5, h6⟩ := knownValue?_tag hx
    simp only [trItemEncode, h5, h6, ↓reduceIte]
    exact encode_withFields v fs f _
  | extra t x kp vp =>
    simp only [trItemEncode]
    exact encode_withFields v fs f _

theorem flatMap_trItemEncode (addr pq : HwBytes) (v : EncodingVariation) (fs : List FieldItem)
    (f : WireFields) :
    ∀ l : List FieldItem, (∀ it ∈ l, ItemWF v f it) →
      l.flatMap (trItemEncode addr { v with fields := fs } f pq) =
        l.flatMap (FieldItem.encode v f)
  | [] => fun _ => rfl
  | it :: l => fun h => by
    simp only [List.flatMap_cons]
    rw [trItemEncode_of_itemWF addr pq v fs f it (h it List.mem_cons_self),
      flatMap_trItemEncode addr pq v fs f l (fun it hit => h it (List.mem_cons_of_mem _ hit))]

/-- Under `HonestWF`, `trWireBytes` for `withSentinel v` reduces to `encodeWith v f` for all
`addr` and `pq`. -/
theorem trWireBytes_withSentinel (addr pq : HwBytes) (v : EncodingVariation) (f : WireFields)
    (h : HonestWF v f) : trWireBytes addr (withSentinel v) f pq = encodeWith v f := by
  simp only [trWireBytes, trFields, withSentinel_ne_canonical v, ↓reduceIte, encodeWith]
  congr 1
  simp only [withSentinel, List.flatMap_cons]
  rw [flatMap_trItemEncode addr pq v _ f v.fields h.items]
  rfl

/-- Uniform wire coverage: a single non-canonical variation `v`, field record `f`, and 8-byte
`mac` represent `b` as `trWireBytes addr v f pq ++ mac` for all `addr` and `pq`. -/
theorem trWireBytes_covered_uniform (b : HwBytes) (m : SignalMessage)
    (h : SignalMessage.tryFrom protoSignalCodec b = .ok m) :
    ∃ v f mac, v ≠ canonicalVariation ∧ (∀ addr pq, b = trWireBytes addr v f pq ++ mac) ∧
      mac.length = macLength ∧
      3 ≤ f.version ∧ f.version ≤ 4 ∧ f.ratchetKey.length = 32 ∧ f.counter < 2 ^ 32 ∧
      f.previousCounter < 2 ^ 32 ∧
      m.messageVersion.toNat = f.version ∧ m.senderRatchetKey.bytes.toList = f.ratchetKey ∧
      m.counter.toNat = f.counter ∧ m.previousCounter.toNat = f.previousCounter ∧
      m.ciphertext = f.ciphertext := by
  obtain ⟨v, f, mac, hb, hmac, hwf, h1, h2, h3, h4, h5⟩ := tryFrom_covered b m h
  refine ⟨withSentinel v, f, mac, withSentinel_ne_canonical v, fun addr pq => ?_, hmac,
    hwf.version.1, hwf.version.2, hwf.ratchetKey, hwf.counter, hwf.previousCounter, h1, h2, h3,
    h4, h5⟩
  rw [trWireBytes_withSentinel addr pq v f hwf, hb]

/-- For `canonicalVariation`, `trWireBytes` appends non-empty `pq_ratchet` and `addresses`
fields after `encodeWith canonicalVariation f`. -/
theorem trWireBytes_canonical (addr pq : HwBytes) (f : WireFields) :
    trWireBytes addr canonicalVariation f pq =
      encodeWith canonicalVariation f ++
        (if pq = [] then [] else encodeField 5 0 0 (.bytes pq)) ++
        (if addr = [] then [] else encodeField 6 0 0 (.bytes addr)) := by
  by_cases hpq : pq = [] <;> by_cases ha : addr = [] <;>
    simp [trWireBytes, trFields, honestTrItems, encodeWith, trItemEncode, hpq, ha,
      canonicalVariation, FieldItem.encode, knownValue?]

section Fold

variable (interpretation : CryptoProofLib.Refinement.ExternInterpretation) (S : OpaqueSymbolSemantics)
  (g : Ghost)

unseal DY.Bytes in
instance instSubFunctionGLit0 : DY.Bytes.SubFunction concretizeLit (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, litFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem gamma_litOf (bs : HwBytes) : gamma interpretation S g (litOf bs) = bs := by
  unfold gamma gamma' litOf
  rw [DY.Bytes.rec_eq concretizeLit (concretizeAll interpretation S g)]
  show ofByteArray _ = _
  simp [ofByteArray, Function.comp_def]

unseal DY.Bytes in
instance instSubFunctionGTrWire0 : DY.Bytes.SubFunction (concretizeTrWire g) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, trWireFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

/-- Unfolds `gamma` on `trWireMsg` using the ghost `addresses` bytes `g.addr`. -/
theorem gamma_trWireMsg (v : UInt8) (rk : DY.Bytes) (c pc : UInt32) (ct pq : DY.Bytes)
    (ev : EncodingVariation) :
    gamma interpretation S g (DY.TrWire.trWireMsg v rk c pc ct pq ev) =
      trWireBytes (g.addr (DY.TrWire.trWireMsg v rk c pc ct pq ev)) ev
        { version := v.toNat, ratchetKey := gamma interpretation S g rk,
          counter := c.toNat, previousCounter := pc.toNat,
          ciphertext := gamma interpretation S g ct }
        (gamma interpretation S g pq) := by
  unfold gamma gamma'
  show ((({ version := v, senderRatchetKey := rk, counter := c, previousCounter := pc,
             ciphertext := ct, pqRatchet := pq, encodingVariation := ev } :
      DY.TrWire.TrWireMsg.SubF DY.Bytes).pack).rec (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeTrWire g) (concretizeAll interpretation S g)]; rfl

end Fold

end DY.Libsignal.Composed.Refinement

namespace DY.Libsignal.TripleRatchet.Refinement
export DY.Libsignal.Composed.Refinement (
  withSentinel withSentinel_ne_canonical encode_withFields knownValue?_tag
  trItemEncode_of_itemWF flatMap_trItemEncode trWireBytes_withSentinel
  trWireBytes_covered_uniform
  trWireBytes_canonical gamma_litOf   gamma_trWireMsg
)
end DY.Libsignal.TripleRatchet.Refinement
