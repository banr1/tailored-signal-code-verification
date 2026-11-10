/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Loop
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbLeaf
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.BV.WidthNorm
import VCVio.Prelude.Core
public meta import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto -- shake: keep
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Prost Round-Trip for `ChainEpochPB`, `ChainPB`, and `VersionNegotiationPB`

`LoopsTo` and `decode ∘ encodeRaw` round-trip theorems for `ChainEpochPB` (depth 1),
`ChainPB` (depth 2), and `VersionNegotiationPB` (depth 1) when the encoded length fits in 64 bits.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.Codec

open CryptoVerification.LibsignalSpqrV1 hiding WireType DecodeErr decodeVarint encodeVarint
open CryptoVerification.LibsignalSpqrV1.Proto (WireType DecodeErr)
open CryptoVerification.SpqrV1.Prost.MessageMerge (protoPrefixStep_chainEpochPB_mergeField
  protoPrefixStep_chainPB_mergeField protoPrefixStep_versionNegotiationPB_mergeField)

/-- Discharges the sub-message premise of `loopsTo_optMessage` from an outer length bound. -/
theorem optMessage_sub {N : Type} [Inhabited N] (mfN : MergeFieldFn N) (dN : Nat)
    (encodeRaw : N → Bytes) (tag : BitVec 32) (o : Option N) (L : Nat)
    (hL : (Proto.encodeOptMessage encodeRaw tag o).length ≤ L) (hL64 : L < 2 ^ 64)
    (hT : ∀ n, (encodeRaw n).length < 2 ^ 64 → LoopsTo mfN dN default (encodeRaw n) n) :
    ∀ n, o = some n → LoopsTo mfN dN default (encodeRaw n) n ∧ (encodeRaw n).length < 2 ^ 64 := by
  rintro n rfl
  have := length_le_encodeOptMessage encodeRaw tag n
  exact ⟨hT n (by omega), by omega⟩

/-! ## `ChainEpochPB` -/

theorem loopsTo_chainEpoch (c : ChainEpochPB) (h : (ChainEpochPB.encodeRaw c).length < 2 ^ 64) :
    LoopsTo ChainEpochPB.mergeField 1 default (ChainEpochPB.encodeRaw c) c := by
  simp only [ChainEpochPB.encodeRaw, List.length_append] at h
  have hA := loopsTo_optMessage ChainEpochPB.mergeField 1 (default : ChainEpochPB) 1#32
    EpochDirectionPB.mergeField 0 EpochDirectionPB.encodeRaw c.send
    (fun x => { (default : ChainEpochPB) with send := x }) (by decide) (by decide) (by decide) rfl
    (optMessage_sub _ _ _ 1#32 _ _ (Nat.le_refl _) (by omega) loopsTo_epochDirection)
    (fun _ _ _ => by simp [ChainEpochPB.mergeField]; rfl)
  have hB := loopsTo_optMessage ChainEpochPB.mergeField 1
    { (default : ChainEpochPB) with send := c.send } 2#32
    EpochDirectionPB.mergeField 0 EpochDirectionPB.encodeRaw c.recv
    (fun x => { (default : ChainEpochPB) with send := c.send, recv := x })
    (by decide) (by decide) (by decide) rfl
    (optMessage_sub _ _ _ 2#32 _ _ (Nat.le_refl _) (by omega) loopsTo_epochDirection)
    (fun _ _ _ => by simp [ChainEpochPB.mergeField]; rfl)
  exact (LoopsTo.append protoPrefixStep_chainEpochPB_mergeField hA hB).congr_res (by cases c; rfl)

theorem decode_chainEpoch (c : ChainEpochPB) (h : (ChainEpochPB.encodeRaw c).length < 2 ^ 64) :
    ChainEpochPB.decode (ChainEpochPB.encodeRaw c) = .ok c :=
  decodeTop_of_loopsTo _ 1 _ _ (by decide) (loopsTo_chainEpoch c h)

/-! ## `ChainPB` -/

theorem loopsTo_chain (c : ChainPB) (h : (ChainPB.encodeRaw c).length < 2 ^ 64) :
    LoopsTo ChainPB.mergeField 2 default (ChainPB.encodeRaw c) c := by
  simp only [ChainPB.encodeRaw, List.length_append] at h
  have hn := length_le_encodeBytesField 4#32 c.nextRoot
  have hA := loopsTo_int32 ChainPB.mergeField 2 (default : ChainPB) 1#32 c.direction
    (fun x => { (default : ChainPB) with direction := x }) (by decide) (by decide) rfl
    (fun _ _ _ => rfl)
  have hB := loopsTo_uint64 ChainPB.mergeField 2 { (default : ChainPB) with direction := c.direction } 2#32
    c.currentEpoch (fun x => { (default : ChainPB) with direction := c.direction, currentEpoch := x })
    (by decide) (by decide) rfl
    (fun _ _ _ => rfl)
  have hC := loopsTo_repeatedMessage ChainPB.mergeField protoPrefixStep_chainPB_mergeField 2
    { (default : ChainPB) with direction := c.direction, currentEpoch := c.currentEpoch } 3#32
    ChainEpochPB.mergeField 1 ChainEpochPB.encodeRaw c.links (·.links) (fun m l => { m with links := l })
    (by decide) (by decide) (by decide)
    (fun n hn => by
      have := length_le_encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 c.links n hn
      exact ⟨loopsTo_chainEpoch n (by omega), by omega⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    (fun _ _ _ _ => rfl)
  have hD := loopsTo_bytes ChainPB.mergeField 2
    { (default : ChainPB) with direction := c.direction, currentEpoch := c.currentEpoch, links := c.links } 4#32
    c.nextRoot
    (fun x => { (default : ChainPB) with
      direction := c.direction, currentEpoch := c.currentEpoch, links := c.links, nextRoot := x })
    (by decide) (by decide) rfl (by omega)
    (fun _ _ _ => rfl)
  have hE := loopsTo_uint64 ChainPB.mergeField 2
    { (default : ChainPB) with
      direction := c.direction, currentEpoch := c.currentEpoch, links := c.links, nextRoot := c.nextRoot }
    5#32 c.sendEpoch
    (fun x => { (default : ChainPB) with
      direction := c.direction, currentEpoch := c.currentEpoch, links := c.links, nextRoot := c.nextRoot,
      sendEpoch := x })
    (by decide) (by decide) rfl
    (fun _ _ _ => rfl)
  have hF := loopsTo_optMessage ChainPB.mergeField 2
    { (default : ChainPB) with
      direction := c.direction, currentEpoch := c.currentEpoch, links := c.links, nextRoot := c.nextRoot,
      sendEpoch := c.sendEpoch }
    6#32 ChainParamsPB.mergeField 0 ChainParamsPB.encodeRaw c.params
    (fun x => { (default : ChainPB) with
      direction := c.direction, currentEpoch := c.currentEpoch, links := c.links, nextRoot := c.nextRoot,
      sendEpoch := c.sendEpoch, params := x })
    (by decide) (by decide) (by decide) rfl
    (optMessage_sub _ _ _ 6#32 _ _ (Nat.le_refl _) (by omega) (fun n _ => loopsTo_chainParams n))
    (fun _ _ _ => rfl)
  exact (((((LoopsTo.append protoPrefixStep_chainPB_mergeField hA hB).append
    protoPrefixStep_chainPB_mergeField hC).append protoPrefixStep_chainPB_mergeField hD).append
    protoPrefixStep_chainPB_mergeField hE).append protoPrefixStep_chainPB_mergeField hF).congr_res
    (by cases c; rfl)

theorem decode_chain (c : ChainPB) (h : (ChainPB.encodeRaw c).length < 2 ^ 64) :
    ChainPB.decode (ChainPB.encodeRaw c) = .ok c :=
  decodeTop_of_loopsTo _ 2 _ _ (by decide) (loopsTo_chain c h)

/-! ## `VersionNegotiationPB` -/

theorem loopsTo_versionNegotiation (v : VersionNegotiationPB)
    (h : (VersionNegotiationPB.encodeRaw v).length < 2 ^ 64) :
    LoopsTo VersionNegotiationPB.mergeField 1 default (VersionNegotiationPB.encodeRaw v) v := by
  simp only [VersionNegotiationPB.encodeRaw, List.length_append] at h
  have ha := length_le_encodeBytesField 1#32 v.authKey
  have hA := loopsTo_bytes VersionNegotiationPB.mergeField 1 (default : VersionNegotiationPB) 1#32 v.authKey
    (fun x => { (default : VersionNegotiationPB) with authKey := x }) (by decide) (by decide) rfl (by omega)
    (fun _ _ _ => rfl)
  have hB := loopsTo_int32 VersionNegotiationPB.mergeField 1 { (default : VersionNegotiationPB) with authKey := v.authKey } 2#32 v.direction
    (fun x => { (default : VersionNegotiationPB) with authKey := v.authKey, direction := x }) (by decide) (by decide) rfl
    (fun _ _ _ => rfl)
  have hC := loopsTo_int32 VersionNegotiationPB.mergeField 1
    { (default : VersionNegotiationPB) with authKey := v.authKey, direction := v.direction } 3#32 v.minVersion
    (fun x => { (default : VersionNegotiationPB) with authKey := v.authKey, direction := v.direction, minVersion := x })
    (by decide) (by decide) rfl
    (fun _ _ _ => rfl)
  have hD := loopsTo_optMessage VersionNegotiationPB.mergeField 1
    { (default : VersionNegotiationPB) with authKey := v.authKey, direction := v.direction, minVersion := v.minVersion } 4#32
    ChainParamsPB.mergeField 0 ChainParamsPB.encodeRaw v.chainParams
    (fun x => { (default : VersionNegotiationPB) with
      authKey := v.authKey, direction := v.direction, minVersion := v.minVersion, chainParams := x })
    (by decide) (by decide) (by decide) rfl
    (optMessage_sub _ _ _ 4#32 _ _ (Nat.le_refl _) (by omega) (fun n _ => loopsTo_chainParams n))
    (fun _ _ _ => rfl)
  exact (((LoopsTo.append protoPrefixStep_versionNegotiationPB_mergeField hA hB).append
    protoPrefixStep_versionNegotiationPB_mergeField hC).append
    protoPrefixStep_versionNegotiationPB_mergeField hD).congr_res (by cases v; rfl)

theorem decode_versionNegotiation (v : VersionNegotiationPB)
    (h : (VersionNegotiationPB.encodeRaw v).length < 2 ^ 64) :
    VersionNegotiationPB.decode (VersionNegotiationPB.encodeRaw v) = .ok v :=
  decodeTop_of_loopsTo _ 1 _ _ (by decide) (loopsTo_versionNegotiation v h)

/-! ## Sanity checks -/

#guard ChainEpochPB.decode (ChainEpochPB.encodeRaw
    { send := some { ctr := 3#32, next := List.replicate 32 7#8 },
      recv := some { ctr := 0#32, prev := [1#8] } }) =
  .ok { send := some { ctr := 3#32, next := List.replicate 32 7#8 },
        recv := some { ctr := 0#32, prev := [1#8] } }
-- An empty sub-message `some {}` is written (key and length 0), so it survives.
#guard ChainEpochPB.decode (ChainEpochPB.encodeRaw { send := some {}, recv := none }) =
  .ok { send := some {}, recv := none }
#guard ChainPB.decode (ChainPB.encodeRaw
    { direction := 1#32, currentEpoch := 5#64,
      links := [{ send := some { ctr := 1#32 } }, {}, { recv := some { next := [9#8] } }],
      nextRoot := List.replicate 32 4#8, sendEpoch := 4#64,
      params := some { maxJump := 25000#32, maxOooKeys := 2000#32 } }) =
  .ok { direction := 1#32, currentEpoch := 5#64,
        links := [{ send := some { ctr := 1#32 } }, {}, { recv := some { next := [9#8] } }],
        nextRoot := List.replicate 32 4#8, sendEpoch := 4#64,
        params := some { maxJump := 25000#32, maxOooKeys := 2000#32 } }
-- Negative `int32` (10-byte varint).
#guard ChainPB.decode (ChainPB.encodeRaw { direction := (-1 : BitVec 32) }) =
  .ok { direction := (-1 : BitVec 32) }
#guard VersionNegotiationPB.decode (VersionNegotiationPB.encodeRaw
    { authKey := [1#8, 2#8], direction := 1#32, minVersion := 1#32, chainParams := some {} }) =
  .ok { authKey := [1#8, 2#8], direction := 1#32, minVersion := 1#32, chainParams := some {} }

end CryptoVerification.SpqrV1Sync.Codec
