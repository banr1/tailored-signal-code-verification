/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.LeakRecordsCompat
public import LibsignalBinary.Specifications.SignalSession.PqDir
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import Symbolic.Proofs.Refinement.RecordBytesBridge

/-!
# Wire and Bundle Codec Bridges

Characterizes `sentBody` on whisper wire messages and equates `BundleTyped` with the image of
`publicBundleOf` on `PreKeyBundleFields`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Cli

open DY DY.Comparse
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.PQXDH.Refinement (PreKeyProto wirePrekeyTag)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SignalSession
open Swarm.Phase0WholeFunctionBridge (paddedVarint_zero_of_lt_128 paddedVarint_zero_of_ge_128
  paddedVarint_zero_eq_encodeVarint)

@[simp]
theorem sentBody_wireWhisper (body : HwBytes) :
    sentBody (wireWhisper :: body) = some body := by
  have h : wireWhisper = wireWhisperTag := by decide
  simp [sentBody, h]

private theorem list_eq_tag_tail {tag : BitVec 8} {n : Nat} {bs : HwBytes}
    (hlen : bs.length = n + 1) (hhd : bs.head? = some tag) :
    ∃ v : List.Vector (BitVec 8) n, bs = tag :: v.toList := by
  cases bs with
  | nil => simp at hhd
  | cons b tl =>
    simp only [List.head?_cons, Option.some.injEq] at hhd; subst hhd
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    exact ⟨⟨tl, hlen⟩, rfl⟩

theorem bundleTyped_iff_exists_bundleE (pb : PublicBundle) :
    BundleTyped pb ↔ ∃ b : PreKeyBundleFields, pb = publicBundleOf b := by
  constructor
  · rintro ⟨hikL, hikH, hskL, hskH, hssL, hkkL, hkkH, hksL, hopk⟩
    obtain ⟨idPub, hidPub⟩ := list_eq_tag_tail hikL hikH
    obtain ⟨spkPub, hspkPub⟩ := list_eq_tag_tail hskL hskH
    obtain ⟨kpkPub, hkpkPub⟩ := list_eq_tag_tail hkkL hkkH
    have hopkE : ∃ opk : Option (BitVec 32 × List.Vector (BitVec 8) 32),
        pb.oneTime = opk.map fun (i, k) => (i, djbKey k) := by
      cases ho : pb.oneTime with
      | none => exact ⟨none, rfl⟩
      | some ik =>
        rcases ik with ⟨i, key⟩
        obtain ⟨hl, hh⟩ := hopk i key ho
        obtain ⟨kv, hkv⟩ := list_eq_tag_tail hl hh
        exact ⟨some (i, kv), by simp [djbKey, hkv]⟩
    rcases hopkE with ⟨opk, hopk_eq⟩
    refine ⟨{ regId := pb.registrationId, opk, spkId := pb.signedId, spkPub,
              spkSig := ⟨pb.signedSig, hssL⟩, kpkId := pb.kyberId, kpkPub,
              kpkSig := ⟨pb.kyberSig, hksL⟩, idPub }, ?_⟩
    cases pb
    simp only [publicBundleOf, djbKey, CryptoVerification.E2E.kyberKey]
      at hidPub hspkPub hkpkPub hopk_eq ⊢
    congr
  · rintro ⟨b, rfl⟩
    unfold BundleTyped publicBundleOf djbKey CryptoVerification.E2E.kyberKey
    refine ⟨by simp, rfl, by simp, rfl, b.spkSig.2, by simp, rfl, b.kpkSig.2, ?_⟩
    intro id key hmem
    cases hb : b.opk with
    | none => simp [hb] at hmem
    | some ik =>
      rcases ik with ⟨i, k⟩
      simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩
      exact ⟨by simp, rfl⟩

end Symbolic.Swarm.CREF.Cli
