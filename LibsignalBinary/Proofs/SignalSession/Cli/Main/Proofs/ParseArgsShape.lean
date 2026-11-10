/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Model
import all Init.Data.String.Defs

/-!
# Proof of `parseArgs_none_of_shape`

Proves that any ASCII `argv` with `ArgvShapeOk argv = false` maps to `none` under `parseArgs`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.LibsignalPublicApi.StoreKit

namespace ParseArgsShape

private theorem char_eq_of_ascii_byte {c₁ c₂ : Char}
    (h₁ : c₁.toNat < 128) (h₂ : c₂.toNat < 128)
    (hb : BitVec.ofNat 8 c₁.toNat = BitVec.ofNat 8 c₂.toNat) :
    c₁ = c₂ := by
  have hn : c₁.toNat = c₂.toNat := by
    have hmod := congrArg BitVec.toNat hb
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hmod
    omega
  rw [← Char.ofNat_toNat c₁, ← Char.ofNat_toNat c₂, hn]

private theorem chars_eq_of_bytes {l₁ l₂ : List Char}
    (h₁ : ∀ c ∈ l₁, c.toNat < 128) (h₂ : ∀ c ∈ l₂, c.toNat < 128)
    (hm : (l₁.map fun c => BitVec.ofNat 8 c.toNat) =
          (l₂.map fun c => BitVec.ofNat 8 c.toNat)) :
    l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons _ _ => cases hm
  | cons x₁ xs₁ ih =>
    cases l₂ with
    | nil => cases hm
    | cons x₂ xs₂ =>
      obtain ⟨hm₁, hm₂⟩ := List.cons.inj hm
      have hx : x₁ = x₂ :=
        char_eq_of_ascii_byte (h₁ x₁ (.head _)) (h₂ x₂ (.head _)) hm₁
      have hxs : xs₁ = xs₂ :=
        ih (fun c hc => h₁ c (.tail _ hc)) (fun c hc => h₂ c (.tail _ hc)) hm₂
      rw [hx, hxs]

private theorem eq_of_bytesOfString_eq_utf8 {s lit : String}
    (hs : PrintableAsciiArg s)
    (hlit_ascii : ∀ c ∈ lit.toList, c.toNat < 128)
    (hlit_utf8 : utf8 lit = bytesOfString lit)
    (heq : bytesOfString s = utf8 lit) :
    s = lit :=
  String.toList_injective <|
    chars_eq_of_bytes (fun c hc => (hs.2 c hc).2) hlit_ascii (heq.trans hlit_utf8)

end ParseArgsShape

open ParseArgsShape in
/-- Proof of `parseArgs_none_of_shape`: any ASCII `argv` with `ArgvShapeOk argv = false` parses to
`none`. -/
theorem parseArgs_none_of_shape_proof (uuidParse : UuidParser) {argv : List String}
    (hascii : ∀ a ∈ argv, PrintableAsciiArg a) (hshape : ArgvShapeOk argv = false) :
    parseArgs uuidParse (argv.map bytesOfString) = none := by
  rcases argv with _ | ⟨c, _ | ⟨a, _ | ⟨x, _ | ⟨_, _⟩⟩⟩⟩
  · rfl
  · rfl
  · have hc : PrintableAsciiArg c := hascii c (.head _)
    have hne_send : bytesOfString c ≠ utf8 "send" := by
      intro h
      have hceq : c = "send" :=
        eq_of_bytesOfString_eq_utf8 hc (by decide +kernel) (by decide +kernel) h
      rw [hceq] at hshape
      exact Bool.noConfusion hshape
    have hne_recv : bytesOfString c ≠ utf8 "recv" := by
      intro h
      have hceq : c = "recv" :=
        eq_of_bytesOfString_eq_utf8 hc (by decide +kernel) (by decide +kernel) h
      rw [hceq] at hshape
      exact Bool.noConfusion hshape
    change (if bytesOfString c = utf8 "send" then _
      else if bytesOfString c = utf8 "recv" then _ else none) = none
    split
    · exact absurd ‹_› hne_send
    · rfl
  · have hc : PrintableAsciiArg c := hascii c (.head _)
    have hne_keygen : bytesOfString c ≠ utf8 "keygen" := by
      intro h
      have hceq : c = "keygen" :=
        eq_of_bytesOfString_eq_utf8 hc (by decide +kernel) (by decide +kernel) h
      rw [hceq] at hshape
      exact Bool.noConfusion hshape
    have hne_init : bytesOfString c ≠ utf8 "init" := by
      intro h
      have hceq : c = "init" :=
        eq_of_bytesOfString_eq_utf8 hc (by decide +kernel) (by decide +kernel) h
      rw [hceq] at hshape
      exact Bool.noConfusion hshape
    change (if bytesOfString c = utf8 "keygen" then _
      else if bytesOfString c = utf8 "init" then _ else none) = none
    split
    · exact absurd ‹_› hne_keygen
    · rfl
  · rfl

private example := [PLift.up @parseArgs_none_of_shape, PLift.up @parseArgs_none_of_shape_proof]
private example : @parseArgs_none_of_shape = @parseArgs_none_of_shape_proof := rfl

end CryptoVerification.SignalSession.Cli.MainHops
