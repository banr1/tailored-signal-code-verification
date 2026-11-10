/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Concrete.ExternInterpretation
public import Symbolic.Proofs.SpecLemmas.ImageSymbolsProofDefs

/-!
# Extern-interpretation totality predicates

Defines `ReturnsLength` and `ExternInterpretationTotalOnUsedSymbols`, specifying totality and
output byte lengths of the Kyber-1024, SHA-512, Ed25519, ML-KEM-768, and HMAC extern symbols on
well-sized inputs.
-/

@[expose] public section

namespace DY.Libsignal.Composed.Refinement

open CryptoProofLib.Refinement (ByteString ExternInterpretation)
open DY.Libsignal.Refinement (StubSymbol)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol kyberDecapsSymbol sha512CompressSymbol
  toEdwardsSymbol edwardsCompressSymbol edwardsNegSymbol torsionFreeSymbol doubleScalarMulSymbol
  scalarModOrderSymbol scalarModOrderWideSymbol mlkem768FromSeedSymbol mlkem768Encaps1Symbol
  mlkem768Encaps2Symbol mlkem768DecapsSymbol mlkem768ValidatePkSymbol libcruxHmacSymbol)

def ReturnsLength (interpretation : ExternInterpretation) (sym : StubSymbol)
    (args : List ByteString) (n : Nat) : Prop :=
  ∃ out, interpretation sym args = some out ∧ out.length = n

/-- Totality and output-length requirements on the Kyber-1024, SHA-512, Ed25519, ML-KEM-768,
and HMAC externs. -/
def ExternInterpretationTotalOnUsedSymbols (interpretation : ExternInterpretation) : Prop :=
  -- Kyber-1024
  (∀ pk rand : ByteString, pk.length = 1568 → rand.length = 32 →
    ReturnsLength interpretation kyberEncapsSymbol [pk, rand] 1600) ∧
  (∀ sk ct : ByteString, sk.length = 3168 → ct.length = 1568 →
    ReturnsLength interpretation kyberDecapsSymbol [sk, ct] 32) ∧
  -- SHA-512 one-block compression
  (∀ st b : ByteString, st.length = 64 → b.length = 128 →
    ReturnsLength interpretation sha512CompressSymbol [st, b] 64) ∧
  -- Ed25519 curve core
  (∀ (u : ByteString) (sign : BitVec 8), u.length = 32 →
    ReturnsLength interpretation toEdwardsSymbol [u, [sign]] 160) ∧
  (∀ pt : ByteString, pt.length = 160 →
    ReturnsLength interpretation edwardsCompressSymbol [pt] 32) ∧
  (∀ pt : ByteString, pt.length = 160 →
    ReturnsLength interpretation edwardsNegSymbol [pt] 160) ∧
  (∀ pt : ByteString, pt.length = 160 → (interpretation torsionFreeSymbol [pt]).isSome) ∧
  (∀ a pt b : ByteString, a.length = 32 → pt.length = 160 → b.length = 32 →
    ReturnsLength interpretation doubleScalarMulSymbol [a, pt, b] 160) ∧
  (∀ b : ByteString, b.length = 32 →
    ReturnsLength interpretation scalarModOrderSymbol [b] 32) ∧
  (∀ b : ByteString, b.length = 64 →
    ReturnsLength interpretation scalarModOrderWideSymbol [b] 32) ∧
  -- ML-KEM-768 incremental
  (∀ seed : ByteString, seed.length = 64 →
    ReturnsLength interpretation mlkem768FromSeedSymbol [seed] 2400) ∧
  (∀ pk1 rand : ByteString, rand.length = 32 →
    ReturnsLength interpretation mlkem768Encaps1Symbol [pk1, rand] (960 + 2080 + 32)) ∧
  (∀ st pk2 : ByteString, st.length = 2080 → pk2.length = 1152 →
    ReturnsLength interpretation mlkem768Encaps2Symbol [st, pk2] 128) ∧
  (∀ sk ct1 ct2 : ByteString, sk.length = 2400 → ct1.length = 960 → ct2.length = 128 →
    ReturnsLength interpretation mlkem768DecapsSymbol [sk, ct1, ct2] 32) ∧
  (∀ pk1 pk2 : ByteString, (interpretation mlkem768ValidatePkSymbol [pk1, pk2]).isSome) ∧
  -- HMAC-SHA-256
  (∀ key data : ByteString, key.length < 2 ^ 32 → data.length < 2 ^ 32 →
    ReturnsLength interpretation libcruxHmacSymbol [key, data] 32)

end DY.Libsignal.Composed.Refinement
