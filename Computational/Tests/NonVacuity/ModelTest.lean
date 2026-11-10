/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.LibsignalWireRoundTrip

/-!
# Non-Vacuity Counterexample for `Corr.SpqrRecvSaltFixed`

Constructs a 1-bit SPQR instance `toyAlternatingSpqr` whose receive salt alternates between `none`
and `some zeroSaltVec` on repeated receives of `[]`, and refutes `Corr.SpqrRecvSaltFixed`.
-/

@[expose] public section

namespace CryptoGames.Spqr.Tests

open CryptoGames.LibsignalSession CryptoGames.LibsignalSM

def zeroSaltVec : List.Vector (BitVec 8) 32 := List.Vector.replicate 32 0

/-- Single-bit `Spqr` instance that flips its state on each `recv` and returns `none` from `false`
and `some zeroSaltVec` from `true`. -/
def toyAlternatingSpqr : Spqr Bool Unit where
  init _ _ := false
  send st _ := some (st, none, [])
  recv st _ := .ok (!st, if st then some zeroSaltVec else none)
  sendPanics _ _ := false
  recvPanics _ _ := false

theorem not_spqrRecvSaltFixed_toyAlternatingSpqr :
    ¬ Corr.SpqrRecvSaltFixed toyAlternatingSpqr := by
  rintro ⟨linkPresent, evalSalt, hpres, hfixed⟩
  have hreach0 : Corr.SpqrReachIn toyAlternatingSpqr 0 false :=
    Corr.SpqrReachIn.init 0 .a2b 0
  have hrecv0 : toyAlternatingSpqr.recv false [] = .ok (true, none) := rfl
  have hrecv1 : toyAlternatingSpqr.recv true [] = .ok (false, some zeroSaltVec) := rfl
  have hlp : linkPresent false [] := hpres 0 false true [] none hreach0 hrecv0
  have heq0 : (none : HKDF.Salt) = evalSalt false [] :=
    hfixed false false true [] none (.refl false) hlp hrecv0
  have heq1 : (some zeroSaltVec : HKDF.Salt) = evalSalt false [] :=
    hfixed false true false [] (some zeroSaltVec) (.recv (.refl false) hrecv0) hlp hrecv1
  exact nomatch heq0.trans heq1.symm

end CryptoGames.Spqr.Tests
