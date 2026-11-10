/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seams

/-!
# Memory Frames and Region-Splitting Lemmas for `segSignal_ok`

Defines invariant frame components (`sgFix`, `sgFrameU`, `sgFrameE`, `sgFrameP`, `sgFrameT`,
`sgFrameK`), poll-buffer region cuts, and `takenRecord` unpack/pack helpers for `segSignal`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

/-! ## Region Cutting Helpers -/

theorem segSignal_memRegion_cut (b b' : BitVec 64) (N n k : Nat) (hb : b' = b + BitVec.ofNat 64 n)
    (hN : N = n + k) (h : N ≤ 2 ^ 64) :
    memRegion b N = memRegion b n ∗ memRegion b' k :=
  memRegion_split' hN hb h

theorem segSignal_mono_front {m : Memory} {P Q W W' Rest : SepProp} (hm : m ⊨ P) (heq : P = W ∗ Rest)
    (hW : W ⊢ W') (hQ : W' ∗ Rest = Q) : m ⊨ Q := by
  rw [heq] at hm
  rw [← hQ]
  exact Satisfies.mono (sepConj_mono_left hW) hm

theorem segSignal_list_len6 {α : Type} (ws : List α) (h : ws.length = 6) :
    ∃ w0 w1 w2 w3 w4 w5, ws = [w0, w1, w2, w3, w4, w5] := by
  rcases ws with _ | ⟨w0, ws⟩; · nomatch h
  rcases ws with _ | ⟨w1, ws⟩; · nomatch h
  rcases ws with _ | ⟨w2, ws⟩; · nomatch h
  rcases ws with _ | ⟨w3, ws⟩; · nomatch h
  rcases ws with _ | ⟨w4, ws⟩; · nomatch h
  rcases ws with _ | ⟨w5, ws⟩; · nomatch h
  rcases ws with _ | ⟨_, _⟩
  · exact ⟨w0, w1, w2, w3, w4, w5, rfl⟩
  · nomatch h

theorem segSignal_list_len16 {α : Type} (ws : List α) (h : ws.length = 16) :
    ∃ d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15,
      ws = [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15] := by
  rcases ws with _ | ⟨d0, ws⟩; · nomatch h
  rcases ws with _ | ⟨d1, ws⟩; · nomatch h
  rcases ws with _ | ⟨d2, ws⟩; · nomatch h
  rcases ws with _ | ⟨d3, ws⟩; · nomatch h
  rcases ws with _ | ⟨d4, ws⟩; · nomatch h
  rcases ws with _ | ⟨d5, ws⟩; · nomatch h
  rcases ws with _ | ⟨d6, ws⟩; · nomatch h
  rcases ws with _ | ⟨d7, ws⟩; · nomatch h
  rcases ws with _ | ⟨d8, ws⟩; · nomatch h
  rcases ws with _ | ⟨d9, ws⟩; · nomatch h
  rcases ws with _ | ⟨d10, ws⟩; · nomatch h
  rcases ws with _ | ⟨d11, ws⟩; · nomatch h
  rcases ws with _ | ⟨d12, ws⟩; · nomatch h
  rcases ws with _ | ⟨d13, ws⟩; · nomatch h
  rcases ws with _ | ⟨d14, ws⟩; · nomatch h
  rcases ws with _ | ⟨d15, ws⟩; · nomatch h
  rcases ws with _ | ⟨_, _⟩
  · exact ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, rfl⟩
  · nomatch h

/-! ## `takenRecord` Unpack and Pack Helpers -/

theorem segSignal_rec_unpack (A : RustAlloc) (sp : BitVec 64) (g : RecordGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8))) :
    sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ⊢
      ∃∗ G : SessionGhost,
        vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
        sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } := by
  rcases g with ⟨prevCap, prevPtr, cur⟩
  cases cur with
  | none =>
    unfold sessionRecordAt takenRecord
    dsimp only
    rw [sepConj_comm]
    exact Entails.pure_left False.elim
  | some G =>
    unfold sessionRecordAt takenRecord
    dsimp only
    have h128 : sp + 0x110#64 + 0x18#64 = sp + 0x128#64 := by bv_omega
    rw [h128]
    exact Entails.sepExists_right G (Entails.refl _)

theorem segSignal_rec_pack (A : RustAlloc) (sp prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8))) :
    (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken }) ⊢
      sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) := by
  unfold sessionRecordAt takenRecord
  dsimp only
  have h128 : sp + 0x110#64 + 0x18#64 = sp + 0x128#64 := by bv_omega
  rw [h128]
  exact Entails.refl _

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
