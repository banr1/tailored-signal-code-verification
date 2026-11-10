/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.TrapRng
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeStateEmpty.Proof
import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Proof

/-!
# In-Image `spqr::decode_state` and `spqr::recv` on an Empty State

With SPQR disabled (`DEV-LS24`), only the empty SPQR state (`st.bytes = []`) is reached:
- `decodeStateEmpty_ok` / `decodeStateEmpty_root`: `spqr::decode_state` satisfies
  `decodeStateEmptySpec A` without allocating or calling extern hooks;
- `spqrRecvEmpty_run`: discharges `SpqrRecvEmptyRunStmt` for `spqr::recv` under any model
  satisfying `SpqrModel.RecvEmptyOk`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap

theorem decodeStateEmpty_ok_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) :
    subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr decodeStateName)
      (decodeStateEmptySpec A) := by
  exact InImage.DecodeStateEmpty.decodeStateEmpty_ok_F b (Rust.withPanics (trTrapExterns C abs)) A

theorem decodeStateEmpty_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr decodeStateName)
      (decodeStateEmptySpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr decodeStateName]
  exact subroutine_ok_kit_of_trTrap (decodeStateEmpty_ok_trap b C A abs)

theorem decodeStateEmpty_root {img : Obj.Image} (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img decodeStateName)
      (decodeStateEmptySpec A) :=
  root_of_tripleRatchetProgAt himg (decodeStateEmpty_ok img.base C A ctl abs)

theorem memcpy_recv_ok_at_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr spqrRecvName + bv% (ls_off% "memcpy" - ls_off% "spqr::recv"))
      InImage.SpqrRecvEmpty.memcpyRecvPcsSpec := by
  refine hook_ok_at_raw (hname := "memcpy") (stub := libsignalSessionCode.fnOff "memcpy")
    (ls_lemma% fnOff "spqr::recv") (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (fun X => by simp only [arm64_norm]) ?_
  exact ⟨hookMemcpy, rfl, InImage.SpqrRecvEmpty.hookMemcpy_recv_pcs_ok⟩

theorem spqrRecvEmpty_base_trap (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image) (hE : S.RecvEmptyOk) :
    subroutine_ok (trTrapProgAt img.base C abs) ((trTrapProgAt img.base C abs).fnAddr spqrRecvName)
      (spqrRecvEmptySpec A S img) := by
  rw [InImage.SpqrRecvEmpty.spqrRecvEmptySpec_eq_code]
  exact InImage.SpqrRecvEmpty.spqrRecvEmpty_base_F img.base (Rust.withPanics (trTrapExterns C abs)) A S img
    (logOff img) hE
    (InImage.SpqrRecvEmpty.memcpyRecvPcsSpecS_inImage_of img (memcpy_recv_ok_at_trap img.base C abs))

/-- Trap-at-rng twin of `SpqrRecvEmptyRunStmt` on `tripleRatchetProg_trap img C abs`. -/
def SpqrRecvEmptyRunStmt_trap (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → S.RecvEmptyOk → Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg_trap img C abs) (entryOf img spqrRecvName)
      (spqrRecvEmptySpec A S img)

theorem spqrRecvEmpty_run_trap (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) :
    SpqrRecvEmptyRunStmt_trap C A S abs img := by
  intro _ hE himg
  exact root_of_tripleRatchetProgAt_trap himg (spqrRecvEmpty_base_trap C A S abs img hE)

/-- Discharges `SpqrRecvEmptyRunStmt` for the in-image `spqr::recv` under `SpqrModel.RecvEmptyOk`. -/
theorem spqrRecvEmpty_run (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) :
    SpqrRecvEmptyRunStmt C A ctl S abs img :=
  fun hH hE himg =>
    subroutine_ok_prog_kit_of_trTrap himg (spqrRecvEmpty_run_trap C A S abs img hH hE himg)

end CryptoVerification.LibsignalTripleRatchet
