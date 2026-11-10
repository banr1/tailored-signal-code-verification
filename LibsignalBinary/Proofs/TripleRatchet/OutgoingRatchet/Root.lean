/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.HmacCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Frame
import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From

/-!
# Root Theorems `otrFrom_run` and `otrApply_run`

Bridges `otrFrom_ok` and `otrApply_ok` from `tripleRatchetProgAt` to the root statements
`OtrFromRunStmt` and `OtrApplyRunStmt`, and re-exports their `[LibsignalPlacement]` counterparts.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet

theorem otrFrom_run_ext (A : RustAlloc) (ext : String → Option (State → State)) (img : Obj.Image)
    (hA : AllocContracts img.base A ext)
    (hDeser : DeserializeExtOk img.base ext)
    (hRemIk : RemoteIdentityKeyExtOk img A ext)
    (hDropSpe : DropSpeExtOk img A ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img otrFromName) (otrFromSpec A img) :=
  root_of_tripleRatchetProgAtExt himg (otrFrom_ok_ext himg hA hDeser hRemIk hDropSpe)

def OtrFromOk_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  OtrFromExtOk img A (trTrapExterns C abs)

def OtrApplyOk_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  OtrApplyExtOk img A (trTrapExterns C abs)

theorem otrFrom_ok_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocHooks A abs)
    (hDeser : DeserializeExtOk img.base (trTrapExterns C abs))
    (hRemIk : RemoteIdentityKeyOk_trap img C A abs)
    (hDropSpe : DropSpeOk_trap img C A abs) :
    OtrFromOk_trap img C A abs :=
  otrFrom_ok_ext himg (AllocContracts.of_tripleRatchetProgAt_trap img.base C A abs hA)
    hDeser hRemIk hDropSpe

theorem otrApply_ok_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (abs : String → Option (State → State))
    (h : TripleRatchetHooks C A S abs) : OtrApplyOk_trap img C A abs :=
  otrApply_ok_ext img A (trTrapExterns C abs)
    (AllocContracts.of_tripleRatchetProgAt_trap img.base C A abs h.alloc)

def _root_.CryptoVerification.LibsignalTripleRatchet.OtrFromRunStmt_trap
    (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs →
  Obj.Loads libsignalSessionImage img →
  subroutine_ok (tripleRatchetProg_trap img C abs) (entryOf img otrFromName)
    (otrFromSpec A img)

def _root_.CryptoVerification.LibsignalTripleRatchet.OtrApplyRunStmt_trap
    (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs →
  Obj.Loads libsignalSessionImage img →
  subroutine_ok (tripleRatchetProg_trap img C abs) (entryOf img otrApplyName)
    (otrApplySpec A img)

theorem otrFrom_run_trap (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image)
    (hDeser : DeserializeExtOk img.base (trTrapExterns C abs))
    (hRemIk : RemoteIdentityKeyOk_trap img C A abs)
    (hDropSpe : DropSpeOk_trap img C A abs) :
    OtrFromRunStmt_trap C A S abs img :=
  fun hH himg => root_of_tripleRatchetProgAt_trap himg
    (otrFrom_ok_trap himg hH.alloc hDeser hRemIk hDropSpe)

/-- `<OutgoingTripleRatchet>::from_session_state` meets `otrFromSpec A img` on
`tripleRatchetProg img C ctl abs` (`OtrFromRunStmt`). -/
theorem otrFrom_run (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image)
    (hDeser : DeserializeOk img.base C ctl abs)
    (hRemIk : RemoteIdentityKeyOk img C A ctl abs)
    (hDropSpe : DropSpeOk img C A ctl abs) :
    OtrFromRunStmt C A ctl S abs img :=
  fun hH himg => root_of_tripleRatchetProgAt himg (otrFrom_ok himg hH.alloc hDeser hRemIk hDropSpe)

theorem otrApply_run_ext (A : RustAlloc) (ext : String → Option (State → State)) (img : Obj.Image)
    (hA : AllocContracts img.base A ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img otrApplyName) (otrApplySpec A img) :=
  root_of_tripleRatchetProgAtExt himg (otrApply_ok_ext img A ext hA)

theorem otrApply_run_trap (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image) :
    OtrApplyRunStmt_trap C A S abs img :=
  fun hH himg => root_of_tripleRatchetProgAt_trap himg (otrApply_ok_trap img C A S abs hH)

/-- `<OutgoingTripleRatchet>::apply_to_session_state` meets `otrApplySpec A img` on
`tripleRatchetProg img C ctl abs` (`OtrApplyRunStmt`). -/
theorem otrApply_run (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image) :
    OtrApplyRunStmt C A ctl S abs img :=
  fun hH himg => subroutine_ok_prog_kit_of_trTrap himg (otrApply_run_trap C A S abs img hH himg)

/-! ## Relocatable `[LibsignalPlacement]` root contracts -/

open CryptoVerification.LibsignalTripleRatchet.Getters

theorem otrFrom_run_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hremIk : subroutine_ok ((blkPC_29).rebase (blkPl_29).base H)
      (blkPl_29).base (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A)))
    (hdropSpe : subroutine_ok ((blkPC_5).rebase (blkPl_5).base H)
      (blkPl_5).base (withLsRoLoaded lsmpl (dropSpeSpec A))) :
    subroutine_ok ((blkPC_19).rebase (blkPl_19).base H) (blkPl_19).base
      (otrFromPlacedSpec A) :=
  otrFrom_placed_ok h_dealloc hremIk hdropSpe

theorem otrApply_run_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (h_panic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_20).rebase (blkPl_20).base H) (blkPl_20).base
      (otrApplyPlacedSpec A) :=
  otrApply_placed_ok h_shim h_alloc h_dealloc h_panic

end CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
