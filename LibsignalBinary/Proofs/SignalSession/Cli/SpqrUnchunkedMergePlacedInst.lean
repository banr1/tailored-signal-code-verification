/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedClPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInst
import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
import LibsignalBinary.Proofs.SpqrV1.Auth.AuthEncodeMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.BytesMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlaced

/-!
# Placed `unchunked::Ct1Sent::merge` & `unchunked::EkSentCt1Received::merge`

Code-and-rodata-loaded (`withLsCodeRoLoaded lsmpl`) own-block and caller-transferred contracts for
`unchunked::Ct1Sent::merge` (Block 312) and `unchunked::EkSentCt1Received::merge` (Block 311),
both over generic hooks and instantiated under `[CliSpqrExt W ext]`.
-/

@[expose] public section
set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrUnchunkedMergePlacedInst

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (LibsignalPlacement LibsignalHooks IsLsBlockProg lsmpl libsignalSessionLib
   withLsCl withLsCodeLoaded ls_blockPlacement_base
   lsProg_261 lsProg_263 lsProg_290 lsProg_291 lsProg_295 lsProg_311 lsProg_312
   blkPC_311 blkPl_311 blkPC_312 blkPl_312)
open CryptoVerification.RecordCodecs.Placed (lsProg_257)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet
  (withLsCodeRoLoaded decodeErrorPushSpec decodeErrorFromSpec)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli (CliSpqrExt)
open CryptoVerification.E2E.HooksE (A0)
open CryptoVerification.SpqrV1.Varint (skipField3Spec decodeVarint2Spec)
open CryptoVerification.SpqrV1.Prost.BytesMerge (bytesMerge3RawSpec)
open CryptoVerification.SpqrV1.Auth (authMergeSpec)
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
  (unchunkedCt1SentMergeSpec unchunkedEkSentCt1ReceivedMergeSpec)
open CryptoVerification.SpqrV1.Top.Recv (ls_subroutine_ok_cro_of_cro ls_subroutine_ok_cro_of_cl)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentClPlaced
  (unchunkedCt1SentMerge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedClPlaced
  (unchunkedEkSentCt1ReceivedMerge_cl_placed_ok_of_contracts)

/-! ### 1. Internal `IsLsBlockProg` & Wrapper Lifting Helpers -/

private theorem isLsBlockProg_257 [LibsignalPlacement] (H : LibsignalHooks) :
    IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 257 H) 257 H :=
  ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_257 H) 257 H).externs_eq⟩

private theorem isLsBlockProg_261 [LibsignalPlacement] (H : LibsignalHooks) :
    IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 261 H) 261 H :=
  ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_261 H) 261 H).externs_eq⟩

private theorem isLsBlockProg_263 [LibsignalPlacement] (H : LibsignalHooks) :
    IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 263 H) 263 H :=
  ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_263 H) 263 H).externs_eq⟩

private theorem isLsBlockProg_290 [LibsignalPlacement] (H : LibsignalHooks) :
    IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 290 H) 290 H :=
  ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_290 H) 290 H).externs_eq⟩

private theorem isLsBlockProg_291 [LibsignalPlacement] (H : LibsignalHooks) :
    IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 291 H) 291 H :=
  ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_291 H) 291 H).externs_eq⟩

private theorem isLsBlockProg_295 [LibsignalPlacement] (H : LibsignalHooks) :
    IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 295 H) 295 H :=
  ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_295 H) 295 H).externs_eq⟩

private theorem isLsBlockProg_311 [LibsignalPlacement] (H : LibsignalHooks) :
    IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 311 H) 311 H :=
  ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_311 H) 311 H).externs_eq⟩

private theorem isLsBlockProg_312 [LibsignalPlacement] (H : LibsignalHooks) :
    IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 312 H) 312 H :=
  ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_312 H) 312 H).externs_eq⟩

private theorem rebase_to_blockProgram [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee : IsLsBlockProg calleeProg j H] {spec : Spec α}
    (h : subroutine_ok calleeProg (libsignalSessionLib.blockPlacement lsmpl j).base spec) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j) spec := by
  have h' : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H)
      (libsignalSessionLib.blockPlacement lsmpl j).base spec :=
    hcallee.eq_blockProgram ▸ h
  rwa [ls_blockPlacement_base (i := j)] at h'

theorem withLsCodeLoaded_of_withLsCl [LibsignalPlacement] {α : Type}
    {P : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P entry (withLsCl lsmpl spec)) :
    subroutine_ok P entry (withLsCodeLoaded lsmpl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      dsimp only [withLsCl, withLsCodeLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)

/-! ### 2. Hook-Generic Own-Block & Caller-Transferred Theorems (`312` and `311`) -/

/-- Block `312` (`unchunked::Ct1Sent::merge`) on `(blkPC_312).rebase` from own-block
    `withLsCodeLoaded` (`257, 261, 263, 291`) and `withLsCodeRoLoaded` (`290, 295`) callee contracts. -/
theorem unchunkedCt1SentMerge_312_rebase_cro [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushSpec A)))
    (h261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromSpec A)))
    (h263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 H) (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A)))
    (h290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    (h291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A)))
    (h295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A))) :
    subroutine_ok ((blkPC_312).rebase (blkPl_312).base H)
      (blkPl_312).base
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A)) := by
  let _ := isLsBlockProg_257 H
  let _ := isLsBlockProg_261 H
  let _ := isLsBlockProg_263 H
  let _ := isLsBlockProg_290 H
  let _ := isLsBlockProg_291 H
  let _ := isLsBlockProg_295 H
  exact unchunkedCt1SentMerge_cl_placed_ok_of_contracts
    (ls_subroutine_ok_cro_of_cl (i := 312) (j := 261) h261)
    (ls_subroutine_ok_cro_of_cl (i := 312) (j := 257) h257)
    (ls_subroutine_ok_cro_of_cl (i := 312) (j := 291) h291)
    (ls_subroutine_ok_cro_of_cl (i := 312) (j := 263) h263)
    (ls_subroutine_ok_cro_of_cro (i := 312) (j := 290) h290)
    (ls_subroutine_ok_cro_of_cro (i := 312) (j := 295) h295)

/-- own-block `blockProgram` contract for Block `312` (`unchunked::Ct1Sent::merge`). -/
theorem unchunkedCt1SentMerge_312_cro [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushSpec A)))
    (h261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromSpec A)))
    (h263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 H) (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A)))
    (h290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    (h291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A)))
    (h295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 312 H)
      (lsmpl.base 312)
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A)) :=
  rebase_to_blockProgram (j := 312)
    (unchunkedCt1SentMerge_312_rebase_cro h257 h261 h263 h290 h291 h295)

/-- Block `311` (`unchunked::EkSentCt1Received::merge`) on `(blkPC_311).rebase` from own-block
    `withLsCodeLoaded` (`257, 261, 263, 291`) and `withLsCodeRoLoaded` (`290, 295`) callee contracts. -/
theorem unchunkedEkSentCt1ReceivedMerge_311_rebase_cro [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushSpec A)))
    (h261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromSpec A)))
    (h263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 H) (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A)))
    (h290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    (h291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A)))
    (h295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A))) :
    subroutine_ok ((blkPC_311).rebase (blkPl_311).base H)
      (blkPl_311).base
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A)) := by
  let _ := isLsBlockProg_257 H
  let _ := isLsBlockProg_261 H
  let _ := isLsBlockProg_263 H
  let _ := isLsBlockProg_290 H
  let _ := isLsBlockProg_291 H
  let _ := isLsBlockProg_295 H
  exact unchunkedEkSentCt1ReceivedMerge_cl_placed_ok_of_contracts
    (ls_subroutine_ok_cro_of_cl (i := 311) (j := 261) h261)
    (ls_subroutine_ok_cro_of_cl (i := 311) (j := 257) h257)
    (ls_subroutine_ok_cro_of_cl (i := 311) (j := 291) h291)
    (ls_subroutine_ok_cro_of_cl (i := 311) (j := 263) h263)
    (ls_subroutine_ok_cro_of_cro (i := 311) (j := 290) h290)
    (ls_subroutine_ok_cro_of_cro (i := 311) (j := 295) h295)

/-- own-block `blockProgram` contract for Block `311` (`unchunked::EkSentCt1Received::merge`). -/
theorem unchunkedEkSentCt1ReceivedMerge_311_cro [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushSpec A)))
    (h261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromSpec A)))
    (h263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 H) (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A)))
    (h290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    (h291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A)))
    (h295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 311 H)
      (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A)) :=
  rebase_to_blockProgram (j := 311)
    (unchunkedEkSentCt1ReceivedMerge_311_rebase_cro h257 h261 h263 h290 h291 h295)

/-! ### 3. `[CliSpqrExt W ext]` Instantiations for `V1State::merge` / `Chunked*` Callers -/

/-- Own-block `blockProgram` contract for Block `312` (`unchunked::Ct1Sent::merge`),
    generic in `[CliSpqrExt W ext]`, from own-block callee contracts (`257, 261, 263, 290, 291, 295`). -/
theorem cliUnchunkedCt1SentMerge_312_cro [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (h257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (h261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (h263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (h290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A0)))
    (h291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (h295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A0))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 312 (Rust.withPanics ext))
      (lsmpl.base 312)
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A0)) :=
  unchunkedCt1SentMerge_312_cro h257 h261 h263 h290 h291 h295

/-- Caller-transferred contract for Block `312` (`unchunked::Ct1Sent::merge`) onto any block `i < 619`
    (e.g. `ChunkedCt1Sampled` `300`, `ChunkedCt1Acknowledged` `307`, `ChunkedEkReceivedCt1Sampled` `310`),
    generic in `[CliSpqrExt W ext]`, in the exact `withLsCodeRoLoaded` form consumed by `V1State::merge` arms. -/
theorem cliUnchunkedCt1SentMerge_caller_cro [LibsignalPlacement]
    {callerProg : Program} {i : Nat} (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (h261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (h263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (h290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A0)))
    (h291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (h295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A0)))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 312)
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A0)) := by
  let _ := isLsBlockProg_312 (Rust.withPanics ext)
  exact ls_subroutine_ok_cro_of_cro (i := i) (j := 312)
    (cliUnchunkedCt1SentMerge_312_cro W h257 h261 h263 h290 h291 h295) hi

/-- Own-block `blockProgram` contract for Block `311` (`unchunked::EkSentCt1Received::merge`),
    generic in `[CliSpqrExt W ext]`, from own-block callee contracts (`257, 261, 263, 290, 291, 295`). -/
theorem cliUnchunkedEkSentCt1ReceivedMerge_311_cro [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (h257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (h261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (h263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (h290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A0)))
    (h291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (h295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A0))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 311 (Rust.withPanics ext))
      (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A0)) :=
  unchunkedEkSentCt1ReceivedMerge_311_cro h257 h261 h263 h290 h291 h295

/-- Caller-transferred contract for Block `311` (`unchunked::EkSentCt1Received::merge`) onto any block `i < 619`
    (e.g. `ChunkedCt1Received` `303`, `ChunkedEkSentCt1Received` `309`),
    generic in `[CliSpqrExt W ext]`, in the exact `withLsCodeRoLoaded` form consumed by `V1State::merge` arms. -/
theorem cliUnchunkedEkSentCt1ReceivedMerge_caller_cro [LibsignalPlacement]
    {callerProg : Program} {i : Nat} (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)))
    (h261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)))
    (h263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0)))
    (h290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A0)))
    (h291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)))
    (h295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A0)))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A0)) := by
  let _ := isLsBlockProg_311 (Rust.withPanics ext)
  exact ls_subroutine_ok_cro_of_cro (i := i) (j := 311)
    (cliUnchunkedEkSentCt1ReceivedMerge_311_cro W h257 h261 h263 h290 h291 h295) hi

/-!
### 4. Uniform `withLsCodeRoLoaded` Variants (All 6 Callees in `withLsCodeRoLoaded` Form)
-/

/-- Own-block `blockProgram` contract for Block `312` (`unchunked::Ct1Sent::merge`),
    generic in `[CliSpqrExt W ext]`, when all 6 callee contracts are given in `withLsCodeRoLoaded` form. -/
theorem cliUnchunkedCt1SentMerge_312_of_cro [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (h257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A0)))
    (h261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A0)))
    (h263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A0)))
    (h290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A0)))
    (h291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A0)))
    (h295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A0))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 312 (Rust.withPanics ext))
      (lsmpl.base 312)
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A0)) := by
  let _ := isLsBlockProg_257 (Rust.withPanics ext)
  let _ := isLsBlockProg_261 (Rust.withPanics ext)
  let _ := isLsBlockProg_263 (Rust.withPanics ext)
  let _ := isLsBlockProg_290 (Rust.withPanics ext)
  let _ := isLsBlockProg_291 (Rust.withPanics ext)
  let _ := isLsBlockProg_295 (Rust.withPanics ext)
  exact rebase_to_blockProgram (j := 312)
    (unchunkedCt1SentMerge_cl_placed_ok_of_contracts
      (ls_subroutine_ok_cro_of_cro (i := 312) (j := 261) h261)
      (ls_subroutine_ok_cro_of_cro (i := 312) (j := 257) h257)
      (ls_subroutine_ok_cro_of_cro (i := 312) (j := 291) h291)
      (ls_subroutine_ok_cro_of_cro (i := 312) (j := 263) h263)
      (ls_subroutine_ok_cro_of_cro (i := 312) (j := 290) h290)
      (ls_subroutine_ok_cro_of_cro (i := 312) (j := 295) h295))

/-- Own-block `blockProgram` contract for Block `311` (`unchunked::EkSentCt1Received::merge`),
    generic in `[CliSpqrExt W ext]`, when all 6 callee contracts are given in `withLsCodeRoLoaded` form. -/
theorem cliUnchunkedEkSentCt1ReceivedMerge_311_of_cro [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (h257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A0)))
    (h261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A0)))
    (h263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A0)))
    (h290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A0)))
    (h291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A0)))
    (h295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A0))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 311 (Rust.withPanics ext))
      (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A0)) := by
  let _ := isLsBlockProg_257 (Rust.withPanics ext)
  let _ := isLsBlockProg_261 (Rust.withPanics ext)
  let _ := isLsBlockProg_263 (Rust.withPanics ext)
  let _ := isLsBlockProg_290 (Rust.withPanics ext)
  let _ := isLsBlockProg_291 (Rust.withPanics ext)
  let _ := isLsBlockProg_295 (Rust.withPanics ext)
  exact rebase_to_blockProgram (j := 311)
    (unchunkedEkSentCt1ReceivedMerge_cl_placed_ok_of_contracts
      (ls_subroutine_ok_cro_of_cro (i := 311) (j := 261) h261)
      (ls_subroutine_ok_cro_of_cro (i := 311) (j := 257) h257)
      (ls_subroutine_ok_cro_of_cro (i := 311) (j := 291) h291)
      (ls_subroutine_ok_cro_of_cro (i := 311) (j := 263) h263)
      (ls_subroutine_ok_cro_of_cro (i := 311) (j := 290) h290)
      (ls_subroutine_ok_cro_of_cro (i := 311) (j := 295) h295))

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrUnchunkedMergePlacedInst
