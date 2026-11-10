/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.InnerReloc
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsExt
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Recv.Contracts
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Top
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Final
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalExt

/-!
# Top-Level `spqr::recv` Correctness

Discharges `SpqrRecvV1Stmt` on the CLI image from `TripleRatchetHooks`, `SpqrHooks`, and
`Obj.Loads`, and re-exports the extended-stack `SpqrRecvContractsExt` entry points.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames.LibsignalSession (Crypto ShaCompress)

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchet



open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalSpqrV1

open CryptoVerification.SpqrV1.Drop

open CryptoVerification.SpqrV1.Alloc

open CryptoVerification.SpqrV1.ChainProofs

open CryptoVerification.SpqrV1.Auth

open CryptoVerification.SpqrV1.Kdf

open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof

open CryptoVerification.SpqrV1.Poly


open CryptoVerification.SpqrV1.Poly.AddChunk

open CryptoVerification.SpqrV1.Poly.EncodeBytes

open CryptoVerification.SpqrV1.Top

open CryptoVerification.SpqrV1.Top.DecodeState

open CryptoVerification.SpqrV1.States.Leaves

open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk

open CryptoVerification.SpqrV1.States.RecvCt2Chunk

open CryptoVerification.SpqrV1.States.FromPb

open CryptoVerification.SpqrV1.States.IntoPb

open CryptoVerification.SpqrV1.States.Recv


open CryptoVerification.CodeLayout

set_option autoImplicit false

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedSimpArgs false

/-- Assemble `SpqrRecvContracts canonicalV1InnerHeap` from `TripleRatchetHooks`, `SpqrHooks`,
and `Obj.Loads`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Recv.spqrRecvContracts_of_hooks_canonical
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {K : MlKem}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hTH : TripleRatchetHooks C A (spqrV1 C.F K) abs)
    (hSH : SpqrHooks C A K abs) :
    SpqrRecvContracts canonicalV1InnerHeap img A C.F K (tripleRatchetExterns C ctl abs) :=
  CryptoVerification.Cli.SpqrV1.Top.Recv.spqrRecvContracts_of_hooks himg hTH hSH
    (states_from_pb_ok_x
      (Stage2Contracts.of_tripleRatchetProgAt img.base C A ctl (spqrV1 C.F K) abs hTH).toAllocContracts)
    (states_recv_ok_x_of_hooks himg hTH hSH)

/-- Top-level `spqr::recv` correctness theorem discharging `SpqrRecvV1Stmt` from
`TripleRatchetHooks`, `SpqrHooks`, and `Obj.Loads`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Recv.spqr_recv_ok
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image) :
    SpqrRecvV1Stmt C A ctl K abs img := by
  intro hHooks hSpqr himg
  exact spqrRecv_ok_of_contracts (CryptoVerification.Cli.SpqrV1.Top.Recv.spqrRecvContracts_of_hooks_canonical himg hHooks hSpqr)

/-- CLI-namespaced re-export of `spqrRecv_ok_ext_of_contracts_ext` under `SpqrRecvContractsExt`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Recv.spqrRecv_ok_ext_of_contracts_ext
    {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName)
      (spqrRecvSpecExactKeyBounded A (spqrV1Recv F K) img) :=
  CryptoVerification.SpqrV1.Top.Recv.spqrRecv_ok_ext_of_contracts_ext hC

/-- CLI-namespaced re-export of `spqrRecv_ok_of_contracts_ext` under `SpqrRecvContractsExt`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Recv.spqrRecv_ok_of_contracts_ext
    {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img spqrRecvName)
      (spqrRecvSpecExactKeyBounded A (spqrV1Recv F K) img) :=
  CryptoVerification.SpqrV1.Top.Recv.spqrRecv_ok_of_contracts_ext hC

end CryptoVerification.SpqrV1.Top.Recv
