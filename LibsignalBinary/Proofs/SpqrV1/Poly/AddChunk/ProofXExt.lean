/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofExt
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofX

@[expose] public section

set_option autoImplicit false

/-!
# 4K-Stack `.inImage` Wrapper for `<PolyDecoder as Decoder>::add_chunk`

Derives `add_chunk_ok_x_4k : AllocContracts4K img.base A ext → AddChunkOkX img A ext`.
-/

namespace LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofXExt

open Arm64 ProofLib
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (subroutine_ok_inImage_of_subroutine_ok)
open CryptoVerification.SpqrV1.Alloc (AllocContracts4K)
open CryptoVerification.SpqrV1.Poly.AddChunk
  (AddChunkOkX addChunkSpecX_of_addChunkSpec add_chunk_ok_ext_4k)

theorem add_chunk_ok_x_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext) :
    AddChunkOkX img A ext :=
  subroutine_ok_inImage_of_subroutine_ok img
    (addChunkSpecX_of_addChunkSpec (add_chunk_ok_ext_4k hA))

end LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofXExt

-- AUTO-BRIDGE BEGIN
namespace CryptoVerification.SpqrV1.Poly.AddChunk
export LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofXExt (add_chunk_ok_x_4k)
end CryptoVerification.SpqrV1.Poly.AddChunk
-- AUTO-BRIDGE END
