/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFrom
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

/-!
# Root Assembly for `<SignalMessage as TryFrom<&[u8]>>::try_from` (`0x25868`)

Combines the prologue, `len = 9` fast path, protobuf decode loop, and shared epilogue
(`TryFrom`) with the post-loop validation, boxing, and cleanup proofs (`TryFromPost`) into
`tryFrom_subroutine_ok`, `tryFrom_run_stmt`, and `tryFrom_subroutine_ok_placed` (Block `85`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Wire

open Arm64 ProofLib CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters

/-- Discharges `TryFromPostOk` via `tryFrom_post_wp`. -/
theorem tryFromPost_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    (hS : TripleRatchetHooksW img C A S abs)
    (hDropErr : DropDecodeErrorOkW img C A ctl abs)
    (hDropSpe : DropSpeOkW img C A ctl abs)
    (hIntoBox : IntoBoxedSliceOk img C A ctl abs)
    (hTryClone : TryCloneFromRefOk img C A ctl abs)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    TryFromPostOk img C A ctl abs := by
  intro x s0 s hgt9 hlt hge3 hle4 hpc hrun hst
  refine SepWPp.mono_pre ?_
    (tryFrom_post_wp ctl hS hDropErr hDropSpe hIntoBox hTryClone hb
      hgt9 hlt hge3 hle4 hpc hrun hst)
  unfold loopPostMem
  simp only [sepConj_assoc]
  exact Entails.refl _

/-- Full subroutine correctness theorem for `<SignalMessage as TryFrom<&[u8]>>::try_from`
(`0x25868`) on `tripleRatchetProgAtW img.base C ctl parse abs = tripleRatchetProgAtExt img.base abs`. -/
theorem tryFrom_subroutine_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    (hS : TripleRatchetHooksW img C A S abs)
    (hvarint : DecodeVarintSliceOkW img C A ctl abs)
    (hint32 : Int32MergeOkW img C A ctl abs)
    (hskip : SkipFieldOkW img C A ctl abs)
    (hbytes : BytesMergeOkW img C A ctl abs)
    (hDropErr : DropDecodeErrorOkW img C A ctl abs)
    (hDropSpe : DropSpeOkW img C A ctl abs)
    (hIntoBox : IntoBoxedSliceOk img C A ctl abs)
    (hTryClone : TryCloneFromRefOk img C A ctl abs)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName)
      (tryFromSpec A img) :=
  tryFrom_subroutine_ok_of_post ctl hS hvarint hint32 hskip hbytes
    (tryFromPost_ok ctl hS hDropErr hDropSpe hIntoBox hTryClone hb)

/-- Subroutine correctness theorem for `<SignalMessage as TryFrom<&[u8]>>::try_from`
(`0x25868`) on `tripleRatchetProgAtExt img.base ext` given `TryFromDeps img C A ctl parse ext`. -/
theorem tryFrom_subroutine_ok_of_deps {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (d : TryFromDeps img C A ctl ext)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryFromName)
      (tryFromSpec A img) :=
  tryFrom_subroutine_ok ctl (TripleRatchetHooksW.of_contracts hC)
    d.varintSlice d.int32Merge d.skipField d.bytesMerge
    d.dropDecodeError d.dropSpe d.intoBoxed d.tryClone hb

/-- Root theorem `TryFromRunStmt` for `<SignalMessage as TryFrom<&[u8]>>::try_from` (`0x25868`)
under the triple-ratchet callee hypotheses. -/
theorem tryFrom_run_stmt {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    {img : Obj.Image}
    (hvarint : TripleRatchetHooks C A S abs → DecodeVarintSliceOkW img C A ctl (tripleRatchetExterns C ctl abs))
    (hint32 : TripleRatchetHooks C A S abs → Int32MergeOkW img C A ctl (tripleRatchetExterns C ctl abs))
    (hskip : TripleRatchetHooks C A S abs → SkipFieldOkW img C A ctl (tripleRatchetExterns C ctl abs))
    (hbytes : TripleRatchetHooks C A S abs → BytesMergeOkW img C A ctl (tripleRatchetExterns C ctl abs))
    (hDropErr : TripleRatchetHooks C A S abs → DropDecodeErrorOkW img C A ctl (tripleRatchetExterns C ctl abs))
    (hDropSpe : TripleRatchetHooks C A S abs → DropSpeOkW img C A ctl (tripleRatchetExterns C ctl abs))
    (hIntoBox : TripleRatchetHooks C A S abs → IntoBoxedSliceOk img C A ctl (tripleRatchetExterns C ctl abs))
    (hTryClone : TripleRatchetHooks C A S abs → TryCloneFromRefOk img C A ctl (tripleRatchetExterns C ctl abs)) :
    TryFromRunStmt C A ctl S abs img :=
  fun hS himg =>
    root_of_tripleRatchetProgAt himg
      (tryFrom_subroutine_ok ctl
        (TripleRatchetHooksW.of_tripleRatchetProgAt img C A ctl S abs hS)
        (hvarint hS) (hint32 hS) (hskip hS) (hbytes hS)
        (hDropErr hS) (hDropSpe hS) (hIntoBox hS) (hTryClone hS) (base_aligned himg))

/-! ## Relocatable `[LibsignalPlacement]` Root Assembly (Block `85`) -/

/-- Discharges `TryFromPostOk_placed` via `tryFrom_post_wp_placed`. -/
theorem tryFromPost_ok_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hDropErr : DropDecodeErrorOkWPlaced A H)
    (hDropSpe : DropSpeOkWPlaced A H)
    (hIntoBox : IntoBoxedSliceOkPlaced A H)
    (hTryClone : TryCloneFromRefOkPlaced A H) :
    TryFromPostOk_placed A H := by
  intro x s0 s hgt9 hlt hge3 hle4 hpc hrun hst
  refine SepWPp.mono_pre ?_
    (tryFrom_post_wp_placed hS hDropErr hDropSpe hIntoBox hTryClone
      hgt9 hlt hge3 hle4 hpc hrun hst)
  unfold loopPostMem
  simp only [sepConj_assoc]
  exact Entails.refl _

/-- Full relocatable subroutine correctness theorem for `<SignalMessage as TryFrom<&[u8]>>::try_from`
(block `85`) on `tryFromPlacedProg H`. -/
theorem tryFrom_subroutine_ok_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hvarint : DecodeVarintSliceOkWPlaced A H)
    (hint32 : Int32MergeOkWPlaced A H)
    (hskip : SkipFieldOkWPlaced A H)
    (hbytes : BytesMergeOkWPlaced A H)
    (hDropErr : DropDecodeErrorOkWPlaced A H)
    (hDropSpe : DropSpeOkWPlaced A H)
    (hIntoBox : IntoBoxedSliceOkPlaced A H)
    (hTryClone : TryCloneFromRefOkPlaced A H) :
    subroutine_ok (tryFromPlacedProg H) (blkPl_85).base
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpec A)) :=
  tryFrom_subroutine_ok_of_post_placed hS hvarint hint32 hskip hbytes
    (tryFromPost_ok_placed hS hDropErr hDropSpe hIntoBox hTryClone)

theorem tryFrom_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hvarint : DecodeVarintSliceOkWPlaced A H)
    (hint32 : Int32MergeOkWPlaced A H)
    (hskip : SkipFieldOkWPlaced A H)
    (hbytes : BytesMergeOkWPlaced A H)
    (hDropErr : DropDecodeErrorOkWPlaced A H)
    (hDropSpe : DropSpeOkWPlaced A H)
    (hIntoBox : IntoBoxedSliceOkPlaced A H)
    (hTryClone : TryCloneFromRefOkPlaced A H) :
    subroutine_ok (tryFromPlacedProg H) (blkPl_85).base
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpec A)) :=
  tryFrom_subroutine_ok_placed hS hvarint hint32 hskip hbytes hDropErr hDropSpe hIntoBox hTryClone

theorem tryFrom_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (d : TryFromDepsPlaced A H) :
    subroutine_ok (tryFromPlacedProg H) (blkPl_85).base
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpec A)) :=
  tryFrom_subroutine_ok_placed hS
    d.varintSlice d.int32Merge d.skipField d.bytesMerge
    d.dropDecodeError d.dropSpe d.intoBoxed d.tryClone

end CryptoVerification.LibsignalTripleRatchet.Wire
