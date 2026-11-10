/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBridge
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOk
public import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeHeap
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOneX
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityFutDropExt
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollX.Fetches
import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollX.Sym
import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreShim
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# CLI `<SessionFiles as SessionStore>::store_session` on a `Prev1` Record

Contracts and proofs for `SessionFiles::store_session` when the input `SessionRecord` holds a
current session `sess` and one archived previous session `enc` (`sessionRecordPrevAt`):
- `sessStorePollPrev1Mem_ok_of_deps` and `sessStorePollPrev1_of_mem` prove the poll against
  `encodeRecordPrev1Mem` and canonical `encodeRecordPrev1`, buffering the serialized record via
  `Dir::put` with `sf.trace = s0.trace`;
- instantiations at `cliExterns W` and `CliExternsOk P A ext`, plus `FsInv` and `DirGhost.changed`
  preservation lemmas.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.Store.StoreSessionPrev1

open Arm64 ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.Store.StorePollX.Helpers
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
open CliStorePollNorm
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre
  readVReg128_setMem_pre readVReg128_setPState_pre readVReg128_writeReg64_pre
  extractLsb_append_lo extractLsb_append_hi

/-! ## 1. Ghost state and specifications for `store_session::{closure#0}` on `Prev1` -/

/-- Ghost inputs for `<SessionFiles as SessionStore>::store_session::{closure#0}` when the record
at `recA` has current session `sess` (ghost `G`) and one archived previous session `enc`. -/
structure SessStorePollPrev1Ghost where
  fut : BitVec 64
  self : BitVec 64
  out : BitVec 64
  addrA : BitVec 64
  addr : AddrGhost
  recA : BitVec 64
  prevCap : BitVec 64
  prevPtr : BitVec 64
  G : SessionGhost
  sess : Session (List (BitVec 8))
  enc : List (BitVec 8)
  dir : DirGhost

/-- Memory-encoding specification of `SessionFiles::store_session::{closure#0}` on a `Prev1`
record (`prevVecAt A recA prevCap prevPtr [enc] ∗ sessionStateReprAt A (recA + 24#64) G sess`), storing
`encodeRecordPrev1Mem G sess enc` into `dir.put (addressText addr.val) ...`. -/
def sessStorePollPrev1MemSpec (A : RustAlloc) (img : Obj.Image) (stk : Nat) :
    Spec SessStorePollPrev1Ghost :=
  ({ pre := fun x s =>
       ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
         x.addr.name.bytes.length < 2 ^ 32 ∧
         (encodeRecordPrev1Mem x.G x.sess x.enc).length < 2 ^ 32 ∧
         x.dir.changed.length < 2 ^ 32⌝ ∗
         sessStoreBoxAt x.fut x.self x.addrA x.recA 0#8 ∗
         dirAt A x.self x.dir ∗ memRegion x.out 48 ∗
         protocolAddressAt A x.addr x.addrA ∗
         prevVecAt A x.recA x.prevCap x.prevPtr [x.enc] ∗
         sessionStateReprAt A (x.recA + 24#64) x.G x.sess ∗
         A.pool ∗ stackAt s.sp stk
     post := fun x s0 sf =>
       ⌜sf.trace = s0.trace⌝ ∗
         sessStoreBoxAt x.fut x.self x.addrA x.recA 1#8 ∗
         dirAt A x.self
           (x.dir.put (addressText x.addr.val) (encodeRecordPrev1Mem x.G x.sess x.enc)) ∗
         (x.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (x.out + 8#64) 40 ∗
         protocolAddressAt A x.addr x.addrA ∗
         prevVecAt A x.recA x.prevCap x.prevPtr [x.enc] ∗
         sessionStateReprAt A (x.recA + 24#64) x.G x.sess ∗
         A.pool ∗ stackAt s0.sp stk
     onPanic := fun _ s0 sf =>
       ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap } :
    Spec SessStorePollPrev1Ghost).inImage img

/-- Canonical-encoding specification of `SessionFiles::store_session::{closure#0}` on
`sessionRecordPrevAt A recA ⟨prevCap, prevPtr, some G⟩ [enc] ⟨some sess⟩` with
`CanonSession G sess`, storing `encodeRecordPrev1 sess enc`. -/
def sessStorePollPrev1Spec (A : RustAlloc) (img : Obj.Image) (stk : Nat) :
    Spec SessStorePollPrev1Ghost :=
  ({ pre := fun x s =>
       ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
         x.addr.name.bytes.length < 2 ^ 32 ∧
         E2E.Record.Serialization.CanonSession x.G x.sess ∧
         (encodeRecordPrev1 x.sess x.enc).length < 2 ^ 32 ∧
         x.dir.changed.length < 2 ^ 32⌝ ∗
         sessStoreBoxAt x.fut x.self x.addrA x.recA 0#8 ∗
         dirAt A x.self x.dir ∗ memRegion x.out 48 ∗
         protocolAddressAt A x.addr x.addrA ∗
         sessionRecordPrevAt A x.recA ⟨x.prevCap, x.prevPtr, some x.G⟩ [x.enc] ⟨some x.sess⟩ ∗
         A.pool ∗ stackAt s.sp stk
     post := fun x s0 sf =>
       ⌜sf.trace = s0.trace⌝ ∗
         sessStoreBoxAt x.fut x.self x.addrA x.recA 1#8 ∗
         dirAt A x.self
           (x.dir.put (addressText x.addr.val) (encodeRecordPrev1 x.sess x.enc)) ∗
         (x.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (x.out + 8#64) 40 ∗
         protocolAddressAt A x.addr x.addrA ∗
         sessionRecordPrevAt A x.recA ⟨x.prevCap, x.prevPtr, some x.G⟩ [x.enc] ⟨some x.sess⟩ ∗
         A.pool ∗ stackAt s0.sp stk
     onPanic := fun _ s0 sf =>
       ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap } :
    Spec SessStorePollPrev1Ghost).inImage img

/-! ## 2. Cell-unpacked `serializePrev1BodySpecX` helper and poll symbolic execution -/

structure SerPrev1CellsGhost where
  recA : BitVec 64
  out : BitVec 64
  prevCap : BitVec 64
  prevPtr : BitVec 64
  G : SessionGhost
  sess : Session (List (BitVec 8))
  enc : List (BitVec 8)
  o0 : BitVec 64
  o1 : BitVec 64
  o2 : BitVec 64
  o3 : BitVec 64
  fsp : BitVec 64

def serializePrev1CellsSpec (A : RustAlloc) (calleeStk : Nat) : Spec SerPrev1CellsGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.recA ∧ s.readReg64 .x8 = g.out ∧ s.sp = g.fsp ∧
      (encodeRecordPrev1Mem g.G g.sess g.enc).length < 2 ^ 32⌝ ∗
    prevVecAt A g.recA g.prevCap g.prevPtr [g.enc] ∗
    sessionStateReprAt A (g.recA + 24#64) g.G g.sess ∗
    (g.out ↦₆₄ g.o0) ∗ ((g.out + 8#64) ↦₆₄ g.o1) ∗
    ((g.out + 16#64) ↦₆₄ g.o2) ∗ ((g.out + 24#64) ↦₆₄ g.o3) ∗
    A.pool ∗ stackAt g.fsp calleeStk
  post := fun g s0 sf =>
    ∃∗ bCap : BitVec 64, ∃∗ bPtr : BitVec 64,
      ⌜sf.trace = s0.trace⌝ ∗
      prevVecAt A g.recA g.prevCap g.prevPtr [g.enc] ∗
      sessionStateReprAt A (g.recA + 24#64) g.G g.sess ∗
      (g.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
      ((g.out + 8#64) ↦₆₄ bCap) ∗ ((g.out + 16#64) ↦₆₄ bPtr) ∗
      ((g.out + 24#64) ↦₆₄ BitVec.ofNat 64 (encodeRecordPrev1Mem g.G g.sess g.enc).length) ∗
      SpqrV1.Alloc.vecU8Buf A bCap bPtr (encodeRecordPrev1Mem g.G g.sess g.enc) ∗
      A.pool ∗ stackAt g.fsp calleeStk
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem serializePrev1_cells_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {calleeStk : Nat}
    (hSer : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordSerializeName)
      ((serializePrev1BodySpecX A).inImage img))
    (hle : Proofs.libsignal.Hooks2.serializeStackX ≤ calleeStk)
    (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordSerializeName)
      ((serializePrev1CellsSpec A calleeStk).inImage img) := by
  refine subroutine_ok_outcome_intro fun g R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (serializePrev1CellsSpec A calleeStk).pre g s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [serializePrev1CellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hfsp, hlen⟩, hmem⟩
  rw [← hfsp] at hmem
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk)
    (calleeStk - Proofs.libsignal.Hooks2.serializeStackX)
  let callG : SerializePrev1BodyGhost :=
    ⟨g.recA, g.out, g.prevCap, g.prevPtr, g.G, g.sess, g.enc⟩
  have hpre0 : s0.mem ⊨ ((serializePrev1BodySpecX A).inImage img).pre callG s0 ∗ (stkRem ∗ R) := by
    refine satisfies_inImage_pre hinv ?_
    dsimp only [serializePrev1BodySpecX, callG]
    simp only [memRegion_32_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨g.o3, g.o2, g.o1, g.o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hlen⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  refine hSer.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, serializePrev1BodySpecX, serializePrev1CellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    dsimp only [vecU8] at hq
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨bCap, bPtr, hq⟩
    refine ⟨bCap, bPtr, ?_⟩
    rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf] at hq
    dsimp only [vecHeader] at hq
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [← hfsp, stackAt_sub_split s0.sp hle hhi]
    dsimp only [okTagVec, stkRem] at hq
    convert hq using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, serializePrev1BodySpecX, serializePrev1CellsSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [Spec.inImage] at hq
    exact (not_satisfies_false_sepConj hq).elim

private theorem close_panic_prev1 {s0 s_call sf : State} {F R : SepProp}
    (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
  refine allowPanic_frame ?_ (by rwa [sepConj_assoc] at hm)
  rintro ⟨hfail, hpref⟩
  unfold allocFailedIn at hfail ⊢
  rw [htr] at hfail hpref
  exact ⟨hfail, hpref⟩

private theorem cells_26_split_prev1 (sp : BitVec 64) :
    cells (sp - 208#64) 26 =
      storePollSlack sp ∗
        cells (sp - 200#64) 6 ∗ cells (sp - 144#64) 4 ∗
        cells (sp - 96#64) 5 ∗ cells (sp - 48#64) 6 := by
  rw [show (26 : Nat) = 1 + 25 from rfl, cells_split_sub sp 208 200 1 25,
    show (25 : Nat) = 6 + 19 from rfl, cells_split_sub sp 200 152 6 19,
    show (19 : Nat) = 1 + 18 from rfl, cells_split_sub sp 152 144 1 18,
    show (18 : Nat) = 4 + 14 from rfl, cells_split_sub sp 144 112 4 14,
    show (14 : Nat) = 2 + 12 from rfl, cells_split_sub sp 112 96 2 12,
    show (12 : Nat) = 5 + 7 from rfl, cells_split_sub sp 96 56 5 7,
    show (7 : Nat) = 1 + 6 from rfl, cells_split_sub sp 56 48 1 6]
  dsimp only [storePollSlack]
  ac_rfl

private theorem cells_sub_4_eq_prev1 (sp : BitVec 64) :
    cells (sp - 144#64) 4 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 144#64) ↦₆₄ v0) ∗ ((sp - 136#64) ↦₆₄ v1) ∗
        ((sp - 128#64) ↦₆₄ v2) ∗ ((sp - 120#64) ↦₆₄ v3) := by
  cells_unfold

private theorem cells_sub_5_eq_prev1 (sp : BitVec 64) :
    cells (sp - 96#64) 5 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗
        ((sp - 72#64) ↦₆₄ v3) ∗ ((sp - 64#64) ↦₆₄ v4) := by
  cells_unfold

private theorem cells_sub_6_200_eq_prev1 (sp : BitVec 64) :
    cells (sp - 200#64) 6 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 200#64) ↦₆₄ v0) ∗ ((sp - 192#64) ↦₆₄ v1) ∗ ((sp - 184#64) ↦₆₄ v2) ∗
        ((sp - 176#64) ↦₆₄ v3) ∗ ((sp - 168#64) ↦₆₄ v4) ∗ ((sp - 160#64) ↦₆₄ v5) := by
  cells_unfold

private theorem cells_sub_6_48_eq_prev1 (sp : BitVec 64) :
    cells (sp - 48#64) 6 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗ ((sp - 32#64) ↦₆₄ v2) ∗
        ((sp - 24#64) ↦₆₄ v3) ∗ ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5) := by
  cells_unfold

def cliStorePollPrev1InnerSpec (A : RustAlloc) (calleeStk : Nat) : Spec SessStorePollPrev1Ghost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      x.addr.name.bytes.length < 2 ^ 32 ∧
      (encodeRecordPrev1Mem x.G x.sess x.enc).length < 2 ^ 32 ∧
      x.dir.changed.length < 2 ^ 32⌝ ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₆₄ x.addrA) ∗
      ((x.fut + 16#64) ↦₆₄ x.recA) ∗ ((x.fut + 24#64) ↦₈ 0#8) ∗
      dirAt A x.self x.dir ∗ memRegion x.out 48 ∗
      protocolAddressAt A x.addr x.addrA ∗
      prevVecAt A x.recA x.prevCap x.prevPtr [x.enc] ∗
      sessionStateReprAt A (x.recA + 24#64) x.G x.sess ∗
      A.pool ∗ stackAt (s.sp - 208#64) calleeStk ∗ cells (s.sp - 208#64) 26
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₆₄ x.addrA) ∗
      ((x.fut + 16#64) ↦₆₄ x.recA) ∗ ((x.fut + 24#64) ↦₈ 1#8) ∗
      dirAt A x.self
        (x.dir.put (addressText x.addr.val) (encodeRecordPrev1Mem x.G x.sess x.enc)) ∗
      (x.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (x.out + 8#64) 40 ∗
      protocolAddressAt A x.addr x.addrA ∗
      prevVecAt A x.recA x.prevCap x.prevPtr [x.enc] ∗
      sessionStateReprAt A (x.recA + 24#64) x.G x.sess ∗
      A.pool ∗ stackAt (s0.sp - 208#64) calleeStk ∗ cells (s0.sp - 208#64) 26
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

set_option maxHeartbeats 600000 in
theorem sessStorePollPrev1Inner_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {addrStk putStk : Nat}
    (hAddr : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressTextName)
      (addrTextSpec A img addrStk))
    (hSer : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordSerializeName)
      ((serializePrev1BodySpecX A).inImage img))
    (hPut : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName)
      (dirPutSpec A img putStk))
    (hhi : max (max addrStk Proofs.libsignal.Hooks2.serializeStackX)
      (max putStk extHookStack) ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessStorePollName)
      ((cliStorePollPrev1InnerSpec A
        (max (max addrStk Proofs.libsignal.Hooks2.serializeStackX)
          (max putStk extHookStack))).inImage img) := by
  let calleeStk := max (max addrStk Proofs.libsignal.Hooks2.serializeStackX)
    (max putStk extHookStack)
  unfold Spec.inImage
  simp (config := { maxSteps := 2000000 }) only [cliStorePollPrev1InnerSpec,
    memRegion_48_cells, memRegion_40_cells,
    cells_26_split_prev1, cells_sub_4_eq_prev1, cells_sub_5_eq_prev1,
    cells_sub_6_200_eq_prev1, cells_sub_6_48_eq_prev1,
    sepExists_sepConj_left, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff sessStorePollName =
      num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") :=
    sessStorePoll_fnOff
  have hAddrCells := addrText_cells_ok (calleeStk := calleeStk) hAddr (by omega) hhi
  have hSerCells := serializePrev1_cells_ok (calleeStk := calleeStk) hSer (by omega) hhi
  have hPutCells := dirPut_cells_ok (calleeStk := calleeStk) hPut (by omega) hhi
  rw [Program.fnAddr_rel (name := sessStorePollName)
    hfn addressText_fnOff
    (k := num% (ls_rel%
      "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"
      "libsignal_cli::stores::address_text"))
    (by decide)] at hAddrCells
  rw [recordSerialize_fnAddr_eq] at hSerCells
  rw [dirPut_fnAddr_eq] at hPutCells
  code_fetches CryptoVerification.libsignalSessionCode cliStorePollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}")) 216
  dsimp only [tripleRatchetProgAtExt] at hAddrCells hSerCells hPutCells ⊢
  clear hfn hAddr hSer hPut
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessStorePollName = fnBase
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  apply ProofLib.SepWPp.of_sepWP_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"
      "libsignal_cli::stores::address_text"))
    hinv0
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv1
  wp_call_inImage hAddrCells hinv1
    (x.addrA, x.addr, s0.sp - 200#64, _, _, _, s0.sp - 208#64)
  case panic =>
    intro sf _ hm
    exact close_panic_prev1 (by simp only [wp_norm, arm64_norm, *]) hm
  apply ProofLib.SepWPp.of_sepWP_inImage
    (mid := fnBase - bv% (ls_rel%
      "<libsignal_protocol::state::session::SessionRecord>::serialize"
      "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"))
    hinv_sf
  wp_steps
  apply SepWP.done (by wp_norm_goal; bv_omega) (by wp_norm_lhs)
  intro hinv2
  wp_call_inImage hSerCells hinv2
    ⟨x.recA, s0.sp - 144#64, x.prevCap, x.prevPtr, x.G, x.sess, x.enc,
      _, _, _, _, s0.sp - 208#64⟩
  case panic =>
    intro sf _ hm
    exact close_panic_prev1 (by simp only [wp_norm, arm64_norm, *]) hm
  apply ProofLib.SepWPp.of_sepWP_inImage
    (mid := fnBase - bv% (ls_rel%
      "<libsignal_cli::stores::Dir>::put::<alloc::string::String>"
      "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"))
    hinv_sf_1
  wp_steps
  apply SepWP.done (by wp_norm_goal; bv_omega) (by wp_norm_lhs)
  intro hinv3
  wp_call_inImage hPutCells hinv3
    (x.self, x.dir, s0.sp - 200#64, addressText x.addr.val,
      s0.sp - 176#64, w, w_1, encodeRecordPrev1Mem x.G x.sess x.enc, s0.sp - 208#64)
  case panic =>
    intro sf _ hm
    exact close_panic_prev1 (by simp only [wp_norm, arm64_norm, *]) hm
  apply SepWPp.of_sepWP_ret
  wp_steps
  wp_done

/-! ## 3. Top-level hop theorems (`sessStorePollPrev1MemSpec` and `sessStorePollPrev1Spec`) -/

theorem sessStorePollPrev1Mem_of_inner {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {calleeStk stk : Nat}
    (hInner : calleeStk ≤ 2 ^ 64 →
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr sessStorePollName)
        ((cliStorePollPrev1InnerSpec A calleeStk).inImage img))
    (hstk : 0xd0 + calleeStk ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessStorePollName)
      (sessStorePollPrev1MemSpec A img stk) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧
      x.addr.name.bytes.length < 2 ^ 32 ∧
      (encodeRecordPrev1Mem x.G x.sess x.enc).length < 2 ^ 32 ∧
      x.dir.changed.length < 2 ^ 32⌝ ∗
      sessStoreBoxAt x.fut x.self x.addrA x.recA 0#8 ∗
      dirAt A x.self x.dir ∗ memRegion x.out 48 ∗
      protocolAddressAt A x.addr x.addrA ∗
      prevVecAt A x.recA x.prevCap x.prevPtr [x.enc] ∗
      sessionStateReprAt A (x.recA + 24#64) x.G x.sess ∗
      A.pool ∗ stackAt s0.sp stk)) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hname, henc, hdir⟩, hmem⟩
  dsimp only [sessStoreBoxAt] at hmem
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64 (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.fut) (v := x.self)
      (R := ((x.fut + 8#64) ↦₆₄ x.addrA) ∗ ((x.fut + 16#64) ↦₆₄ x.recA) ∗
        ((x.fut + 24#64) ↦₈ 0#8) ∗ memRegion (x.fut + 25#64) 7 ∗
        dirAt A x.self x.dir ∗ memRegion x.out 48 ∗
        protocolAddressAt A x.addr x.addrA ∗
        prevVecAt A x.recA x.prevCap x.prevPtr [x.enc] ∗
        sessionStateReprAt A (x.recA + 24#64) x.G x.sess ∗ A.pool ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; ac_rfl
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 208 ≤ 2 ^ 64 := by omega
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 208) (by omega) hstk_hi,
    stackAt_storePoll_frame s0.sp hframe_hi] at hmem
  let F_extra := memRegion (x.fut + 25#64) 7 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 208))
  have hpre_in : s0.mem ⊨ ((cliStorePollPrev1InnerSpec A calleeStk).inImage img).pre x s0 ∗
      (F_extra ∗ R) := by
    refine satisfies_inImage_pre hinv ?_
    dsimp only [cliStorePollPrev1InnerSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hname, henc, hdir⟩, ?_⟩
    dsimp only [F_extra]
    convert hmem using 1; ac_rfl
  refine (hInner hcal_hi).mono_outcome x (F_extra ∗ R) s0 hpc hrun hpre_in hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, cliStorePollPrev1InnerSpec, sessStorePollPrev1MemSpec,
      sessStoreBoxAt] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp (subStk := calleeStk + 208) (by omega) hstk_hi,
      stackAt_storePoll_frame s0.sp hframe_hi]
    dsimp only [F_extra] at hq
    convert hq using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, cliStorePollPrev1InnerSpec, sessStorePollPrev1MemSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [Spec.inImage] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-- `store_session::{closure#0}` meets `sessStorePollPrev1MemSpec A img stk` from its callees. -/
theorem sessStorePollPrev1Mem_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {addrStk putStk stk : Nat}
    (hAddr : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressTextName)
      (addrTextSpec A img addrStk))
    (hSer : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordSerializeName)
      ((serializePrev1BodySpecX A).inImage img))
    (hPut : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName)
      (dirPutSpec A img putStk))
    (hstk : 0xd0 + max (max addrStk Proofs.libsignal.Hooks2.serializeStackX)
      (max putStk extHookStack) ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessStorePollName)
      (sessStorePollPrev1MemSpec A img stk) :=
  sessStorePollPrev1Mem_of_inner
    (fun hhi => sessStorePollPrev1Inner_ok hAddr hSer hPut hhi) hstk

/-- Canonical-encoding `store_session::{closure#0}` contract (`sessStorePollPrev1Spec`). -/
theorem sessStorePollPrev1_of_mem {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    (hMem : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessStorePollName)
      (sessStorePollPrev1MemSpec A img stk)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessStorePollName)
      (sessStorePollPrev1Spec A img stk) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpre' := hpre
  dsimp only [sessStorePollPrev1Spec, Spec.inImage] at hpre'
  rw [sessionRecordPrevAt_some_eq A x.recA x.prevCap x.prevPtr x.G x.sess [x.enc],
    sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨hinv, hpre'⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx8, hname, hcanon, hlen, hdir⟩, hmem⟩
  have henc := encodeRecordPrev1Mem_eq_of_canon x.enc hcanon
  have hpre_mem : s0.mem ⊨ (sessStorePollPrev1MemSpec A img stk).pre x s0 ∗ R := by
    dsimp only [sessStorePollPrev1MemSpec, Spec.inImage]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hname, henc.symm ▸ hlen, hdir⟩, ?_⟩
    convert hmem using 1; ac_rfl
  refine hMem.mono_outcome x R s0 hpc hrun hpre_mem hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessStorePollPrev1MemSpec, sessStorePollPrev1Spec, Spec.inImage] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    rw [henc] at hq
    rw [sessionRecordPrevAt_some_eq A x.recA x.prevCap x.prevPtr x.G x.sess [x.enc]]
    refine ⟨htr, ?_⟩
    convert hq using 1; ac_rfl
  · exact Or.inl ⟨hpan, hq⟩ |> Or.inr
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

theorem sessStorePollPrev1_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {addrStk putStk stk : Nat}
    (hAddr : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressTextName)
      (addrTextSpec A img addrStk))
    (hSer : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordSerializeName)
      ((serializePrev1BodySpecX A).inImage img))
    (hPut : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName)
      (dirPutSpec A img putStk))
    (hstk : 0xd0 + max (max addrStk Proofs.libsignal.Hooks2.serializeStackX)
      (max putStk extHookStack) ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessStorePollName)
      (sessStorePollPrev1Spec A img stk) :=
  sessStorePollPrev1_of_mem (sessStorePollPrev1Mem_ok_of_deps hAddr hSer hPut hstk)

/-! ## 4. CLI instantiations (`cliExterns W`, `E2E.HooksE.A0`) & `FsInv` preservation -/

/-- `SessionRecord::serialize` (`serializePrev1BodySpecX`) instantiated at `cliExterns W` and `A0`. -/
theorem serializePrev1Body_cli (W : CliHooks) (img : Obj.Image) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr recordSerializeName)
      ((serializePrev1BodySpecX E2E.HooksE.A0).inImage img) :=
  serializePrev1Body_ok_of_trAllocContractsX (MainHops.allocContractsX_cli W img)

/-- `SessionRecord::serialize` (`serializePrev1CanonSpecX`) instantiated at `cliExterns W` and `A0`. -/
theorem serializePrev1CanonX_cli (W : CliHooks) (img : Obj.Image) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr recordSerializeName)
      ((serializePrev1CanonSpecX E2E.HooksE.A0).inImage img) :=
  serializePrev1CanonX_ok_of_trAllocContractsX (MainHops.allocContractsX_cli W img)

/-- `SessionRecord::serialize` (`SerializePrev1OkStmt`) instantiated at `cliExterns W` and `A0`. -/
theorem serializePrev1_cli (W : CliHooks) (img : Obj.Image) :
    SerializePrev1OkStmt img E2E.HooksE.A0 (cliExterns W) :=
  serializePrev1_ok_of_trAllocContractsX (MainHops.allocContractsX_cli W img)

/-- CLI `SessionFiles::store_session::{closure#0}` on a `Prev1` record (`encodeRecordPrev1Mem`)
at `fnAddr sessStorePollName`. -/
theorem sessStorePollPrev1Mem_cli (W : CliHooks) {img : Obj.Image} {stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hstk : SessKit.storePollNeedX ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr sessStorePollName)
      (sessStorePollPrev1MemSpec E2E.HooksE.A0 img stk) := by
  have hh := RunSkeleton.RunHooks.cli W img
  have hb : (img.base &&& 0xfff#64) = 0#64 := RunSkeleton.base_aligned himg
  have hC : AllocContractsX img E2E.HooksE.A0 (cliExterns W) := hh.alloc
  have hRes := RunSkeleton.reserve_ok hh (Nat.le_refl doReserveStackX)
  have hDec := Decimal.decimal_ok_of_deps hRes (Nat.le_refl SessKit.decNeed) hb
  have hAddr := AddressText.addressText_ok_of_deps hC hRes hDec
    (Nat.le_refl SessKit.addrTextNeed) hb
  have hGrow := GrowOne.growOneDir_ok_x hC (Nat.le_refl SessKit.growOneDirNeed) hb
  have hPut := Put.dirPut_ok_of_deps hC hh.bcmp hGrow (Nat.le_refl SessKit.dirPutNeed) hb
  exact sessStorePollPrev1Mem_ok_of_deps hAddr (serializePrev1Body_cli W img) hPut hstk

/-- CLI `SessionFiles::store_session::{closure#0}` on a `Prev1` record (`encodeRecordPrev1Mem`)
at `img.base + cliSessStorePollOff` (vtable poll slot). -/
theorem sessStorePollPrev1Mem_cli_at (W : CliHooks) {img : Obj.Image} {stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hstk : SessKit.storePollNeedX ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      (img.base + cliSessStorePollOff)
      (sessStorePollPrev1MemSpec E2E.HooksE.A0 img stk) := by
  have h := sessStorePollPrev1Mem_cli W himg hstk
  rw [cliSessStorePoll_fnAddr] at h
  exact h

/-- CLI `SessionFiles::store_session::{closure#0}` on a canonical `Prev1` record
(`encodeRecordPrev1`) at `fnAddr sessStorePollName`. -/
theorem sessStorePollPrev1_cli (W : CliHooks) {img : Obj.Image} {stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hstk : SessKit.storePollNeedX ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr sessStorePollName)
      (sessStorePollPrev1Spec E2E.HooksE.A0 img stk) :=
  sessStorePollPrev1_of_mem (sessStorePollPrev1Mem_cli W himg hstk)

/-- CLI `SessionFiles::store_session::{closure#0}` on a canonical `Prev1` record
(`encodeRecordPrev1`) at `img.base + cliSessStorePollOff` (vtable poll slot). -/
theorem sessStorePollPrev1_cli_at (W : CliHooks) {img : Obj.Image} {stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hstk : SessKit.storePollNeedX ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      (img.base + cliSessStorePollOff)
      (sessStorePollPrev1Spec E2E.HooksE.A0 img stk) := by
  have h := sessStorePollPrev1_cli W himg hstk
  rw [cliSessStorePoll_fnAddr] at h
  exact h

/-- CLI `SessionFiles::store_session` shim at `img.base + cliSessStoreShimOff`
(vtable method slot `+0x20`, boxing the future regardless of `previous_sessions`). -/
theorem sessStoreShim_cli_at (W : CliHooks) {img : Obj.Image} {stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hstk : SessKit.storeShimNeed ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      (img.base + cliSessStoreShimOff)
      (sessStoreShimSpec E2E.HooksE.A0 img stk) := by
  have hh := RunSkeleton.RunHooks.cli W img
  have hb : (img.base &&& 0xfff#64) = 0#64 := RunSkeleton.base_aligned himg
  have h := StoreShim.sessStoreShim_ok_of_deps hh.alloc hstk hb
  rw [cliSessStoreShim_fnAddr] at h
  exact h

/-- CLI `SessionFiles::store_session` future drop at `img.base + cliIdFutDropOff`
(vtable drop slot `+0x00`, no-op `ret` on the future box). -/
theorem sessStoreFutDrop_cli_at (W : CliHooks) (img : Obj.Image) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      (img.base + cliIdFutDropOff)
      futDropSpec :=
  cliIdFutDrop_ok_ext

/-- Filesystem preservation across `store_session` (and any trace-silent CLI call): since
`Dir::put` buffers in memory until `Stores::commit` (`sf.trace = s0.trace`), `TraceFsSound`
guarantees `sf.fs.files = s0.fs.files`. -/
theorem cli_steps_files_eq_of_trace_eq (W : CliHooks) {b : BitVec 64} {s0 sf : State}
    (hsteps : Steps (tripleRatchetProgAtExt b (cliExterns W)) s0 sf)
    (htr : sf.trace = s0.trace) :
    sf.fs.files = s0.fs.files :=
  (RunGlue.traceFsSound_cli W b).files_eq hsteps (evs := [])
    (by simp [htr]) NoFsEv.nil

/-- `FsInv` preservation across any CLI `Steps` (including `store_session`): follows from
`RunGlue.traceFsSound_cli` via `FsInv.of_steps`. -/
theorem cli_steps_fsInv (W : CliHooks) {b : BitVec 64} {F0 : FsFiles}
    {T0 : List TraceEvent} {s0 sf : State}
    (hinv : FsInv F0 T0 s0)
    (hsteps : Steps (tripleRatchetProgAtExt b (cliExterns W)) s0 sf) :
    FsInv F0 T0 sf :=
  hinv.of_steps (RunGlue.traceFsSound_cli W b) hsteps

/-- `FsInv` preservation across `store_session` (trace-silent specialization). -/
theorem cli_steps_fsInv_of_trace_eq (W : CliHooks) {b : BitVec 64} {F0 : FsFiles}
    {T0 : List TraceEvent} {s0 sf : State}
    (hinv : FsInv F0 T0 s0)
    (hsteps : Steps (tripleRatchetProgAtExt b (cliExterns W)) s0 sf)
    (_htr : sf.trace = s0.trace) :
    FsInv F0 T0 sf :=
  cli_steps_fsInv W hinv hsteps

/-- `DirGhost.changed` bound preservation under `d.put (addressText peer.val) bytes`: holds
for arbitrary serialized `bytes` (including `encodeRecordPrev1` / `encodeRecordPrev1Mem`),
and guarantees `addressText peer.val ∈ (d.put ...).changed.map Prod.fst` afterwards. -/
theorem changedLt_put_self {peer : AddrGhost} {d : DirGhost} (bytes : List (BitVec 8))
    (h : d.changed.length < 2 ^ 32 ∧
      (d.changed.length + 1 < 2 ^ 32 ∨ addressText peer.val ∈ d.changed.map Prod.fst)) :
    (d.put (addressText peer.val) bytes).changed.length < 2 ^ 32 ∧
      ((d.put (addressText peer.val) bytes).changed.length + 1 < 2 ^ 32 ∨
        addressText peer.val ∈ (d.put (addressText peer.val) bytes).changed.map Prod.fst) := by
  obtain ⟨hlt, hroom⟩ := h
  refine ⟨?_, Or.inr (KitInst.mem_setOrPush_self _ _ _)⟩
  show (DirGhost.setOrPush _ _ d.changed).length < 2 ^ 32
  rcases hroom with hroom | hmem
  · exact Nat.lt_of_le_of_lt (KitInst.setOrPush_length_le _ _ _) hroom
  · rw [KitInst.setOrPush_length_of_mem hmem]; exact hlt

/-! ## 5. Contract-backed instantiations (`CliExternsOk P A ext` & `AllocContractsX`) -/

attribute [local irreducible] Program.fnOff

private theorem serializeName_eq_recordSerializeName :
    E2E.Record.Serialization.serializeName = recordSerializeName := rfl

/-- `SessionRecord::serialize` (`serializePrev1BodySpecX`) from generic `AllocContractsX`. -/
theorem serializePrev1Body_of_allocContractsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordSerializeName)
      ((serializePrev1BodySpecX A).inImage img) :=
  serializeName_eq_recordSerializeName ▸ serializePrev1Body_ok_of_trAllocContractsX hC

/-- `SessionRecord::serialize` (`serializePrev1CanonSpecX`) from generic `AllocContractsX`. -/
theorem serializePrev1CanonX_of_allocContractsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordSerializeName)
      ((serializePrev1CanonSpecX A).inImage img) :=
  serializeName_eq_recordSerializeName ▸ serializePrev1CanonX_ok_of_trAllocContractsX hC

/-- `SessionRecord::serialize` (`SerializePrev1OkStmt`) from generic `AllocContractsX`. -/
theorem serializePrev1_of_allocContractsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsX img A ext) :
    SerializePrev1OkStmt img A ext :=
  serializePrev1_ok_of_trAllocContractsX hC

/-- `SessionRecord::serialize` (`serializePrev1BodySpecX`) instantiated from `CliExternsOk P A ext`. -/
theorem serializePrev1Body_ext {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr recordSerializeName)
      ((serializePrev1BodySpecX A).inImage img) :=
  serializePrev1Body_of_allocContractsX (MainHops.AllocContractsX.of_externsOk hOk img)

/-- `SessionRecord::serialize` (`serializePrev1CanonSpecX`) instantiated from `CliExternsOk P A ext`. -/
theorem serializePrev1CanonX_ext {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr recordSerializeName)
      ((serializePrev1CanonSpecX A).inImage img) :=
  serializePrev1CanonX_of_allocContractsX (MainHops.AllocContractsX.of_externsOk hOk img)

/-- `SessionRecord::serialize` (`SerializePrev1OkStmt`) instantiated from `CliExternsOk P A ext`. -/
theorem serializePrev1_ext {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    SerializePrev1OkStmt img A (cliExternsWith ext) :=
  serializePrev1_ok_of_trAllocContractsX (MainHops.AllocContractsX.of_externsOk hOk img)

/-- Generic `SessionFiles::store_session::{closure#0}` on a `Prev1` record from minimal hook
contracts (`AllocContractsX` and `bcmp`). -/
theorem sessStorePollPrev1Mem_of_hooks {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    (hC : AllocContractsX img A ext)
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (himg : Obj.Loads libsignalSessionImage img)
    (hstk : SessKit.storePollNeedX ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessStorePollName)
      (sessStorePollPrev1MemSpec A img stk) := by
  have hb : (img.base &&& 0xfff#64) = 0#64 := RunSkeleton.base_aligned himg
  have hRes := MainHops.cliDoReserve_ok hC (Nat.le_refl doReserveStackX)
  have hDec := Decimal.decimal_ok_of_deps hRes (Nat.le_refl SessKit.decNeed) hb
  have hAddr := AddressText.addressText_ok_of_deps hC hRes hDec
    (Nat.le_refl SessKit.addrTextNeed) hb
  have hGrow := GrowOne.growOneDir_ok_x hC (Nat.le_refl SessKit.growOneDirNeed) hb
  have hPut := Put.dirPut_ok_of_deps hC hBcmp hGrow (Nat.le_refl SessKit.dirPutNeed) hb
  exact sessStorePollPrev1Mem_ok_of_deps hAddr (serializePrev1Body_of_allocContractsX hC) hPut hstk

/-- `SessionFiles::store_session::{closure#0}` on a `Prev1` record (`encodeRecordPrev1Mem`)
from `CliExternsOk P A ext` at `fnAddr sessStorePollName`. -/
theorem sessStorePollPrev1Mem_ext {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext)
    {img : Obj.Image} {stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hstk : SessKit.storePollNeedX ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr sessStorePollName)
      (sessStorePollPrev1MemSpec A img stk) :=
  sessStorePollPrev1Mem_of_hooks (MainHops.AllocContractsX.of_externsOk hOk img)
    (RunGlue.hookSat_bcmp_cliExternsWith hOk) himg hstk

/-- `SessionFiles::store_session::{closure#0}` on a `Prev1` record (`encodeRecordPrev1Mem`)
from `CliExternsOk P A ext` at `img.base + cliSessStorePollOff` (vtable poll slot). -/
theorem sessStorePollPrev1Mem_ext_at {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext)
    {img : Obj.Image} {stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hstk : SessKit.storePollNeedX ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      (img.base + cliSessStorePollOff)
      (sessStorePollPrev1MemSpec A img stk) := by
  have h := sessStorePollPrev1Mem_ext hOk himg hstk
  rw [cliSessStorePoll_fnAddr] at h
  exact h

/-- `SessionFiles::store_session::{closure#0}` on a canonical `Prev1` record (`encodeRecordPrev1`)
from `CliExternsOk P A ext` at `fnAddr sessStorePollName`. -/
theorem sessStorePollPrev1_ext {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext)
    {img : Obj.Image} {stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hstk : SessKit.storePollNeedX ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr sessStorePollName)
      (sessStorePollPrev1Spec A img stk) :=
  sessStorePollPrev1_of_mem (sessStorePollPrev1Mem_ext hOk himg hstk)

/-- `SessionFiles::store_session::{closure#0}` on a canonical `Prev1` record (`encodeRecordPrev1`)
from `CliExternsOk P A ext` at `img.base + cliSessStorePollOff` (vtable poll slot). -/
theorem sessStorePollPrev1_ext_at {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext)
    {img : Obj.Image} {stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hstk : SessKit.storePollNeedX ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      (img.base + cliSessStorePollOff)
      (sessStorePollPrev1Spec A img stk) := by
  have h := sessStorePollPrev1_ext hOk himg hstk
  rw [cliSessStorePoll_fnAddr] at h
  exact h

/-- `SessionFiles::store_session` shim from `CliExternsOk P A ext` at
`img.base + cliSessStoreShimOff` (vtable method slot `+0x20`). -/
theorem sessStoreShim_ext_at {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext)
    {img : Obj.Image} {stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hstk : SessKit.storeShimNeed ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      (img.base + cliSessStoreShimOff)
      (sessStoreShimSpec A img stk) := by
  have hb : (img.base &&& 0xfff#64) = 0#64 := RunSkeleton.base_aligned himg
  have h := StoreShim.sessStoreShim_ok_of_deps
    (MainHops.AllocContractsX.of_externsOk hOk img) hstk hb
  rw [cliSessStoreShim_fnAddr] at h
  exact h

/-- `SessionFiles::store_session` future drop at `img.base + cliIdFutDropOff`
on `cliExternsWith ext`. -/
theorem sessStoreFutDrop_ext_at {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (_hOk : CliExternsOk P A ext) (img : Obj.Image) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      (img.base + cliIdFutDropOff)
      futDropSpec :=
  cliIdFutDrop_ok_ext

/-- Filesystem preservation across any trace-silent `cliExternsWith ext` call from
`CliExternsOk P A ext`. -/
theorem ext_steps_files_eq_of_trace_eq {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext)
    {b : BitVec 64} {s0 sf : State}
    (hsteps : Steps (tripleRatchetProgAtExt b (cliExternsWith ext)) s0 sf)
    (htr : sf.trace = s0.trace) :
    sf.fs.files = s0.fs.files :=
  (RunGlue.traceFsSound_cliExternsWith hOk b).files_eq hsteps (evs := [])
    (by simp [htr]) NoFsEv.nil

/-- `FsInv` preservation across any `cliExternsWith ext` `Steps` from `CliExternsOk P A ext`. -/
theorem ext_steps_fsInv {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext)
    {b : BitVec 64} {F0 : FsFiles} {T0 : List TraceEvent} {s0 sf : State}
    (hinv : FsInv F0 T0 s0)
    (hsteps : Steps (tripleRatchetProgAtExt b (cliExternsWith ext)) s0 sf) :
    FsInv F0 T0 sf :=
  hinv.of_steps (RunGlue.traceFsSound_cliExternsWith hOk b) hsteps

/-- `FsInv` preservation across `store_session` on `cliExternsWith ext` (trace-silent). -/
theorem ext_steps_fsInv_of_trace_eq {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext)
    {b : BitVec 64} {F0 : FsFiles} {T0 : List TraceEvent} {s0 sf : State}
    (hinv : FsInv F0 T0 s0)
    (hsteps : Steps (tripleRatchetProgAtExt b (cliExternsWith ext)) s0 sf)
    (_htr : sf.trace = s0.trace) :
    FsInv F0 T0 sf :=
  ext_steps_fsInv hOk hinv hsteps

/-- Filesystem preservation across any trace-silent raw `ext` call from `CliExternsOk P A ext`. -/
theorem rawExt_steps_files_eq_of_trace_eq {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext)
    {b : BitVec 64} {s0 sf : State}
    (hsteps : Steps (tripleRatchetProgAtExt b ext) s0 sf)
    (htr : sf.trace = s0.trace) :
    sf.fs.files = s0.fs.files :=
  (RunGlue.traceFsSound_of_ok hOk b).files_eq hsteps (evs := [])
    (by simp [htr]) NoFsEv.nil

/-- `FsInv` preservation across any raw `ext` `Steps` from `CliExternsOk P A ext`. -/
theorem rawExt_steps_fsInv {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext)
    {b : BitVec 64} {F0 : FsFiles} {T0 : List TraceEvent} {s0 sf : State}
    (hinv : FsInv F0 T0 s0)
    (hsteps : Steps (tripleRatchetProgAtExt b ext) s0 sf) :
    FsInv F0 T0 sf :=
  hinv.of_steps (RunGlue.traceFsSound_of_ok hOk b) hsteps

end CryptoVerification.SignalSession.Cli.Store.StoreSessionPrev1
