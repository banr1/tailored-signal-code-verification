/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Session
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsX
public import LibsignalBinary.Proofs.E2E.InMem.SessionStoreImpl.ReprBridge
public import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeHeap
import LibsignalBinary.Proofs.Common.InImageKit

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.StorePollX.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoGames.LibsignalSessionApi
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

theorem recordSerialize_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr recordSerializeName =
      (tripleRatchetProgAtExt b ext).fnAddr sessStorePollName -
        bv% (ls_rel% "<libsignal_protocol::state::session::SessionRecord>::serialize"
          "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") := by
  have h1 := sessStorePoll_fnOff
  have h2 := recordSerialize_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, sessStorePollName,
    recordSerializeName, h1, h2]
  bv_omega

theorem dirPut_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr dirPutName =
      (tripleRatchetProgAtExt b ext).fnAddr sessStorePollName -
        bv% (ls_rel% "<libsignal_cli::stores::Dir>::put::<alloc::string::String>"
          "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") := by
  have h1 := sessStorePoll_fnOff
  have h2 := dirPut_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, sessStorePollName,
    dirPutName, h1, h2]
  bv_omega

theorem canonRecord_of_satisfies_sessionRecordAt (A : RustAlloc) (a : BitVec 64)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) (R : SepProp) (m : Memory)
    (hm : m ⊨ sessionRecordAt A a g r ∗ R) :
    E2E.Record.Serialization.CanonRecord (E2E.InMem.SessionStoreImpl.toRecordGhost g) r := by
  unfold sessionRecordAt at hm
  rw [sepConj_assoc] at hm
  have hcur := Satisfies.of_sep_right hm
  cases hg : g.cur <;> cases hr : r.currentSession
  · unfold E2E.Record.Serialization.CanonRecord E2E.Record.Serialization.CanonCur
      E2E.InMem.SessionStoreImpl.toRecordGhost
    simp [hg, hr]
  · rw [hg, hr] at hcur
    dsimp only at hcur
    exact (not_satisfies_false_sepConj hcur).elim
  · rw [hg, hr] at hcur
    dsimp only at hcur
    exact (not_satisfies_false_sepConj hcur).elim
  · rename_i G s
    rw [hg, hr] at hcur
    dsimp only at hcur
    unfold E2E.Record.Serialization.CanonRecord E2E.Record.Serialization.CanonCur
      E2E.InMem.SessionStoreImpl.toRecordGhost
    dsimp only
    rw [hg, hr]
    exact E2E.InMem.SessionStoreImpl.canonSession_of_satisfies_sessionAt A (a + 0x18#64) G s m
      (Satisfies.of_sep_left hcur)

theorem memRegion_bound_of_pointsTo64 {m : Memory} {b a v : BitVec 64} {n : Nat} {R : SepProp}
    (h : m ⊨ memRegion b n ∗ ((a ↦₆₄ v) ∗ R)) : n ≤ 2 ^ 64 := by
  by_cases hn0 : n = 0
  · omega
  · have hd := disjointRegions_of_coversRegion (Nat.pos_of_ne_zero hn0) (by decide)
      (IsBlock.memRegion b n).covers (IsBlock.pointsTo64 a v).covers h
    have h1 := hd.1
    omega

theorem stackAt_sub_split (sp : BitVec 64) {subStk topStk : Nat}
    (hle : subStk ≤ topStk) (hhi : topStk ≤ 2 ^ 64) :
    stackAt sp topStk =
      memRegion (sp - BitVec.ofNat 64 topStk) (topStk - subStk) ∗ stackAt sp subStk := by
  have heq : topStk = subStk + (topStk - subStk) := by omega
  conv_lhs => rw [heq]
  rw [ProofLib.stackAt_split_bottom sp subStk (topStk - subStk) (by omega), ← heq]

theorem stackAt_storePoll_frame (sp : BitVec 64) {calleeStk : Nat}
    (hhi : calleeStk + 208 ≤ 2 ^ 64) :
    stackAt sp (calleeStk + 208) =
      stackAt (sp - 208#64) calleeStk ∗ cells (sp - 208#64) 26 :=
  ProofLib.stackAt_split_cells sp calleeStk 26 hhi

theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_32_cells (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        (a ↦₆₄ v3) ∗ ((a + 8#64) ↦₆₄ v2) ∗ ((a + 16#64) ↦₆₄ v1) ∗ ((a + 24#64) ↦₆₄ v0)) := by
  rw [show (32 : Nat) = 8 + 24 by rfl, memRegion_split a 8 24 (by decide),
    ProofLib.memRegion_eight, memRegion_24_cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_40_cells (a : BitVec 64) :
    memRegion a 40 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64,
        (a ↦₆₄ v4) ∗ ((a + 8#64) ↦₆₄ v3) ∗ ((a + 16#64) ↦₆₄ v2) ∗
        ((a + 24#64) ↦₆₄ v1) ∗ ((a + 32#64) ↦₆₄ v0)) := by
  rw [show (40 : Nat) = 8 + 32 by rfl, memRegion_split a 8 32 (by decide),
    ProofLib.memRegion_eight, memRegion_32_cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_48_cells (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        (a ↦₆₄ v5) ∗ ((a + 8#64) ↦₆₄ v4) ∗ ((a + 16#64) ↦₆₄ v3) ∗
        ((a + 24#64) ↦₆₄ v2) ∗ ((a + 32#64) ↦₆₄ v1) ∗ ((a + 40#64) ↦₆₄ v0)) := by
  rw [show (48 : Nat) = 8 + 40 by rfl, memRegion_split a 8 40 (by decide),
    ProofLib.memRegion_eight, memRegion_40_cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem vecU8_intro (A : RustAlloc) (v bCap bPtr : BitVec 64) (bs : List (BitVec 8)) :
    ((v ↦₆₄ bCap) ∗ ((v + 8#64) ↦₆₄ bPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
      SpqrV1.Alloc.vecU8Buf A bCap bPtr bs ⊢ vecU8 A v bs := by
  have heq :
      ((v ↦₆₄ bCap) ∗ ((v + 8#64) ↦₆₄ bPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
        SpqrV1.Alloc.vecU8Buf A bCap bPtr bs =
      vecU8At A v bCap bPtr bs := by
    rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
    rfl
  rw [heq]
  exact Entails.sepExists_right bCap (Entails.sepExists_right bPtr (Entails.refl _))

abbrev AddrCellsGhost :=
  BitVec 64 × AddrGhost × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

def addrTextCellsSpec (A : RustAlloc) (calleeStk : Nat) : Spec AddrCellsGhost where
  pre := fun (addrA, g, ret, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = addrA ∧ s.sp = fsp ∧
      g.name.bytes.length < 2 ^ 32⌝ ∗
    protocolAddressAt A g addrA ∗
    (ret ↦₆₄ o0) ∗ ((ret + 8#64) ↦₆₄ o1) ∗ ((ret + 16#64) ↦₆₄ o2) ∗
    stackAt fsp calleeStk ∗ A.pool
  post := fun (addrA, g, ret, _o0, _o1, _o2, fsp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ vecU8 A ret (addressText g.val) ∗
    protocolAddressAt A g addrA ∗ stackAt fsp calleeStk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem addrText_cells_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {addrStk calleeStk : Nat}
    (hAddr : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressTextName)
      (addrTextSpec A img addrStk))
    (hle : addrStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressTextName)
      ((addrTextCellsSpec A calleeStk).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨addrA, g, ret, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (addrTextCellsSpec A calleeStk).pre (addrA, g, ret, o0, o1, o2, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [addrTextCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfsp, hlen⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - addrStk)
  let callG : AddrTextGhost := ⟨addrA, g, ret⟩
  have hpre0 : s0.mem ⊨ (addrTextSpec A img addrStk).pre callG s0 ∗ (stkRem ∗ R) := by
    dsimp only [addrTextSpec, callG]
    refine satisfies_inImage_pre hinv ?_
    simp only [memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hlen⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  refine hAddr.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, addrTextSpec, addrTextCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, addrTextSpec, addrTextCellsSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [addrTextSpec, Spec.inImage] at hq
    exact (not_satisfies_false_sepConj hq).elim

abbrev SerCellsGhost :=
  BitVec 64 × BitVec 64 × E2E.Record.RecordGhost × SessionRecord (List (BitVec 8)) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

def serializeCellsSpec (A : RustAlloc) (calleeStk : Nat) : Spec SerCellsGhost where
  pre := fun (recA, out, g, r, o0, o1, o2, o3, fsp) s =>
    ⌜s.readReg64 .x0 = recA ∧ s.readReg64 .x8 = out ∧ s.sp = fsp ∧
      E2E.Record.Serialization.CanonRecord g r ∧
      (E2E.Record.encodeRecord r).length < 2 ^ 32⌝ ∗
    E2E.Record.sessionRecordAt A recA g r ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗ ((out + 24#64) ↦₆₄ o3) ∗
    A.pool ∗ stackAt fsp calleeStk
  post := fun (recA, out, g, r, _o0, _o1, _o2, _o3, fsp) s0 sf =>
    ∃∗ bCap : BitVec 64, ∃∗ bPtr : BitVec 64,
      ⌜sf.trace = s0.trace⌝ ∗ E2E.Record.sessionRecordAt A recA g r ∗
      (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
      ((out + 8#64) ↦₆₄ bCap) ∗ ((out + 16#64) ↦₆₄ bPtr) ∗
      ((out + 24#64) ↦₆₄ BitVec.ofNat 64 (E2E.Record.encodeRecord r).length) ∗
      SpqrV1.Alloc.vecU8Buf A bCap bPtr (E2E.Record.encodeRecord r) ∗
      A.pool ∗ stackAt fsp calleeStk
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem serialize_cells_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {calleeStk : Nat}
    (hSer : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordSerializeName)
      ((Proofs.libsignal.Hooks2.serializeCanonSpecX A).inImage img))
    (hle : Proofs.libsignal.Hooks2.serializeStackX ≤ calleeStk)
    (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordSerializeName)
      ((serializeCellsSpec A calleeStk).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨recA, out, g, r, o0, o1, o2, o3, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (serializeCellsSpec A calleeStk).pre (recA, out, g, r, o0, o1, o2, o3, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [serializeCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hfsp, hcanon, hlen⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk)
    (calleeStk - Proofs.libsignal.Hooks2.serializeStackX)
  let callG : E2E.Record.Serialization.SerializeGhost := ⟨recA, out, g, r⟩
  have hpre0 : s0.mem ⊨ ((Proofs.libsignal.Hooks2.serializeCanonSpecX A).inImage img).pre
      callG s0 ∗ (stkRem ∗ R) := by
    refine satisfies_inImage_pre hinv ?_
    dsimp only [Proofs.libsignal.Hooks2.serializeCanonSpecX, callG]
    simp only [memRegion_32_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o3, o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hcanon, hlen⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  refine hSer.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, Proofs.libsignal.Hooks2.serializeCanonSpecX,
      serializeCellsSpec, callG] at hq ⊢
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
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [okTagVec, stkRem] at hq
    convert hq using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, Proofs.libsignal.Hooks2.serializeCanonSpecX,
      E2E.Record.Serialization.allocPanic, serializeCellsSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [Spec.inImage] at hq
    exact (not_satisfies_false_sepConj hq).elim

abbrev PutCellsGhost :=
  BitVec 64 × DirGhost × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64

def dirPutCellsSpec (A : RustAlloc) (calleeStk : Nat) : Spec PutCellsGhost where
  pre := fun (self, dir, nameV, name, bytesV, bCap, bPtr, bytes, fsp) s =>
    ⌜s.readReg64 .x0 = self ∧ s.readReg64 .x1 = nameV ∧ s.readReg64 .x2 = bytesV ∧
      s.sp = fsp ∧ dir.changed.length < 2 ^ 32⌝ ∗
    dirAt A self dir ∗ vecU8 A nameV name ∗
    (bytesV ↦₆₄ bCap) ∗ ((bytesV + 8#64) ↦₆₄ bPtr) ∗
    ((bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 bytes.length) ∗
    SpqrV1.Alloc.vecU8Buf A bCap bPtr bytes ∗
    stackAt fsp calleeStk ∗ A.pool
  post := fun (self, dir, nameV, name, bytesV, _bCap, _bPtr, bytes, fsp) s0 sf =>
    ∃∗ n0 : BitVec 64, ∃∗ n1 : BitVec 64, ∃∗ n2 : BitVec 64,
    ∃∗ m0 : BitVec 64, ∃∗ m1 : BitVec 64, ∃∗ m2 : BitVec 64,
      ⌜sf.trace = s0.trace⌝ ∗ dirAt A self (dir.put name bytes) ∗
      (nameV ↦₆₄ n0) ∗ ((nameV + 8#64) ↦₆₄ n1) ∗ ((nameV + 16#64) ↦₆₄ n2) ∗
      (bytesV ↦₆₄ m0) ∗ ((bytesV + 8#64) ↦₆₄ m1) ∗ ((bytesV + 16#64) ↦₆₄ m2) ∗
      stackAt fsp calleeStk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem dirPut_cells_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {putStk calleeStk : Nat}
    (hPut : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName)
      (dirPutSpec A img putStk))
    (hle : putStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName)
      ((dirPutCellsSpec A calleeStk).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨self, dir, nameV, name, bytesV, bCap, bPtr, bytes, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (dirPutCellsSpec A calleeStk).pre (self, dir, nameV, name, bytesV, bCap, bPtr, bytes, fsp) s0) ∗
    R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [dirPutCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hfsp, hlen⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - putStk)
  let callG : DirPutGhost := ⟨self, dir, nameV, name, bytesV, bytes⟩
  have hmem_vec : s0.mem ⊨ vecU8 A bytesV bytes ∗
      (dirAt A self dir ∗ vecU8 A nameV name ∗ stackAt s0.sp putStk ∗ A.pool ∗ stkRem ∗ R) := by
    refine Satisfies.mono (sepConj_mono_left (vecU8_intro A bytesV bCap bPtr bytes)) ?_
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  have hpre0 : s0.mem ⊨ (dirPutSpec A img putStk).pre callG s0 ∗ (stkRem ∗ R) := by
    dsimp only [dirPutSpec, Spec.inImage, callG]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen⟩, ?_⟩
    convert hmem_vec using 1; ac_rfl
  refine hPut.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, dirPutSpec, dirPutCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    simp only [memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists] at hq ⊢
    rcases hq with ⟨m2, m1, m0, n2, n1, n0, hq⟩
    refine ⟨n0, n1, n2, m0, m1, m2, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, dirPutSpec, dirPutCellsSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [dirPutSpec, Spec.inImage] at hq
    exact (not_satisfies_false_sepConj hq).elim

def cliStorePollInnerSpec (A : RustAlloc) (calleeStk : Nat) : Spec SessStorePollGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.call.fut ∧ s.readReg64 .x8 = x.call.out ∧
      x.call.call.addr.name.bytes.length < 2 ^ 32 ∧
      (E2E.Record.encodeRecord x.call.call.record).length < 2 ^ 32 ∧
      x.dir.changed.length < 2 ^ 32 ∧
      E2E.Record.Serialization.CanonRecord (E2E.InMem.SessionStoreImpl.toRecordGhost x.call.call.g)
        x.call.call.record⌝ ∗
      (x.call.fut ↦₆₄ x.self) ∗ ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
      ((x.call.fut + 16#64) ↦₆₄ x.call.call.recA) ∗ ((x.call.fut + 24#64) ↦₈ 0#8) ∗
      dirAt A x.self x.dir ∗ memRegion x.call.out 48 ∗
      protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
      E2E.Record.sessionRecordAt A x.call.call.recA
        (E2E.InMem.SessionStoreImpl.toRecordGhost x.call.call.g) x.call.call.record ∗
      A.pool ∗ stackAt (s.sp - 208#64) calleeStk ∗ cells (s.sp - 208#64) 26
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.call.fut ↦₆₄ x.self) ∗ ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
      ((x.call.fut + 16#64) ↦₆₄ x.call.call.recA) ∗ ((x.call.fut + 24#64) ↦₈ 1#8) ∗
      dirAt A x.self (x.dir.put (addressText x.call.call.addr.val)
        (E2E.Record.encodeRecord x.call.call.record)) ∗
      (x.call.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (x.call.out + 8#64) 40 ∗
      protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
      E2E.Record.sessionRecordAt A x.call.call.recA
        (E2E.InMem.SessionStoreImpl.toRecordGhost x.call.call.g) x.call.call.record ∗
      A.pool ∗ stackAt (s0.sp - 208#64) calleeStk ∗ cells (s0.sp - 208#64) 26
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem sessStorePoll_of_inner {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {calleeStk stk : Nat}
    (hInner : calleeStk ≤ 2 ^ 64 →
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr sessStorePollName)
        ((cliStorePollInnerSpec A calleeStk).inImage img))
    (hstk : 0xd0 + calleeStk ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessStorePollName)
      (sessStorePollSpec A img stk) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (⌜s0.readReg64 .x0 = x.call.fut ∧ s0.readReg64 .x8 = x.call.out ∧
      x.call.call.addr.name.bytes.length < 2 ^ 32 ∧
      (E2E.Record.encodeRecord x.call.call.record).length < 2 ^ 32 ∧
      x.dir.changed.length < 2 ^ 32⌝ ∗
      sessStoreBoxAt x.call.fut x.self x.call.call.addrA x.call.call.recA 0#8 ∗
      dirAt A x.self x.dir ∗ memRegion x.call.out 48 ∗
      protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
      sessionRecordAt A x.call.call.recA x.call.call.g x.call.call.record ∗
      A.pool ∗ stackAt s0.sp stk)) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hname, henc, hdir⟩, hmem⟩
  dsimp only [sessStoreBoxAt] at hmem
  have hcanon : E2E.Record.Serialization.CanonRecord
      (E2E.InMem.SessionStoreImpl.toRecordGhost x.call.call.g) x.call.call.record := by
    refine canonRecord_of_satisfies_sessionRecordAt A x.call.call.recA
      x.call.call.g x.call.call.record
      ((x.call.fut ↦₆₄ x.self) ∗ ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
        ((x.call.fut + 16#64) ↦₆₄ x.call.call.recA) ∗ ((x.call.fut + 24#64) ↦₈ 0#8) ∗
        memRegion (x.call.fut + 25#64) 7 ∗
        dirAt A x.self x.dir ∗ memRegion x.call.out 48 ∗
        protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
        A.pool ∗ stackAt s0.sp stk ∗ R) s0.mem ?_
    convert hmem using 1; ac_rfl
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64 (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.call.fut) (v := x.self)
      (R := ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
        ((x.call.fut + 16#64) ↦₆₄ x.call.call.recA) ∗ ((x.call.fut + 24#64) ↦₈ 0#8) ∗
        memRegion (x.call.fut + 25#64) 7 ∗
        dirAt A x.self x.dir ∗ memRegion x.call.out 48 ∗
        protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
        sessionRecordAt A x.call.call.recA x.call.call.g x.call.call.record ∗
        A.pool ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; ac_rfl
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 208 ≤ 2 ^ 64 := by omega
  rw [← E2E.InMem.SessionStoreImpl.record_sessionRecordAt_eq] at hmem
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 208) (by omega) hstk_hi,
    stackAt_storePoll_frame s0.sp hframe_hi] at hmem
  let F_extra := memRegion (x.call.fut + 25#64) 7 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 208))
  have hpre_in : s0.mem ⊨ ((cliStorePollInnerSpec A calleeStk).inImage img).pre x s0 ∗
      (F_extra ∗ R) := by
    refine satisfies_inImage_pre hinv ?_
    dsimp only [cliStorePollInnerSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hname, henc, hdir, hcanon⟩, ?_⟩
    dsimp only [F_extra]
    convert hmem using 1; ac_rfl
  refine (hInner hcal_hi).mono_outcome x (F_extra ∗ R) s0 hpc hrun hpre_in hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, cliStorePollInnerSpec, sessStorePollSpec, sessStoreBoxAt] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    refine ⟨htr, ?_⟩
    rw [E2E.InMem.SessionStoreImpl.record_sessionRecordAt_eq] at hq
    rw [stackAt_sub_split s0.sp (subStk := calleeStk + 208) (by omega) hstk_hi,
      stackAt_storePoll_frame s0.sp hframe_hi]
    dsimp only [F_extra] at hq
    convert hq using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, cliStorePollInnerSpec, sessStorePollSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [Spec.inImage] at hq
    exact (not_satisfies_false_sepConj hq).elim

end CryptoVerification.SignalSession.Cli.Store.StorePollX.Helpers
