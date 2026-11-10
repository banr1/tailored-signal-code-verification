/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Support.Image
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymB
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymD
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymE
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymF
public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.FromRecordCalleesCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.Canon
import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLen
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChain
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRaw
import LibsignalBinary.Proofs.E2E.Record.Serialization.MsgKeyLen
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBody
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionClone
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLen
import LibsignalBinary.Proofs.E2E.Record.Serialization.VecVecClone
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local1
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.VecExt
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Ext
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarint

/-!
# Top-level assembly for `SessionRecord::serialize` (`0x1857c`)

Combines the serialization leaf contracts into `serialize_ok` (`serializeSpec`), refines it on
canonical records via `encRecordMem_eq_of_canon` (`serializeCanon_ok`, `serializeCanon_root`), and
provides the relocatable `[LibsignalPlacement]` counterparts on block `52`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-- `SessionRecord::serialize` (`0x1857c`) satisfies `serializeSpec` given `AllocHooks A abs`. -/
theorem serialize_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    OkAt b C ctl abs serializeName (serializeSpec A) := by
  have hDR : OkAt b C ctl abs doReserveName (doReserveSpec A) := do_reserve_ok hA
  have hEV : Prost.EncodeVarintOk b C A ctl abs :=
    Prost.encodeVarint_ok b C A ctl abs hDR
  have hmk := msgKeyLen_ok b C A ctl abs
  have hchain := chainLen_ok b C A ctl abs hmk
  exact serialize_ok_of_leaves b C A ctl abs hA
    (sessionClone_ok b C A ctl abs hA)
    (vecVecCloneEmpty_ok b C ctl abs)
    (sessionLen_ok b C A ctl abs hchain)
    hEV
    (encodeRaw_ok b C A ctl abs hEV hDR
      (encodeChain_ok b C A ctl abs hEV hDR hchain hmk))
    hDR
    (FromRecordCallees.drop_session_structure_local1_ok hA (Getters.drop_vec_message_key_ok hA)
      (Getters.drop_vec_chain_ok hA))

/-- Refines `serializeSpec` to `serializeCanonSpec` on canonical records via `encRecordMem_eq_of_canon`. -/
theorem serializeCanon_of_serialize (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (h : OkAt b C ctl abs serializeName (serializeSpec A)) :
    OkAt b C ctl abs serializeName (serializeCanonSpec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hp hsp_align => ?_
  have hp' := hp
  simp only [serializeCanonSpec] at hp'
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp'
  obtain ⟨⟨h0, h8, hcanon, hlen⟩, hrest⟩ := hp'
  have henc := encRecordMem_eq_of_canon x.g x.r hcanon
  have hpre : s0.mem ⊨ (serializeSpec A).pre x s0 ∗ R := by
    simp only [serializeSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨h0, h8, henc ▸ hlen⟩, hrest⟩
  refine h.mono_outcome x R s0 hpc hrun hpre hsp_align fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [serializeSpec, serializeCanonSpec, henc] using hq
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

/-- `SessionRecord::serialize` on a canonical record satisfies `serializeCanonSpec` on `tripleRatchetProgAt`. -/
theorem serializeCanon_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    OkAt b C ctl abs serializeName (serializeCanonSpec A) :=
  serializeCanon_of_serialize b C A ctl abs (serialize_ok b C A ctl abs hA)

/-- `SessionRecord::serialize` on a canonical record satisfies `serializeCanonSpec` on `tripleRatchetProg sessionImg0`. -/
theorem serializeCanon_root (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProg E2E.Record.sessionImg0 C ctl abs)
      (entryOf E2E.Record.sessionImg0 serializeName) (serializeCanonSpec A) :=
  root_of_tripleRatchetProgAt E2E.Record.loads_sessionImg0 (serializeCanon_ok _ C A ctl abs hA)

/-! ## Relocatable `[LibsignalPlacement]` assembly (block `52`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

/-- Block-level callee contracts required by `SessionRecord::serialize` (block `52`). -/
structure PlacedSerializeCallees [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop where
  sessionClone : subroutine_ok (lsProg_80 H) (blkPl_80).base
    (withLsCodeLoaded lsmpl (sessionCloneSpec A))
  vecVecClone : subroutine_ok (lsProg_117 H) (blkPl_117).base vecVecCloneEmptySpec
  sessionLen : subroutine_ok (lsProg_86 H) (blkPl_86).base
    (withLsCodeLoaded lsmpl (sessionLenSpec A))
  encodeVarint : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
    (withLsCodeLoaded lsmpl (Prost.encodeVarintSpec A))
  encodeRaw : subroutine_ok (lsProg_14 H) (blkPl_14).base
    (withLsCodeLoaded lsmpl (encodeRawSpec A))
  dropSessionStructureLocal1 : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H) (blkPl_6).base
    (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal1Spec A))

theorem placedSerializeCallees_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} (hH : PlacedSerializeHooks A H) :
    PlacedSerializeCallees A H where
  sessionClone := sessionClone_placed_ok_of_hooks hH
  vecVecClone := vecVecCloneEmpty_placed_ok H
  sessionLen := sessionLen_placed_ok A H
  encodeVarint := Prost.encode_varint_placed_ok hH.shim hH.alloc hH.realloc hH.panic_handle_error
  encodeRaw := encodeRaw_placed_ok_of_hooks hH
  dropSessionStructureLocal1 := FromRecordCallees.drop_session_structure_local1_placed_ok hH.dealloc

/-- Relocatable `SessionRecord::serialize` (block `52`) from `PlacedSerializeCallees` and direct external hooks. -/
theorem serialize_placed_ok_of_callee_bundle [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym LibsignalTripleRatchet.sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hC : PlacedSerializeCallees A H) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base (withLsCodeLoaded lsmpl (serializeSpec A)) :=
  serialize_placed_ok_of_callees hshim halloc hmemcpy hpanic
    hC.sessionClone hC.vecVecClone hC.sessionLen
    hC.encodeVarint hC.encodeRaw hC.dropSessionStructureLocal1

/-- Relocatable `SessionRecord::serialize` (block `52`) satisfies `withLsCodeLoaded lsmpl (serializeSpec A)`. -/
theorem serialize_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym LibsignalTripleRatchet.sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base (withLsCodeLoaded lsmpl (serializeSpec A)) :=
  serialize_placed_ok_of_callees
    hshim halloc hmemcpy hpanic
    (sessionClone_placed_ok hshim halloc hmemcpy hpanic)
    (vecVecCloneEmpty_placed_ok H)
    (sessionLen_placed_ok A H)
    (Prost.encode_varint_placed_ok hshim halloc hrealloc hpanic)
    (encodeRaw_placed_ok hshim halloc hrealloc hmemcpy hpanic)
    (FromRecordCallees.drop_session_structure_local1_placed_ok hdealloc)

/-- Relocatable `SessionRecord::serialize` (block `52`) from `PlacedSerializeHooks`. -/
theorem serialize_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hH : PlacedSerializeHooks A H) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base (withLsCodeLoaded lsmpl (serializeSpec A)) :=
  serialize_placed_ok hH.shim hH.alloc hH.realloc hH.dealloc hH.memcpy hH.panic_handle_error

/-- Lifts `withLsCodeLoaded pl (serializeSpec A)` to `serializeCanonSpec A` on canonical records. -/
theorem serializeCanon_of_serialize_placed {prog : Program} {pl : MultiPlacement}
    {entry : BitVec 64} {A : RustAlloc}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl (serializeSpec A))) :
    subroutine_ok prog entry (withLsCodeLoaded pl (serializeCanonSpec A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hp hsp_align => ?_
  have hp0 := hp
  dsimp only [withLsCodeLoaded] at hp0
  rw [sepConj_assoc, sepConj_left_comm ((serializeCanonSpec A).pre x s0),
    satisfies_pure_sepConj] at hp0
  obtain ⟨hcl0, hp'⟩ := hp0
  simp only [serializeCanonSpec] at hp'
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp'
  obtain ⟨⟨h0, h8, hcanon, hlen⟩, hrest⟩ := hp'
  have henc := encRecordMem_eq_of_canon x.g x.r hcanon
  have hpre : s0.mem ⊨ (withLsCodeLoaded pl (serializeSpec A)).pre x s0 ∗ R := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm ((serializeSpec A).pre x s0),
      satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    simp only [serializeSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨h0, h8, henc ▸ hlen⟩, hrest⟩
  refine h.mono_outcome x R s0 hpc hrun hpre hsp_align fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [serializeSpec, serializeCanonSpec, henc] using hq
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

/-- Canonical relocatable `SessionRecord::serialize` (block `52`) from caller-program callee contracts. -/
theorem serializeCanon_placed_ok_of_caller_callees [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok (lsProg_52 H) (lsρ lsRustNoAllocShimSym)
      LibsignalTripleRatchet.sessionShimSpec)
    (halloc : subroutine_ok (lsProg_52 H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok (lsProg_52 H) (lsρ lsMemcpySym) framelessMemcpySpec)
    (hpanic : (lsProg_52 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked)
    (hClone : subroutine_ok (lsProg_52 H) (blkPl_80).base
      (withLsCodeLoaded lsmpl (sessionCloneSpec A)))
    (hVV : subroutine_ok (lsProg_52 H) (blkPl_117).base
      (withLsCodeLoaded lsmpl vecVecCloneEmptySpec))
    (hLen : subroutine_ok (lsProg_52 H) (blkPl_86).base
      (withLsCodeLoaded lsmpl (sessionLenSpec A)))
    (hEV : subroutine_ok (lsProg_52 H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (Prost.encodeVarintSpec A)))
    (hRaw : subroutine_ok (lsProg_52 H) (blkPl_14).base
      (withLsCodeLoaded lsmpl (encodeRawSpec A)))
    (hDrop : subroutine_ok (lsProg_52 H) (blkPl_6).base
      (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal1Spec A))) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base (withLsCodeLoaded lsmpl (serializeCanonSpec A)) :=
  serializeCanon_of_serialize_placed
    (serialize_placed_ok_of_caller_callees
      hshim halloc hmemcpy hpanic hClone hVV hLen hEV hRaw hDrop)

/-- Canonical relocatable `SessionRecord::serialize` (block `52`) from block-level callee contracts. -/
theorem serializeCanon_placed_ok_of_callees [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym LibsignalTripleRatchet.sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hClone : subroutine_ok (lsProg_80 H) (blkPl_80).base
      (withLsCodeLoaded lsmpl (sessionCloneSpec A)))
    (hVV : subroutine_ok (lsProg_117 H) (blkPl_117).base vecVecCloneEmptySpec)
    (hLen : subroutine_ok (lsProg_86 H) (blkPl_86).base
      (withLsCodeLoaded lsmpl (sessionLenSpec A)))
    (hEV : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (Prost.encodeVarintSpec A)))
    (hRaw : subroutine_ok (lsProg_14 H) (blkPl_14).base
      (withLsCodeLoaded lsmpl (encodeRawSpec A)))
    (hDrop : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H) (blkPl_6).base
      (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal1Spec A))) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base (withLsCodeLoaded lsmpl (serializeCanonSpec A)) :=
  serializeCanon_of_serialize_placed
    (serialize_placed_ok_of_callees
      hshim halloc hmemcpy hpanic hClone hVV hLen hEV hRaw hDrop)

/-- Canonical relocatable `SessionRecord::serialize` (block `52`) from external hook hypotheses. -/
theorem serializeCanon_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym LibsignalTripleRatchet.sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base (withLsCodeLoaded lsmpl (serializeCanonSpec A)) :=
  serializeCanon_of_serialize_placed
    (serialize_placed_ok hshim halloc hrealloc hdealloc hmemcpy hpanic)

/-- Canonical relocatable `SessionRecord::serialize` (block `52`) from `PlacedSerializeHooks`. -/
theorem serializeCanon_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hH : PlacedSerializeHooks A H) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base (withLsCodeLoaded lsmpl (serializeCanonSpec A)) :=
  serializeCanon_of_serialize_placed (serialize_placed_ok_of_hooks hH)

end Placed

end CryptoVerification.E2E.Record.Serialization
