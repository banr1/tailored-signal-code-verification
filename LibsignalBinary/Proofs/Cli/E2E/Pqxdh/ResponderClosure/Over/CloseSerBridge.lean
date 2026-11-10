/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBody
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyB
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecClone
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropSsLocal1Ext
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionCloneX
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueX
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarint

/-!
# `SessionRecord::serialize` (`Prev1`) Bridge and Contract Assembly

Bridges the internal 32-byte-output body contract `SerializePrev1BodyOkStmt` for
`SessionRecord::serialize` with one previous session to the 48-byte contract `SerializePrev1OkStmt`
and the canonical-ghost form `serializePrev1CanonSpecX`, closing both from `SerContractsX` and
`AllocContractsX`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Bin
open Proofs.libsignal.Hooks2

private theorem stackAt_sub_split_k5b (sp : BitVec 64) (k m : Nat) (hkm : k ≤ m)
    (hm : m ≤ 2 ^ 64) :
    stackAt sp m =
      memRegion (sp - BitVec.ofNat 64 m) (m - k) ∗ stackAt sp k := by
  unfold stackAt
  exact memRegion_split' (b := sp - BitVec.ofNat 64 m) (b' := sp - BitVec.ofNat 64 k)
    (N := m) (n := m - k) (k := k) (by omega)
    (by
      have h1 : BitVec.ofNat 64 m = BitVec.ofNat 64 (m - k) + BitVec.ofNat 64 k := by
        rw [← BitVec.ofNat_add, Nat.sub_add_cancel hkm]
      rw [h1]
      bv_lin)
    (by omega)

private theorem stackAt_recordSerialize_split_k5b (sp : BitVec 64) :
    stackAt sp CryptoVerification.E2E.Bin.recordSerializeStack =
      memRegion (sp - BitVec.ofNat 64 CryptoVerification.E2E.Bin.recordSerializeStack)
        (CryptoVerification.E2E.Bin.recordSerializeStack - serializeStackX) ∗
      stackAt sp serializeStackX :=
  stackAt_sub_split_k5b sp serializeStackX CryptoVerification.E2E.Bin.recordSerializeStack
    serializeStackX_le_recordSerializeStack (by decide)

private theorem memRegion_48_split_32_16_k5b (out : BitVec 64) :
    memRegion out 48 = memRegion out 32 ∗ memRegion (out + 32#64) 16 :=
  memRegion_split out 32 16 (by decide)

theorem sessionRecordPrevAt_some_eq (A : RustAlloc) (r cap ptr : BitVec 64)
    (G : SessionGhost) (s : Session (List (BitVec 8))) (ps : List (List (BitVec 8))) :
    sessionRecordPrevAt A r ⟨cap, ptr, some G⟩ ps ⟨some s⟩ =
      prevVecAt A r cap ptr ps ∗ sessionStateReprAt A (r + 24#64) G s := by
  rw [sessionRecordPrevAt_eq, recCurAt_some]

theorem serializePrev1_bridge : SerializePrev1BridgeStmt := by
  intro img A ext hBody
  unfold SerializePrev1BodyOkStmt at hBody
  unfold SerializePrev1OkStmt
  have hAddr :
      (SP2Ext img.base ext).fnAddr CryptoVerification.E2E.Record.Serialization.serializeName =
        img.base + CryptoVerification.E2E.Bin.serializeOff := by
    change (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
        CryptoVerification.E2E.Bin.recordSerializeName =
      img.base + CryptoVerification.E2E.Bin.serializeOff
    rw [Program.fnAddr_rebase, CryptoVerification.E2E.Bin.serialize_fnOff]
  rw [SP2Ext_eq_contractProg, hAddr] at hBody
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' := hpre
  dsimp only [Spec.inImage, serializePrev1Spec] at hpre'
  rw [sessionRecordPrevAt_some_eq A x.self x.prevCap x.prevPtr x.G x.sess [x.enc],
      memRegion_48_split_32_16_k5b x.out,
      stackAt_recordSerialize_split_k5b s0.sp,
      sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hF, hsym⟩, hpre'⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx8, hcanon, hlen⟩, hmem⟩
  have henc : encodeRecordPrev1Mem x.G x.sess x.enc = encodeRecordPrev1 x.sess x.enc :=
    encodeRecordPrev1Mem_eq_of_canon x.enc hcanon.toCanonSession
  let x_body : SerializePrev1BodyGhost :=
    ⟨x.self, x.out, x.prevCap, x.prevPtr, x.G, x.sess, x.enc⟩
  let R_body : SepProp :=
    memRegion (x.out + 32#64) 16 ∗
      memRegion (s0.sp - BitVec.ofNat 64 CryptoVerification.E2E.Bin.recordSerializeStack)
        (CryptoVerification.E2E.Bin.recordSerializeStack - serializeStackX) ∗ R
  have hpre_body : s0.mem ⊨ ((serializePrev1BodySpecX A).inImage img).pre x_body s0 ∗ R_body := by
    dsimp only [Spec.inImage, serializePrev1BodySpecX, x_body, R_body]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hF, hsym⟩, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, henc.symm ▸ hlen⟩, ?_⟩
    exact Satisfies.of_eq hmem (by ac_rfl)
  refine hBody.mono_outcome x_body R_body s0 hpc hrun hpre_body hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, serializePrev1BodySpecX, x_body, R_body] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq_mem⟩
    rw [henc] at hq_mem
    dsimp only [Spec.inImage, serializePrev1Spec]
    rw [sessionRecordPrevAt_some_eq A x.self x.prevCap x.prevPtr x.G x.sess [x.enc],
        stackAt_recordSerialize_split_k5b s0.sp,
        sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    exact Satisfies.of_eq hq_mem (by ac_rfl)
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, serializePrev1BodySpecX, serializePrev1Spec, R_body] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hfail, hq_mem⟩
    refine ⟨hfail, ?_⟩
    have hany : (anyHeap ∗ memRegion (x.out + 32#64) 16 ∗
        memRegion (s0.sp - BitVec.ofNat 64 CryptoVerification.E2E.Bin.recordSerializeStack)
          (CryptoVerification.E2E.Bin.recordSerializeStack - serializeStackX)) ∗ R ⊢ anyHeap ∗ R :=
      sepConj_mono_left (entails_anyHeap _)
    exact Arm64.Satisfies.mono hany (Satisfies.of_eq hq_mem (by ac_rfl))
  · dsimp only [Spec.inImage, serializePrev1BodySpecX] at hq
    rw [satisfies_pure_sepConj] at hq
    exact hq.1.elim
  · dsimp only [Spec.inImage, serializePrev1BodySpecX] at hq
    rw [satisfies_pure_sepConj] at hq
    exact hq.1.elim

/-- Canonical-ghost 32-byte-`out` contract for `SessionRecord::serialize` with one previous session
at `serializeStackX`. -/
def serializePrev1CanonSpecX (A : RustAlloc) : Spec SerializePrev1BodyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧
      CanonSession x.G x.sess ∧
      (encodeRecordPrev1 x.sess x.enc).length < 2 ^ 32⌝ ∗
      sessionRecordPrevAt A x.self ⟨x.prevCap, x.prevPtr, some x.G⟩ [x.enc] ⟨some x.sess⟩ ∗
      memRegion x.out 32 ∗ A.pool ∗ stackAt s.sp serializeStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      sessionRecordPrevAt A x.self ⟨x.prevCap, x.prevPtr, some x.G⟩ [x.enc] ⟨some x.sess⟩ ∗
      (x.out ↦₆₄ okTagVec) ∗ vecU8 A (x.out + 8#64) (encodeRecordPrev1 x.sess x.enc) ∗
      A.pool ∗ stackAt s0.sp serializeStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem serializePrev1CanonX_of_body {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hBody : SerializePrev1BodyOkStmt img A ext) :
    subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr serializeName)
      ((serializePrev1CanonSpecX A).inImage img) := by
  unfold SerializePrev1BodyOkStmt at hBody
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' := hpre
  simp only [Spec.inImage, serializePrev1CanonSpecX,
    sessionRecordPrevAt_some_eq A x.self x.prevCap x.prevPtr x.G x.sess [x.enc]] at hpre'
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  obtain ⟨⟨hF, hsym⟩, hpre'⟩ := hpre'
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  obtain ⟨⟨hx0, hx8, hcanon, hlen⟩, hmem⟩ := hpre'
  have henc := encodeRecordPrev1Mem_eq_of_canon x.enc hcanon
  have hpre_body : s0.mem ⊨ ((serializePrev1BodySpecX A).inImage img).pre x s0 ∗ R := by
    simp only [Spec.inImage, serializePrev1BodySpecX]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hF, hsym⟩, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx8, henc.symm ▸ hlen⟩, Satisfies.of_eq hmem (by ac_rfl)⟩
  refine hBody.mono_outcome x R s0 hpc hrun hpre_body hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, serializePrev1BodySpecX] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq_mem⟩
    dsimp only [Spec.inImage, serializePrev1CanonSpecX]
    rw [sessionRecordPrevAt_some_eq A x.self x.prevCap x.prevPtr x.G x.sess [x.enc],
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htr, Satisfies.of_eq (henc ▸ hq_mem) (by ac_rfl)⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

/-! ## Closed contracts from `SerContractsX` and `AllocContractsX` -/

theorem serializePrev1Body_ok_of_serContractsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : SerContractsX img A ext) :
    SerializePrev1BodyOkStmt img A ext := by
  have hDR := Proofs.libsignal.Hooks2.do_reserve_ok_ext_x hC.alloc
  have hEV := CryptoVerification.LibsignalTripleRatchet.Prost.encodeVarint_ok_ext_x img A ext hDR
  exact serializePrev1Body_ok hC
    (CryptoVerification.E2E.Record.Serialization.sessionClone_ok_ext hC)
    hEV
    (Proofs.libsignal.Hooks2.encodeRaw_ok_of_serContractsX hC)
    (vecVecClone1_okX_of_ser hC)
    (serField2_step hC hDR hEV)
    (serPrev1Tail_ok hC (Proofs.libsignal.Hooks2.drop_session_structure_local1_ok_ext hC.alloc))

theorem serializePrev1_ok_of_serContractsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : SerContractsX img A ext) :
    SerializePrev1OkStmt img A ext :=
  serializePrev1_bridge img A ext (serializePrev1Body_ok_of_serContractsX hC)

theorem serializePrev1Body_ok_of_trAllocContractsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr serializeName)
      ((serializePrev1BodySpecX A).inImage img) :=
  serializePrev1Body_ok_of_serContractsX
    (CryptoVerification.SignalSession.Cli.Store.SerGlueX.serContractsX_of_trAllocContractsX hA)

theorem serializePrev1CanonX_ok_of_trAllocContractsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr serializeName)
      ((serializePrev1CanonSpecX A).inImage img) :=
  serializePrev1CanonX_of_body (serializePrev1Body_ok_of_trAllocContractsX hA)

theorem serializePrev1_ok_of_trAllocContractsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext) :
    SerializePrev1OkStmt img A ext :=
  serializePrev1_bridge img A ext (serializePrev1Body_ok_of_trAllocContractsX hA)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
