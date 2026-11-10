/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternal
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.LeavesCodeSymA
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.LeavesCodeSym -- shake: keep

/-!
# SPQR V1 Send-Leaf Transitions: Relocatable `[LibsignalPlacement]` Specifications & Bridges

Relocatable `[LibsignalPlacement]` specifications (`*PlacedSpec`), `*PlacedOkX` contract
abbreviations, `withLsCodeRoLoaded` ↔ `withLsCallInv` bridges, and `call_polyNextChunk_placed`
(Block `416`) for `SpqrV1/States/Leaves`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ChainProofs
open NextKeyInternalFacts

/-! ## 1. `withLsCodeRoLoaded` ↔ `withLsCallInv` & Left-Pure Bridges -/

theorem lsCallInv_iff_codeRoLoaded (pl : Arm64.Obj.MultiPlacement) (m : Memory) :
    LsCallInv pl m ↔ LibsignalCodeRoLoaded pl m :=
  ⟨fun ⟨hro, hcl⟩ => ⟨hcl, hro⟩, fun ⟨hcl, hro⟩ => ⟨hro, hcl⟩⟩

theorem subroutine_ok_withLsCodeLoaded_of_left {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : Arm64.Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry
      { spec with pre := fun x s => ⌜LibsignalCodeLoaded pl s.mem⌝ ∗ spec.pre x s }) :
    subroutine_ok prog entry (withLsCodeLoaded pl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hp
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hcl, hpre⟩)
    (fun _ _ _ _ hq => hq)

theorem subroutine_ok_withLsCodeRoLoaded_of_left {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : Arm64.Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry
      { spec with pre := fun x s => ⌜LibsignalCodeRoLoaded pl s.mem⌝ ∗ spec.pre x s }) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hfr, hpre⟩ := extract_withLsCodeRoLoaded hp
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hfr, hpre⟩)
    (fun _ _ _ _ hq => hq)

theorem subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : Arm64.Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeRoLoaded pl spec)) :
    subroutine_ok prog entry (withLsCallInv pl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      dsimp only [withLsCallInv] at hp
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      dsimp only [withLsCodeRoLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨(lsCallInv_iff_codeRoLoaded pl _).mp hp.1, hp.2⟩)
    (fun _ _ _ _ hq => hq)

theorem subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : Arm64.Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCallInv pl spec)) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hfr, hpre⟩ := extract_withLsCodeRoLoaded hp
      dsimp only [withLsCallInv]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨(lsCallInv_iff_codeRoLoaded pl _).mpr hfr, hpre⟩)
    (fun _ _ _ _ hq => hq)

theorem subroutine_ok_withLsCodeRoLoaded_of_plain {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : Arm64.Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => (extract_withLsCodeRoLoaded hp).2)
    (fun _ _ _ _ hq => hq)

theorem subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : Arm64.Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec)) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hfr, hpre⟩ := extract_withLsCodeRoLoaded hp
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hfr.1, hpre⟩)
    (fun _ _ _ _ hq => hq)

/-! ## 2. Relocatable `[LibsignalPlacement]` Specifications for Send Leaf Transitions -/

/-- Relocatable specification of `<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>::send_ct1_chunk` (Block `344`). -/
def ekReceivedCt1SampledSendCt1ChunkPlacedSpec [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) :
    Spec (EkReceivedCt1SampledSendCt1ChunkGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ct1_chunk = .ok (x.outSt, x.chunk)⌝ ∗
      memRegion x.outA (528 + chunkSize) ∗
      chunkedEkReceivedCt1SampledAt A x.stA x.st ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗ stackAt s.sp (polyNextChunkStack + 960)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chunkedEkReceivedCt1SampledAt A x.outA x.outSt ∗
      chunkAt (x.outA + 528#64) x.chunk ∗
      memRegion x.stA 528 ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp (polyNextChunkStack + 960)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable specification of `<spqr::v1::chunked::send_ct::Ct2Sampled>::send_ct2_chunk` (Block `354`). -/
def ct2SampledSendCt2ChunkPlacedSpec [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) :
    Spec (Ct2SampledSendCt2ChunkGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ct2_chunk = .ok (x.outSt, x.chunk)⌝ ∗
      memRegion x.outA (456 + chunkSize) ∗
      chunkedCt2SampledAt A x.stA x.st ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗ stackAt s.sp (polyNextChunkStack + 896)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chunkedCt2SampledAt A x.outA x.outSt ∗
      chunkAt (x.outA + 456#64) x.chunk ∗
      memRegion x.stA 456 ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp (polyNextChunkStack + 896)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable specification of `<spqr::v1::chunked::send_ek::HeaderSent>::send_ek_chunk` (Block `336`). -/
def headerSentSendEkChunkPlacedSpec [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) :
    Spec (HeaderSentSendEkChunkGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ek_chunk = .ok (x.outSt, x.chunk)⌝ ∗
      memRegion x.outA (880 + chunkSize) ∗
      chunkedHeaderSentAt A x.stA x.st ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗ stackAt s.sp (polyNextChunkStack + 1328)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chunkedHeaderSentAt A x.outA x.outSt ∗
      chunkAt (x.outA + 880#64) x.chunk ∗
      memRegion x.stA 880 ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp (polyNextChunkStack + 1328)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable specification of `<spqr::v1::chunked::send_ek::Ct1Received>::send_ek_chunk` (Block `345`). -/
def ct1ReceivedSendEkChunkPlacedSpec [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) :
    Spec (Ct1ReceivedSendEkChunkGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ek_chunk = .ok (x.outSt, x.chunk)⌝ ∗
      memRegion x.outA (504 + chunkSize) ∗
      chunkedCt1ReceivedAt A x.stA x.st ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗ stackAt s.sp (polyNextChunkStack + 944)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chunkedCt1ReceivedAt A x.outA x.outSt ∗
      chunkAt (x.outA + 504#64) x.chunk ∗
      memRegion x.stA 504 ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp (polyNextChunkStack + 944)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable specification of `<spqr::v1::chunked::send_ct::Ct1Sampled>::send_ct1_chunk` (Block `335`). -/
def ct1SampledSendCt1ChunkPlacedSpec [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) :
    Spec (Ct1SampledSendCt1ChunkGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ct1_chunk = .ok (x.outSt, x.chunk)⌝ ∗
      memRegion x.outA (928 + chunkSize) ∗
      chunkedCt1SampledAt A x.stA x.st ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗ stackAt s.sp (polyNextChunkStack + 1376)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chunkedCt1SampledAt A x.outA x.outSt ∗
      chunkAt (x.outA + 928#64) x.chunk ∗
      memRegion x.stA 928 ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp (polyNextChunkStack + 1376)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## 3. Contract Abbreviations (`*PlacedOkX`) -/

theorem ls_subroutine_ok_to_blockProgram [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok calleeProg entry spec) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) entry spec :=
  hcallee.eq_blockProgram ▸ h

def Ct2SampledRecvNextEpochPlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_355 (Rust.withPanics ext)) (blkPl_355).base
    (withLsCodeLoaded lsmpl (ct2SampledRecvNextEpochSpec A F))

def HeaderSentSendEkChunkPlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 336 (Rust.withPanics ext)) (lsmpl.base 336)
    (withLsCodeRoLoaded lsmpl (headerSentSendEkChunkPlacedSpec A F))

def Ct1ReceivedSendEkChunkPlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 345 (Rust.withPanics ext)) (lsmpl.base 345)
    (withLsCodeRoLoaded lsmpl (ct1ReceivedSendEkChunkPlacedSpec A F))

def Ct1SampledSendCt1ChunkPlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 335 (Rust.withPanics ext)) (lsmpl.base 335)
    (withLsCodeRoLoaded lsmpl (ct1SampledSendCt1ChunkPlacedSpec A F))

def EkReceivedCt1SampledSendCt1ChunkPlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 344 (Rust.withPanics ext)) (lsmpl.base 344)
    (withLsCodeRoLoaded lsmpl (ekReceivedCt1SampledSendCt1ChunkPlacedSpec A F))

def Ct2SampledSendCt2ChunkPlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 354 (Rust.withPanics ext)) (lsmpl.base 354)
    (withLsCodeRoLoaded lsmpl (ct2SampledSendCt2ChunkPlacedSpec A F))

/-! ## 4. Relocatable `of_sepWP_lscro` / `of_sepWP_lscl` & `call_polyNextChunk_placed` Helpers -/

theorem sepWP_seq_lscl {prog : Program} {pl : Arm64.Obj.MultiPlacement} {mid tgt : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem → SepWP prog tgt sm Pm post)) :
    SepWP prog tgt s P post :=
  SepWP.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl h

theorem of_sepWP_lscl {prog : Program} {pl : Arm64.Obj.MultiPlacement} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl h

theorem of_sepWP_lscro {prog : Program} {pl : Arm64.Obj.MultiPlacement} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeRoLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  sepWPp_seq_lscro hcro h

/-- Framed relocatable call rule for `withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpec A)` (Block `416`),
bridging from `SepWP` before the call to `SepWPp` (propagating `allocFailedIn s0 sf`) and back to
`SepWP` after the call. -/
theorem call_polyNextChunk_placed [LibsignalPlacement] {A : RustAlloc}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpec A)))
    (outChunkA encA : BitVec 64) (enc enc' : PolyEncoder) (chunk : Chunk)
    {s0 s : State} {sp_call v19 v20 : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hregs : Regs19To27Eq s v19 v20 s0)
    (hx8 : s.readReg64 Reg.x8 = outChunkA)
    (hx0 : s.readReg64 Reg.x0 = encA)
    (hnc : enc.nextChunk = .ok (enc', chunk))
    (hsplit : P = (memRegion outChunkA chunkSize ∗ polyEncoderAt A encA enc ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗ stackAt sp_call polyNextChunkStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → Regs19To27Eq sf v19 v20 s0 → sf.trace = s0.trace →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((chunkAt outChunkA chunk ∗ polyEncoderAt A encA enc' ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗ stackAt sp_call polyNextChunkStack) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm =>
        LibsignalCodeRoLoaded lsmpl sm.mem →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun
  intro hcro
  refine SepWPp.call hcall (x := ⟨outChunkA, encA, enc, enc', chunk⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withLsCodeRoLoaded, polyNextChunkPlacedSpec]
    rw [hsp]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx8, hx0, hnc⟩, hm⟩
  · rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [withLsCodeRoLoaded, polyNextChunkPlacedSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    have hassoc :
        (chunkAt outChunkA chunk ∗ polyEncoderAt A encA enc' ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗ stackAt sp_call polyNextChunkStack) ∗ Frame =
        (chunkAt outChunkA chunk ∗ (polyEncoderAt A encA enc' ∗
          (tokenInitPlacedAt ∗ (reduceTablePlacedAt ∗
            (A.pool ∗ stackAt sp_call polyNextChunkStack))))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) (hregs.of_cs hcs_sf) (htr.trans htrace)

end CryptoVerification.SpqrV1.States.Leaves
