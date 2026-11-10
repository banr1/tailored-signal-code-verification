/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBase
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCS
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MessageEncodeCodeSym
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import ProofLib.SepLogic.WPp

/-!
# Relocatable `[LibsignalPlacement]` Shared Step Lemmas for `PolynomialEncoder::encode`

Provides relocatable `[LibsignalPlacement]` call wrappers and basic-block steppers shared between
`PolynomialEncoder::encode [local#1]` (`Block 153`) and `[local#2]` (`Block 316`).
-/

@[expose] public section


namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalProtoCodec
  CryptoVerification.LibsignalTripleRatchet.Prost
  CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
  CryptoVerification.CodeLayout
  CryptoVerification.LibsignalSpqrV1
  CryptoVerification.SpqrV1.Alloc
  CryptoVerification.SpqrV1.Varint
  CryptoVerification.SpqrV1.ProtoRepr
  CryptoVerification.SpqrV1.Poly
  CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 EncodedLen.ule_self_64 EncodedLen.ult_self_64

theorem step_msg48rep_encode_varint_call_placed {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {prog : Program} (A : RustAlloc) {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (val v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length + (LibsignalProtoCodec.encodeVarint val).length ≤ curCap.toNat ∨
      curBs.length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (LibsignalProtoCodec.encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A v nextCap nextPtr (curBs ++ LibsignalProtoCodec.encodeVarint val) ∗
          A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  refine step_msg48_encode_varint_call_placed A henc val v curCap curPtr sp ret_pc curBs hlen_lt
    (F := memRegion (sp - 48#64 - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗ F)
    hpc hrun hsp halign htr hlr hx0 hx1 hcs
    (by rw [hP, stackAt_encodeRepeated_eq_varint hres (sp - 48#64)]; ac_rfl) ?_
  intro sm nextCap nextPtr hpcm hrunm hspm htrm hcsm hcs_m hge hpres
  refine SepWPp.weaken_pre ?_
    (hnext sm nextCap nextPtr hpcm hrunm hspm htrm hcsm hcs_m hge hpres)
  rw [stackAt_encodeRepeated_eq_varint hres (sp - 48#64)]
  exact Entails.of_eq (by ac_rfl)

theorem step_msg48rep_do_reserve2_call_placed {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {prog : Program} (A : RustAlloc) {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (add : Nat)
    (hres_bound : reserveCap curCap.toNat curBs.length add + 1 ≤ 2 ^ 63)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = add)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((vecU8At A v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) newPtr curBs ∗
          A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  refine step_msg48_do_reserve2_call_placed (by omega) A hdoReserve v curCap curPtr sp ret_pc curBs add
    hres_bound
    (F := memRegion (sp - 48#64 - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗ F)
    hpc hrun hsp halign htr hlr hx0 hx1 hx2 hcs
    (by rw [hP, stackAt_encodeRepeated_eq_varint hres (sp - 48#64)]; ac_rfl) ?_
  intro sm newPtr hpcm hrunm hspm htrm hcsm hcs_m
  refine SepWPp.weaken_pre ?_ (hnext sm newPtr hpcm hrunm hspm htrm hcsm hcs_m)
  rw [stackAt_encodeRepeated_eq_varint hres (sp - 48#64)]
  exact Entails.of_eq (by ac_rfl)

theorem step_msg48rep_do_reserve7_call_placed {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {prog : Program} (A : RustAlloc) {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (doReserveSpecOf resStack A)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (add : Nat)
    (hres_bound : reserveCap curCap.toNat curBs.length add + 1 ≤ 2 ^ 63)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = add)
    (hx3 : s.readReg64 .x3 = 1#64) (hx4 : s.readReg64 .x4 = 1#64)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((vecU8At A v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) newPtr curBs ∗
          A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  refine step_msg48_do_reserve7_call_placed (by omega) A hdoReserve v curCap curPtr sp ret_pc curBs add
    hres_bound
    (F := memRegion (sp - 48#64 - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗ F)
    hpc hrun hsp halign htr hlr hx0 hx1 hx2 hx3 hx4 hcs
    (by rw [hP, stackAt_encodeRepeated_eq_varint hres (sp - 48#64)]; ac_rfl) ?_
  intro sm newPtr hpcm hrunm hspm htrm hcsm hcs_m
  refine SepWPp.weaken_pre ?_ (hnext sm newPtr hpcm hrunm hspm htrm hcsm hcs_m)
  rw [stackAt_encodeRepeated_eq_varint hres (sp - 48#64)]
  exact Entails.of_eq (by ac_rfl)

/-- Execute `bl PolynomialEncoder::encoded_len` (via `polynomialEncoderEncodedLenElemsOutSpec`)
at `call_pc` when the stack at `sp - 48#64` is `stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)`. -/
theorem step_msg48rep_polyEncLen_call_placed {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {prog : Program} (A : RustAlloc) {call_pc : BitVec 64} {s0 s : State}
    (hencLen : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (polynomialEncoderEncodedLenElemsOutSpec A)))
    (encA sp ret_pc : BitVec 64) (g : Poly.ProtoPolynomialEncoderGhost)
    (pb : ProtoPolynomialEncoder)
    (hlen_lt : polynomialEncoderPBEncodedLen pb < 2 ^ 64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = encA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (Poly.protoPolynomialEncoderPinnedAt A g encA pb ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (ptsElems polysElems : List (BitVec 64 × List (BitVec 8))),
      ptsElems.map Prod.snd = pb.pts → pb.pts.length * 24 < 2 ^ 63 →
      polysElems.map Prod.snd = pb.polys → pb.polys.length * 24 < 2 ^ 63 →
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb) →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
          polyEncoderRestAt A encA g ptsElems polysElems ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_48_aligned halign
  have hst : stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) =
      memRegion (sp - 48#64 - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗
      (memRegion (sp - 48#64 - BitVec.ofNat 64 (0x30 + resStack)) (32 + resStack) ∗
        stackAt (sp - 48#64) polyEncodedLenStack) := by
    rw [stackAt_encodeRepeated_eq_varint hres (sp - 48#64),
      stackAt_varint_eq_stack16 (by omega) (sp - 48#64)]
  refine SepWPp.call_cs_placed (x := PinnedEncLenGhost.mk encA g pb)
    (F := memRegion (sp - 48#64 - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗
      memRegion (sp - 48#64 - BitVec.ofNat 64 (0x30 + resStack)) (32 + resStack) ∗ F)
    hencLen hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, hst] at hm
    simp only [withMsgEnc48CSPlaced, polynomialEncoderEncodedLenElemsOutSpec,
      polynomialEncoderEncodedLenPinnedSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hlen_lt⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withMsgEnc48CSPlaced, polynomialEncoderEncodedLenElemsOutSpec,
      sepConj_assoc, satisfies_pure_sepConj] at hm
    exact False.elim hm.1
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withMsgEnc48CSPlaced, polynomialEncoderEncodedLenElemsOutSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun ptsElems => ?_
    refine SepWPp.exists_elim fun polysElems => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hpts_eq, hpts_lt, hpolys_eq, hpolys_lt⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm ptsElems polysElems hpts_eq hpts_lt hpolys_eq hpolys_lt
        hpcm hrunm hspm htrm' hx0m hcsm
        (hcs.trans (MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [hst]
    exact Entails.of_eq (by ac_rfl)


theorem polyEncoder_unpinned_of_pinned_placed_x [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (encodePolyEncoderPinnedSpecOf resStack A))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (encodePolyEncoderSpecOf resStack A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; obtain ⟨hinv0, hpre⟩ := hpre
  dsimp only [encodePolyEncoderSpecOf] at hpre
  rw [protoPolynomialEncoderAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (encodePolyEncoderPinnedSpecOf resStack A)).pre
      ⟨x.encA, g, x.enc, x.v, x.cap, x.ptr, x.bs⟩ s0 ∗ R := by
    dsimp only [withLsCodeLoaded]; rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hinv0, hpre⟩
  refine (hpinned.to_outcome ⟨x.encA, g, x.enc, x.v, x.cap, x.ptr, x.bs⟩ R s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest)
  · exact Or.inl ⟨hret, hcc, polyEncoder_post_unpinned_of_pinned hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)


def IsPolyEncoderEncodeEntryProg (prog : Program) (entry : BitVec 64) : Prop :=
  (∃ b ext, prog = tripleRatchetProgAtExt b ext ∧ IsPolyEncoderEncodeEntry b ext entry) ∨
  (∃ (inst : LibsignalPlacement) (H : String → Option (State → State)),
    prog = @lsProg_153 inst H ∧ entry = (@blkPl_153 inst).base) ∨
  (∃ (inst : LibsignalPlacement) (H : String → Option (State → State)),
    prog = @lsProg_316 inst H ∧ entry = (@blkPl_316 inst).base)

theorem polyEncoderEncode_fetch_entry_placed {prog : Program} {entry : BitVec 64}
    (hfn : IsPolyEncoderEncodeEntryProg prog entry) {ins : Instr}
    (h1 : ∀ b ext, (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder1Name) = some ins)
    (h2 : ∀ b ext, (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name) = some ins)
    (h_182 : ∀ [LibsignalPlacement] H,
      (lsProg_153 H).fetch ((blkPl_153).base + 0#64) = some ins)
    (h_366 : ∀ [LibsignalPlacement] H,
      (lsProg_316 H).fetch ((blkPl_316).base + 0#64) = some ins) :
    prog.fetch entry = some ins := by
  rcases hfn with ⟨b, ext, rfl, rfl | rfl⟩ | ⟨inst, H, rfl, rfl⟩ | ⟨inst, H, rfl, rfl⟩
  · exact h1 b ext
  · exact h2 b ext
  · simpa using @h_182 inst H
  · simpa using @h_366 inst H

theorem polyEncoderEncode_fetch_add_placed {prog : Program} {entry : BitVec 64}
    (hfn : IsPolyEncoderEncodeEntryProg prog entry) {k : Nat} {ins : Instr}
    (h1 : ∀ b ext, (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder1Name + BitVec.ofNat 64 k) = some ins)
    (h2 : ∀ b ext, (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + BitVec.ofNat 64 k) = some ins)
    (h_182 : ∀ [LibsignalPlacement] H,
      (lsProg_153 H).fetch ((blkPl_153).base + BitVec.ofNat 64 k) = some ins)
    (h_366 : ∀ [LibsignalPlacement] H,
      (lsProg_316 H).fetch ((blkPl_316).base + BitVec.ofNat 64 k) = some ins) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with ⟨b, ext, rfl, rfl | rfl⟩ | ⟨inst, H, rfl, rfl⟩ | ⟨inst, H, rfl, rfl⟩
  · exact h1 b ext
  · exact h2 b ext
  · exact @h_182 inst H
  · exact @h_366 inst H

open Lean Elab Tactic in
elab "polyEncoder_fetches_range_placed " _entry:term:max hfn:ident
    kStart:num kEnd:num : tactic => do
  let off1 := 0x37774
  let off2 := 0x4d2dc
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let fnOff1 := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x37774
  let fnOff2 := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x4d2dc
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let dec1 := mkIdent (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      s!"libsignalSessionBin_decode_0x{String.ofList (Nat.toDigits 16 (off1 + k))}")
    let dec2 := mkIdent (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      s!"libsignalSessionBin_decode_0x{String.ofList (Nat.toDigits 16 (off2 + k))}")
    let kHex := String.ofList (Nat.toDigits 16 k)
    let p182 := mkIdent (`CryptoVerification |>.str s!"blkPC_153_rebase_fetch_0x{kHex}")
    let p366 := mkIdent (`CryptoVerification |>.str s!"blkPC_316_rebase_fetch_0x{kHex}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := polyEncoderEncode_fetch_entry_placed $hfn
          (fun b ext => $fetchEntry (b := b) (H := Rust.withPanics ext) $fnOff1 (by decide) $dec1)
          (fun b ext => $fetchEntry (b := b) (H := Rust.withPanics ext) $fnOff2 (by decide) $dec2)
          (fun [LibsignalPlacement] H => $p182 _ H)
          (fun [LibsignalPlacement] H => $p366 _ H)))
    else
      evalTactic (← `(tactic|
        have := polyEncoderEncode_fetch_add_placed $hfn (k := $kq)
          (fun b ext => $fetchAdd (b := b) (H := Rust.withPanics ext) (k := $kq) $fnOff1 (by decide) $dec1)
          (fun b ext => $fetchAdd (b := b) (H := Rust.withPanics ext) (k := $kq) $fnOff2 (by decide) $dec2)
          (fun [LibsignalPlacement] H => $p182 _ H)
          (fun [LibsignalPlacement] H => $p366 _ H)))

/-- Shared prologue (`+0x000..+0x014`, offsets `0..20`):
allocates the 48-byte stack frame, saves `x29, x30, x21, x20, x19`, and sets `x19 = v`. -/
theorem step_polyEncoder_prologue_placed {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {prog : Program} {entry : BitVec 64} (hfn : IsPolyEncoderEncodeEntryProg prog entry)
    (encA v sp : BitVec 64)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hhs0 : s = s0) (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = encA) (hx1 : s.readReg64 .x1 = v) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = stackAt sp (msgEnc48RepeatedStackOf resStack) ∗ F)
    (hnext : ∀ (sm : State) (sv3 : BitVec 64),
      sm.pc = entry + 20#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = encA → sm.readReg64 .x1 = v → sm.readReg64 .x19 = v →
      MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  polyEncoder_fetches_range_placed entry hfn 0 20
  examples_hide_fetches; subst hP hhs0
  have hsp_aligned := sp_sub_48_aligned halign
  rw [stackAt_msgEnc48_repeated hres sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun sv0 => SepWPp.exists_elim fun sv1 =>
    SepWPp.exists_elim fun sv2 => SepWPp.exists_elim fun sv3 =>
    SepWPp.exists_elim fun sv4 => SepWPp.exists_elim fun sv5 => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := entry + 20#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  refine SepWPp.weaken_pre (by dsimp only [msgEnc48SavedFrame]; exact Entails.of_eq (by ac_rfl))
    (hnext _ sv3
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv))

/-- Shared header tag push (`+0x028..+0x040`, offsets `40..64`):
given `curBs.length < curCap.toNat`, pushes `0x12#8` (`tag = 2`, `lengthDelimited`) to `buf`
and sets `x0 = encA`. -/
theorem step_polyEncoder_push_hdr_tag_placed {prog : Program} (A : RustAlloc)
    {entry : BitVec 64} (hfn : IsPolyEncoderEncodeEntryProg prog entry)
    (encA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 40#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 64#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = encA → sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA →
      MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        (vecU8At A v curCap curPtr (curBs ++ [0x12#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  polyEncoder_fetches_range_placed entry hfn 40 64
  examples_hide_fetches; subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := entry + 64#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  refine SepWPp.weaken_pre (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x12#8 hlt]; exact Entails.of_eq (by ac_rfl))
    (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv))

theorem step_polyEncoder_mov_x1_x19_68_placed {prog : Program}
    {entry : BitVec 64} (hfn : IsPolyEncoderEncodeEntryProg prog entry) (val encA v sp : BitVec 64)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 68#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 72#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = val → sm.readReg64 .x1 = v → sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = encA → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp prog ret sm P Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  polyEncoder_fetches_range_placed entry hfn 68 72
  examples_hide_fetches
  apply SepWPp.of_sepWP_cs_placed (mid := entry + 72#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  exact hnext _
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv)

/-- Shared `idx` load and zero check (`+0x04c..+0x054`, offsets `76..84`):
loads `w0 = [x20, #0x30]` (`pb.idx`) and branches to `entry + 128#64` if `pb.idx == 0#32`,
else falls through to `entry + 84#64`. -/
theorem step_polyEncoder_check_idx_placed {prog : Program}
    {entry : BitVec 64} (hfn : IsPolyEncoderEncodeEntryProg prog entry)
    (encA v sp : BitVec 64) (g : Poly.ProtoPolynomialEncoderGhost) (pb : ProtoPolynomialEncoder)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8)))
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 76#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s) (hP : P = polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + (if pb.idx == 0#32 then 128#64 else 84#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.idx.zeroExtend 64 → sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA →
      MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        (polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  polyEncoder_fetches_range_placed entry hfn 76 84
  examples_hide_fetches; subst hP; dsimp only [polyEncoderElemsAt]
  cases hidx : (pb.idx == 0#32)
  · have hidx64 : (BitVec.zeroExtend 64 pb.idx == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hidx]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 84#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre (by dsimp only [polyEncoderElemsAt]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv))
  · have hidx64 : (BitVec.zeroExtend 64 pb.idx == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hidx]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 128#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre (by dsimp only [polyEncoderElemsAt]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv))

/-- Shared `idx` tag push (`+0x064..+0x07c`, offsets `100..124`):
given `curBs.length < curCap.toNat`, pushes `0x08#8` (`tag = 1`, varint) to `buf`
and sets `x1 = v`, preserving `x0 = pb.idx.zeroExtend 64`. -/
theorem step_polyEncoder_push_idx_tag_placed {prog : Program} (A : RustAlloc)
    {entry : BitVec 64} (hfn : IsPolyEncoderEncodeEntryProg prog entry)
    (encA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (pb : ProtoPolynomialEncoder) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 100#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = pb.idx.zeroExtend 64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 124#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.idx.zeroExtend 64 → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        (vecU8At A v curCap curPtr (curBs ++ [0x08#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  polyEncoder_fetches_range_placed entry hfn 100 124
  examples_hide_fetches; subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := entry + 124#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  refine SepWPp.weaken_pre (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x08#8 hlt]; exact Entails.of_eq (by ac_rfl))
    (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv))

/-- Shared `pts` argument setup (`+0x080..+0x08c`, offsets `128..140`):
loads `x1 = g.pts.ptr`, `x2 = BitVec.ofNat 64 pb.pts.length`, sets `w0 = 2#32`, `x3 = v`. -/
theorem step_polyEncoder_prep_pts_placed {prog : Program}
    {entry : BitVec 64} (hfn : IsPolyEncoderEncodeEntryProg prog entry)
    (encA v sp : BitVec 64) (g : Poly.ProtoPolynomialEncoderGhost) (pb : ProtoPolynomialEncoder)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8)))
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 128#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s) (hP : P = polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 140#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg32 .x0 = 2#32 → sm.readReg64 .x1 = g.pts.ptr →
      sm.readReg64 .x2 = BitVec.ofNat 64 pb.pts.length → sm.readReg64 .x3 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        (polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  polyEncoder_fetches_range_placed entry hfn 128 140
  examples_hide_fetches; subst hP; dsimp only [polyEncoderElemsAt]
  apply SepWPp.of_sepWP_cs_placed (mid := entry + 140#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  refine SepWPp.weaken_pre (by dsimp only [polyEncoderElemsAt]; exact Entails.of_eq (by ac_rfl))
    (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by dsimp only [State.readReg32, Reg.x0]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv))

/-- Shared `polys` argument setup + frame restore (`+0x090..+0x0a8`, offsets `144..168`):
loads `x1 = g.polys.ptr`, `x2 = BitVec.ofNat 64 pb.polys.length`, sets `w0 = 3#32`, `x3 = v`,
and restores the 48-byte stack frame (`sp = sp`, `lr = s0.readReg64 .lr`), arriving at
`entry + 168#64` (`+0x0a8`, the `b encode_repeated` tailcall). -/
theorem step_polyEncoder_prep_polys_epilogue_placed {prog : Program}
    {entry : BitVec 64} (hfn : IsPolyEncoderEncodeEntryProg prog entry)
    (encA v sp sv3 : BitVec 64) (g : Poly.ProtoPolynomialEncoderGhost) (pb : ProtoPolynomialEncoder)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8)))
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 144#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyEncoderElemsAt encA g pb ptsElems polysElems ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 168#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .lr = s0.readReg64 .lr → sm.readReg32 .x0 = 3#32 →
      sm.readReg64 .x1 = g.polys.ptr → sm.readReg64 .x2 = BitVec.ofNat 64 pb.polys.length →
      sm.readReg64 .x3 = v → CalleeSavedPreserved s0 sm → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  polyEncoder_fetches_range_placed entry hfn 144 168
  examples_hide_fetches; subst hP
  have hsp_aligned := sp_sub_48_aligned halign
  rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs, hinv0⟩
  dsimp only [polyEncoderElemsAt, msgEnc48SavedFrame]
  apply SepWPp.of_sepWP_cs_placed (mid := entry + 168#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine SepWPp.weaken_pre (by dsimp only [polyEncoderElemsAt, msgEnc48SavedFrame]; exact Entails.of_eq (by ac_rfl))
    (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by dsimp only [State.readReg32, Reg.x0]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by epochEncLen_cc_close)
      ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *], hinv0.trans hinv1⟩)

theorem pe1_fetch_add_mono {b : BitVec 64} {ext : String → Option (State → State)}
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder1Name = entry)
    {k : Nat} {ins : Instr}
    (h1 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder1Name + BitVec.ofNat 64 k) = some ins) :
    (tripleRatchetProgAtExt b ext).fetch (entry + BitVec.ofNat 64 k) = some ins := by
  subst hfn; exact h1

open Lean Elab Tactic in
elab "pe1_fetches " b:term:max H:term:max hfn:ident kStart:num kEnd:num : tactic => do
  let off := 0x37774
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let fnOff := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x37774
  let helper := mkIdent ``CryptoVerification.SpqrV1.Prost.MessageEncode.pe1_fetch_add_mono
  for i in [kStart.getNat / 4 : kEnd.getNat / 4] do
    let k := 4 * i
    let dec := mkIdent (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      s!"libsignalSessionBin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    evalTactic (← `(tactic|
      have := $helper $hfn (k := $kq) ($fetchAdd (b := $b) (H := $H) (k := $kq) $fnOff (by decide) $dec)))

end CryptoVerification.SpqrV1.Prost.MessageEncode
