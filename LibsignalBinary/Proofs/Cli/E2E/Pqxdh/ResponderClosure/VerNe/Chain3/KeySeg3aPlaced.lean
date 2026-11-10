/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.KeySeg3a
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.KeyDefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.EntryPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import ProofLib.SepLogic.WPp

/-!
# Placed `message::merge<Chain> [local#4]`: ChainKey Segment 3a (`Chain3Seg3aPlacedStmt`)

`[LibsignalPlacement]` Block-`516` counterpart of `VerNe.Chain3.KeySeg3a`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
  (sliceCursorAt sliceCursorAfter DecodeVarintSlowGhost)
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalPlacement
open CryptoVerification.CliHandshake.Placed

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  ChainMergeStateSimp.sp_setPC_pre_seedChain
  ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.calleeSavedVRegs_setPC_pre_seedChain
  ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_pre_seedChain

attribute [local simp, local arm64_norm] ChainMergeStateSimp.getLsbD_63_eq_seedChain

/-! ## 1. `decode_varint [local#4]` call step -/

set_option maxHeartbeats 400000 in
theorem step_c3a_decodeVarint_placed_atW [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hC : Chain3CalleesPlacedW ext)
    (bufRef slot curPtr sp0 ret_pc v : BitVec 64) (b0 : BitVec 8) (rem1 : List (BitVec 8))
    (hdv : decodeVarint (b0 :: rem1) = some (v, rem1))
    (hlen_lt : (b0 :: rem1).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 515)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 0xf0#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s_init.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = bufRef)
    (hP : P = ((bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot curPtr (b0 :: rem1) ∗
      stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 0xf0#64 →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.trace = s_init.trace →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = 0#64 →
      sm.readReg64 .x1 = v →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗
          (curPtr ↦₈ b0) ∗
          sliceCursorAt slot (curPtr + 1#64) rem1 ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s_init sf ∗ R))) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s_init sf ∗ R)) := by
  have hlen_lt63 : (b0 :: rem1).length < 2 ^ 63 := by omega
  rw [hP]
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_240_aligned halign
  refine SepWPp.call_lscl_c3
    (x := DecodeVarintSlowGhost.mk bufRef slot curPtr (b0 :: rem1))
    (F := memRegion (sp0 - 0xf0#64 - BitVec.ofNat 64 chainMerge3SubStackX)
      (chainMerge3SubStackX - decodeVarint2StackX) ∗ F)
    hC.dv hpc hrun hsp_aligned hcl hlr ?_ ?_ ?_ ?_
  · intro R' hm
    refine intro_withLsCl_c3 hcl ?_
    rw [stackAt_c3Sub_to_decodeVarint (sp0 - 0xf0#64)] at hm
    dsimp only [decodeVarint2SpecX]
    have hpool : A0.pool = emp := rfl
    rw [hpool, hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hlen_lt63⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    dsimp only [withLsCl, decodeVarint2SpecX] at hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withLsCl, decodeVarint2SpecX, chainMerge3PlacedSpecW, chainMerge3RawSpecW,
      Serialization.allocPanic] at hm ⊢
    simp only [allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hclm hcsm
    rw [hsp] at hspm
    dsimp only [withLsCl, decodeVarint2SpecX]
    rw [hdv, hsp]
    dsimp only
    have hpool : A0.pool = emp := rfl
    rw [hpool]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun _ => ?_
    refine SepWPp.pure_elim fun ⟨hx0m, hx1m⟩ => ?_
    refine SepWPp.pure_elim fun htrm => ?_
    have hcur := sliceCursorAfter_append_eq_seedChain slot curPtr [b0] rem1
    simp only [List.singleton_append, List.length_singleton, pointsToBytes_cons,
      pointsToBytes_nil, sepConj_emp] at hcur
    refine SepWPp.mono_pre_seedChain ?_
      (hnext sm hpcm hrunm hspm hclm (htrm.trans htr) hcsm hx0m hx1m)
    rw [hcur, stackAt_c3Sub_to_decodeVarint (sp0 - 0xf0#64)]
    exact sep_ac_seedChain (by ac_rfl)

/-! ## 2. Straight-line phases -/

set_option maxHeartbeats 400000 in
/-- Phase A (`+0x0a8 → bl decode_varint#4` at `+0x0bc`): `remaining > outerTailLen`. -/
theorem c3a_phaseA_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (bufRef slot ptr sp0 : BitVec 64) (bs : List (BitVec 8)) (outer : Nat)
    (hgt : outer < bs.length) (hlen : bs.length < 2 ^ 62)
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = lsmpl.base 516 + 0xa8#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 0xf0#64)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx21 : s0.readReg64 .x21 = BitVec.ofNat 64 outer)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 515 →
      s1.status = .Running →
      s1.sp = sp0 - 0xf0#64 →
      LibsignalCodeLoaded lsmpl s1.mem →
      s1.trace = s_init.trace →
      s1.readReg64 .lr = lsmpl.base 516 + 0xc0#64 →
      s1.readReg64 .x0 = bufRef →
      C3aKeep s0 s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot ptr bs ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F) Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s0
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr bs ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F) Q Qp := by
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hgt hlen
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hgt hlen
  change s0.pc = (blkPl_516).base + 0xa8#64 at hpc
  have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h21 : s0.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 outer := hx21
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 515) hcl ?_
  unfold sliceCursorAt
  simp only [sepConj_assoc]
  iterate 6 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hcl1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [hsp, arm64_norm]) hcl1 (by simp only [htr, arm64_norm])
    (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  unfold sliceCursorAt
  exact sep_ac_seedChain (by ac_rfl)

set_option maxHeartbeats 400000 in
/-- Phase C (`+0x0c0 → +0x118 → +0x1fc → bl decode_varint#4` at `+0x220`): key `0x1a` dispatches
to field 3; the niche `[a + 0x48] == noneCap` takes the default `ChainKey` init; wire type 2. -/
theorem c3a_phaseC_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (a bufRef sp0 : BitVec 64)
    {ret : BitVec 64} {s_init s2 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s2.pc = lsmpl.base 516 + 0xc0#64)
    (hrun : s2.status = .Running)
    (hsp : s2.sp = sp0 - 0xf0#64)
    (hcl : LibsignalCodeLoaded lsmpl s2.mem)
    (htr : s2.trace = s_init.trace)
    (hx0 : s2.readReg64 .x0 = 0#64)
    (hx1 : s2.readReg64 .x1 = 0x1a#64)
    (hx19 : s2.readReg64 .x19 = bufRef)
    (hx20 : s2.readReg64 .x20 = a)
    (hx23 : s2.readReg64 .x23 = 1#64)
    (hnext : ∀ (s3 : State),
      s3.pc = lsmpl.base 515 →
      s3.status = .Running →
      s3.sp = sp0 - 0xf0#64 →
      LibsignalCodeLoaded lsmpl s3.mem →
      s3.trace = s_init.trace →
      s3.readReg64 .lr = lsmpl.base 516 + 0x224#64 →
      s3.readReg64 .x0 = bufRef →
      C3aKeep s2 s3 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s3
        ((chain3VecAt A0 (a + 0x48#64) [] ∗
          ((a + 0x60#64) ↦₃₂ 0#32) ∗
          memRegion (a + 0x64#64) 4) ∗ F) Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s2
      ((((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24) ∗ F) Q Qp := by
  change s2.pc = (blkPl_516).base + 0xc0#64 at hpc
  have h0 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s2.readReg64 (Reg.gpr 1#5) = 0x1a#64 := hx1
  have h19 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s2.readReg64 (Reg.gpr 20#5) = a := hx20
  have h23 : s2.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 515) hcl ?_
  rw [memRegion24_split_ck_seedChain a]
  unfold noneCap
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w50
  apply SepWP.exists_elim; intro w58
  apply SepWP.exists_elim; intro w60
  iterate 24 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hcl1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [hsp, arm64_norm]) hcl1 (by simp only [htr, arm64_norm])
    (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  have hvec := default_cells_entail_chain3VecAt A0 (a + 0x48#64)
  have h48_8 : (a + 0x48#64) + 8#64 = a + 0x50#64 := by bv_omega
  have h48_16 : (a + 0x48#64) + 16#64 = a + 0x58#64 := by bv_omega
  rw [h48_8, h48_16] at hvec
  refine Entails.trans (sep_ac_seedChain (Q :=
    (((a + 0x48#64) ↦₆₄ 0#64) ∗ ((a + 0x50#64) ↦₆₄ 1#64) ∗ ((a + 0x58#64) ↦₆₄ 0#64)) ∗
      (((a + 0x60#64) ↦₃₂ 0#32) ∗ memRegion (a + 0x64#64) 4 ∗ F)) (by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hvec) ?_
  exact sep_ac_seedChain (by ac_rfl)

set_option maxHeartbeats 400000 in
/-- Phase E (`+0x224 → +0x340 → +0x368`): `x25 := remaining - len = |after|`. -/
theorem c3a_phaseE_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (bufRef slot ptr : BitVec 64) (ck after : List (BitVec 8))
    (hlen : ck.length + after.length < 2 ^ 62)
    {ret : BitVec 64} {s_init s4 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s4.pc = lsmpl.base 516 + 0x224#64)
    (hrun : s4.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s4.mem)
    (htr : s4.trace = s_init.trace)
    (hx0 : s4.readReg64 .x0 = 0#64)
    (hx1 : s4.readReg64 .x1 = BitVec.ofNat 64 ck.length)
    (hx19 : s4.readReg64 .x19 = bufRef)
    (hnext : ∀ (s5 : State),
      s5.pc = lsmpl.base 516 + 0x368#64 →
      s5.status = .Running →
      s5.sp = s4.sp →
      LibsignalCodeLoaded lsmpl s5.mem →
      s5.trace = s_init.trace →
      s5.readReg64 .x25 = BitVec.ofNat 64 after.length →
      C3aKeep s4 s5 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s5
        (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (ck ++ after)) ∗ F) Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s4
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (ck ++ after)) ∗ F) Q Qp := by
  have hlen_app : (ck ++ after).length = ck.length + after.length := List.length_append
  have hule := c3a_ule_ofNat_add_right (m := ck.length) (k := after.length) hlen
  have hsub := c3a_ofNat_add_sub_left ck.length after.length
  change s4.pc = (blkPl_516).base + 0x224#64 at hpc
  have h0 : s4.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s4.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 ck.length := hx1
  have h19 : s4.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 516 + 0x368#64) hcl ?_
  unfold sliceCursorAt
  rw [hlen_app]
  simp only [sepConj_assoc]
  iterate 5 wp_step
  refine SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [hrun, arm64_norm]) ?_
  intro hcl1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]; rfl) (by simp only [hrun, arm64_norm])
    (by simp only [arm64_norm]) hcl1 (by simp only [htr, arm64_norm])
    (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  unfold sliceCursorAt
  rw [hlen_app]
  exact sep_ac_seedChain (by ac_rfl)

/-! ## 3. Segment 3a -/

set_option maxHeartbeats 400000 in
theorem step_chain3_seg3a_placed [LibsignalPlacement] (ext : String → Option (State → State)) :
    Chain3Seg3aPlacedStmt ext := by
  intro hC a bufRef slot ptr sp0 ck_body afterCk outerTailLen hck_lt houter_le hlen_lt
    x R ret s_init s0 F Q
    hpc hrun hsp halign hcl htr hvregs hx29 hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27 hx28 hnext
  have hlenA : (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)).length < 2 ^ 62 := by
    simp only [List.length_cons, List.length_append]; omega
  have hgtA : outerTailLen < (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)).length := by
    simp only [List.length_cons, List.length_append]; omega
  have hlenB : (BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)).length < 2 ^ 62 := by
    simp only [List.length_cons, List.length_append]; omega
  have hlenE : ck_body.length + afterCk.length < 2 ^ 62 := by omega
  refine SepWPp.mono_pre_seedChain (sep_ac_seedChain (Q :=
    ((bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
      stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗
      ((((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24) ∗ F)) (by ac_rfl)) ?_
  refine c3a_phaseA_placed bufRef slot ptr sp0 _ outerTailLen hgtA hlenA
    hpc hrun hsp hcl htr hx19 hx21 ?_
  intro s1 hpc1 hrun1 hsp1 hcl1 htr1 hlr1 hx0_1 hk1
  refine step_c3a_decodeVarint_placed_atW hC bufRef slot ptr sp0
    (lsmpl.base 516 + 0xc0#64) 0x1a#64 0x1a#8
    (BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk))
    (c3a_decodeVarint_1a _) hlenA
    hpc1 hrun1 hsp1 halign hcl1 htr1 hlr1 hx0_1 rfl ?_
  intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hcs2 hx0_2 hx1_2
  have hk2 : C3aKeep s0 s2 := hk1.trans (.of_calleeSaved hcs2)
  refine SepWPp.mono_pre_seedChain (sep_ac_seedChain (Q :=
    (((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24) ∗
      (((bufRef ↦₆₄ slot) ∗ (ptr ↦₈ 0x1a#8) ∗
        sliceCursorAt slot (ptr + 1#64) (BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)) (by ac_rfl)) ?_
  refine c3a_phaseC_placed a bufRef sp0 hpc2 hrun2 hsp2 hcl2 htr2 hx0_2 hx1_2
    (hk2.1.trans hx19) (hk2.2.1.trans hx20) (hk2.2.2.2.2.1.trans hx23) ?_
  intro s3 hpc3 hrun3 hsp3 hcl3 htr3 hlr3 hx0_3 hk3'
  have hk3 : C3aKeep s0 s3 := hk2.trans hk3'
  refine SepWPp.mono_pre_seedChain (sep_ac_seedChain (Q :=
    ((bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot (ptr + 1#64) (BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
      stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗
      ((ptr ↦₈ 0x1a#8) ∗ (chain3VecAt A0 (a + 0x48#64) [] ∗ ((a + 0x60#64) ↦₃₂ 0#32) ∗
        memRegion (a + 0x64#64) 4) ∗ F)) (by ac_rfl)) ?_
  refine step_c3a_decodeVarint_placed_atW hC bufRef slot (ptr + 1#64) sp0
    (lsmpl.base 516 + 0x224#64) (BitVec.ofNat 64 ck_body.length)
    (BitVec.ofNat 8 ck_body.length) (ck_body ++ afterCk)
    (c3a_decodeVarint_lt128 ck_body.length hck_lt _) hlenB
    hpc3 hrun3 hsp3 halign hcl3 htr3 hlr3 hx0_3 rfl ?_
  intro s4 hpc4 hrun4 hsp4 hcl4 htr4 hcs4 hx0_4 hx1_4
  have hk4 : C3aKeep s0 s4 := hk3.trans (.of_calleeSaved hcs4)
  refine SepWPp.mono_pre_seedChain (sep_ac_seedChain (Q :=
    ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot (ptr + 1#64 + 1#64) (ck_body ++ afterCk)) ∗
      (((ptr + 1#64) ↦₈ BitVec.ofNat 8 ck_body.length) ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX ∗
        (ptr ↦₈ 0x1a#8) ∗ (chain3VecAt A0 (a + 0x48#64) [] ∗ ((a + 0x60#64) ↦₃₂ 0#32) ∗
          memRegion (a + 0x64#64) 4) ∗ F)) (by ac_rfl)) ?_
  refine c3a_phaseE_placed bufRef slot (ptr + 1#64 + 1#64) ck_body afterCk hlenE
    hpc4 hrun4 hcl4 htr4 hx0_4 hx1_4 (hk4.1.trans hx19) ?_
  intro s5 hpc5 hrun5 hsp5 hcl5 htr5 hx25_5 hk5'
  have hk5 : C3aKeep s0 s5 := hk4.trans hk5'
  obtain ⟨k19, k20, k21, k22, k23, k24, k26, k27, k28, k29, kv⟩ := hk5
  refine SepWPp.mono_pre_seedChain ?_ (hnext s5 hpc5 hrun5 hcl5 htr5 (kv.trans hvregs)
    ⟨hsp5.trans hsp4, k29.trans hx29, k19.trans hx19, k20.trans hx20, k21.trans hx21,
     k22.trans hx22, k23.trans hx23, k24.trans hx24, hx25_5, k26.trans hx26, k27.trans hx27,
     k28.trans hx28⟩)
  have hptr2 : ptr + 1#64 + 1#64 = ptr + 2#64 := by bv_omega
  rw [hptr2, ← c3a_hdr_combine ptr ck_body.length]
  exact sep_ac_seedChain (by ac_rfl)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
