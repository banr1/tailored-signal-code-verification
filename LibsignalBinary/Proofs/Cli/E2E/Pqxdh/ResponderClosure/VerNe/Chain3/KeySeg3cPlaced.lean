/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.KeySeg3c
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.KeyInnerPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import ProofLib.SepLogic.WPp

/-!
# Placed `message::merge<Chain> [local#4]`: ChainKey Key-Bytes Field (`Chain3Seg3cPlacedStmt`)

`[LibsignalPlacement]` Block-`516` counterpart of `VerNe.Chain3.KeySeg3c`.
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
  (sliceCursorAt sliceCursorAfter BytesMergeGhost DecodeVarintSlowGhost)
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG (SepWPp.focus_pre)
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalPlacement
open CryptoVerification.CliHandshake.Placed

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  Arm64.calleeSavedVRegs_advancePC Arm64.calleeSavedVRegs_setPC Arm64.calleeSavedVRegs_setMem
  Arm64.calleeSavedVRegs_setPState Arm64.calleeSavedVRegs_writeReg64 Arm64.calleeSavedVRegs_writeReg32
  Arm64.calleeSavedVRegs_writeReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.calleeSavedVRegs_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.sp_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg64_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg32_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain
attribute [local simp, local arm64_norm]
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.getLsbD_63_eq_seedChain

/-! ## 1. `bytes::merge [local#5]` call -/

set_option maxHeartbeats 400000 in
/-- `bl bytes::merge [local#5]` on a `< 128`-byte field `[|b|] ++ b` (possibly empty) into the
empty `chain3VecAt A0 v []` (`cap = 0`). -/
theorem c3k3c_bm_call_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (hC : Chain3CalleesPlacedW ext)
    (v bufRef slot curPtr sp0 ret_pc : BitVec 64) (b rest : List (BitVec 8))
    (hb : b.length < 128)
    (hlen_lt : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 514)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 0xf0#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : (s.readReg64 .x0).setWidth 8 = 2#8)
    (hx1 : s.readReg64 .x1 = v)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp0 - 0xf0#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → sm.readReg64 .x0 = 0#64 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        ((vecU8 A0 v b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      ((chain3VecAt A0 v [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R)) := by
  have hlen_lt63 : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 63 := by omega
  refine SepWPp.mono_pre_seedChain
    (sepConj_mono_left (sepConj_mono_left (chain3VecAt_nil_elim A0 v))) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun ptr0 => ?_
  refine SepWPp.call_lscl_c3
    (x := BytesMergeGhost.mk .lengthDelimited v 0#64 ptr0 [] bufRef slot curPtr
      ([BitVec.ofNat 8 b.length] ++ b ++ rest))
    (F := F)
    hC.bm hpc hrun (c3k3c_spAligned hsp halign) hcl hlr ?_ ?_ ?_ ?_
  · intro R' hm
    refine intro_withLsCl_c3 hcl ?_
    rw [stackAt_c3Sub_eq_bytesMerge (sp0 - 0xf0#64)] at hm
    dsimp only [bytesMerge3RawSpec]
    have hpool : A0.pool = emp := rfl
    rw [hpool, hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen_lt63, Prost.bytesMergeCapOk_zero⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    dsimp only [bytesMerge3PlacedSpec, withLsCl, bytesMerge3RawSpec] at hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [bytesMerge3PlacedSpec, withLsCl, bytesMerge3RawSpec, chainMerge3PlacedSpecW,
      chainMerge3RawSpecW, Serialization.allocPanic] at hm ⊢
    simp only [allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hclm hcsm
    rw [hsp] at hspm
    have hmB := mergeBytes_lt128_seedChain b rest hb
    dsimp only [bytesMerge3PlacedSpec, withLsCl, bytesMerge3RawSpec]
    rw [hmB, hsp]
    dsimp only
    have hpool : A0.pool = emp := rfl
    rw [hpool]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun _ => ?_
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_elim fun hx0m => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_elim fun _ => ?_
    have hcur := sliceCursorAfter_append_eq_seedChain slot curPtr ([BitVec.ofNat 8 b.length] ++ b) rest
    have hlen1 : ([BitVec.ofNat 8 b.length] ++ b).length = b.length + 1 := by simp
    rw [hlen1] at hcur
    have hv : vecU8At A0 v cap' ptr' b ⊢ vecU8 A0 v b := by
      unfold vecU8
      exact Entails.sepExists_right cap' (Entails.sepExists_right ptr' (Entails.refl _))
    refine SepWPp.mono_pre_seedChain ?_
      (hnext sm hpcm hrunm hspm hclm (htrm.trans htr) hcsm hx0m)
    rw [hcur, ← stackAt_c3Sub_eq_bytesMerge (sp0 - 0xf0#64)]
    have hEq1 :
        (bufRef ↦₆₄ slot) ∗ emp ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX ∗
          vecU8At A0 v cap' ptr' b ∗
          ((curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
            sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest) ∗ F =
        vecU8At A0 v cap' ptr' b ∗
          ((bufRef ↦₆₄ slot) ∗
            (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
            sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
            stackAt (sp0 - 0xf0#64) chainMerge3SubStackX ∗ F) := by
      simp only [emp_sepConj]; ac_rfl
    have hEq2 :
        vecU8 A0 v b ∗
          ((bufRef ↦₆₄ slot) ∗
            (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
            sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
            stackAt (sp0 - 0xf0#64) chainMerge3SubStackX ∗ F) =
        (vecU8 A0 v b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F := by
      ac_rfl
    rw [hEq1, ← hEq2]
    exact sepConj_mono_left hv

/-! ## 2. Straight-line segments -/

set_option maxHeartbeats 400000 in
/-- Placed inner key `0x12` dispatch (`+0x380 → +0x3b8`): tag 2, wire type 2, `x1 = a + 0x48`, `x2 = bufRef`. -/
theorem step_c3k3c_dispatch_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (sp0 bufRef a : BitVec 64) (outerTailLen innerTailLen : Nat)
    {ret : BitVec 64} {s_init s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 0x380#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s_init)
    (hregs : Chain3InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s_init s)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx1 : s.readReg64 .x1 = 0x12#64)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 514 →
      s1.status = .Running → LibsignalCodeLoaded lsmpl s1.mem →
      s1.trace = s_init.trace → calleeSavedVRegs s1 = calleeSavedVRegs s_init →
      s1.readReg64 .lr = lsmpl.base 516 + 0x3bc#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 →
      s1.readReg64 .x1 = a + 0x48#64 →
      s1.readReg64 .x2 = bufRef →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s_init s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1 P Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s P Q Qp := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28⟩
  change s.pc = (blkPl_516).base + 0x380#64 at hpc
  have h0 : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s.readReg64 (Reg.gpr 1#5) = 0x12#64 := hx1
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 0x50#64 := hx29
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 outerTailLen := hx21
  have h22 : s.readReg64 (Reg.gpr 22#5) = sp0 - 0xe8#64 := hx22
  have h23 : s.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  have h24 : s.readReg64 (Reg.gpr 24#5) = 104#64 := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 innerTailLen := hx25
  have h26 : s.readReg64 (Reg.gpr 26#5) = s_init.readReg64 (Reg.gpr 26#5) := hx26
  have h27 : s.readReg64 (Reg.gpr 27#5) = s_init.readReg64 (Reg.gpr 27#5) := hx27
  have h28 : s.readReg64 (Reg.gpr 28#5) = s_init.readReg64 (Reg.gpr 28#5) := hx28
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 514) hcl ?_
  iterate 15 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hcl1
  exact hnext _ (by simp only [arm64_norm])
    (by simp only [hrun, arm64_norm]) hcl1
    (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
    (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    ⟨by simp only [hsp, arm64_norm],
     by simp only [h29, arm64_norm],
     by simp only [h19, arm64_norm],
     by simp only [h20, arm64_norm],
     by simp only [h21, arm64_norm],
     by simp only [h22, arm64_norm],
     by simp only [h23, arm64_norm],
     by simp only [h24, arm64_norm],
     by simp only [h25, arm64_norm],
     by simp only [h26, arm64_norm],
     by simp only [h27, arm64_norm],
     by simp only [h28, arm64_norm]⟩

set_option maxHeartbeats 400000 in
/-- Placed post-call return (`+0x3bc → +0x368`) back to the inner loop head when `x0 = 0`. -/
theorem step_c3k3c_ret_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (sp0 bufRef a : BitVec 64) (outerTailLen innerTailLen : Nat)
    {ret : BitVec 64} {s_init s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 0x3bc#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s_init)
    (hregs : Chain3InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s_init s)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 516 + 0x368#64 →
      s1.status = .Running → LibsignalCodeLoaded lsmpl s1.mem →
      s1.trace = s_init.trace → calleeSavedVRegs s1 = calleeSavedVRegs s_init →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s_init s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1 P Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s P Q Qp := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28⟩
  change s.pc = (blkPl_516).base + 0x3bc#64 at hpc
  have h0 : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 0x50#64 := hx29
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 outerTailLen := hx21
  have h22 : s.readReg64 (Reg.gpr 22#5) = sp0 - 0xe8#64 := hx22
  have h23 : s.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  have h24 : s.readReg64 (Reg.gpr 24#5) = 104#64 := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 innerTailLen := hx25
  have h26 : s.readReg64 (Reg.gpr 26#5) = s_init.readReg64 (Reg.gpr 26#5) := hx26
  have h27 : s.readReg64 (Reg.gpr 27#5) = s_init.readReg64 (Reg.gpr 27#5) := hx27
  have h28 : s.readReg64 (Reg.gpr 28#5) = s_init.readReg64 (Reg.gpr 28#5) := hx28
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 516 + 0x368#64) hcl ?_
  iterate 4 wp_step
  refine SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [hrun, arm64_norm]) ?_
  intro hcl1
  exact hnext _ (by simp only [arm64_norm]; rfl)
    (by simp only [hrun, arm64_norm]) hcl1
    (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
    ⟨by simp only [hsp, arm64_norm],
     by simp only [h29, arm64_norm],
     by simp only [h19, arm64_norm],
     by simp only [h20, arm64_norm],
     by simp only [h21, arm64_norm],
     by simp only [h22, arm64_norm],
     by simp only [h23, arm64_norm],
     by simp only [h24, arm64_norm],
     by simp only [h25, arm64_norm],
     by simp only [h26, arm64_norm],
     by simp only [h27, arm64_norm],
     by simp only [h28, arm64_norm]⟩

/-! ## 3. Main theorem: `chain3_seg3c_placed` -/

set_option maxHeartbeats 400000 in
/-- Placed segment 3c (`+0x368 → +0x368`): `ChainKey` inner field 2 (`key`). -/
theorem chain3_seg3c_placed [LibsignalPlacement] (ext : String → Option (State → State)) :
    Chain3Seg3cPlacedStmt ext := by
  intro hC a bufRef slot ptr sp0 k afterCk outerTailLen hk_lt hlen_lt x R ret s_init s0 F Q
    hpc hrun halign hcl htr hvregs hregs hnext
  have hpb : pbBytes 2 k = 0x12#8 :: BitVec.ofNat 8 k.length :: k :=
    DeserializeGeneral.pbBytes_lt128_eq_seedChain 2 (by decide) k hk_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 k.length] ++ k ++ afterCk
  have hcons_eq : pbBytes 2 k ++ afterCk = 0x12#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : afterCk.length < (0x12#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x12#8 :: rem1).length < 2 ^ 62 := by
    rw [← hcons_eq]; exact hlen_lt
  rw [hcons_eq]
  refine SepWPp.focus_pre
    (step_c3ck_ihead_placed sp0 bufRef a slot ptr outerTailLen 0x12#8 rem1 afterCk
      hlen_gt hlen_cons_lt hpc hrun hcl htr hvregs hregs ?_)
  intro s1 hpc1 hrun1 hcl1 htr1 hvregs1 hlr1 hx0_1 hregs1
  have hcons_app : (0x12#8 :: rem1) = [0x12#8] ++ rem1 := rfl
  rw [hcons_app]
  have hdv1 : decodeVarint ([0x12#8] ++ rem1) = some (0x12#64, rem1) := rfl
  refine SepWPp.focus_pre
    (c3ck_dv_call_placed hC bufRef slot ptr sp0
      (lsmpl.base 516 + 0x380#64) 0x12#64 [0x12#8] rem1
      hdv1 hlen_cons_lt hpc1 hrun1 hregs1.1 halign hcl1 htr1 hlr1 hx0_1 ?_)
  intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hcs2 hx0_2 hx1_2
  obtain ⟨hregs2, hvregs2⟩ := c3ck_regs_after_call hregs1 hvregs1 hsp2 hcs2
  refine step_c3k3c_dispatch_placed sp0 bufRef a outerTailLen afterCk.length
    hpc2 hrun2 hcl2 htr2 hvregs2 hregs2 hx0_2 hx1_2 ?_
  intro s3 hpc3 hrun3 hcl3 htr3 hvregs3 hlr3 hx0_3 hx1_3 hx2_3 hregs3
  have hrem1_lt : ([BitVec.ofNat 8 k.length] ++ k ++ afterCk).length < 2 ^ 62 := by
    simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
  have hlen1 : BitVec.ofNat 64 ([0x12#8] : List (BitVec 8)).length = 1#64 := rfl
  rw [hlen1]
  refine SepWPp.focus_pre
    (c3k3c_bm_call_placed hC (a + 0x48#64) bufRef slot (ptr + 1#64) sp0
      (lsmpl.base 516 + 0x3bc#64) k afterCk hk_lt hrem1_lt
      hpc3 hrun3 hregs3.1 halign hcl3 htr3 hlr3 hx0_3 hx1_3 hx2_3 ?_)
  intro s4 hpc4 hrun4 hsp4 hcl4 htr4 hcs4 hx0_4
  obtain ⟨hregs4, hvregs4⟩ := c3ck_regs_after_call hregs3 hvregs3 hsp4 hcs4
  refine step_c3k3c_ret_placed sp0 bufRef a outerTailLen afterCk.length
    hpc4 hrun4 hcl4 htr4 hvregs4 hregs4 hx0_4 ?_
  intro s5 hpc5 hrun5 hcl5 htr5 hvregs5 hregs5
  refine SepWPp.mono_pre_seedChain ?_
    (hnext s5 hpc5 hrun5 hcl5 htr5 hvregs5 hregs5)
  rw [DeserializeGeneral.pbBytes_ptr_advance_seedChain 2 (by decide) ptr k hk_lt,
    ← c3k3c_pointsTo_12_combine ptr k hk_lt]
  exact sep_ac_seedChain (by ac_rfl)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
