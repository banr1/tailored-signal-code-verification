/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8a
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8d
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8cPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8dPlaced
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 8 (`EkReceivedCt1Sampled`, `+1764`, Block `333`)

Relocatable (`Obj.MultiPlacedLib`) top-level proof for Variant 8 (`InnerState.ekReceivedCt1Sampled`,
`+1764 -> s0.x30`), composing `Authenticator` cloning, `<PolyEncoder>::from_pb`, and shared epilogue staging.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8Placed

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.FromPb
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8aPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8bPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8cPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8dPlaced

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

private theorem v8_sepWPp_seq_clean_lscl [LibsignalPlacement] {prog : Program}
    {mid target_pc : BitVec 64} {s : State} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    {P P_mid : SepProp} {Q : State → Prop}
    {post Qpan : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm →
      SepWPp prog target_pc sm P_mid post Qpan) :
    SepWPp prog target_pc s P post Qpan :=
  SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    (SepWP.mono h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ hcl' =>
      SepWPp.weaken_pre hPm (h2 sm hpc hrun hcl' hQ))

private theorem v8_sepWPp_bind_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64} {s : State}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    {P : SepProp} {Q_mid Q Qp : State → SepProp → Prop}
    (h1 : SepWPp prog mid s P Q_mid Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_mid sm Pm → SepWPp prog ret sm Pm Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL; obtain ⟨sm, hsteps1, hout1⟩ := h1 R hm hL
  rcases hout1 with ⟨hpcm, hrunm, Pm, hmm, hqm⟩ | hpan
  · obtain ⟨sf, hsteps2, hout2⟩ := h2 sm Pm hpcm hrunm (hcl.of_keepsFrozen hsteps1.keepsFrozen) hqm R hmm (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact ⟨sm, hsteps1, Or.inr hpan⟩

private theorem v8_sepWPp_call_ret_entails_lscl [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    {x : α} {s : State} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    {P_step F : SepProp} {Qpan : State → SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hpre : P_step ⊢ spec.pre x s)
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf) (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post (fun sf P_f => P_f ⊢ Qpan sf) :=
  SepWPp.call (x := x) (F := F) hcall hpc hrun hsp_align hlr
    (fun R' hm => by
      rw [sepConj_assoc] at hm
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hcl, Satisfies.mono (sepConj_mono_left hpre) hm⟩)
    (fun sf code R' _ hm => by
      dsimp only [withLsCodeLoaded] at hm
      rw [hexit_eq] at hm; exact not_satisfies_false_sepConj hm)
    (hoom := fun sf R' _ hm => by
      dsimp only [withLsCodeLoaded] at hm
      rw [hoom_eq] at hm; exact False.elim (not_satisfies_false_sepConj hm))
    (fun sf _ => by
      dsimp only [withLsCodeLoaded]
      exact hpan sf)
    (fun sf hpcf hrunf hspf hcsf => by
      dsimp only [withLsCodeLoaded]
      exact SepWPp.of_sepWP_ret (hnext sf hpcf hrunf hspf hcsf))

set_option maxHeartbeats 800000 in
theorem v8_stage_11264_to_ret_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)} (hA : FromPbAllocHooks A ext)
    (s0 s : State) (fsp out tag ep pa1 l1 pa2 l2 ca3 pa3 ca4 pa4 ca5 pa5 : BitVec 64) (bs : List (BitVec 8)) (hbs : bs.length = 384) (hi32 : BitVec 32) (enc : PolyEncoder) (P_heap : SepProp) (hreloc :
      ((out + 8#64) ↦₆₄ tag) ∗ (((out + 8#64) + 8#64) ↦ₛ bs) ∗ (((out + 8#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap ⊢ polyEncoderAt A (out + 8#64) enc) (rootKey macKey es ek ct1 : List (BitVec 8))
    (hl1 : l1 = BitVec.ofNat 64 rootKey.length) (hl2 : l2 = BitVec.ofNat 64 macKey.length) (hes : es.length = 2080) (hek : ek.length = 1152) (hct1 : ct1.length = 960) (Frame : SepProp)
    (halign : (s0.sp &&& 15#64 == 0#64) = true) (hfsp : fsp = s0.sp - 2400#64) (hpc : s.pc = lsmpl.base 333 + 11264#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx15 : s.readReg64 .x15 = tag) (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = pa5) (hx22 : s.readReg64 .x22 = l1) (hx23 : s.readReg64 .x23 = fsp + 848#64) (hx26 : s.readReg64 .x26 = ca3)
    (hx28 : s.readReg64 .x28 = l2) (htr : TraceCalleeSaved s s0) : SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s ((memRegion (fsp + 72#64) 48 ∗ memRegion (fsp + 160#64) 16 ∗ memRegion (fsp + 192#64) 8 ∗
        memRegion (fsp + 208#64) 8 ∗ memRegion (fsp + 232#64) 8 ∗ memRegion (fsp + 240#64) 1648) ∗ stackAt fsp encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       memRegion fsp 64 ∗ ((fsp + 64#64) ↦₆₄ ca5) ∗ ((fsp + 120#64) ↦₆₄ ep) ∗ memRegion (fsp + 128#64) 32 ∗ ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 200#64) ↦₆₄ pa1) ∗ ((fsp + 216#64) ↦₆₄ pa4) ∗ ((fsp + 224#64) ↦₆₄ ca4) ∗ ((fsp + 1888#64) ↦₆₄ tag) ∗ v8_encCellsAt (fsp + 1888#64) bs ∗
       ((fsp + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ memRegion (fsp + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ P_heap ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗
       vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1 ∗ Frame) (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.ok (.ekReceivedCt1Sampled { uc := { auth := { rootKey := rootKey, macKey := macKey }, es := es, ek := ek, ct1 := ct1, epoch := ep }, sending_ct1 := enc })) ∗
          stackAt s0.sp statesFromPbStack ∗ Frame) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp ▸ sp_sub_2400_align s0.sp halign
  refine SepWP.weaken_pre (sepConj_mono_left (v8_fsp_split_11264_all fsp)) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine ProofLib.SepWP.exists_left fun u887 => ProofLib.SepWP.exists_left fun u880 =>
    ProofLib.SepWP.exists_left fun u864 => ProofLib.SepWP.exists_left fun uq848 =>
    ProofLib.SepWP.exists_left fun u832 => ProofLib.SepWP.exists_left fun uq816 =>
    ProofLib.SepWP.exists_left fun uq800 => ProofLib.SepWP.exists_left fun uq784 =>
    ProofLib.SepWP.exists_left fun uq768 => ProofLib.SepWP.exists_left fun uq752 =>
    ProofLib.SepWP.exists_left fun uq736 => ProofLib.SepWP.exists_left fun uq720 =>
    ProofLib.SepWP.exists_left fun uq704 => ProofLib.SepWP.exists_left fun uq688 =>
    ProofLib.SepWP.exists_left fun uq672 => ProofLib.SepWP.exists_left fun uq656 =>
    ProofLib.SepWP.exists_left fun uq640 => ProofLib.SepWP.exists_left fun uq624 =>
    ProofLib.SepWP.exists_left fun uq608 => ProofLib.SepWP.exists_left fun w592 =>
    ProofLib.SepWP.exists_left fun q576 => ProofLib.SepWP.exists_left fun bs240 =>
    ProofLib.SepWP.exists_left fun u232 => ProofLib.SepWP.exists_left fun u208 =>
    ProofLib.SepWP.exists_left fun w192 => ProofLib.SepWP.exists_left fun d172 =>
    ProofLib.SepWP.exists_left fun u160 => ProofLib.SepWP.exists_left fun w112 =>
    ProofLib.SepWP.exists_left fun w104 => ProofLib.SepWP.exists_left fun d96 =>
    ProofLib.SepWP.exists_left fun d92 => ?_
  have hstep := v8_stage_11264_to_8180_placed (ext := ext) s0 s fsp out tag l1 pa1 l2 pa2 ca3 pa3 pa4 ca5 pa5 (hi32 ++ enc.idx) bs d96 w104 w112 u160 d172 w192 u208 u232
    uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816 u832 uq848 u864 u880 u887 (stackAt fsp encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
     memRegion fsp 64 ∗ memRegion (fsp + 72#64) 20 ∗ ((fsp + 92#64) ↦₃₂ d92) ∗ memRegion (fsp + 100#64) 4 ∗ ((fsp + 120#64) ↦₆₄ ep) ∗ memRegion (fsp + 128#64) 32 ∗
     memRegion (fsp + 168#64) 4 ∗ ((fsp + 224#64) ↦₆₄ ca4) ∗ ((fsp + 240#64) ↦ₛ bs240.val) ∗ memRegion (fsp + 568#64) 8 ∗ ((fsp + 576#64) ↦₁₂₈ q576) ∗
     ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗ memRegion (fsp + 599#64) 9 ∗ memRegion (fsp + 840#64) 8 ∗ memRegion (fsp + 871#64) 9 ∗ memRegion (fsp + 895#64) 993 ∗
     ((fsp + 1888#64) ↦₆₄ tag) ∗ memRegion (fsp + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ P_heap ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗
     vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1 ∗ Frame) hfsp_align hpc hrun hsp hx15 hx19 hx21 hx22 hx23 hx26 hx28 htr
  refine SepWP.weaken_pre ?_ (EncoderFromPb.seq_clean hstep ?_)
  · unfold v8_stagingSlotsPre; exact Entails.of_eq (by ac_rfl)
  intro s2 hpc2 hrun2 ⟨hsp2, hx6_2, hx8_2, hx15_2, hx20_2, hx13_2, hx25_2, hx30_2, hx9_2, hx14_2, hx18_2, hx17_2, hx0_2, hx3_2, hx27_lo_2, hx27_mid_2, hx27_hi_2,
    hx4_2, hx5_2, hx21_2, hx7_2, hx2_2, hx11_2, hx22_2, hx24_2, hx10_2, hx26_2, hx12_2, hx1_2, hx28_2, hx16_2, hx19_2, hx23_2, htr2⟩
  subst hfsp
  have h92 := v8_fsp_64_72_entails_92 (s0.sp - 2400#64) ca5
  have h96 := v8_fsp_96_100_entails_8 (s0.sp - 2400#64) ((loByte (v8_wordAt bs 104)).zeroExtend 32)
  have h176 := v8_fsp_176_184_cells_entails_16 (s0.sp - 2400#64) pa3 pa2
  have h200 := ProofLib.pointsTo64_entails_memRegion ((s0.sp - 2400#64) + 200#64) pa1
  have h216 := ProofLib.pointsTo64_entails_memRegion ((s0.sp - 2400#64) + 216#64) pa4
  have h1888 := v8_fsp_1888_entails_epilogue (s0.sp - 2400#64) tag (hi32 ++ enc.idx) bs hbs
  have hP2_ep : (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗
      v8_stagingSlotsPost (s0.sp - 2400#64) bs pa5 l2 ∗ v8_encCellsAt ((s0.sp - 2400#64) + 1888#64) bs ∗ (((s0.sp - 2400#64) + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗ memRegion (s0.sp - 2400#64) 64 ∗ memRegion ((s0.sp - 2400#64) + 72#64) 20 ∗
       (((s0.sp - 2400#64) + 92#64) ↦₃₂ d92) ∗ memRegion ((s0.sp - 2400#64) + 100#64) 4 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ ep) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗
       memRegion ((s0.sp - 2400#64) + 168#64) 4 ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ (((s0.sp - 2400#64) + 240#64) ↦ₛ bs240.val) ∗ memRegion ((s0.sp - 2400#64) + 568#64) 8 ∗
       (((s0.sp - 2400#64) + 576#64) ↦₁₂₈ q576) ∗ (((s0.sp - 2400#64) + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗ memRegion ((s0.sp - 2400#64) + 599#64) 9 ∗ memRegion ((s0.sp - 2400#64) + 840#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 871#64) 9 ∗ memRegion ((s0.sp - 2400#64) + 895#64) 993 ∗ (((s0.sp - 2400#64) + 1888#64) ↦₆₄ tag) ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ P_heap ∗
       vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗ vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1 ∗ Frame) ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗ epilogueStackSlots (s0.sp - 2400#64) d92 ((loByte (v8_wordAt bs 128)).zeroExtend 32)
        pa5 960#64 ep l2 1152#64 (v8_wordAt bs 0) ca4 l2 bs240.val q576 w592 (v8_quadAt bs 152) (v8_quadAt bs 168) (v8_quadAt bs 184) (v8_quadAt bs 200)
        (v8_quadAt bs 216) (v8_quadAt bs 232) (v8_quadAt bs 248) (v8_quadAt bs 264) (v8_quadAt bs 280) (v8_quadAt bs 296) (v8_quadAt bs 312) (v8_quadAt bs 328) (v8_quadAt bs 344) (v8_quadAt bs 360) (v8_wordAt bs 376)
        (v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)) (v8_wordAt bs 144 >>> 8) (unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) (v8_wordAt bs 112 >>> 8)
        (v8_wordAt bs 0 ++ tag) (v8_wordAt bs 16 ++ v8_wordAt bs 8) (v8_wordAt bs 24) ∗ epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗
      (P_heap ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗ vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1 ∗ Frame) := by
    unfold v8_stagingSlotsPost epilogueStackSlots epilogueStackGaps
    refine Entails.trans (Entails.of_eq (show _ = (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 20) ∗
      ((((s0.sp - 2400#64) + 96#64) ↦₃₂ (loByte (v8_wordAt bs 104)).zeroExtend 32) ∗ memRegion ((s0.sp - 2400#64) + 100#64) 4) ∗ ((((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2)) ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ tag) ∗ v8_encCellsAt ((s0.sp - 2400#64) + 1888#64) bs ∗
       (((s0.sp - 2400#64) + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗ (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       (((s0.sp - 2400#64) + 92#64) ↦₃₂ d92) ∗ (((s0.sp - 2400#64) + 104#64) ↦₆₄ pa5) ∗ (((s0.sp - 2400#64) + 112#64) ↦₆₄ 960#64) ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ ep) ∗
       memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ (((s0.sp - 2400#64) + 160#64) ↦₆₄ l2) ∗ memRegion ((s0.sp - 2400#64) + 168#64) 4 ∗ (((s0.sp - 2400#64) + 172#64) ↦₃₂ (loByte (v8_wordAt bs 128)).zeroExtend 32) ∗
       (((s0.sp - 2400#64) + 192#64) ↦₆₄ 1152#64) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ v8_wordAt bs 0) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ l2) ∗
       (((s0.sp - 2400#64) + 240#64) ↦ₛ bs240.val) ∗ memRegion ((s0.sp - 2400#64) + 568#64) 8 ∗ (((s0.sp - 2400#64) + 576#64) ↦₁₂₈ q576) ∗ (((s0.sp - 2400#64) + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
       memRegion ((s0.sp - 2400#64) + 599#64) 9 ∗ (((s0.sp - 2400#64) + 608#64) ↦₁₂₈ v8_quadAt bs 152) ∗ (((s0.sp - 2400#64) + 624#64) ↦₁₂₈ v8_quadAt bs 168) ∗ (((s0.sp - 2400#64) + 640#64) ↦₁₂₈ v8_quadAt bs 184) ∗
       (((s0.sp - 2400#64) + 656#64) ↦₁₂₈ v8_quadAt bs 200) ∗ (((s0.sp - 2400#64) + 672#64) ↦₁₂₈ v8_quadAt bs 216) ∗ (((s0.sp - 2400#64) + 688#64) ↦₁₂₈ v8_quadAt bs 232) ∗
       (((s0.sp - 2400#64) + 704#64) ↦₁₂₈ v8_quadAt bs 248) ∗ (((s0.sp - 2400#64) + 720#64) ↦₁₂₈ v8_quadAt bs 264) ∗ (((s0.sp - 2400#64) + 736#64) ↦₁₂₈ v8_quadAt bs 280) ∗
       (((s0.sp - 2400#64) + 752#64) ↦₁₂₈ v8_quadAt bs 296) ∗ (((s0.sp - 2400#64) + 768#64) ↦₁₂₈ v8_quadAt bs 312) ∗ (((s0.sp - 2400#64) + 784#64) ↦₁₂₈ v8_quadAt bs 328) ∗
       (((s0.sp - 2400#64) + 800#64) ↦₁₂₈ v8_quadAt bs 344) ∗ (((s0.sp - 2400#64) + 816#64) ↦₁₂₈ v8_quadAt bs 360) ∗ (((s0.sp - 2400#64) + 832#64) ↦₆₄ v8_wordAt bs 376) ∗ memRegion ((s0.sp - 2400#64) + 840#64) 8 ∗
       (((s0.sp - 2400#64) + 848#64) ↦₁₂₈ v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)) ∗ (((s0.sp - 2400#64) + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v8_wordAt bs 144 >>> 8)) ∗
       memRegion ((s0.sp - 2400#64) + 871#64) 9 ∗ (((s0.sp - 2400#64) + 880#64) ↦₆₄ unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) ∗
       (((s0.sp - 2400#64) + 888#64) ↦ₛ EncoderFromPb.loBytes7 (v8_wordAt bs 112 >>> 8)) ∗ memRegion ((s0.sp - 2400#64) + 895#64) 993 ∗ statesFromPbSavedCells s0 ∗ P_heap ∗
       vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗ vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1 ∗ Frame) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono h92 (sepConj_mono h96 (sepConj_mono h176 (sepConj_mono h200 (sepConj_mono h216 (sepConj_mono_left h1888)))))) ?_
    exact Entails.of_eq (by ac_rfl)
  have hep := states_from_pb_epilogue_8180_placed hA.memcpy s0 s2 out d92 ((loByte (v8_wordAt bs 128)).zeroExtend 32) pa5 960#64 ep l2 1152#64 (v8_wordAt bs 0) ca4 l2 bs240.val bs240.property q576 w592
    (v8_quadAt bs 152) (v8_quadAt bs 168) (v8_quadAt bs 184) (v8_quadAt bs 200) (v8_quadAt bs 216) (v8_quadAt bs 232) (v8_quadAt bs 248) (v8_quadAt bs 264)
    (v8_quadAt bs 280) (v8_quadAt bs 296) (v8_quadAt bs 312) (v8_quadAt bs 328) (v8_quadAt bs 344) (v8_quadAt bs 360) (v8_wordAt bs 376) (v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144))
    (v8_wordAt bs 144 >>> 8) (unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) (v8_wordAt bs 112 >>> 8) (v8_wordAt bs 0 ++ tag) (v8_wordAt bs 16 ++ v8_wordAt bs 8) (v8_wordAt bs 24)
    (P_heap ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗ vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1 ∗ Frame) halign hpc2 hrun2 hsp2 hx6_2 hx19_2 hx23_2 htr2
  rw [hx8_2, hx15_2, hx20_2, hx13_2, hx25_2, hx30_2, hx9_2, hx14_2, hx18_2, hx17_2, hx0_2, hx3_2, hx27_lo_2, hx27_mid_2, hx27_hi_2, hx4_2, hx5_2, hx21_2, hx7_2,
      hx2_2, hx11_2, hx22_2, hx24_2, hx10_2, hx26_2, hx12_2, hx1_2, hx28_2, hx16_2] at hep
  refine SepWP.weaken_pre hP2_ep (SepWP.mono hep ?_)
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
  refine ⟨Entails.trans hPf ?_, hsp_f, hcs_f, htr_f⟩
  have hout := v8_epilogueOutFull_entails_ekReceivedCt1Sampled A (F := F) out tag l1 pa1 l2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 ep bs hbs hi32 enc P_heap hreloc rootKey macKey es ek ct1 hl1 hl2 hes hek hct1
    (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592) bs240.val bs240.property (v8_wordAt bs 0 ++ tag) (v8_wordAt bs 16 ++ v8_wordAt bs 8) (v8_wordAt bs 24)
  refine Entails.trans (Entails.of_eq (show _ = (epilogueOutFull out 10#64 tag (v8_wordAt bs 0) (v8_wordAt bs 8) (v8_wordAt bs 16) (v8_wordAt bs 24) (v8_wordAt bs 32) (v8_wordAt bs 40)
      (v8_wordAt bs 48) (v8_wordAt bs 56) (v8_wordAt bs 64) (v8_wordAt bs 72) ((v8_wordAt bs 80).extractLsb' 0 8) ((v8_wordAt bs 80).extractLsb' 8 32)
      ((v8_wordAt bs 80).extractLsb' 40 16) ((v8_wordAt bs 80).extractLsb' 56 8) (v8_wordAt bs 88) (v8_wordAt bs 96) (loByte (v8_wordAt bs 104)) (unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112)))
      (overlapWord7 (unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) (v8_wordAt bs 112 >>> 8)) (v8_wordAt bs 120) (((loByte (v8_wordAt bs 128)).zeroExtend 32).setWidth 8)
      (v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)) (overlapWord7 ((v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)).extractLsb' 64 64) (v8_wordAt bs 144 >>> 8))
      (v8_quadAt bs 152) (v8_quadAt bs 168) (v8_quadAt bs 184) (v8_quadAt bs 200) (v8_quadAt bs 216) (v8_quadAt bs 232) (v8_quadAt bs 248) (v8_quadAt bs 264)
      (v8_quadAt bs 280) (v8_quadAt bs 296) (v8_quadAt bs 312) (v8_quadAt bs 328) (v8_quadAt bs 344) (v8_quadAt bs 360) (v8_wordAt bs 376) (hi32 ++ enc.idx) l1 pa1 l1 l2 pa2 l2
      ca3 pa3 2080#64 ca4 pa4 1152#64 ca5 pa5 960#64 ep (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592) bs240.val (v8_wordAt bs 0 ++ tag) (v8_wordAt bs 16 ++ v8_wordAt bs 8) (v8_wordAt bs 24) ∗
     P_heap ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗ vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1) ∗ stackAt s0.sp statesFromPbStack ∗ Frame by ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_left hout) (Entails.of_eq (by ac_rfl))

theorem v8_call_encoder_from_pb_10900_to_10904_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hE : Variant2aPlaced.EncoderFromPbPlacedOkExt A ext)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp out pa5 l1 u8 pbA l2 : BitVec 64)
    (pbEnc : PolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (Frame : SepProp)
    (hpts : ∀ bs ∈ (pbToProtoPolyEncoder pbEnc).pts, bs.length ≤ 2 * 0x0555555555555555)
    (halign : (s0.sp &&& 15#64 == 0#64) = true) (hfsp : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 10900#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 1888#64) (hx1 : s.readReg64 .x1 = fsp + 240#64)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = pa5) (hx22 : s.readReg64 .x22 = l1)
    (hx23 : s.readReg64 .x23 = fsp + 848#64) (hx26 : s.readReg64 .x26 = u8)
    (hx27 : s.readReg64 .x27 = pbA) (hx28 : s.readReg64 .x28 = l2)
    (htr : TraceCalleeSaved s s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10904#64) s
      (memRegion (fsp + 1888#64) 400 ∗ v1_optProtoPolyEncoderWordsAt (fsp + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
       stackAt fsp encoderFromPbStack ∗ A.pool ∗ Frame)
      (fun sf Pf =>
        (Pf ⊢ resultPolyEncoderFromPbAt A (fsp + 1888#64) (fromPbResult (pbToProtoPolyEncoder pbEnc)) ∗
          memRegion (fsp + 240#64) 56 ∗ stackAt fsp encoderFromPbStack ∗ A.pool ∗ Frame) ∧
        sf.sp = fsp ∧ sf.readReg64 .x19 = out ∧ sf.readReg64 .x21 = pa5 ∧ sf.readReg64 .x22 = l1 ∧
        sf.readReg64 .x23 = fsp + 848#64 ∧ sf.readReg64 .x26 = u8 ∧ sf.readReg64 .x27 = pbA ∧
        sf.readReg64 .x28 = l2 ∧ TraceCalleeSaved sf s0)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  subst hfsp
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 2400#64 halign (by decide)
  have hpre : memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool ∗ Frame ⊢
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion ((s0.sp - 2400#64) + 1888#64) polyEncoderSize ∗ protoPolynomialEncoderAt A ((s0.sp - 2400#64) + 240#64) (pbToProtoPolyEncoder pbEnc) ∗ A.pool) ∗ Frame := by
    dsimp only [polyEncoderSize]
    refine Entails.trans (Entails.of_eq (show _ = (v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48) ∗ (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool ∗ Frame) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left (v1_optProtoPolyEncoderAt_pack_some A ((s0.sp - 2400#64) + 240#64) (pbToProtoPolyEncoder pbEnc) w0 w8 w16 w24 w32 w40 w48)) (Entails.of_eq (by ac_rfl))
  refine SepWPp.weaken_pre hpre ?_
  have hsub := v1_encoder_from_pb_ok_at_statesFromPb_placed hE
  refine v8_sepWPp_seq_clean_lscl hcl
    (mid := lsmpl.base 374)
    (P_mid := (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion ((s0.sp - 2400#64) + 1888#64) polyEncoderSize ∗
      protoPolynomialEncoderAt A ((s0.sp - 2400#64) + 240#64) (pbToProtoPolyEncoder pbEnc) ∗
      A.pool) ∗ Frame)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x30 = (blkPl_333).base + 10904#64 ∧
      sm.readReg64 .x0 = (s0.sp - 2400#64) + 1888#64 ∧
      sm.readReg64 .x1 = (s0.sp - 2400#64) + 240#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x21 = pa5 ∧
      sm.readReg64 .x22 = l1 ∧
      sm.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 ∧
      sm.readReg64 .x26 = u8 ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = l2 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · change s.pc = (blkPl_333).base + 10900#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 374) s _ _
    wp_steps
    refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_
    wp_done
  · intro sm hpc_m hrun_m hcl_m ⟨hsp_m, hlr_m, hx0_m, hx1_m, hx19_m, hx21_m, hx22_m, hx23_m, hx26_m, hx27_m, hx28_m, htr_m⟩
    have hsp_align_m : sm.spAligned = true := by
      unfold State.spAligned; rw [hsp_m]; exact hfsp_align
    refine v8_sepWPp_call_ret_entails_lscl hsub
      (x := EncoderFromPbGhost.mk ((s0.sp - 2400#64) + 1888#64) ((s0.sp - 2400#64) + 240#64) (pbToProtoPolyEncoder pbEnc))
      hcl_m hpc_m hrun_m hsp_align_m hlr_m
      (by dsimp only [encoderFromPbSpec]
          rw [hsp_m]
          exact Entails.pure_right ⟨hx0_m, hx1_m, hpts⟩ (Entails.of_eq (by ac_rfl)))
      (fun sf => by
        dsimp only [encoderFromPbSpec, encoderFromPbOnPanic, statesFromPbOnPanic]
        exact v10_onPanic_frame_entails htr_m)
      (fun _ _ => rfl)
      (fun sf hpcf hrunf hspf hcsf => ?_)
    dsimp only [encoderFromPbSpec, protoPolynomialEncoderSize]
    rw [hsp_m] at hspf ⊢
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc]
    apply SepWP.pure_elim; intro htr_sf
    apply SepWP.done hpcf hrunf
    rcases hcsf with ⟨hx19_f, _hx20_f, hx21_f, hx22_f, hx23_f, _hx24_f, _hx25_f, hx26_f, hx27_f, hx28_f, _hx29_f, hvregs_f⟩
    refine ⟨Entails.of_eq (by ac_rfl), hspf,
      hx19_f.trans hx19_m, hx21_f.trans hx21_m, hx22_f.trans hx22_m,
      hx23_f.trans hx23_m, hx26_f.trans hx26_m, hx27_f.trans hx27_m,
      hx28_f.trans hx28_m, ⟨htr_sf.trans htr_m.1, hvregs_f.trans htr_m.2⟩⟩

set_option maxHeartbeats 800000 in
theorem v8_ekReceivedCt1Sampled_from_10836_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)} (hA : FromPbAllocHooks A ext) (hE : Variant2aPlaced.EncoderFromPbPlacedOkExt A ext)
    (s0 s : State) (out pbA : BitVec 64) (u : V1State.Unchunked.Ct1SentEkReceived) (auth : ProtoAuthenticator) (sendingCt1 : Option PolynomialEncoder) (hpts : optEncoderPtsBound sendingCt1)
    (u8 u16 u32 u40 u56 u64 u80 u88 u96 u104 u112 u120 : BitVec 64) (pa1 l1 pa2 l2 : BitVec 64) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (hlen : (u.es.length == ENCAPSULATION_STATE_SIZE &&
      u.ct1.length == CIPHERTEXT1_SIZE && u.ek.length == ENCAPSULATION_KEY_SIZE) = true) (hes : u.es.length = 2080) (hek : u.ek.length = 1152) (hct1 : u.ct1.length = 960) (hauth : u.auth = some auth)
    (hl1 : l1 = BitVec.ofNat 64 auth.rootKey.length) (hl2 : l2 = BitVec.ofNat 64 auth.macKey.length) (hcl : LibsignalCodeLoaded lsmpl s.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 10836#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64) (hx9 : s.readReg64 .x9 = u64) (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = u64) (hx22 : s.readReg64 .x22 = l1) (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64) (hx26 : s.readReg64 .x26 = u8) (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = l2) (htr : TraceCalleeSaved s s0) : SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗
        memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
        memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗
        vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
        v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (pbA + 192#64) 32 ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool) (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ekReceivedCt1Sampled { uc := some u, sendingCt1 := sendingCt1 }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  have hpb_col := v8_pb_uc_enc_entails_224 pbA u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch w0 w8 w16 w24 w32 w40 w48
  cases sendingCt1 with
  | none =>
    rw [v8_states_from_pb_sendingCt1_none_eq u auth hlen hauth]
    simp only [Option.map_none, v1_optProtoPolyEncoderHeap]
    rw [show stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
        (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗
        v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ ⌜w0 = noneCap⌝ ∗
        memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
        v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool = ⌜w0 = noneCap⌝ ∗ ((vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗
        vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1) ∗ ((pbA ↦₆₄ 0x8000000000000008#64) ∗
        v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (pbA + 192#64) 32) ∗
       v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
       (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
       (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
       memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) by ac_rfl]
    refine SepWPp.pure_left fun hw0 => ?_
    apply SepWPp.of_sepWP_ret
    refine SepWP.weaken_pre (sepConj_mono (v8_5vecs_entails_dealloc A l1 pa1 l2 pa2 u8 u16 u32 u40 u56 u64 auth.rootKey auth.macKey u.es u.ek u.ct1) (sepConj_mono_left hpb_col)) ?_
    subst hw0
    have hw_eq : v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) noneCap w8 w16 w24 w32 w40 w48 = (((s0.sp - 2400#64) + 1520#64) ↦₆₄ noneCap) ∗
        ((((s0.sp - 2400#64) + 1520#64 + 8#64) ↦₆₄ w8) ∗ (((s0.sp - 2400#64) + 1520#64 + 16#64) ↦₆₄ w16) ∗ (((s0.sp - 2400#64) + 1520#64 + 24#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1520#64 + 32#64) ↦₆₄ w32) ∗
         (((s0.sp - 2400#64) + 1520#64 + 40#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 1520#64 + 48#64) ↦₆₄ w48)) := rfl
    have hstep1 := v8_check_sendingCt1_10836_none_placed (ext := ext) s0 s out u64 l1 l2 u8 (((((s0.sp - 2400#64) + 1520#64 + 8#64) ↦₆₄ w8) ∗ (((s0.sp - 2400#64) + 1520#64 + 16#64) ↦₆₄ w16) ∗
        (((s0.sp - 2400#64) + 1520#64 + 24#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1520#64 + 32#64) ↦₆₄ w32) ∗ (((s0.sp - 2400#64) + 1520#64 + 40#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 1520#64 + 48#64) ↦₆₄ w48)) ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ vecCapPtrDealloc A l1 pa1 ∗ vecCapPtrDealloc A l2 pa2 ∗ vecCapPtrDealloc A u8 u16 ∗
       vecCapPtrDealloc A u32 u40 ∗ vecCapPtrDealloc A u56 u64 ∗ A.pool ∗ (memRegion (s0.sp - 2400#64) 64 ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
        memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
        memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)) hsp0_align hpc hrun hsp hx9 hx19 hx21 hx22 hx26 hx28 htr
    refine SepWP.weaken_pre (by rw [hw_eq]; exact Entails.of_eq (by ac_rfl)) (SepWP.seq hstep1 ?_)
    intro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, hx9_2, hx19_2, hx21_2, hx22_2, hx26_2, hx28_2, htr2⟩
    have hstep2 := v8_cleanup_5vecs_11120_placed hA s0 s2 out l1 pa1 l2 pa2 u8 u16 u32 u40 u56 u64 (v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) noneCap w8 w16 w24 w32 w40 w48 ∗
       memRegion (s0.sp - 2400#64) 64 ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
       memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
       memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) hsp0_align hpc2 hrun2 hsp2 hx9_2 hx19_2 hx21_2 hx22_2 hx26_2 hx28_2 htr2
    refine SepWP.weaken_pre (Entails.trans hP2 (by rw [hw_eq]; exact Entails.of_eq (by ac_rfl))) (SepWP.seq hstep2 ?_)
    intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx19_3, hx20_3, htr3⟩
    have hcol1 := v8_fsp_collapse_240_to_1888 (s0.sp - 2400#64) noneCap w8 w16 w24 w32 w40 w48
    have hcol2 := v8_fsp_collapse_2304 (s0.sp - 2400#64) u56 u.epoch u16 pa2 pa1 u40 u32
    have hP3' : P3 ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) := by
      refine Entails.trans hP3 ?_
      refine Entails.trans (Entails.of_eq (show _ = (memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗
          v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) noneCap w8 w16 w24 w32 w40 w48 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312) ∗
        (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
          (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
          (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
          memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hcol1) ?_
      refine Entails.trans (Entails.of_eq (show _ = (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
          (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
          (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
          memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hcol2) (Entails.of_eq (by ac_rfl))
    have hx20_byte : (s3.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx20_3]; rfl
    refine SepWP.weaken_pre hP3' (SepWP.mono (v8_err_4240_placed (A := A) (F := F) s0 s3 out (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_byte htr3) ?_)
    intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
  | some pbEnc =>
    dsimp only [optEncoderPtsBound] at hpts
    simp only [Option.map_some]
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ = v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
         (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
         (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
         memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
         memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
         v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
         memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) by ac_rfl)) (sepConj_mono (v1_optProtoPolyEncoderHeap_extract_w0 A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48)
          (sepConj_mono_left (v8_fsp_240_split_56 (s0.sp - 2400#64))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPp.exists_elim; intro z288; apply SepWPp.exists_elim; intro z280; apply SepWPp.exists_elim; intro z272; apply SepWPp.exists_elim; intro z264; apply SepWPp.exists_elim; intro z256
    apply SepWPp.exists_elim; intro z248; apply SepWPp.exists_elim; intro z240
    refine SepWPp.pure_left fun hw0_lt => ?_
    have hw_fsp : v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 = (((s0.sp - 2400#64) + 1520#64) ↦₆₄ w0) ∗ (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w8) ∗
        ((((s0.sp - 2400#64) + 1520#64 + 16#64) ↦₆₄ w16) ∗ (((s0.sp - 2400#64) + 1520#64 + 24#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1520#64 + 32#64) ↦₆₄ w32) ∗ (((s0.sp - 2400#64) + 1520#64 + 40#64) ↦₆₄ w40) ∗
         (((s0.sp - 2400#64) + 1520#64 + 48#64) ↦₆₄ w48)) := by
      dsimp only [v1_optProtoPolyEncoderWordsAt]
      have h1528 : (s0.sp - 2400#64 + 1520#64) + 8#64 = s0.sp - 2400#64 + 1528#64 := by bv_omega
      rw [h1528]
    have hw_pbA : v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 = ((pbA + 136#64) ↦₆₄ w0) ∗ ((pbA + 144#64) ↦₆₄ w8) ∗ ((pbA + 152#64) ↦₆₄ w16) ∗
        ((pbA + 160#64) ↦₆₄ w24) ∗ ((pbA + 168#64) ↦₆₄ w32) ∗ ((pbA + 176#64) ↦₆₄ w40) ∗ ((pbA + 184#64) ↦₆₄ w48) := by
      dsimp only [v1_optProtoPolyEncoderWordsAt]
      simp only [v8_bv_add_add_lit, BitVec.ofNat_eq_ofNat]
    have hcopy := v8_copy_enc_10836_to_10900_placed (ext := ext) s0 s out pbA u64 l1 u8 l2 w0 w8 w16 w24 w32 w40 w48 z240 z248 z256 z264 z272 z280 z288
      ((((s0.sp - 2400#64) + 1520#64 + 16#64) ↦₆₄ w16) ∗ (((s0.sp - 2400#64) + 1520#64 + 24#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1520#64 + 32#64) ↦₆₄ w32) ∗ (((s0.sp - 2400#64) + 1520#64 + 40#64) ↦₆₄ w40) ∗
       (((s0.sp - 2400#64) + 1520#64 + 48#64) ↦₆₄ w48) ∗ ((pbA + 136#64) ↦₆₄ w0) ∗ v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
       (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
       (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗
       vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
       v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)
      hw0_lt hsp0_align hpc hrun hsp hx19 hx21 hx22 hx23 hx26 hx27 hx28 htr
    refine SepWPp.weaken_pre (by rw [hw_fsp, hw_pbA]; exact Entails.of_eq (by ac_rfl)) (v8_sepWPp_seq_clean_lscl hcl hcopy ?_)
    intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hx1_2, hx19_2, hx21_2, hx22_2, hx23_2, hx26_2, hx27_2, hx28_2, htr2⟩
    have hP2_col : v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗ (((s0.sp - 2400#64) + 1520#64) ↦₆₄ w0) ∗ (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w8) ∗
        ((pbA + 144#64) ↦₆₄ w8) ∗ ((pbA + 152#64) ↦₆₄ w16) ∗ ((pbA + 160#64) ↦₆₄ w24) ∗ ((pbA + 168#64) ↦₆₄ w32) ∗ ((pbA + 176#64) ↦₆₄ w40) ∗ ((pbA + 184#64) ↦₆₄ w48) ∗
        ((((s0.sp - 2400#64) + 1520#64 + 16#64) ↦₆₄ w16) ∗ (((s0.sp - 2400#64) + 1520#64 + 24#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1520#64 + 32#64) ↦₆₄ w32) ∗ (((s0.sp - 2400#64) + 1520#64 + 40#64) ↦₆₄ w40) ∗
         (((s0.sp - 2400#64) + 1520#64 + 48#64) ↦₆₄ w48) ∗ ((pbA + 136#64) ↦₆₄ w0) ∗ v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
         (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
         (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
         memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗
         vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
         v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) ⊢
        memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool ∗
        (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
         (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
         (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
         memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
         memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
         memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) := by
      refine Entails.trans (Entails.of_eq (show _ = ((pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗
         (((pbA + 136#64) ↦₆₄ w0) ∗ ((pbA + 144#64) ↦₆₄ w8) ∗ ((pbA + 152#64) ↦₆₄ w16) ∗ ((pbA + 160#64) ↦₆₄ w24) ∗ ((pbA + 168#64) ↦₆₄ w32) ∗ ((pbA + 176#64) ↦₆₄ w40) ∗ ((pbA + 184#64) ↦₆₄ w48)) ∗
         memRegion (pbA + 192#64) 32) ∗ ((((s0.sp - 2400#64) + 1520#64) ↦₆₄ w0) ∗ (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w8) ∗
         ((((s0.sp - 2400#64) + 1520#64 + 16#64) ↦₆₄ w16) ∗ (((s0.sp - 2400#64) + 1520#64 + 24#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1520#64 + 32#64) ↦₆₄ w32) ∗ (((s0.sp - 2400#64) + 1520#64 + 40#64) ↦₆₄ w40) ∗
          (((s0.sp - 2400#64) + 1520#64 + 48#64) ↦₆₄ w48))) ∗ (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool ∗
         memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
         (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
         (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
         memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ statesFromPbJumpTablePlacedAt) by ac_rfl)) ?_
      rw [← hw_pbA, ← hw_fsp]
      exact Entails.trans (sepConj_mono_left hpb_col) (Entails.of_eq (by ac_rfl))
    have hcall := v8_call_encoder_from_pb_10900_to_10904_placed hE s0 s2 hcl2 (s0.sp - 2400#64) out u64 l1 u8 pbA l2 pbEnc w0 w8 w16 w24 w32 w40 w48
      (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
       (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
       (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
       memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) hpts hsp0_align rfl hpc2 hrun2 hsp2 hx0_2 hx1_2 hx19_2 hx21_2 hx22_2 hx23_2 hx26_2 hx27_2 hx28_2 htr2
    refine SepWPp.weaken_pre hP2_col (v8_sepWPp_seq hcall ?_)
    intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx19_3, hx21_3, hx22_3, hx23_3, hx26_3, hx27_3, hx28_3, htr3⟩; apply SepWPp.of_sepWP_ret
    refine SepWP.weaken_pre hP3 ?_
    have hcol_1648 : memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion ((s0.sp - 2400#64) + 1576#64) 312 ⊢ memRegion ((s0.sp - 2400#64) + 240#64) 1648 := v8_fsp_collapse_240_to_1888 (s0.sp - 2400#64) w0 w8 w16 w24 w32 w40 w48
    cases henc : fromPbResult (pbToProtoPolyEncoder pbEnc) with
    | error err =>
      rw [v8_states_from_pb_sendingCt1_err_any_eq u auth pbEnc err hlen hauth henc]
      have herr_tag := v8_resultPolyEncoder_err_entails_tag_392 A (s0.sp - 2400#64) err
      have hpre_err : resultPolyEncoderFromPbAt A ((s0.sp - 2400#64) + 1888#64) (.error err) ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool ∗
          (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
           (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
           (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
           memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
           memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) ⊢ (((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗ (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ vecCapPtrDealloc A l1 pa1 ∗ vecCapPtrDealloc A l2 pa2 ∗ vecCapPtrDealloc A u8 u16 ∗
           vecCapPtrDealloc A u32 u40 ∗ vecCapPtrDealloc A u56 u64 ∗ A.pool ∗ (memRegion (s0.sp - 2400#64) 64 ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
            memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
            memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗
            memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)) := by
        refine Entails.trans (Entails.of_eq (show _ = resultPolyEncoderFromPbAt A ((s0.sp - 2400#64) + 1888#64) (.error err) ∗ (memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗
           v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312) ∗ (vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗
           vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1) ∗ (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool ∗
           memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
           (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
           (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
           memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono herr_tag (sepConj_mono hcol_1648 (sepConj_mono_left (v8_5vecs_entails_dealloc A l1 pa1 l2 pa2 u8 u16 u32 u40 u56 u64 auth.rootKey auth.macKey u.es u.ek u.ct1))))
          (Entails.of_eq (by ac_rfl))
      refine SepWP.weaken_pre hpre_err (SepWP.seq (v8_check_enc_res_10904_err_placed s0 s3 _ hsp0_align hpc3 hrun3 hsp3 htr3) ?_)
      intro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, hx19_4, hx21_4, hx22_4, hx26_4, hx28_4, htr4⟩
      rw [hx19_3] at hx19_4; rw [hx21_3] at hx21_4; rw [hx22_3] at hx22_4
      rw [hx26_3] at hx26_4; rw [hx28_3] at hx28_4
      have hclean := v8_cleanup_5vecs_10916_placed hA s0 s4 out l1 pa1 l2 pa2 u8 u16 u32 u40 u56 u64 ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗
         memRegion (s0.sp - 2400#64) 64 ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
         memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
         memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗
         memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
        hsp0_align hpc4 hrun4 hsp4 hx19_4 hx21_4 hx22_4 hx26_4 hx28_4 htr4
      refine SepWP.weaken_pre (Entails.trans hP4 (Entails.of_eq (by ac_rfl))) (SepWP.seq hclean ?_)
      intro s5 P5 hpc5 hrun5 ⟨hP5, hsp5, hx19_5, hx20_5, htr5⟩
      have hcol2 := v8_fsp_collapse_2304 (s0.sp - 2400#64) u56 u.epoch u16 pa2 pa1 u40 u32
      have hP5' : P5 ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) := by
        refine Entails.trans hP5 ?_
        refine Entails.trans (Entails.of_eq (show _ = ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗ memRegion ((s0.sp - 2400#64) + 1896#64) 392) ∗
          (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
            (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
            (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
            memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
            memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) by ac_rfl)) ?_
        refine Entails.trans (sepConj_mono_left (v8_tag2_392_entails_400 (s0.sp - 2400#64))) ?_
        refine Entails.trans (Entails.of_eq (show _ = (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
            (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
            (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
            memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hcol2) (Entails.of_eq (by ac_rfl))
      have hx20_byte : (s5.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
        rw [hx20_5]; rfl
      refine SepWP.weaken_pre hP5' (SepWP.mono (v8_err_4240_placed (A := A) (F := F) s0 s5 out (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) hsp0_align hpc5 hrun5 hsp5 hx19_5 hx20_byte htr5) ?_)
      intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
    | ok enc =>
      rw [v8_states_from_pb_ok_eq u auth pbEnc enc hlen hauth henc]
      dsimp only [resultPolyEncoderFromPbAt]
      have hrel := v8_polyEncoderAt_relocate A ((s0.sp - 2400#64) + 1888#64) (out + 8#64) enc
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ = polyEncoderAt A ((s0.sp - 2400#64) + 1888#64) enc ∗ (memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗
           v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312) ∗ (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool ∗
           memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
           (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
           (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
           memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗
           vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) by ac_rfl))
          (sepConj_mono hrel (sepConj_mono_left hcol_1648))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro tag; apply ProofLib.SepWP.exists_left; intro bs; apply ProofLib.SepWP.exists_left; intro hi32; apply ProofLib.SepWP.exists_left; intro P_heap
      apply ProofLib.SepWP.pure_elim; rintro ⟨htag, hreloc⟩
      have hbs_cells := v8_bs384_eq_encCells bs.val bs.property ((s0.sp - 2400#64) + 1888#64)
      have ha2280 : ((s0.sp - 2400#64) + 1888#64) + 392#64 = (s0.sp - 2400#64) + 2280#64 := by bv_omega
      rw [hbs_cells, ha2280]
      refine SepWP.seq (v8_check_enc_res_10904_ok_placed s0 s3 tag htag _ hsp0_align hpc3 hrun3 hsp3 htr3) ?_
      intro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, hx15_4, hx19_4, hx21_4, hx22_4, hx23_4, hx26_4, hx28_4, htr4⟩
      rw [hx19_3] at hx19_4; rw [hx21_3] at hx21_4; rw [hx22_3] at hx22_4
      rw [hx23_3] at hx23_4; rw [hx26_3] at hx26_4; rw [hx28_3] at hx28_4
      have hstage := v8_stage_11264_to_ret_placed (F := F) hA s0 s4 (s0.sp - 2400#64) out tag u.epoch pa1 l1 pa2 l2 u8 u16 u32 u40 u56 u64 bs.val bs.property hi32 enc P_heap hreloc
        auth.rootKey auth.macKey u.es u.ek u.ct1 hl1 hl2 hes hek hct1 (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)
        hsp0_align rfl hpc4 hrun4 hsp4 hx15_4 hx19_4 hx21_4 hx22_4 hx23_4 hx26_4 hx28_4 htr4
      refine SepWP.weaken_pre (Entails.trans hP4 (Entails.of_eq (by ac_rfl))) (SepWP.mono hstage ?_)
      intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

set_option maxHeartbeats 800000 in
theorem v8_ekReceivedCt1Sampled_from_1984_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)} (hA : FromPbAllocHooks A ext) (hE : Variant2aPlaced.EncoderFromPbPlacedOkExt A ext)
    (s0 s : State) (out pbA : BitVec 64) (u : V1State.Unchunked.Ct1SentEkReceived) (auth : ProtoAuthenticator) (sendingCt1 : Option PolynomialEncoder) (hpts : optEncoderPtsBound sendingCt1)
    (u8 u16 u32 u40 u56 u64 u80 u88 u104 u112 : BitVec 64) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (hlen : (u.es.length == ENCAPSULATION_STATE_SIZE && u.ct1.length == CIPHERTEXT1_SIZE &&
      u.ek.length == ENCAPSULATION_KEY_SIZE) = true) (hes : u.es.length = 2080) (hek : u.ek.length = 1152) (hct1 : u.ct1.length = 960) (hauth : u.auth = some auth) (hcl : LibsignalCodeLoaded lsmpl s.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 1984#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64) (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = u80)
    (hx26 : s.readReg64 .x26 = u8) (hx27 : s.readReg64 .x27 = pbA) (htr : TraceCalleeSaved s s0) : SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 896 ∗ v8_ucWordsAt ((s0.sp - 2400#64) + 896#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length) u104 u112
          (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗ memRegion ((s0.sp - 2400#64) + 1024#64) 496 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 728 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        vecU8Payload A u80 u88 auth.rootKey ∗ vecU8Payload A u104 u112 auth.macKey ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
        v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ekReceivedCt1Sampled { uc := some u, sendingCt1 := sendingCt1 }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ = vecU8Payload A u80 u88 auth.rootKey ∗ memRegion (s0.sp - 2400#64) 896 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 728 ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ v8_ucWordsAt ((s0.sp - 2400#64) + 896#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length) u104 u112
         (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗ memRegion ((s0.sp - 2400#64) + 1024#64) 496 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A u104 u112 auth.macKey ∗
       vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88
         (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) by ac_rfl)) (sepConj_mono (vecU8Payload_extract_len_lt63 A u80 u88 auth.rootKey) (sepConj_mono (v8_fsp_896_split_1984 (s0.sp - 2400#64))
          (sepConj_mono_left (v8_fsp_1576_split_728 (s0.sp - 2400#64)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro v224; apply SepWPp.exists_elim; intro v216; apply SepWPp.exists_elim; intro v200; apply SepWPp.exists_elim; intro v184; apply SepWPp.exists_elim; intro v176
  apply SepWPp.exists_elim; intro v120; apply SepWPp.exists_elim; intro v64
  refine SepWPp.pure_left fun hr_lt63 => ?_
  have hl1_lt : (BitVec.ofNat 64 auth.rootKey.length).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hr_lt63
  have hclone1 := v8_clone_rootKey_1984_to_10680_placed hA s0 s out pbA u8 u80 u88 u.epoch v120 v200 auth.rootKey (((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
     ((s0.sp - 2400#64 + 912#64) ↦₆₄ 2080#64) ∗ ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 928#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 936#64) ↦₆₄ 1152#64) ∗
     ((s0.sp - 2400#64 + 944#64) ↦₆₄ u56) ∗ ((s0.sp - 2400#64 + 952#64) ↦₆₄ u64) ∗ ((s0.sp - 2400#64 + 960#64) ↦₆₄ 960#64) ∗ ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
     ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗ ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗ ((s0.sp - 2400#64 + 1008#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
     memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ v64) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗
     memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ v176) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ v216) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ v224) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 600 ∗ memRegion ((s0.sp - 2400#64) + 1024#64) 496 ∗
     v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
     memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ vecU8Payload A u104 u112 auth.macKey ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
     v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗
     v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt) hsp0_align hpc hrun hsp hx19 hx23 hx26 hx27 htr
  refine SepWPp.weaken_pre (by rw [v8_ucWordsAt_896_eq]; exact Entails.of_eq (by ac_rfl)) (v8_sepWPp_bind_lscl hcl hclone1 ?_)
  intro s2 P2 hpc2 hrun2 hcl2 ⟨pa1, hP2, hsp2, hx19_2, hx22_2, hx23_2, hx24_2, hx26_2, hx27_2, htr2⟩
  have hclone2 := v8_clone_macKey_10680_to_10740_placed hA s0 s2 out pbA u8 (BitVec.ofNat 64 auth.rootKey.length) u80 u88 u104 u112 v184 auth.macKey
    ((((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 976#64) ↦₆₄ u88) ∗ (((s0.sp - 2400#64) + 984#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
     (((s0.sp - 2400#64) + 1016#64) ↦₆₄ u.epoch) ∗ vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗ vecCapPtrDealloc A u80 u88 ∗
     ((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 912#64) ↦₆₄ 2080#64) ∗ ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗
     ((s0.sp - 2400#64 + 928#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 936#64) ↦₆₄ 1152#64) ∗ ((s0.sp - 2400#64 + 944#64) ↦₆₄ u56) ∗ ((s0.sp - 2400#64 + 952#64) ↦₆₄ u64) ∗
     ((s0.sp - 2400#64 + 960#64) ↦₆₄ 960#64) ∗ ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗ memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ v64) ∗
     memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ v176) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ v216) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ v224) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 600 ∗ memRegion ((s0.sp - 2400#64) + 1024#64) 496 ∗
     v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
     memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
     vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88
       (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
     memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt) hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx23_2 hx24_2 hx26_2 hx27_2 htr2
  refine SepWPp.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl))) (v8_sepWPp_bind_lscl hcl2 hclone2 ?_)
  intro s3 P3 hpc3 hrun3 hcl3 ⟨pa2, hP3, hsp3, hx19_3, hx20_3, hx22_3, hx23_3, hx24_3, hx26_3, hx27_3, hx28_3, htr3⟩
  have hdealloc := v8_dealloc_old_auth_10740_to_10836_placed hA s0 s3 out pbA u8 u16 u32 u40 u56 u64 u80 u88 u104 u112 (BitVec.ofNat 64 auth.rootKey.length) (BitVec.ofNat 64 auth.macKey.length) v64 v176 v216 v224
    ((((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 1000#64) ↦₆₄ u112) ∗ (((s0.sp - 2400#64) + 1008#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
     vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 976#64) ↦₆₄ u88) ∗
     (((s0.sp - 2400#64) + 984#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗ (((s0.sp - 2400#64) + 1016#64) ↦₆₄ u.epoch) ∗ vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
     ((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 912#64) ↦₆₄ 2080#64) ∗ ((s0.sp - 2400#64 + 936#64) ↦₆₄ 1152#64) ∗ ((s0.sp - 2400#64 + 960#64) ↦₆₄ 960#64) ∗ ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
     memRegion (s0.sp - 2400#64) 64 ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
     memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
     memRegion ((s0.sp - 2400#64) + 296#64) 600 ∗ memRegion ((s0.sp - 2400#64) + 1024#64) 496 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
     v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
     memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
     (pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗
     v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt)
    hl1_lt hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx22_3 hx23_3 hx24_3 hx26_3 hx27_3 hx28_3 htr3
  refine SepWPp.weaken_pre (Entails.trans hP3 (Entails.of_eq (by ac_rfl))) (v8_sepWPp_seq_clean_lscl hcl3 hdealloc ?_)
  intro s4 hpc4 hrun4 hcl4 ⟨hsp4, hx9_4, hx19_4, hx21_4, hx22_4, hx23_4, hx26_4, hx27_4, hx28_4, htr4⟩
  have hcol_1224 := v8_fsp_296_to_1520_collapse (s0.sp - 2400#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch
  rw [v8_ucWordsAt_896_eq] at hcol_1224
  refine SepWPp.weaken_pre ?_ (v8_ekReceivedCt1Sampled_from_10836_placed (F := F) hA hE s0 s4 out pbA u auth sendingCt1 hpts u8 u16 u32 u40 u56 u64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length) u104 u112
      (BitVec.ofNat 64 auth.macKey.length) pa1 (BitVec.ofNat 64 auth.rootKey.length) pa2 (BitVec.ofNat 64 auth.macKey.length) w0 w8 w16 w24 w32 w40 w48
      hlen hes hek hct1 hauth rfl rfl hcl4 hsp0_align hpc4 hrun4 hsp4 hx9_4 hx19_4 hx21_4 hx22_4 hx23_4 hx26_4 hx27_4 hx28_4 htr4)
  exact Entails.trans (Entails.of_eq (show _ = (memRegion ((s0.sp - 2400#64) + 296#64) 600 ∗ (((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 912#64) ↦₆₄ 2080#64) ∗ ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 928#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 936#64) ↦₆₄ 1152#64) ∗
        ((s0.sp - 2400#64 + 944#64) ↦₆₄ u56) ∗ ((s0.sp - 2400#64 + 952#64) ↦₆₄ u64) ∗ ((s0.sp - 2400#64 + 960#64) ↦₆₄ 960#64) ∗ ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗
        ((s0.sp - 2400#64 + 984#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗ ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗ ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
        ((s0.sp - 2400#64 + 1008#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗ ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u.epoch)) ∗ memRegion ((s0.sp - 2400#64) + 1024#64) 496) ∗ (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
       memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
       v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗ vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
       vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88
         (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) by ac_rfl)) (Entails.trans (sepConj_mono_left hcol_1224) (Entails.of_eq (by ac_rfl)))

theorem v8_check_lengths_1936_err_x26_placed [LibsignalPlacement] {ext : String → Option (State → State)} (s0 s1 : State) (out : BitVec 64) (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (z928 z936 z944 z952 : BitVec 64) (Rest : SepProp) (herr : u24 ≠ 2080#64 ∨ u72 ≠ 960#64 ∨ u48 ≠ 1152#64) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1936#64) (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64) (hx9_1 : s1.readReg64 .x9 = u24)
    (hq0_1 : s1.readVReg128 0#5 = u48 ++ u40) (hq1_1 : s1.readVReg128 1#5 = u64 ++ u56) (hx19_1 : s1.readReg64 .x19 = out) (htr1 : TraceCalleeSaved s1 s0) : SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2100#64) s1 (((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 912#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗ ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗
        ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗ ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗ ((s0.sp - 2400#64 + 960#64) ↦₆₄ u72) ∗ ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
        ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗ ((s0.sp - 2400#64 + 984#64) ↦₆₄ u96) ∗ ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗ ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
        ((s0.sp - 2400#64 + 1008#64) ↦₆₄ u120) ∗ ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u128) ∗ Rest) (fun sm Pm =>
        (Pm ⊢ v8_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ Rest) ∧ sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = s1.readReg64 .x26 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  change s1.pc = (blkPl_333).base + 1936#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 2100#64) s1 _ _
  by_cases h24 : u24 = 2080#64
  · subst h24
    by_cases h72 : u72 = 960#64
    · subst h72
      have h48 : u48 ≠ 1152#64 := by
        rcases herr with h | h | h
        · exact False.elim (h rfl)
        · exact False.elim (h rfl)
        · exact h
      have h48_bne : (u48 != 1152#64) = true := bne_iff_ne.mpr h48
      wp_steps; simp only [v8_ucWordsAt, sepConj_assoc]; wp_done
    · have h72_bne : (u72 != 960#64) = true := bne_iff_ne.mpr h72
      wp_steps; simp only [v8_ucWordsAt, sepConj_assoc]; wp_done
  · have h24_bne : (u24 != 2080#64) = true := bne_iff_ne.mpr h24
    wp_steps; simp only [v8_ucWordsAt, sepConj_assoc]; wp_done

theorem v8_step_1872_to_2100_len_err_x26_placed [LibsignalPlacement] {ext : String → Option (State → State)} (s0 s1 : State) (out pbA : BitVec 64) (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (Rest : SepProp) (herr : u24 ≠ 2080#64 ∨ u72 ≠ 960#64 ∨ u48 ≠ 1152#64) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hpc1 : s1.pc = lsmpl.base 333 + 1872#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out) (hx23_1 : s1.readReg64 .x23 = s0.sp - 2400#64 + 848#64)
    (hx26_1 : s1.readReg64 .x26 = u8) (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) : SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 2100#64) s1
      (memRegion (s0.sp - 2400#64) 1392 ∗ v8_ucWordsAt (s0.sp - 2400#64 + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ v8_ucWordsAt (pbA + 8#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ Rest) (fun sm Pm =>
        (Pm ⊢ memRegion (s0.sp - 2400#64) 896 ∗ v8_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
          v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ Rest) ∧ sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x26 = u8 ∧ TraceCalleeSaved sm s0) := by
  refine SepWP.weaken_pre (sepConj_mono_left (v8_memRegion_1392_split_896_128_368 (s0.sp - 2400#64))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro z1016; apply ProofLib.SepWP.exists_left; intro z1008; apply ProofLib.SepWP.exists_left; intro z1000; apply ProofLib.SepWP.exists_left; intro z992
  apply ProofLib.SepWP.exists_left; intro z984; apply ProofLib.SepWP.exists_left; intro z976; apply ProofLib.SepWP.exists_left; intro z968; apply ProofLib.SepWP.exists_left; intro z960
  apply ProofLib.SepWP.exists_left; intro z952; apply ProofLib.SepWP.exists_left; intro z944; apply ProofLib.SepWP.exists_left; intro z936; apply ProofLib.SepWP.exists_left; intro z928
  apply ProofLib.SepWP.exists_left; intro z920; apply ProofLib.SepWP.exists_left; intro z912; apply ProofLib.SepWP.exists_left; intro z904; apply ProofLib.SepWP.exists_left; intro z896
  have hcopy := v8_copy_uc_1872_to_1936_placed (ext := ext) s0 s1 out pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 z896 z904 z912 z920 z960 z968 z976 z984 z992 z1000 z1008 z1016 (memRegion (s0.sp - 2400#64) 896 ∗
      ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗ ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗ ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗ ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗ memRegion (s0.sp - 2400#64 + 1024#64) 368 ∗
      ((s0.sp - 2400#64 + 1392#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 1392#64 + 16#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 1392#64 + 24#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 1392#64 + 32#64) ↦₆₄ u40) ∗
      ((s0.sp - 2400#64 + 1392#64 + 40#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 1392#64 + 48#64) ↦₆₄ u56) ∗ ((s0.sp - 2400#64 + 1392#64 + 56#64) ↦₆₄ u64) ∗ ((s0.sp - 2400#64 + 1392#64 + 64#64) ↦₆₄ u72) ∗
      ((s0.sp - 2400#64 + 1392#64 + 72#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 1392#64 + 80#64) ↦₆₄ u88) ∗ ((s0.sp - 2400#64 + 1392#64 + 88#64) ↦₆₄ u96) ∗ ((s0.sp - 2400#64 + 1392#64 + 96#64) ↦₆₄ u104) ∗
      ((s0.sp - 2400#64 + 1392#64 + 104#64) ↦₆₄ u112) ∗ ((s0.sp - 2400#64 + 1392#64 + 112#64) ↦₆₄ u120) ∗ ((s0.sp - 2400#64 + 1392#64 + 120#64) ↦₆₄ u128) ∗ Rest)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx26_1 hx27_1 htr1
  have h1400 : (s0.sp - 2400#64 + 1392#64) + 8#64 = s0.sp - 2400#64 + 1400#64 := by bv_omega
  refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 1936#64) (P_mid := ((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
      ((s0.sp - 2400#64 + 912#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗ ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗
      ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗ ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗ ((s0.sp - 2400#64 + 960#64) ↦₆₄ u72) ∗ ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
      ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗ ((s0.sp - 2400#64 + 984#64) ↦₆₄ u96) ∗ ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗ ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
      ((s0.sp - 2400#64 + 1008#64) ↦₆₄ u120) ∗ ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u128) ∗ (memRegion (s0.sp - 2400#64) 896 ∗ memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗ v8_ucWordsAt (pbA + 8#64)
         u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ Rest)) (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x9 = u24 ∧ s2.readVReg128 0#5 = u48 ++ u40 ∧ s2.readVReg128 1#5 = u64 ++ u56 ∧ s2.readReg64 .x19 = out ∧ s2.readReg64 .x26 = u8 ∧ TraceCalleeSaved s2 s0)
    (SepWP.weaken_pre (by dsimp only [v8_ucWordsAt]; rw [h1400]; exact Entails.of_eq (by ac_rfl)) (SepWP.mono hcopy fun s2 P2 _ _ ⟨hP2, hsp2, hx9_2, hq0_2, hq1_2, hx19_2, hx26_2, _, htr2⟩ => ?_)) ?_
  · refine ⟨Entails.trans hP2 ?_, hsp2, hx9_2, hq0_2, hq1_2, hx19_2, hx26_2, htr2⟩
    have hm496 := v8_merge_368_ucWords_496 (s0.sp - 2400#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
    dsimp only [v8_ucWordsAt] at hm496 ⊢
    rw [h1400] at hm496
    refine Entails.trans (Entails.of_eq (show _ = (memRegion (s0.sp - 2400#64 + 1024#64) 368 ∗ (((s0.sp - 2400#64 + 1392#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 1400#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 1392#64 + 16#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 1392#64 + 24#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 1392#64 + 32#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 1392#64 + 40#64) ↦₆₄ u48) ∗
        ((s0.sp - 2400#64 + 1392#64 + 48#64) ↦₆₄ u56) ∗ ((s0.sp - 2400#64 + 1392#64 + 56#64) ↦₆₄ u64) ∗ ((s0.sp - 2400#64 + 1392#64 + 64#64) ↦₆₄ u72) ∗ ((s0.sp - 2400#64 + 1392#64 + 72#64) ↦₆₄ u80) ∗
        ((s0.sp - 2400#64 + 1392#64 + 80#64) ↦₆₄ u88) ∗ ((s0.sp - 2400#64 + 1392#64 + 88#64) ↦₆₄ u96) ∗ ((s0.sp - 2400#64 + 1392#64 + 96#64) ↦₆₄ u104) ∗ ((s0.sp - 2400#64 + 1392#64 + 104#64) ↦₆₄ u112) ∗
        ((s0.sp - 2400#64 + 1392#64 + 112#64) ↦₆₄ u120) ∗ ((s0.sp - 2400#64 + 1392#64 + 120#64) ↦₆₄ u128))) ∗ (((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
       ((s0.sp - 2400#64 + 912#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗ ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗
       ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗ ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗ ((s0.sp - 2400#64 + 960#64) ↦₆₄ u72) ∗ ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
       ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗ ((s0.sp - 2400#64 + 984#64) ↦₆₄ u96) ∗ ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗ ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
       ((s0.sp - 2400#64 + 1008#64) ↦₆₄ u120) ∗ ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u128) ∗ memRegion (s0.sp - 2400#64) 896 ∗ ((pbA + 8#64) ↦₆₄ u8) ∗ ((pbA + 8#64 + 8#64) ↦₆₄ u16) ∗
       ((pbA + 8#64 + 16#64) ↦₆₄ u24) ∗ ((pbA + 8#64 + 24#64) ↦₆₄ u32) ∗ ((pbA + 8#64 + 32#64) ↦₆₄ u40) ∗ ((pbA + 8#64 + 40#64) ↦₆₄ u48) ∗ ((pbA + 8#64 + 48#64) ↦₆₄ u56) ∗ ((pbA + 8#64 + 56#64) ↦₆₄ u64) ∗
       ((pbA + 8#64 + 64#64) ↦₆₄ u72) ∗ ((pbA + 8#64 + 72#64) ↦₆₄ u80) ∗ ((pbA + 8#64 + 80#64) ↦₆₄ u88) ∗ ((pbA + 8#64 + 88#64) ↦₆₄ u96) ∗ ((pbA + 8#64 + 96#64) ↦₆₄ u104) ∗ ((pbA + 8#64 + 104#64) ↦₆₄ u112) ∗
       ((pbA + 8#64 + 112#64) ↦₆₄ u120) ∗ ((pbA + 8#64 + 120#64) ↦₆₄ u128) ∗ Rest) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hm496) (Entails.of_eq (by ac_rfl))
  · intro s2 hpc2 hrun2 ⟨hsp2, hx9_2, hq0_2, hq1_2, hx19_2, hx26_2, htr2⟩
    have hchk := v8_check_lengths_1936_err_x26_placed (ext := ext) s0 s2 out u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 z928 z936 z944 z952
      (memRegion (s0.sp - 2400#64) 896 ∗ memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗ v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ Rest)
      herr hsp0_align hpc2 hrun2 hsp2 hx9_2 hq0_2 hq1_2 hx19_2 htr2
    refine SepWP.mono hchk fun sf Pf _ _ ⟨hPf, hsp_f, hx19_f, hx26_f, htr_f⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hx19_f, Eq.trans hx26_f hx26_2, htr_f⟩

set_option maxHeartbeats 800000 in
theorem states_from_pb_ekReceivedCt1Sampled_1764_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)} (hA : FromPbAllocHooks A ext) (hE : Variant2aPlaced.EncoderFromPbPlacedOkExt A ext)
    (s : V1State.Chunked.EkReceivedCt1Sampled) (hpts : optEncoderPtsBound s.sendingCt1) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (out pbA : BitVec 64) (R : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1764#64) (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64) (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1 (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A pbA (some (.ekReceivedCt1Sampled s)) ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ekReceivedCt1Sampled s) }) ∗ memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  refine v8_sepWPp_weaken_panic R ?_
  rw [v8_optProtoInnerStateAt_ekReceivedCt1Sampled_eq]
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ = optProtoUnchunkedCt1SentEkReceivedAt A (pbA + 8#64) s.uc ∗ optProtoPolynomialEncoderAt A (pbA + 136#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗
       statesFromPbJumpTablePlacedAt ∗ A.pool) by ac_rfl)) (sepConj_mono (v8_optProtoUnchunkedCt1SentEkReceivedAt_unpack A (pbA + 8#64) s.uc) (sepConj_mono_left (v1_optProtoPolyEncoderAt_unpack A (pbA + 136#64)
          (s.sendingCt1.map pbToProtoPolyEncoder))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro w0; apply SepWPp.exists_elim; intro w8; apply SepWPp.exists_elim; intro w16; apply SepWPp.exists_elim; intro w24; apply SepWPp.exists_elim; intro w32; apply SepWPp.exists_elim; intro w40
  apply SepWPp.exists_elim; intro w48; apply SepWPp.exists_elim; intro u8; apply SepWPp.exists_elim; intro u16; apply SepWPp.exists_elim; intro u24; apply SepWPp.exists_elim; intro u32
  apply SepWPp.exists_elim; intro u40; apply SepWPp.exists_elim; intro u48; apply SepWPp.exists_elim; intro u56; apply SepWPp.exists_elim; intro u64
  apply SepWPp.exists_elim; intro u72; apply SepWPp.exists_elim; intro u80; apply SepWPp.exists_elim; intro u88; apply SepWPp.exists_elim; intro u96
  apply SepWPp.exists_elim; intro u104; apply SepWPp.exists_elim; intro u112; apply SepWPp.exists_elim; intro u120; apply SepWPp.exists_elim; intro u128
  cases s with | mk uc sendingCt1 =>
  dsimp only at hpts ⊢
  cases uc with
  | none =>
    rw [v8_states_from_pb_uc_none_eq]
    simp only [v8_optProtoUcHeap, sepConj_assoc]
    rw [show v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ ⌜u8 = noneCap⌝ ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool = ⌜u8 = noneCap⌝ ∗
      ((v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48) ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗
       v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) by ac_rfl]
    refine SepWPp.pure_left fun hu8 => ?_
    subst hu8
    rw [v8_uc_and_enc_words_eq_pb128]
    apply SepWPp.of_sepWP_ret
    exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (v8_ekReceivedCt1Sampled_uc_none_placed (F := F) hA s0 s1 out pbA u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
        (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1)
  | some u =>
    simp only [v8_optProtoUcHeap, sepConj_assoc]
    rw [show v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ ⌜u8.toNat < 2 ^ 63 ∧ u24 = BitVec.ofNat 64 u.es.length ∧
          u32.toNat < 2 ^ 63 ∧ u48 = BitVec.ofNat 64 u.ek.length ∧ u56.toNat < 2 ^ 63 ∧ u72 = BitVec.ofNat 64 u.ct1.length ∧ u128 = u.epoch⌝ ∗
        vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool = ⌜u8.toNat < 2 ^ 63 ∧ u24 = BitVec.ofNat 64 u.es.length ∧ u32.toNat < 2 ^ 63 ∧ u48 = BitVec.ofNat 64 u.ek.length ∧ u56.toNat < 2 ^ 63 ∧ u72 = BitVec.ofNat 64 u.ct1.length ∧
        u128 = u.epoch⌝ ∗ (vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ ((v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
         v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48) ∗ memRegion (s0.sp - 2400#64) 2304 ∗ v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗
        v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)) by ac_rfl]
    refine SepWPp.pure_left fun ⟨hu8, hu24, hu32, hu48, hu56, hu72, hu128⟩ => ?_
    rw [v8_uc_and_enc_words_eq_pb128]
    refine SepWPp.weaken_pre (sepConj_mono (vecU8Payload_extract_len_lt63 A u8 u16 u.es) (sepConj_mono (vecU8Payload_extract_len_lt63 A u32 u40 u.ek)
          (sepConj_mono_left (vecU8Payload_extract_len_lt63 A u56 u64 u.ct1)))) ?_
    rw [show (⌜u.es.length < 2 ^ 63⌝ ∗ vecU8Payload A u8 u16 u.es) ∗ (⌜u.ek.length < 2 ^ 63⌝ ∗ vecU8Payload A u32 u40 u.ek) ∗ (⌜u.ct1.length < 2 ^ 63⌝ ∗ vecU8Payload A u56 u64 u.ct1) ∗
        (v8_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (s0.sp - 2400#64) 2304 ∗ v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗
         v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) = ⌜u.es.length < 2 ^ 63⌝ ∗ ⌜u.ek.length < 2 ^ 63⌝ ∗ ⌜u.ct1.length < 2 ^ 63⌝ ∗
      (memRegion (s0.sp - 2400#64) 2304 ∗ v8_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 w0 w8 w16 w24 w32 w40 w48 ∗
       (vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗
        v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)) by ac_rfl]
    refine SepWPp.pure_left fun hes_lt =>
      SepWPp.pure_left fun hek_lt =>
      SepWPp.pure_left fun hct1_lt => ?_
    have hcopy := v8_copy_pb_to_stack_1764_placed (ext := ext) s0 s1 out pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 w0 w8 w16 w24 w32 w40 w48
      (vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗
       v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
    have hu8_ne : (u8 + 1#64 == 0#64) = false := v10_cap_add_one_beq_zero_false hu8
    simp only [hu8_ne, Bool.false_eq_true, ↓reduceIte] at hcopy
    refine v8_sepWPp_seq_clean_lscl hcl1 hcopy ?_
    intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx23_2, hx26_2, hx27_2, htr2⟩
    rw [hx23_1] at hx23_2
    rw [← v8_uc_and_enc_words_eq_pb128]
    cases hlen : (u.es.length == ENCAPSULATION_STATE_SIZE && u.ct1.length == CIPHERTEXT1_SIZE && u.ek.length == ENCAPSULATION_KEY_SIZE) with
    | false =>
      rw [v8_states_from_pb_len_err_eq u sendingCt1 hlen]
      have herr : u24 ≠ 2080#64 ∨ u72 ≠ 960#64 ∨ u48 ≠ 1152#64 := by
        rw [hu24, hu72, hu48]
        exact v8_len_err_of_false u hlen hes_lt hct1_lt hek_lt
      apply SepWPp.of_sepWP_ret
      have hstep := v8_step_1872_to_2100_len_err_x26_placed (ext := ext) s0 s2 out pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 (v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
         memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
         v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)
        herr hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx26_2 hx27_2 htr2
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (sepWP_seq_lscl hcl2 (SepWP.mono hstep fun s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx19_3, hx26_3, htr3⟩ hcl3 => ?_))
      have hpb_col := v8_pb_uc_enc_entails_224 pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 w0 w8 w16 w24 w32 w40 w48
      have h3v := v8_3vecs_entails_dealloc A u8 u16 u32 u40 u56 u64 u.es u.ek u.ct1
      have hP3' : P3 ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 896 ∗ v8_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗ v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          vecCapPtrDealloc A u8 u16 ∗ vecCapPtrDealloc A u32 u40 ∗ vecCapPtrDealloc A u56 u64 ∗ v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗ A.pool ∗
          (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) := by
        refine Entails.trans hP3 ?_
        refine Entails.trans (Entails.of_eq (show _ = ((pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
           v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (pbA + 192#64) 32) ∗ (vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 896 ∗ v8_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
           memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗ v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
           v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗ A.pool ∗ statesFromPbJumpTablePlacedAt) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hpb_col (sepConj_mono_left h3v)) (Entails.of_eq (by ac_rfl))
      refine SepWP.weaken_pre hP3' (SepWP.mono (v8_drop_uc_and_sendingCt1_2100_placed (F := F) hA s0 s3 out u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 u.auth
        (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) hcl3 hsp0_align hpc3 hrun3 hsp3 hx19_3 hx26_3 htr3) ?_)
      intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
    | true =>
      obtain ⟨hes, hct1, hek⟩ := v8_len_ok_of_true u hlen
      have hu24_eq : u24 = 2080#64 := by rw [hu24, hes]
      have hu48_eq : u48 = 1152#64 := by rw [hu48, hek]
      have hu72_eq : u72 = 960#64 := by rw [hu72, hct1]
      subst hu24_eq hu48_eq hu72_eq hu128
      have hstep := v8_step_1872_to_1972_len_ok_placed (ext := ext) s0 s2 out pbA u8 u16 u32 u40 u56 u64 u80 u88 u96 u104 u112 u120 u.epoch (v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
         memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
         v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)
        hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx26_2 hx27_2 htr2
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (v8_sepWPp_seq_clean_lscl hcl2 hstep ?_)
      intro s3 hpc3 hrun3 hcl3 ⟨hsp3, hx19_3, hx26_3, hx27_3, htr3⟩
      cases hauth : u.auth with
      | none =>
        rw [v8_states_from_pb_auth_none_eq u sendingCt1 hlen hauth]
        dsimp only [v1_optProtoAuthHeap]
        rw [show memRegion (s0.sp - 2400#64) 896 ∗ v8_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
            v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ (v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
             ⌜u80 = noneCap⌝ ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) = ⌜u80 = noneCap⌝ ∗
          (v8_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ ((pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64)
              u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (pbA + 192#64) 32) ∗
           stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 896 ∗ memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
           v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
           statesFromPbJumpTablePlacedAt ∗ A.pool) by ac_rfl]
        refine SepWPp.pure_left fun hu80 => ?_
        subst hu80
        apply SepWPp.of_sepWP_ret
        have hpb_col := v8_pb_uc_enc_entails_224 pbA u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 noneCap u88 u96 u104 u112 u120 u.epoch w0 w8 w16 w24 w32 w40 w48
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left hpb_col)) ?_
        have hchk := v8_check_auth_1972_none_placed (ext := ext) s0 s3 out u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u88 u96 u104 u112 u120 u.epoch (memRegion pbA optProtoInnerStateSize ∗
           stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 896 ∗ memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
           v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
           statesFromPbJumpTablePlacedAt ∗ A.pool) hsp0_align hpc3 hrun3 hsp3 hx19_3 htr3
        refine sepWP_seq_lscl hcl3 (SepWP.mono hchk fun s4 P4 hpc4 hrun4 ⟨hP4, hsp4, hx19_4, htr4⟩ hcl4 => ?_)
        have hdrop := v8_drop_uc_auth_none_10544_placed (F := F) hA s0 s4 out u u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u88 u96 u104 u112 u120 (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48
          (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) hcl4 hsp0_align hu8 (by rw [hes]; rfl) hu32 (by rw [hek]; rfl) hu56 (by rw [hct1]; rfl) hauth hpc4 hrun4 hsp4 hx19_4 htr4
        refine SepWP.weaken_pre (Entails.trans hP4 (Entails.of_eq (by ac_rfl))) (SepWP.mono hdrop ?_)
        intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
        exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
      | some auth =>
        dsimp only [v1_optProtoAuthHeap]
        rw [show memRegion (s0.sp - 2400#64) 896 ∗ v8_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
            v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ (v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
             (⌜u80.toNat < 2 ^ 63 ∧ u96 = BitVec.ofNat 64 auth.rootKey.length ∧ u120 = BitVec.ofNat 64 auth.macKey.length⌝ ∗ vecU8Payload A u80 u88 auth.rootKey ∗ vecU8Payload A u104 u112 auth.macKey) ∗
             v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) = ⌜u80.toNat < 2 ^ 63 ∧ u96 = BitVec.ofNat 64 auth.rootKey.length ∧
            u120 = BitVec.ofNat 64 auth.macKey.length⌝ ∗ (v8_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗
           (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 896 ∗ memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
            v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
            memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A u80 u88 auth.rootKey ∗ vecU8Payload A u104 u112 auth.macKey ∗
            vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64)
              u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
            memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)) by ac_rfl]
        refine SepWPp.pure_left fun ⟨hu80, hu96, hu120⟩ => ?_
        subst hu96 hu120
        have hchk := v8_check_auth_1972_some_placed (ext := ext) s0 s3 out pbA u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 896 ∗ memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
           v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A u80 u88 auth.rootKey ∗ vecU8Payload A u104 u112 auth.macKey ∗
           vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88
             (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) hu80 hsp0_align hpc3 hrun3 hsp3 hx19_3 hx26_3 hx27_3 htr3
        refine v8_sepWPp_seq_clean_lscl hcl3 hchk ?_
        intro s4 hpc4 hrun4 hcl4 ⟨hsp4, hx19_4, hx23_4, hx26_4, hx27_4, htr4⟩
        exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (v8_ekReceivedCt1Sampled_from_1984_placed (F := F) hA hE s0 s4 out pbA u auth sendingCt1 hpts u8 u16 u32 u40 u56 u64 u80 u88 u104 u112 w0 w8 w16 w24 w32 w40 w48
            hlen hes hek hct1 hauth hcl4 hsp0_align hpc4 hrun4 hsp4 hx19_4 hx23_4 hx26_4 hx27_4 htr4)

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8Placed

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8Placed (
  v8_stage_11264_to_ret_placed
  v8_call_encoder_from_pb_10900_to_10904_placed
  v8_ekReceivedCt1Sampled_from_10836_placed
  v8_ekReceivedCt1Sampled_from_1984_placed
  v8_check_lengths_1936_err_x26_placed
  v8_step_1872_to_2100_len_err_x26_placed
  states_from_pb_ekReceivedCt1Sampled_1764_placed
)

end CryptoVerification.SpqrV1.States.FromPb
