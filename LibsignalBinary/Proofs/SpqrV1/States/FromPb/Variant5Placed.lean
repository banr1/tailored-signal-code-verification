/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5cPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5d
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5dPlaced
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 5 (`NoHeaderReceived`, `+1344`)

Relocatable Block-`333` top-level composition from `+1344` to return for
`InnerState.noHeaderReceived`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open V1State.Chunked
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1
open LibsignalBinary.Proofs.SpqrV1.States
open LibsignalBinary.Proofs.SpqrV1.States.FromPb
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5aPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5bPlaced

set_option linter.style.longLine false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible]
  Program.fetch Program.externAt? Program.fnOff libsignalSessionCode
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

private theorem v5_sepWPp_seq_clean_lscl [LibsignalPlacement] {prog : Program}
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

private theorem v5_sepWPp_bind_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64} {s : State}
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

private theorem v5_sepWPp_call_ret_lscl [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    {x : α} {s : State} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    {P_step F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P_step ∗ R') → (s.mem ⊨ spec.pre x s ∗ R'))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine SepWPp.call_wpp (x := x) (F := F) hcall hpc hrun hsp_align hlr ?_ ?_ ?_ ?_ (hoom := ?_)
  · intro R' hm
    rw [sepConj_assoc] at hm
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, hpre (F ∗ R') hm⟩
  · intro sf code R' _ hpost
    dsimp only [withLsCodeLoaded] at hpost
    rw [hexit_eq] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sf _ _ hm_f
    exact Satisfies.mono (sepConj_mono_left (hpan sf)) hm_f
  · intro sf hpcm hrunm hspm hcsm
    exact SepWPp.of_sepWP_ret (hnext sf hpcm hrunm hspm hcsm)
  · intro sf R' _ hpost
    dsimp only [withLsCodeLoaded] at hpost
    rw [hoom_eq] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

/-! ## `<PolyDecoder>::from_pb` (`+6064 -> s0.x30`) -/

set_option maxHeartbeats 800000 in
/-- At `+6064`, when `receivingHdr = some decPb` and `(decPb.ptsNeeded == 48#32) = true`,
    stages `ProtoPolynomialDecoder` at `fsp + 1392`, calls `<PolyDecoder>::from_pb`,
    and either cleans up on `Err` (`+6132 -> +6520 -> +6500`) or copies `Ok dec`
    (`+6132 -> +8180 -> s0.x30`). -/
theorem v5_noHeaderReceived_6064_some_to_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (hDec : DecoderFromPbPlacedOkExt A ext)
    (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out pbA p1_new p2_new ep w8 w16 w24 w40 w80 : BitVec 64)
    (d36 : BitVec 32)
    (authPb : ProtoAuthenticator) (decPb : PolynomialDecoder) (R : SepProp)
    (heq48 : (decPb.ptsNeeded == 48#32) = true)
    (_hr_lt63 : authPb.rootKey.length < 2 ^ 63)
    (_hm_lt63 : authPb.macKey.length < 2 ^ 63)
    (hl1_lt : (BitVec.ofNat 64 authPb.rootKey.length).toNat < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 6064#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 authPb.rootKey.length)
    (hx22_1 : s1.readReg64 .x22 = w16) (hx23_1 : s1.readReg64 .x23 = w8)
    (hx25_1 : s1.readReg64 .x25 = (48#32).zeroExtend 64)
    (hx27_1 : s1.readReg64 .x27 = p1_new) (hx28_1 : s1.readReg64 .x28 = w24)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (v5a_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder decPb)) w8 w16 w24 48#32 d36 w40 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 136 ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
        memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
        memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗
        (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗
        memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗
        vecU8Payload A (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
        vecU8Payload A (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.noHeaderReceived
                  { uc := some { auth := some authPb, epoch := ep },
                    receivingHdr := some decPb }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hpack := v5a_protoPolyDecoderAt_pack A
    ((s0.sp - 2400#64) + 1392#64) (pbToProtoPolyDecoder decPb)
    w8 w16 w24 48#32 d36 w40
  refine SepWPp.weaken_pre
    (Entails.trans
      (sepConj_mono_left
        (v5_optProtoPolyDecoderHeap_some_dup A (pbToProtoPolyDecoder decPb) w8 w16 w24 48#32 d36 w40))
      (Entails.of_eq (by ac_rfl))) ?_
  refine SepWPp.pure_left fun ⟨_, hw8_lt⟩ => ?_
  have h2068_split :
      memRegion ((s0.sp - 2400#64) + 236#64) 2068 ⊢
        (∃∗ z236 : BitVec 32, ((s0.sp - 2400#64) + 236#64) ↦₃₂ z236) ∗
        memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗
        (∃∗ z0 : BitVec 64, ∃∗ z8 : BitVec 64, ∃∗ z16 : BitVec 64,
         ∃∗ zd24 : BitVec 32, ∃∗ zd28 : BitVec 32, ∃∗ z32 : BitVec 64,
           v5a_optProtoPolyDecoderWordsAt ((s0.sp - 2400#64) + 1392#64) z0 z8 z16 zd24 zd28 z32) ∗
        memRegion ((s0.sp - 2400#64) + 1432#64) 456 ∗
        memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 :=
    Entails.trans (v5_memRegion_2068_split_dec (s0.sp - 2400#64))
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (v5c_memRegion_40_to_polyDecoderWordsAt ((s0.sp - 2400#64) + 1392#64)))))
  refine SepWPp.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗
        (v5a_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder decPb)) w8 w16 w24 48#32 d36 w40 ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion (s0.sp - 2400#64) 136 ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
         memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
         memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗
         (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
         (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗
         vecU8Payload A (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
         vecU8Payload A (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) by ac_rfl))
      (sepConj_mono_left h2068_split)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun z0 => SepWPp.exists_elim fun z8 =>
    SepWPp.exists_elim fun z16 => SepWPp.exists_elim fun zd24 =>
    SepWPp.exists_elim fun zd28 => SepWPp.exists_elim fun z32 =>
    SepWPp.exists_elim fun z236 => ?_
  let R_post_call : SepProp :=
    (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗
    (((s0.sp - 2400#64) + 236#64) ↦₃₂ z236) ∗
    memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗ memRegion ((s0.sp - 2400#64) + 1432#64) 456 ∗
    memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ memRegion (s0.sp - 2400#64) 136 ∗
    (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗
    (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗
    (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
    (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
    vecU8Payload A (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
    vecU8Payload A (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt
  refine SepWPp.weaken_pre
    (Entails.of_eq (show _ =
      (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗
      v5a_optProtoPolyDecoderWordsAt ((s0.sp - 2400#64) + 1392#64) z0 z8 z16 zd24 zd28 z32 ∗
      (v5a_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder decPb)) w8 w16 w24 48#32 d36 w40 ∗
       (((s0.sp - 2400#64) + 236#64) ↦₃₂ z236) ∗ memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗
       memRegion ((s0.sp - 2400#64) + 1432#64) 456 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
       memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 136 ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
       memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
       memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗
       (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
       (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
       vecU8Payload A (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
       vecU8Payload A (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) by ac_rfl)) ?_
  have hcopy := v5c_step_6064_some_to_call_35448_placed (ext := ext) s0 s1
    (s0.sp - 2400#64) out (BitVec.ofNat 64 authPb.rootKey.length) p1_new w8 w16 w24 w40 d36
    z0 z8 z16 zd24 zd28 z32
    (v5a_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder decPb)) w8 w16 w24 48#32 d36 w40 ∗
     (((s0.sp - 2400#64) + 236#64) ↦₃₂ z236) ∗ memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗
     memRegion ((s0.sp - 2400#64) + 1432#64) 456 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
     memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     memRegion (s0.sp - 2400#64) 136 ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
     memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
     memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗
     (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
     (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
     vecU8Payload A (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
     vecU8Payload A (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)
    hfsp_align hl1_lt hw8_lt hpc1 hrun1 hsp1 hx19_1 hx20_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1 htr1
  refine v5_sepWPp_seq_clean_lscl hcl1 hcopy ?_
  intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hx1_2, hx19_2, hx20_2, hx21_2, hx27_2, hx30_2, htr2⟩
  refine SepWPp.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        (v5a_optProtoPolyDecoderWordsAt ((s0.sp - 2400#64) + 1392#64) w8 w16 w24 48#32 d36 w40 ∗
         v5a_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder decPb)) w8 w16 w24 48#32 d36 w40) ∗
        (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ A.pool ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ R_post_call) by dsimp only [R_post_call]; ac_rfl))
      (Entails.trans (sepConj_mono_left hpack)
        (Entails.of_eq (show _ =
          (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
           protoPolynomialDecoderAt A ((s0.sp - 2400#64) + 1392#64) (pbToProtoPolyDecoder decPb) ∗
           A.pool ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack) ∗ R_post_call by ac_rfl)))) ?_
  have hsub := v5a_sub_ok_decoder_from_pb_placed hDec
  have hsp2_align : s2.spAligned = true := by unfold State.spAligned; rw [hsp2]; exact hfsp_align
  refine v5_sepWPp_call_ret_lscl hsub
    (x := { out := (s0.sp - 2400#64) + 1888#64,
            pbA := (s0.sp - 2400#64) + 1392#64,
            pb := pbToProtoPolyDecoder decPb })
    hcl2 hpc2 hrun2 hsp2_align hx30_2
    (fun R' hm => Satisfies.mono (sepConj_mono_left
      (Entails.pure_right ⟨hx0_2, hx1_2⟩
        (by dsimp only [polyDecoderSize, decoderFromPbStack]; rw [hsp2]; exact Entails.refl _))) hm)
    (fun sf => v5a_onPanic_frame_entails htr2) (fun _ _ => rfl) ?_
  intro s3 hpc3 hrun3 hsp3_2 hcs23
  simp only [decoderFromPbSpec, protoPolynomialDecoderSize, decoderFromPbStack, R_post_call, sepConj_assoc]
  apply ProofLib.SepWP.pure_elim; intro htr3_2
  have hsp3 : s3.sp = s0.sp - 2400#64 := hsp3_2.trans hsp2
  have hx19_3 : s3.readReg64 .x19 = out := (hcs23.1).trans hx19_2
  have hx20_3 : s3.readReg64 .x20 = (s0.sp - 2400#64) + 1888#64 := (hcs23.2.1).trans hx20_2
  have hx21_3 : s3.readReg64 .x21 = BitVec.ofNat 64 authPb.rootKey.length := (hcs23.2.2.1).trans hx21_2
  have hx27_3 : s3.readReg64 .x27 = p1_new := (hcs23.2.2.2.2.2.2.2.2.1).trans hx27_2
  have htr3 : TraceCalleeSaved s3 s0 := ⟨htr3_2.trans htr2.1, hcs23.2.2.2.2.2.2.2.2.2.2.2.trans htr2.2⟩
  have hm1648 := v5_memRegion_240_merge_1648 (s0.sp - 2400#64)
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        (memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗
         memRegion ((s0.sp - 2400#64) + 1392#64) 40 ∗
         memRegion ((s0.sp - 2400#64) + 1432#64) 456) ∗
        resultPolyDecoderFromPbAt A ((s0.sp - 2400#64) + 1888#64)
          (decoderFromPbResult (pbToProtoPolyDecoder decPb)) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗
         (((s0.sp - 2400#64) + 236#64) ↦₃₂ z236) ∗ memRegion (s0.sp - 2400#64) 136 ∗
         (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗
         (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
         (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
         vecU8Payload A (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
         vecU8Payload A (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) by rw [hsp2]; ac_rfl))
      (sepConj_mono_left hm1648)) ?_
  rw [v5a_states_from_pb_noHeaderReceived_auth_some_dec_some F authPb ep decPb heq48]
  cases hres : decoderFromPbResult (pbToProtoPolyDecoder decPb) with
  | error err =>
    refine SepWP.weaken_pre
      (Entails.trans
        (sepConj_mono_right (sepConj_mono_left (v9_resultPolyDecoder_err_entails_tag_392 A (s0.sp - 2400#64) err)))
        (Entails.of_eq (show _ =
          (((s0.sp - 2400#64) + 1888#64) ↦₆₄ noneCap) ∗
          (memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗
           memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ (((s0.sp - 2400#64) + 236#64) ↦₃₂ z236) ∗
           stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 136 ∗
           (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗
           (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
           (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
           (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗
           vecU8Payload A (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
           vecU8Payload A (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) by ac_rfl))) ?_
    have h6520 := v5c_step_6132_err_to_6520_placed (ext := ext) s0 s3
      (s0.sp - 2400#64) out (BitVec.ofNat 64 authPb.rootKey.length) p1_new
      (memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗
       memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ (((s0.sp - 2400#64) + 236#64) ↦₃₂ z236) ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 136 ∗
       (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗
       (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
       (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗
       vecU8Payload A (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
       vecU8Payload A (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)
      hfsp_align hpc3 hrun3 hsp3 hx19_3 hx21_3 hx27_3 htr3
    refine EncoderFromPb.seq_clean h6520 ?_
    intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, hx21_4, hx27_4, htr4⟩
    have hj2068 := v5_memRegion_2068_join_err (s0.sp - 2400#64) z236 noneCap
    refine SepWP.weaken_pre
      (Entails.trans
        (Entails.of_eq (show _ =
          ((((s0.sp - 2400#64) + 236#64) ↦₃₂ z236) ∗ memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗
           (((s0.sp - 2400#64) + 1888#64) ↦₆₄ noneCap) ∗ memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗
           memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 136 ∗
           (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗
           (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
           (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
           (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗
           vecU8Payload A (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
           vecU8Payload A (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗
           (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)) by ac_rfl))
        (Entails.trans (sepConj_mono_left hj2068)
          (Entails.of_eq (show _ =
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 136 ∗
            (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗
            (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗
            (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
            (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗
            memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗
            vecU8Payload A (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
            vecU8Payload A (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
            statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗
            (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) by ac_rfl)))) ?_
    have herr := v5_err_6520_to_ret_placed (A := A) (F := F) hA s0 s4
      out p1_new p2_new (BitVec.ofNat 64 authPb.rootKey.length)
      (BitVec.ofNat 64 authPb.macKey.length) ep w80 w40 d36 authPb.rootKey authPb.macKey
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
      hsp0_align hpc4 hrun4 hsp4 hx19_4 hx21_4 hx27_4 htr4
    refine SepWP.mono herr ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
  | ok dec =>
    dsimp only [resultPolyDecoderFromPbAt]
    refine SepWP.weaken_pre
      (sepConj_mono_right
        (sepConj_mono_left (v9_polyDecoderAt_relocate A ((s0.sp - 2400#64) + 1888#64) (out + 64#64) dec))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine ProofLib.SepWP.exists_left fun bs =>
      ProofLib.SepWP.exists_left fun w392 =>
      ProofLib.SepWP.exists_left fun P_heap => ?_
    have hm160 := v5_memRegion_160_merge_48 (s0.sp - 2400#64) w80
    have hm232 := v9_pointsTo32_pair_eq_pointsTo64 ((s0.sp - 2400#64) + 232#64) d36 z236
    have ha236 : ((s0.sp - 2400#64) + 232#64) + 4#64 = (s0.sp - 2400#64) + 236#64 := by bv_omega
    have ha2272 : ((s0.sp - 2400#64) + 1888#64) + 384#64 = (s0.sp - 2400#64) + 2272#64 := by bv_omega
    have ha2280 : ((s0.sp - 2400#64) + 1888#64) + 392#64 = (s0.sp - 2400#64) + 2280#64 := by bv_omega
    rw [ha236] at hm232
    rw [v5c_bs384_eq_decCells bs.val bs.property ((s0.sp - 2400#64) + 1888#64), ha2272, ha2280]
    refine SepWP.weaken_pre
      (Entails.trans
        (Entails.of_eq (show _ =
          ⌜(v9_wordAt bs.val 0).toNat < 2 ^ 63 ∧
            EncoderFromPb.loByte w392 = boolByte dec.isComplete ∧
            (((out + 64#64) ↦ₛ bs.val) ∗
             (((out + 64#64) + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
             (((out + 64#64) + 392#64) ↦₆₄ w392) ∗ P_heap ⊢
               polyDecoderAt A (out + 64#64) dec)⌝ ∗
          (memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80)) ∗
          ((((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗ (((s0.sp - 2400#64) + 236#64) ↦₃₂ z236)) ∗
          (memRegion (s0.sp - 2400#64) 136 ∗ memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗
           memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗
           stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
           (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
           (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
           (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
           (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗
           v5c_decCellsAt ((s0.sp - 2400#64) + 1888#64) bs.val ∗
           (((s0.sp - 2400#64) + 2272#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
           (((s0.sp - 2400#64) + 2280#64) ↦₆₄ w392) ∗
           memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ P_heap ∗
           vecU8Payload A (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
           vecU8Payload A (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
           (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)) by ac_rfl))
        (sepConj_mono_right
          (sepConj_mono hm160 (sepConj_mono_left (Entails.of_eq hm232))))) ?_
    apply ProofLib.SepWP.pure_elim; rintro ⟨hw0_lt, _, hreloc_out⟩
    refine SepWP.weaken_pre
      (Entails.of_eq (show _ =
        (memRegion (s0.sp - 2400#64) 136 ∗ memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗
         memRegion ((s0.sp - 2400#64) + 160#64) 48 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 1648) ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
        (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
        (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ (z236 ++ d36)) ∗
        v5c_decCellsAt ((s0.sp - 2400#64) + 1888#64) bs.val ∗
        (((s0.sp - 2400#64) + 2272#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        (((s0.sp - 2400#64) + 2280#64) ↦₆₄ w392) ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ P_heap ∗
        vecU8Payload A (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
        vecU8Payload A (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) by ac_rfl)) ?_
    have hok := v5c_noHeaderReceived_6132_ok_to_ret_placed (A := A) (F := F) hA s0 s3
      (s0.sp - 2400#64) out ep
      p1_new (BitVec.ofNat 64 authPb.rootKey.length)
      p2_new (BitVec.ofNat 64 authPb.macKey.length)
      w40 (z236 ++ d36) w392 bs.val bs.property hw0_lt dec P_heap hreloc_out
      authPb.rootKey authPb.macKey rfl rfl
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)
      hsp0_align rfl hpc3 hrun3 hsp3 hx19_3 hx20_3 hx21_3 hx27_3 htr3
    refine SepWP.mono hok ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

/-! ## Unified `+3744 -> s0.x30` & Top-Level Variant 5 Theorem (`+1344 -> s0.x30`) -/

set_option maxHeartbeats 800000 in
/-- Unified continuation from `+3744` when `receivingHdr = none` (`d32_eq : True`)
    or `receivingHdr = some decPb` with `d32 = 48#32` (`(decPb.ptsNeeded == 48#32) = true`). -/
theorem v5_noHeaderReceived_3744_to_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (hDec : DecoderFromPbPlacedOkExt A ext)
    (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out pbA w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 : BitVec 64)
    (d32 d36 : BitVec 32)
    (uc : Option V1State.Unchunked.NoHeaderReceived)
    (receivingHdr : Option PolynomialDecoder) (R : SepProp)
    (hd32_48 : ∀ decPb, receivingHdr = some decPb → d32 = 48#32 ∧ (decPb.ptsNeeded == 48#32) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3744#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = w88) (hx9_1 : s1.readReg64 .x9 = w96)
    (hx10_1 : s1.readReg64 .x10 = w80) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = w64) (hx21_1 : s1.readReg64 .x21 = w72)
    (hx22_1 : s1.readReg64 .x22 = w16) (hx23_1 : s1.readReg64 .x23 = w8)
    (hx24_1 : s1.readReg64 .x24 = w48) (hx25_1 : s1.readReg64 .x25 = d32.zeroExtend 64)
    (hx26_1 : s1.readReg64 .x26 = w56) (hx28_1 : s1.readReg64 .x28 = w24)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (v5a_optProtoUcHeap A uc w48 w56 w64 w72 w80 w88 w96 ∗
        v5a_optProtoPolyDecoderHeap A (receivingHdr.map pbToProtoPolyDecoder) w8 w16 w24 d32 d36 w40 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 224 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗
        memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.noHeaderReceived { uc := uc, receivingHdr := receivingHdr }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hj2304 := v5b_memRegion_2304_join_224_232 (s0.sp - 2400#64) w40 d36
  let P_6420 : SepProp :=
    v5a_optProtoPolyDecoderHeap A (receivingHdr.map pbToProtoPolyDecoder) w8 w16 w24 d32 d36 w40 ∗
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗
    (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
  cases uc with
  | none =>
    have hres_eq :
        States.from_pb spqrPolyApi (spqrAuthApi F)
          { innerState := some (.noHeaderReceived { uc := none, receivingHdr := receivingHdr }) } =
        .error (.err .stateDecode) := by
      cases receivingHdr with
      | none => exact v5a_states_from_pb_noHeaderReceived_uc_none_dec_none F
      | some decPb => exact v5a_states_from_pb_noHeaderReceived_uc_none_dec_some F decPb (hd32_48 decPb rfl).2
    rw [hres_eq]
    dsimp only [v5a_optProtoUcHeap]
    refine SepWPp.pure_left fun hw48 => ?_
    rw [hw48] at hx24_1
    apply SepWPp.of_sepWP_ret
    refine SepWP.weaken_pre
      (Entails.trans
        (Entails.of_eq (show _ =
          (memRegion (s0.sp - 2400#64) 224 ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗
           (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗ memRegion ((s0.sp - 2400#64) + 236#64) 2068) ∗
          (v5a_optProtoPolyDecoderHeap A (receivingHdr.map pbToProtoPolyDecoder) w8 w16 w24 d32 d36 w40 ∗
           stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗
           (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)) by ac_rfl))
        (Entails.trans (sepConj_mono_left hj2304)
          (Entails.of_eq (show _ = P_6420 by dsimp only [P_6420]; ac_rfl)))) ?_
    have h6420 := v5b_step_3744_uc_none_to_6420_placed (ext := ext) s0 s1
      (s0.sp - 2400#64) out w16 w8 w24 P_6420
      hpc1 hrun1 hsp1 hx19_1 hx22_1 hx23_1 hx24_1 hx28_1 htr1
    refine EncoderFromPb.seq_clean h6420 ?_
    intro s2 hpc2 hrun2 ⟨hpres2, hx28_2⟩
    have herr := v5_err_6420_to_ret_placed (A := A) (F := F) hA s0 s2 out w8 w16 w24 w40 d32 d36
      receivingHdr (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
      hsp0_align hpc2 hrun2 hpres2 hx28_2
    refine SepWP.mono herr ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
  | some ucVal =>
    rcases ucVal with ⟨ep, optAuth⟩
    cases optAuth with
    | none =>
      have hres_eq :
          States.from_pb spqrPolyApi (spqrAuthApi F)
            { innerState := some (.noHeaderReceived
                { uc := some { auth := none, epoch := ep }, receivingHdr := receivingHdr }) } =
          .error (.err .stateDecode) := by
        cases receivingHdr with
        | none => exact v5a_states_from_pb_noHeaderReceived_auth_none_dec_none F ep
        | some decPb => exact v5a_states_from_pb_noHeaderReceived_auth_none_dec_some F ep decPb (hd32_48 decPb rfl).2
      rw [hres_eq]
      dsimp only [v5a_optProtoUcHeap]
      refine SepWPp.pure_left fun ⟨hw48, _⟩ => ?_
      rw [hw48] at hx24_1
      apply SepWPp.of_sepWP_ret
      refine SepWP.weaken_pre
        (Entails.trans
          (Entails.of_eq (show _ =
            (memRegion (s0.sp - 2400#64) 224 ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗
             (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗ memRegion ((s0.sp - 2400#64) + 236#64) 2068) ∗
            (v5a_optProtoPolyDecoderHeap A (receivingHdr.map pbToProtoPolyDecoder) w8 w16 w24 d32 d36 w40 ∗
             stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗
             (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)) by ac_rfl))
          (Entails.trans (sepConj_mono_left hj2304)
            (Entails.of_eq (show _ = P_6420 by dsimp only [P_6420]; ac_rfl)))) ?_
      have h6420 := v5b_step_3744_auth_none_to_6420_placed (ext := ext) s0 s1
        (s0.sp - 2400#64) out w16 w8 w24 P_6420
        hpc1 hrun1 hsp1 hx19_1 hx22_1 hx23_1 hx24_1 hx28_1 htr1
      refine EncoderFromPb.seq_clean h6420 ?_
      intro s2 hpc2 hrun2 ⟨hpres2, hx28_2⟩
      have herr := v5_err_6420_to_ret_placed (A := A) (F := F) hA s0 s2 out w8 w16 w24 w40 d32 d36
        receivingHdr (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
        hsp0_align hpc2 hrun2 hpres2 hx28_2
      refine SepWP.mono herr ?_
      intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
    | some authPb =>
      refine SepWPp.weaken_pre
        (Entails.of_eq (show _ =
          v5a_optProtoUcHeap A (some { auth := some authPb, epoch := ep }) w48 w56 w64 w72 w80 w88 w96 ∗
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 224 ∗ A.pool ∗
          (v5a_optProtoPolyDecoderHeap A (receivingHdr.map pbToProtoPolyDecoder) w8 w16 w24 d32 d36 w40 ∗
           (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗
           memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗ statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗
           statesFromPbJumpTablePlacedAt) by ac_rfl)) ?_
      have h6064 := v5_auth_some_3744_to_6064_placed hA s0 s1
        out w16 w8 w24 (d32.zeroExtend 64) w48 w56 w64 w72 w80 w88 w96 ep authPb
        (v5a_optProtoPolyDecoderHeap A (receivingHdr.map pbToProtoPolyDecoder) w8 w16 w24 d32 d36 w40 ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗
         memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗
         statesFromPbJumpTablePlacedAt) R
        hsp0_align hpc1 hrun1 hsp1 hx8_1 hx9_1 hx10_1 hx19_1 hx20_1
        hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1 htr1
      refine v5_sepWPp_bind_lscl hcl1 h6064 ?_
      intro s2 P2 hpc2 hrun2 hcl2 ⟨p1_new, p2_new, hr_lt63, hm_lt63, hl1_lt, hP2,
        hsp2, hx19_2, hx20_2, hx22_2, hx23_2, hx25_2, hx27_2, hx28_2, htr2⟩
      cases receivingHdr with
      | none =>
        rw [v5a_states_from_pb_noHeaderReceived_auth_some_dec_none F authPb ep]
        dsimp only [Option.map, v5a_optProtoPolyDecoderHeap] at hP2
        let P_6520 : SepProp :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 136 ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
          memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
          memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗
          (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
          (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗
          memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗
          vecU8Payload A (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
          vecU8Payload A (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗
          (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
        refine SepWPp.weaken_pre
          (Entails.trans hP2
            (Entails.of_eq (show _ = ⌜w8 = noneCap⌝ ∗ P_6520 by dsimp only [P_6520]; ac_rfl))) ?_
        refine SepWPp.pure_left fun hw8 => ?_
        rw [hw8] at hx23_2
        apply SepWPp.of_sepWP_ret
        have h6520 := v5c_step_6064_none_to_6520_placed (ext := ext) s0 s2
          (s0.sp - 2400#64) out (BitVec.ofNat 64 authPb.rootKey.length) p1_new P_6520
          hl1_lt hpc2 hrun2 hsp2 hx19_2 hx20_2 hx23_2 hx27_2 htr2
        refine EncoderFromPb.seq_clean h6520 ?_
        intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx21_3, hx27_3, htr3⟩
        have herr := v5_err_6520_to_ret_placed (A := A) (F := F) hA s0 s3
          out p1_new p2_new (BitVec.ofNat 64 authPb.rootKey.length)
          (BitVec.ofNat 64 authPb.macKey.length) ep w80 w40 d36 authPb.rootKey authPb.macKey
          (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
          hsp0_align hpc3 hrun3 hsp3 hx19_3 hx21_3 hx27_3 htr3
        refine SepWP.mono herr ?_
        intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
        exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
      | some decPb =>
        rcases hd32_48 decPb rfl with ⟨rfl, heq48⟩
        exact SepWPp.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl)))
          (v5_noHeaderReceived_6064_some_to_ret_placed (A := A) (F := F) hA hDec s0 s2 hcl2
            out pbA p1_new p2_new ep w8 w16 w24 w40 w80 d36 authPb decPb R
            heq48 hr_lt63 hm_lt63 hl1_lt hsp0_align hpc2 hrun2 hsp2
            hx19_2 hx20_2 hx22_2 hx23_2 hx25_2 hx27_2 hx28_2 htr2)

set_option maxHeartbeats 800000 in
/-- Complete Variant 5 (`NoHeaderReceived`, `+1344 -> s0.x30`) theorem. -/
theorem states_from_pb_noHeaderReceived_1344_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (hDec : DecoderFromPbPlacedOkExt A ext)
    (s : V1State.Chunked.NoHeaderReceived)
    (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out pbA : BitVec 64) (R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1344#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (_hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A pbA (some (.noHeaderReceived s)) ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.noHeaderReceived s) }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  rcases s with ⟨uc, receivingHdr⟩
  refine SepWPp.weaken_pre
    (sepConj_mono_right
      (sepConj_mono (v5b_memRegion_2304_split_224_232 (s0.sp - 2400#64))
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (v5a_optProtoInnerStateAt_unpack A pbA ⟨uc, receivingHdr⟩)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w8 => SepWPp.exists_elim fun w16 =>
    SepWPp.exists_elim fun w24 => SepWPp.exists_elim fun d32 =>
    SepWPp.exists_elim fun d36 => SepWPp.exists_elim fun w40 =>
    SepWPp.exists_elim fun w48 => SepWPp.exists_elim fun w56 =>
    SepWPp.exists_elim fun w64 => SepWPp.exists_elim fun w72 =>
    SepWPp.exists_elim fun w80 => SepWPp.exists_elim fun w88 =>
    SepWPp.exists_elim fun w96 => SepWPp.exists_elim fun z232 =>
    SepWPp.exists_elim fun z224 => ?_
  cases receivingHdr with
  | none =>
    refine SepWPp.weaken_pre
      (Entails.trans
        (Entails.of_eq (show _ =
          v5a_optProtoPolyDecoderHeap A none w8 w16 w24 d32 d36 w40 ∗
          (v5a_pbAHeadersAt pbA w8 w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 ∗
           (((s0.sp - 2400#64) + 224#64) ↦₆₄ z224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ z232) ∗
           (v5a_optProtoUcHeap A uc w48 w56 w64 w72 w80 w88 w96 ∗
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 224 ∗
            memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗ statesFromPbSavedCells s0 ∗
            memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)) by ac_rfl))
        (sepConj_mono_left (v5_optProtoPolyDecoderHeap_none_dup A w8 w16 w24 d32 d36 w40))) ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun hw8 => ?_
    subst hw8
    refine SepWPp.weaken_pre
      (Entails.of_eq (show _ =
        v5a_pbAHeadersAt pbA noneCap w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ z224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ z232) ∗
        (v5a_optProtoPolyDecoderHeap A (Option.map pbToProtoPolyDecoder none) noneCap w16 w24 d32 d36 w40 ∗
         v5a_optProtoUcHeap A uc w48 w56 w64 w72 w80 w88 w96 ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 224 ∗
         memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) by ac_rfl)) ?_
    have h3744 := v5b_step_1344_to_3744_none_placed (ext := ext) s0 s1
      (s0.sp - 2400#64) out pbA w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 z224 z232
      (v5a_optProtoPolyDecoderHeap A (Option.map pbToProtoPolyDecoder none) noneCap w16 w24 d32 d36 w40 ∗
       v5a_optProtoUcHeap A uc w48 w56 w64 w72 w80 w88 w96 ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 224 ∗
       memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)
      hfsp_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
    refine v5_sepWPp_seq_clean_lscl hcl1 h3744 ?_
    intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx8_2, hx9_2, hx10_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, _, hx28_2, htr2⟩
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (v5_noHeaderReceived_3744_to_ret_placed (A := A) (F := F) hA hDec s0 s2 hcl2
        out pbA noneCap w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 d32 d36 uc none R
        (fun _ h => nomatch h) hsp0_align hpc2 hrun2 hsp2
        hx8_2 hx9_2 hx10_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx28_2 htr2)
  | some decPb =>
    refine SepWPp.weaken_pre
      (Entails.trans
        (Entails.of_eq (show _ =
          v5a_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder decPb)) w8 w16 w24 d32 d36 w40 ∗
          (v5a_pbAHeadersAt pbA w8 w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 ∗
           (((s0.sp - 2400#64) + 224#64) ↦₆₄ z224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ z232) ∗
           (v5a_optProtoUcHeap A uc w48 w56 w64 w72 w80 w88 w96 ∗
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 224 ∗
            memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗ statesFromPbSavedCells s0 ∗
            memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)) by ac_rfl))
        (sepConj_mono_left
          (v5_optProtoPolyDecoderHeap_some_dup A (pbToProtoPolyDecoder decPb) w8 w16 w24 d32 d36 w40))) ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨hd32, hw8_lt⟩ => ?_
    change d32 = decPb.ptsNeeded at hd32
    by_cases h48 : decPb.ptsNeeded = 48#32
    · have hd32_48 : d32 = 48#32 := hd32.trans h48
      subst hd32_48
      have heq48 : (decPb.ptsNeeded == 48#32) = true := beq_iff_eq.mpr h48
      refine SepWPp.weaken_pre
        (Entails.of_eq (show _ =
          v5a_pbAHeadersAt pbA w8 w16 w24 48#32 d36 w40 w48 w56 w64 w72 w80 w88 w96 ∗
          (((s0.sp - 2400#64) + 224#64) ↦₆₄ z224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ z232) ∗
          (v5a_optProtoPolyDecoderHeap A (Option.map pbToProtoPolyDecoder (some decPb)) w8 w16 w24 48#32 d36 w40 ∗
           v5a_optProtoUcHeap A uc w48 w56 w64 w72 w80 w88 w96 ∗
           stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 224 ∗
           memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗ statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) by ac_rfl)) ?_
      have h3744 := v5b_step_1344_to_3744_some_placed (ext := ext) s0 s1
        (s0.sp - 2400#64) out pbA w8 w16 w24 d36 w40 w48 w56 w64 w72 w80 w88 w96 z224 z232
        (v5a_optProtoPolyDecoderHeap A (Option.map pbToProtoPolyDecoder (some decPb)) w8 w16 w24 48#32 d36 w40 ∗
         v5a_optProtoUcHeap A uc w48 w56 w64 w72 w80 w88 w96 ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 224 ∗
         memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)
        hfsp_align hw8_lt hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
      refine v5_sepWPp_seq_clean_lscl hcl1 h3744 ?_
      intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx8_2, hx9_2, hx10_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, _, hx28_2, htr2⟩
      exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (v5_noHeaderReceived_3744_to_ret_placed (A := A) (F := F) hA hDec s0 s2 hcl2
          out pbA w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 48#32 d36 uc (some decPb) R
          (fun _ h => by cases h; exact ⟨rfl, heq48⟩) hsp0_align hpc2 hrun2 hsp2
          hx8_2 hx9_2 hx10_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx28_2 htr2)
    · have hd32_ne : d32 ≠ 48#32 := fun h => h48 (hd32.symm.trans h)
      have hne48 : (decPb.ptsNeeded == 48#32) = false := beq_false_of_ne h48
      rw [v5a_states_from_pb_noHeaderReceived_ptsNeeded_ne F decPb uc hne48]
      apply SepWPp.of_sepWP_ret
      refine SepWP.weaken_pre
        (Entails.of_eq (show _ =
          v5a_pbAHeadersAt pbA w8 w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 ∗
          (((s0.sp - 2400#64) + 224#64) ↦₆₄ z224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ z232) ∗
          (v5a_optProtoPolyDecoderHeap A (Option.map pbToProtoPolyDecoder (some decPb)) w8 w16 w24 d32 d36 w40 ∗
           v5a_optProtoUcHeap A uc w48 w56 w64 w72 w80 w88 w96 ∗
           stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 224 ∗
           memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗ statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) by ac_rfl)) ?_
      have h1396 := v5b_step_1344_to_1396_err_placed (ext := ext) s0 s1
        (s0.sp - 2400#64) out pbA w8 w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 z224 z232
        (v5a_optProtoPolyDecoderHeap A (Option.map pbToProtoPolyDecoder (some decPb)) w8 w16 w24 d32 d36 w40 ∗
         v5a_optProtoUcHeap A uc w48 w56 w64 w72 w80 w88 w96 ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 224 ∗
         memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)
        hfsp_align hw8_lt hd32_ne hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
      refine EncoderFromPb.seq_clean h1396 ?_
      intro s2 hpc2 hrun2 ⟨hsp2, hx10_2, hx19_2, hx21_2, hx22_2, hx23_2, hx24_2, hx26_2, hx28_2, htr2⟩
      have hj2304 := v5b_memRegion_2304_join_224_232 (s0.sp - 2400#64) w40 d36
      refine SepWP.weaken_pre
        (Entails.trans
          (Entails.of_eq (show _ =
            (memRegion (s0.sp - 2400#64) 224 ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗
             (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗ memRegion ((s0.sp - 2400#64) + 236#64) 2068) ∗
            (v5a_optProtoUcHeap A uc w48 w56 w64 w72 w80 w88 w96 ∗
             v5a_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder decPb)) w8 w16 w24 d32 d36 w40 ∗
             stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
             memRegion out chunkedStatesSize ∗ A.pool ∗
             (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)) by ac_rfl))
          (Entails.trans (sepConj_mono_left hj2304)
            (Entails.of_eq (show _ =
              v5a_optProtoUcHeap A uc w48 w56 w64 w72 w80 w88 w96 ∗
              v5a_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder decPb)) w8 w16 w24 d32 d36 w40 ∗
              stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
              statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗
              (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) by ac_rfl)))) ?_
      have herr := v5_err_1396_to_ret_placed (A := A) (F := F) hA s0 s2
        out w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 d32 d36 uc decPb
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
        hsp0_align hpc2 hrun2 hsp2 hx10_2 hx19_2 hx21_2 hx22_2 hx23_2 hx24_2 hx26_2 hx28_2 htr2
      refine SepWP.mono herr ?_
      intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

end CryptoVerification.SpqrV1.States.FromPb
