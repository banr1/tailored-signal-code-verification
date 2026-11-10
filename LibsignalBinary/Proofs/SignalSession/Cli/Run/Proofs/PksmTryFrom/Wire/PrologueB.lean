/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromLoop
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrAt
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W0Spec
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ParseLemmas
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Prologue
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

/-!
# `PreKeySignalMessage::try_from`: Unified Prologue Theorems (`+0x000 → +0x504 / +0x460`)

Combines the prologue branches with `PreKeyDecodeLoopF4OkW` / `PreKeyDecodeLoopF4Ok` into
`preKey_earlyErr_to_504_wpE` (`+0x000 → +0x504`) and `preKey_valid_to_460_wpW` /
`preKey_valid_to_460_wpX` (`+0x000 → +0x460`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

private abbrev SepWPp := @Wire.SepWPp
private abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev SepWPp.bind := @Wire.SepWPp.bind
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev SepWPp.bind_frame_entails := @Wire.SepWPp.bind_frame_entails
private abbrev SepWPp.bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom

attribute [local irreducible] Program.fetch Program.externAt?

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## `ProofLib.SepWPp` Bridge Combinators (for `W0Spec.PreKeyDecodeLoopF4Ok`) -/

private theorem plb_to_proofLib {prog : Program} {ret : BitVec 64} {s : Arm64.State} {P : SepProp}
    {Q Qp : Arm64.State → SepProp → Prop} (h : Wire.SepWPp prog ret s P Q Qp) :
    ProofLib.SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hq, _⟩ | hpan⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, hq⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

private theorem plb_mono_pre_p {prog : Program} {ret : BitVec 64} {s : Arm64.State}
    {P P' : SepProp} {Q Qp : Arm64.State → SepProp → Prop}
    (hent : P ⊢ P') (h : ProofLib.SepWPp prog ret s P' Q Qp) :
    ProofLib.SepWPp prog ret s P Q Qp := by
  intro R hm hL
  exact h R (Satisfies.mono (sepConj_mono_left hent) hm) hL

private theorem plb_frame_tryFrom_p {prog : Program} {ret : BitVec 64} {s0 s : Arm64.State}
    {P F : SepProp} {Q Q' : Arm64.State → SepProp → Prop}
    (h : ProofLib.SepWPp prog ret s P Q' (tryFromQp s0))
    (hq : ∀ sf Pm, Q' sf Pm → Q sf (Pm ∗ F)) :
    ProofLib.SepWPp prog ret s (P ∗ F) Q (tryFromQp s0) := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pm, hmm, hqm⟩ | ⟨hpan, P_f, hmp, hqp⟩ | ⟨_, hoom⟩⟩ :=
    h (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmm
    exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pm ∗ F, hmm, hq sf Pm hqm⟩⟩
  · rw [← sepConj_assoc] at hmp
    exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f ∗ F, hmp, tryFromQp_frame hqp⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem plb_bind_frame_tryFrom_p {prog : Program} {mid ret : BitVec 64} {s0 s : Arm64.State}
    {P F : SepProp} {Qm Q : Arm64.State → SepProp → Prop}
    (h1 : ProofLib.SepWPp prog mid s P Qm (tryFromQp s0))
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Qm sm Pm →
      ProofLib.SepWPp prog ret sm (Pm ∗ F) Q (tryFromQp s0)) :
    ProofLib.SepWPp prog ret s (P ∗ F) Q (tryFromQp s0) := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hqm⟩ | ⟨hpan, P_f, hmp, hqp⟩ | ⟨_, hoom⟩⟩ :=
    h1 (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmm
    obtain ⟨sf, hs', hout⟩ := h2 sm Pm hpc hrun hqm R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hs', hout⟩
  · rw [← sepConj_assoc] at hmp
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_f ∗ F, hmp, tryFromQp_frame hqp⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem plb_bind_frame_entails_p {prog : Program} {mid ret : BitVec 64} {s0 s : Arm64.State}
    {P P' F : SepProp} {R_st : Arm64.State → Prop} {Q : Arm64.State → SepProp → Prop}
    (h1 : ProofLib.SepWPp prog mid s P (fun sm Pm => R_st sm ∧ (Pm ⊢ P')) (tryFromQp s0))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → R_st sm →
      ProofLib.SepWPp prog ret sm (P' ∗ F) Q (tryFromQp s0)) :
    ProofLib.SepWPp prog ret s (P ∗ F) Q (tryFromQp s0) := by
  refine plb_bind_frame_tryFrom_p h1 ?_
  intro sm Pm hpc hrun ⟨hr, hent⟩
  exact plb_mono_pre_p (sepConj_mono_left hent) (h2 sm hpc hrun hr)

/-! ## `PreKeyDecodeLoopF4OkW` (`Wire.SepWPp` variant preserving `calleeSavedVRegs`) -/

/-- `PreKeyDecodeLoopF4Ok` with `Wire.SepWPp` (preserving `calleeSavedVRegs`). -/
def PreKeyDecodeLoopF4OkW (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (s0 : State) (sp' sret len ptr0 : BitVec 64) (vb : BitVec 8) (fuel : Nat) (s : State)
    (ptr : BitVec 64) (b0 : BitVec 8) (bs1 : List (BitVec 8)) (m : ProtoPreKeySignalMessage),
    s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0f4#64 →
    s.status = .Running →
    PreKeyLoopRegs sp' sret len ptr0 vb s →
    s.readReg64 .x28 = sp' + 296#64 → s.readReg64 .x26 = sp' + 304#64 →
    s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length →
    s.spAligned = true → img.FrozenLoaded s → s.symtab = img.symtab → s.trace = s0.trace →
    (b0 :: bs1).length ≤ fuel + 1 → (b0 :: bs1).length < 2 ^ 32 →
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr (b0 :: bs1) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr (b0 :: bs1)
        (Pksm.decodeProtoLoop (fuel + 1) m (b0 :: bs1)))
      (tryFromQp s0)

private theorem plb_ofNat64_cons_sub_one (b0 : BitVec 8) (bs : List (BitVec 8)) :
    BitVec.ofNat 64 (b0 :: bs).length - 1#64 = BitVec.ofNat 64 bs.length := by
  simp only [List.length_cons]
  bv_omega

/-- Chained valid-version + non-empty protobuf body (`x.bytes = vb :: b1 :: bs1`, `Wire.SepWPp`):
steps `+0x080 → +0x0bc → +0x0f4` and invokes `hLoopF4 : PreKeyDecodeLoopF4OkW img A ext`
(at `fuel := bs1.length`, `m := Pksm.emptyProto`) to reach `+0x460` (`1120`) with
`preKeyLoopExitPost` while preserving `calleeSavedVRegs`. -/
theorem preKey_init_to_460_wpW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hLoopF4 : PreKeyDecodeLoopF4OkW img A ext)
    {sret sp' ptr : BitVec 64} {vb b1 : BitVec 8} {bs1 : List (BitVec 8)}
    {s0 s2 : State}
    (hlt : (vb :: b1 :: bs1).length < 2 ^ 32)
    (hst : PostEpilogueState img s0 sp' s2)
    (hpc : s2.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 128#64)
    (hrun : s2.status = .Running)
    (hx29 : s2.readReg64 .x29 = sp' + 512#64)
    (hx27 : s2.readReg64 .x27 = 0x8000000000000002#64)
    (hx22 : s2.readReg64 .x22 = vb.zeroExtend 64)
    (hx21 : s2.readReg64 .x21 = ptr)
    (hx19 : s2.readReg64 .x19 = sret)
    (hx1 : s2.readReg64 .x1 = BitVec.ofNat 64 (vb :: b1 :: bs1).length) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1120#64) s2
      (((ptr + 1#64) ↦ₛ (b1 :: bs1)) ∗
        memRegion (sp' + 296#64) 152 ∗
        memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (preKeyLoopExitPost img A s0 sp' sret
        (BitVec.ofNat 64 (vb :: b1 :: bs1).length) ptr vb
        (ptr + 1#64) (b1 :: bs1) (Pksm.decodeProto (b1 :: bs1)))
      (tryFromQp s0) := by
  refine SepWPp.mono_pre
    (P' := memRegion (sp' + 296#64) 152 ∗
      (((ptr + 1#64) ↦ₛ (b1 :: bs1)) ∗
        memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (prologue_80_init_wpX hst hpc hrun hx29 hx27 hx22 hx21 hx19 hx1) ?_
  intro s3 P3 hpc3 hrun3
    ⟨hst3, hpstate3, hx29_3, hx27_3, hx22_3, hx21_3, hx20_3, hx19_3, hx8_3, hx2_3, hent3⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent3) ?_
  clear hent3
  have hge2 : 2 ≤ (vb :: b1 :: bs1).length := by simp
  have hsub1 :
      BitVec.ofNat 64 (vb :: b1 :: bs1).length - 1#64 = BitVec.ofNat 64 (b1 :: bs1).length :=
    plb_ofNat64_cons_sub_one vb (b1 :: bs1)
  have hwire := emptyPreKey_cells_entails_wirePreKeyOf A (sp' + 312#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hwire
  refine SepWPp.mono_pre
    (P' := emp ∗
      (sliceCursorAt (sp' + 296#64) (ptr + 1#64) (b1 :: bs1) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) Pksm.emptyProto))
    (by
      rw [emp_sepConj]
      unfold sliceCursorAt
      rw [hsub1]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right hwire)))))
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_entails
    (prologue_bc_gt1_to_f4_wpX hge2 hlt hst3 hpc3 hrun3
      hpstate3 hx29_3 hx27_3 hx22_3 hx21_3 hx20_3 hx19_3 hx8_3 hx2_3) ?_
  intro s4 hpc4 hrun4
    ⟨hregs4, ⟨_, hsp4, hF4, hsym4, htr4⟩, hx28_4, hx26_4, hx2_4⟩
  rw [hsub1] at hx2_4
  have hlt_body : (b1 :: bs1).length < 2 ^ 32 := by
    simp only [List.length_cons] at hlt ⊢; omega
  have hloop := hLoopF4 s0 sp' sret (BitVec.ofNat 64 (vb :: b1 :: bs1).length) ptr vb
    bs1.length s4 (ptr + 1#64) b1 bs1 Pksm.emptyProto
    hpc4 hrun4 hregs4 hx28_4 hx26_4 hx2_4 hsp4 hF4 hsym4 htr4 (Nat.le_refl _) hlt_body
  simpa [Pksm.decodeProto] using hloop

/-- Chained valid-version + non-empty protobuf body (`x.bytes = vb :: b1 :: bs1`, `ProofLib.SepWPp`
taking `W0Spec.PreKeyDecodeLoopF4Ok`). -/
theorem preKey_init_to_460_wpX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hLoopF4 : PreKeyDecodeLoopF4Ok img A ext)
    {sret sp' ptr : BitVec 64} {vb b1 : BitVec 8} {bs1 : List (BitVec 8)}
    {s0 s2 : State}
    (hlt : (vb :: b1 :: bs1).length < 2 ^ 32)
    (hst : PostEpilogueState img s0 sp' s2)
    (hpc : s2.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 128#64)
    (hrun : s2.status = .Running)
    (hx29 : s2.readReg64 .x29 = sp' + 512#64)
    (hx27 : s2.readReg64 .x27 = 0x8000000000000002#64)
    (hx22 : s2.readReg64 .x22 = vb.zeroExtend 64)
    (hx21 : s2.readReg64 .x21 = ptr)
    (hx19 : s2.readReg64 .x19 = sret)
    (hx1 : s2.readReg64 .x1 = BitVec.ofNat 64 (vb :: b1 :: bs1).length) :
    ProofLib.SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1120#64) s2
      (((ptr + 1#64) ↦ₛ (b1 :: bs1)) ∗
        memRegion (sp' + 296#64) 152 ∗
        memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (preKeyLoopExitPost img A s0 sp' sret
        (BitVec.ofNat 64 (vb :: b1 :: bs1).length) ptr vb
        (ptr + 1#64) (b1 :: bs1) (Pksm.decodeProto (b1 :: bs1)))
      (tryFromQp s0) := by
  refine plb_mono_pre_p
    (P' := memRegion (sp' + 296#64) 152 ∗
      (((ptr + 1#64) ↦ₛ (b1 :: bs1)) ∗
        memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
    (by apply entails_of_eq; ac_rfl) ?_
  refine plb_bind_frame_tryFrom_p
    (plb_to_proofLib (prologue_80_init_wpX hst hpc hrun hx29 hx27 hx22 hx21 hx19 hx1)) ?_
  intro s3 P3 hpc3 hrun3
    ⟨hst3, hpstate3, hx29_3, hx27_3, hx22_3, hx21_3, hx20_3, hx19_3, hx8_3, hx2_3, hent3⟩
  refine plb_mono_pre_p (sepConj_mono_left hent3) ?_
  clear hent3
  have hge2 : 2 ≤ (vb :: b1 :: bs1).length := by simp
  have hsub1 :
      BitVec.ofNat 64 (vb :: b1 :: bs1).length - 1#64 = BitVec.ofNat 64 (b1 :: bs1).length :=
    plb_ofNat64_cons_sub_one vb (b1 :: bs1)
  have hwire := emptyPreKey_cells_entails_wirePreKeyOf A (sp' + 312#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hwire
  refine plb_mono_pre_p
    (P' := emp ∗
      (sliceCursorAt (sp' + 296#64) (ptr + 1#64) (b1 :: bs1) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) Pksm.emptyProto))
    (by
      rw [emp_sepConj]
      unfold sliceCursorAt
      rw [hsub1]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right hwire)))))
      apply entails_of_eq; ac_rfl) ?_
  refine plb_bind_frame_entails_p
    (plb_to_proofLib (prologue_bc_gt1_to_f4_wpX hge2 hlt hst3 hpc3 hrun3
      hpstate3 hx29_3 hx27_3 hx22_3 hx21_3 hx20_3 hx19_3 hx8_3 hx2_3)) ?_
  intro s4 hpc4 hrun4
    ⟨hregs4, ⟨_, hsp4, hF4, hsym4, htr4⟩, hx28_4, hx26_4, hx2_4⟩
  rw [hsub1] at hx2_4
  have hlt_body : (b1 :: bs1).length < 2 ^ 32 := by
    simp only [List.length_cons] at hlt ⊢; omega
  have hloop := hLoopF4 s0 sp' sret (BitVec.ofNat 64 (vb :: b1 :: bs1).length) ptr vb
    bs1.length s4 (ptr + 1#64) b1 bs1 Pksm.emptyProto
    hpc4 hrun4 hregs4 hx28_4 hx26_4 hx2_4 hsp4 hF4 hsym4 htr4 (Nat.le_refl _) hlt_body
  simpa [Pksm.decodeProto] using hloop

/-! ## Top-Level Entry-to-Exit / Entry-to-`+0x460` Theorems -/

/-- Unified early-error theorem (`+0x000 → +0x504` / `1284`):
Whenever `x.bytes = []`, or `x.bytes = vb :: body` with `(vb >>> 4) < 3#8` or `4#8 < (vb >>> 4)`,
or `x.bytes = [vb]`, execution from `+0x000` reaches `+0x504` (`1284`) with `PostEpilogueState`,
`Pksm.pksmParse x.bytes = none`, and `pksmErrE A [] x.ret e` for some `e : SignalProtocolError`. -/
theorem preKey_earlyErr_to_504_wpE {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {x : RunCompose.PksmGhost} {s0 : State}
    (herr : x.bytes = [] ∨
      (∃ vb body, x.bytes = vb :: body ∧
        ((vb >>> 4) < 3#8 ∨ 4#8 < (vb >>> 4) ∨ body = [])))
    (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (contractProg img.base ext).fnAddr preKeyTryFromName)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hF : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab)
    (hx0 : s0.readReg64 .x0 = x.ptr)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s0
      ((x.ptr ↦ₛ x.bytes) ∗
        memRegion x.ret 248 ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 512#64) 96)
      (fun sf Pf =>
        PostEpilogueState img s0 (s0.sp - 608#64) sf ∧
        Pksm.pksmParse x.bytes = none ∧
        ∃ e : SignalProtocolError,
          Pf ⊢ pksmErrE A [] x.ret e ∗
            (x.ptr ↦ₛ x.bytes) ∗
            memRegion (s0.sp - 608#64) 296 ∗
            memRegion (s0.sp - 608#64 + 296#64) 152 ∗
            preKeyCalleeSavedAt (s0.sp - 608#64) s0)
      (tryFromQp s0) := by
  set sp' := s0.sp - 608#64
  rcases herr with hnil | ⟨vb, body, hcons, hcase⟩
  ·
    have hx1_0 : s0.readReg64 .x1 = 0#64 := by rw [hx1, hnil]; rfl
    have hparse : Pksm.pksmParse x.bytes = none := by rw [hnil]; exact pksmParse_nil
    refine SepWPp.mono_pre
      (P' := ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248 ∗ memRegion (sp' + 512#64) 96) ∗
        (memRegion sp' 296 ∗ memRegion (sp' + 296#64) 152))
      (by apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (prologue_nil_to_504_wpE (A := A) hnil hpc hrun hsp hF hsym hx1_0 hx8) ?_
    intro sf Pf ⟨hstf, hentf⟩
    refine ⟨hstf, hparse, .ciphertextMessageTooShort 0,
      Entails.trans (sepConj_mono_left hentf) ?_⟩
    apply entails_of_eq; ac_rfl
  ·
    have hne : x.bytes ≠ [] := by rw [hcons]; simp
    refine SepWPp.mono_pre
      (P' := memRegion (sp' + 512#64) 96 ∗
        ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248 ∗
          memRegion sp' 296 ∗ memRegion (sp' + 296#64) 152))
      (by apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.bind_frame_tryFrom
      (prologue_entry_ne_nil_wpX hne hlt hpc hrun hsp hF hsym hx0 hx1 hx8) ?_
    intro s1 P1 hpc1 hrun1 ⟨hst1, hx0_1, hx1_1, hx19_1, hx29_1, hent1⟩
    refine SepWPp.mono_pre (sepConj_mono_left hent1) ?_
    clear hent1
    by_cases hlt3 : (vb >>> 4) < 3#8
    ·
      have hvb30 : vb < 0x30#8 := by
        rw [BitVec.lt_def, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hlt3
        rw [BitVec.lt_def]
        change vb.toNat / 16 < 3 at hlt3
        change vb.toNat < 48
        omega
      have hparse : Pksm.pksmParse x.bytes = none := by
        rw [hcons]; exact pksmParse_legacy hvb30
      refine SepWPp.mono_pre
        (P' := ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248) ∗
          (preKeyCalleeSavedAt sp' s0 ∗ memRegion sp' 296 ∗ memRegion (sp' + 296#64) 152))
        (by apply entails_of_eq; ac_rfl) ?_
      refine SepWPp.frame_tryFrom
        (prologue_28_legacyVer_wpE (A := A) hcons hlt3 hst1 hpc1 hrun1 hx0_1 hx19_1) ?_
      intro sf Pf ⟨hstf, hentf⟩
      refine ⟨hstf, hparse, .legacyCiphertextVersion (vb >>> 4),
        Entails.trans (sepConj_mono_left hentf) ?_⟩
      apply entails_of_eq; ac_rfl
    · by_cases hgt4 : 4#8 < (vb >>> 4)
      ·
        have hvb4f : 0x4f#8 < vb := by
          have hvb_lt := vb.isLt
          rw [BitVec.lt_def, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hgt4
          rw [BitVec.lt_def]
          change 4 < vb.toNat / 16 at hgt4
          change 79 < vb.toNat
          omega
        have hparse : Pksm.pksmParse x.bytes = none := by
          rw [hcons]; exact pksmParse_unrec hvb4f
        refine SepWPp.mono_pre
          (P' := ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248) ∗
            (preKeyCalleeSavedAt sp' s0 ∗ memRegion sp' 296 ∗ memRegion (sp' + 296#64) 152))
          (by apply entails_of_eq; ac_rfl) ?_
        refine SepWPp.frame_tryFrom
          (prologue_28_unrecognizedVer_wpE (A := A) hcons hlt3 hgt4 hst1 hpc1 hrun1 hx0_1 hx19_1) ?_
        intro sf Pf ⟨hstf, hentf⟩
        refine ⟨hstf, hparse, .unrecognizedCiphertextVersion (vb >>> 4),
          Entails.trans (sepConj_mono_left hentf) ?_⟩
        apply entails_of_eq; ac_rfl
      ·
        have hbody : body = [] := by
          rcases hcase with h | h | h
          · exact absurd h hlt3
          · exact absurd h hgt4
          · exact h
        have hparse : Pksm.pksmParse x.bytes = none := by
          rw [hcons, hbody]; exact pksmParse_bkNone decodeProto_nil rfl
        have hbytes1 : (x.ptr ↦ₛ x.bytes) = (x.ptr ↦₈ vb) := by
          rw [hcons, hbody, pointsToBytes_singleton]
        refine SepWPp.mono_pre
          (P' := (x.ptr ↦₈ vb) ∗
            (preKeyCalleeSavedAt sp' s0 ∗ memRegion x.ret 248 ∗
              memRegion sp' 296 ∗ memRegion (sp' + 296#64) 152))
          (by rw [← hbytes1]; apply entails_of_eq; ac_rfl) ?_
        refine SepWPp.bind_frame_tryFrom
          (prologue_28_validVer_wpX hlt3 hgt4 hst1 hpc1 hrun1 hx0_1 hx1_1 hx19_1 hx29_1) ?_
        intro s2 P2 hpc2 hrun2
          ⟨hst2, hx29_2, hx27_2, hx22_2, hx21_2, hx19_2, hx1_2, hent2⟩
        refine SepWPp.mono_pre (sepConj_mono_left hent2) ?_
        clear hent2
        have hx1_2' : s2.readReg64 .x1 = 1#64 := by
          rw [hx1_2, hcons, hbody]; rfl
        refine SepWPp.mono_pre
          (P' := memRegion (sp' + 296#64) 152 ∗
            ((x.ptr ↦ₛ x.bytes) ∗ preKeyCalleeSavedAt sp' s0 ∗
              memRegion x.ret 248 ∗ memRegion sp' 296))
          (by rw [← hbytes1]; apply entails_of_eq; ac_rfl) ?_
        refine SepWPp.bind_frame_tryFrom
          (prologue_80_init_wpX hst2 hpc2 hrun2 hx29_2 hx27_2 hx22_2 hx21_2 hx19_2 hx1_2') ?_
        intro s3 P3 hpc3 hrun3
          ⟨hst3, hpstate3, hx29_3, hx27_3, _, _, _, hx19_3, _, _, hent3⟩
        refine SepWPp.mono_pre (sepConj_mono_left hent3) ?_
        clear hent3
        refine SepWPp.mono_pre
          (P' := (memRegion x.ret 248 ∗
              memRegion sp' 296 ∗
              ((sp' + 296#64) ↦₆₄ (x.ptr + 1#64)) ∗
              ((sp' + 304#64) ↦₆₄ 0#64) ∗
              (((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗
                ((sp' + 336#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 344#64) 16 ∗
                ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗
                ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗
                ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗
                ((sp' + 416#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 420#64) 4 ∗
                ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗
                ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4) ∗
              ((sp' + 440#64) ↦₆₄ (sp' + 296#64))) ∗
            ((x.ptr ↦ₛ x.bytes) ∗ preKeyCalleeSavedAt sp' s0))
          (by simp only [BitVec.sub_self]; apply entails_of_eq; ac_rfl) ?_
        refine SepWPp.frame_tryFrom
          (prologue_bc_len1_to_504_wpE (A := A) (ptr := x.ptr)
            hst3 hpc3 hrun3 hpstate3 hx29_3 hx27_3 hx19_3) ?_
        intro sf Pf ⟨hstf, hentf⟩
        refine ⟨hstf, hparse, .invalidProtobufEncoding,
          Entails.trans (sepConj_mono_left hentf) ?_⟩
        apply entails_of_eq; ac_rfl

/-- Unified valid-version + non-empty body theorem (`+0x000 → +0x460` / `1120`, `Wire.SepWPp`):
When `x.bytes = vb :: b1 :: bs1` with `¬ (vb >>> 4) < 3#8` and `¬ 4#8 < (vb >>> 4)`,
execution from `+0x000` reaches `+0x460` (`1120`) with `preKeyLoopExitPost` while preserving
`calleeSavedVRegs`. -/
theorem preKey_valid_to_460_wpW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hLoopF4 : PreKeyDecodeLoopF4OkW img A ext)
    {x : RunCompose.PksmGhost} {vb b1 : BitVec 8} {bs1 : List (BitVec 8)} {s0 : State}
    (hcons : x.bytes = vb :: b1 :: bs1)
    (hge3 : ¬ (vb >>> 4) < 3#8) (hle4 : ¬ 4#8 < (vb >>> 4))
    (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (contractProg img.base ext).fnAddr preKeyTryFromName)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hF : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab)
    (hx0 : s0.readReg64 .x0 = x.ptr)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1120#64) s0
      ((x.ptr ↦ₛ x.bytes) ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        memRegion (s0.sp - 608#64 + 512#64) 96 ∗
        A.pool ∗ stackAt (s0.sp - 608#64) (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        PreKeyLoopExitState img s0 (s0.sp - 608#64) x.ret
          (BitVec.ofNat 64 x.bytes.length) x.ptr vb sf ∧
        (Pf ⊢ (x.ptr ↦₈ vb) ∗
          preKeyLoopExitMem A (s0.sp - 608#64) (x.ptr + 1#64) (b1 :: bs1)
            (sf.readReg64 .x24) (Pksm.decodeProto (b1 :: bs1)) ∗
          preKeyCalleeSavedAt (s0.sp - 608#64) s0))
      (tryFromQp s0) := by
  set sp' := s0.sp - 608#64
  have hne : x.bytes ≠ [] := by rw [hcons]; simp
  refine SepWPp.mono_pre
    (P' := memRegion (sp' + 512#64) 96 ∗
      ((x.ptr ↦ₛ x.bytes) ∗
        memRegion (sp' + 296#64) 152 ∗ memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (prologue_entry_ne_nil_wpX hne hlt hpc hrun hsp hF hsym hx0 hx1 hx8) ?_
  intro s1 P1 hpc1 hrun1 ⟨hst1, hx0_1, hx1_1, hx19_1, hx29_1, hent1⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent1) ?_
  clear hent1
  have hbytes : (x.ptr ↦ₛ x.bytes) = (x.ptr ↦₈ vb) ∗ ((x.ptr + 1#64) ↦ₛ (b1 :: bs1)) := by
    rw [hcons, pointsToBytes_cons]
  refine SepWPp.mono_pre
    (P' := (x.ptr ↦₈ vb) ∗
      (((x.ptr + 1#64) ↦ₛ (b1 :: bs1)) ∗
        preKeyCalleeSavedAt sp' s0 ∗
        memRegion (sp' + 296#64) 152 ∗ memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
    (by rw [hbytes]; apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (prologue_28_validVer_wpX hge3 hle4 hst1 hpc1 hrun1 hx0_1 hx1_1 hx19_1 hx29_1) ?_
  intro s2 P2 hpc2 hrun2
    ⟨hst2, hx29_2, hx27_2, hx22_2, hx21_2, hx19_2, hx1_2, hent2⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent2) ?_
  clear hent2
  refine SepWPp.mono_pre
    (P' := (((x.ptr + 1#64) ↦ₛ (b1 :: bs1)) ∗
        memRegion (sp' + 296#64) 152 ∗
        memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
      ((x.ptr ↦₈ vb) ∗ preKeyCalleeSavedAt sp' s0))
    (by apply entails_of_eq; ac_rfl) ?_
  have hlt' : (vb :: b1 :: bs1).length < 2 ^ 32 := by rwa [← hcons]
  have hx1_2' : s2.readReg64 .x1 = BitVec.ofNat 64 (vb :: b1 :: bs1).length := by
    rwa [← hcons]
  refine SepWPp.frame_tryFrom
    (preKey_init_to_460_wpW hLoopF4 hlt' hst2 hpc2 hrun2
      hx29_2 hx27_2 hx22_2 hx21_2 hx19_2 hx1_2') ?_
  intro sf Pf ⟨hstf, hentf⟩
  rw [← hcons] at hstf
  refine ⟨hstf, Entails.trans (sepConj_mono_left hentf) ?_⟩
  apply entails_of_eq; ac_rfl

/-- Unified valid-version + non-empty body theorem (`+0x000 → +0x460` / `1120`, `ProofLib.SepWPp`
taking `W0Spec.PreKeyDecodeLoopF4Ok`). -/
theorem preKey_valid_to_460_wpX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hLoopF4 : PreKeyDecodeLoopF4Ok img A ext)
    {x : RunCompose.PksmGhost} {vb b1 : BitVec 8} {bs1 : List (BitVec 8)} {s0 : State}
    (hcons : x.bytes = vb :: b1 :: bs1)
    (hge3 : ¬ (vb >>> 4) < 3#8) (hle4 : ¬ 4#8 < (vb >>> 4))
    (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (contractProg img.base ext).fnAddr preKeyTryFromName)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hF : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab)
    (hx0 : s0.readReg64 .x0 = x.ptr)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    ProofLib.SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1120#64) s0
      ((x.ptr ↦ₛ x.bytes) ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        memRegion (s0.sp - 608#64 + 512#64) 96 ∗
        A.pool ∗ stackAt (s0.sp - 608#64) (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        PreKeyLoopExitState img s0 (s0.sp - 608#64) x.ret
          (BitVec.ofNat 64 x.bytes.length) x.ptr vb sf ∧
        (Pf ⊢ (x.ptr ↦₈ vb) ∗
          preKeyLoopExitMem A (s0.sp - 608#64) (x.ptr + 1#64) (b1 :: bs1)
            (sf.readReg64 .x24) (Pksm.decodeProto (b1 :: bs1)) ∗
          preKeyCalleeSavedAt (s0.sp - 608#64) s0))
      (tryFromQp s0) := by
  set sp' := s0.sp - 608#64
  have hne : x.bytes ≠ [] := by rw [hcons]; simp
  refine plb_mono_pre_p
    (P' := memRegion (sp' + 512#64) 96 ∗
      ((x.ptr ↦ₛ x.bytes) ∗
        memRegion (sp' + 296#64) 152 ∗ memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
    (by apply entails_of_eq; ac_rfl) ?_
  refine plb_bind_frame_tryFrom_p
    (plb_to_proofLib (prologue_entry_ne_nil_wpX hne hlt hpc hrun hsp hF hsym hx0 hx1 hx8)) ?_
  intro s1 P1 hpc1 hrun1 ⟨hst1, hx0_1, hx1_1, hx19_1, hx29_1, hent1⟩
  refine plb_mono_pre_p (sepConj_mono_left hent1) ?_
  clear hent1
  have hbytes : (x.ptr ↦ₛ x.bytes) = (x.ptr ↦₈ vb) ∗ ((x.ptr + 1#64) ↦ₛ (b1 :: bs1)) := by
    rw [hcons, pointsToBytes_cons]
  refine plb_mono_pre_p
    (P' := (x.ptr ↦₈ vb) ∗
      (((x.ptr + 1#64) ↦ₛ (b1 :: bs1)) ∗
        preKeyCalleeSavedAt sp' s0 ∗
        memRegion (sp' + 296#64) 152 ∗ memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
    (by rw [hbytes]; apply entails_of_eq; ac_rfl) ?_
  refine plb_bind_frame_tryFrom_p
    (plb_to_proofLib (prologue_28_validVer_wpX hge3 hle4 hst1 hpc1 hrun1 hx0_1 hx1_1 hx19_1 hx29_1)) ?_
  intro s2 P2 hpc2 hrun2
    ⟨hst2, hx29_2, hx27_2, hx22_2, hx21_2, hx19_2, hx1_2, hent2⟩
  refine plb_mono_pre_p (sepConj_mono_left hent2) ?_
  clear hent2
  refine plb_mono_pre_p
    (P' := (((x.ptr + 1#64) ↦ₛ (b1 :: bs1)) ∗
        memRegion (sp' + 296#64) 152 ∗
        memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
      ((x.ptr ↦₈ vb) ∗ preKeyCalleeSavedAt sp' s0))
    (by apply entails_of_eq; ac_rfl) ?_
  have hlt' : (vb :: b1 :: bs1).length < 2 ^ 32 := by rwa [← hcons]
  have hx1_2' : s2.readReg64 .x1 = BitVec.ofNat 64 (vb :: b1 :: bs1).length := by
    rwa [← hcons]
  refine plb_frame_tryFrom_p
    (preKey_init_to_460_wpX hLoopF4 hlt' hst2 hpc2 hrun2
      hx29_2 hx27_2 hx22_2 hx21_2 hx19_2 hx1_2') ?_
  intro sf Pf ⟨hstf, hentf⟩
  rw [← hcons] at hstf
  refine ⟨hstf, Entails.trans (sepConj_mono_left hentf) ?_⟩
  apply entails_of_eq; ac_rfl

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
