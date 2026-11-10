/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrB
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.ErrExit
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Common
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologue
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5
import all Init.Data.String.Defs

/-!
# Relocatable Substage P3.5 Error Paths over General `prevSessionsEmptyAt`
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.CliHandshake.RespClosurePlaced CryptoVerification.CliHandshake.Placed
open CryptoVerification.LibsignalTripleRatchet.Getters CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

private theorem lscro_of_steps_err [LibsignalPlacement] {prog : Program} {s sm : State}
    (hsteps : Steps prog s sm) (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) :
    StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem :=
  hcro.of_keepsFrozen hsteps.keepsFrozen

private theorem bind_sepWP_lscro_frame_err [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_step P_step_post F : SepProp} {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step (fun sm P_m => (P_m ⊢ P_step_post) ∧ Q_regs sm)) (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm → SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL; rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨_, hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim hoom | exact (not_satisfies_false_sepConj hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]; exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpcm hrunm (lscro_of_steps_err hsteps hcro) hregs R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem call_raw_nopanic_err [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]; exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout⟩ := subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hoom_post⟩
  rotate_right; · rw [hoom_false] at hoom_post; exact (not_satisfies_false_sepConj hoom_post).elim
  · rw [← sepConj_assoc] at hpost; rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm (lscro_of_steps_err hsteps hcro) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [hpan_false] at hpost; exact (allowPanic_not_exited hpost).elim
  · rw [hexit_false] at hpost; exact (allowPanic_not_exited hpost).elim

private theorem call_lscl_nopanic_err [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp :=
  call_raw_nopanic_err (spec := withLsCodeLoaded lsmpl spec) (x := x)
    (φ := φ ∧ LibsignalCodeLoaded lsmpl s.mem) (T := T) (F := F) hcro hcall hpc hrun hsp hlr
    (by dsimp only [withLsCodeLoaded]; rw [hspec, sepConj_assoc, sepConj_comm T, ← sepConj_assoc, pure_sepConj_pure])
    ⟨hφ, hcro.1⟩ hP hpan_false hexit_false hnext hoom_false

private theorem call_lscl_ro_nopanic_err [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl spec)))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  have hpre_eq : (withLsRoLoaded lsmpl spec).pre x s = (⌜φ ∧ LibsignalRoLoaded lsmpl s.mem⌝ ∗ T) := by
    dsimp only [withLsRoLoaded]; rw [hspec, sepConj_assoc, sepConj_comm T, ← sepConj_assoc, pure_sepConj_pure]
  exact call_lscl_nopanic_err (spec := withLsRoLoaded lsmpl spec) (x := x)
    (φ := φ ∧ LibsignalRoLoaded lsmpl s.mem) (T := T) (F := F)
    hcro hcall hpc hrun hsp hlr hpre_eq ⟨hφ, hcro.2⟩ hP hpan_false hexit_false hnext hoom_false

private theorem call_lscl_oom_err [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State} {φ : Prop}
    {P T F : SepProp} {Q : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_oom : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (P3P4.PanicOomProp s0))
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q (P3P4.PanicOomProp s0) := by
  intro R hm hL
  have hm' : s.mem ⊨ (withLsCodeLoaded lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded]; rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro.1, ?_⟩; rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]; exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout⟩ := subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpanm, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hoom_post⟩
  rotate_right; · dsimp only [withLsCodeLoaded] at hoom_post; rw [hoom_false] at hoom_post; exact (not_satisfies_false_sepConj hoom_post).elim
  · dsimp only [withLsCodeLoaded] at hpost; rw [← sepConj_assoc] at hpost; rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm (lscro_of_steps_err hsteps hcro) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeLoaded] at hpost; rw [hpan_oom, ← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpanm, _, hpost, allowPanic_oom_of_prefix (F := F) (htr ▸ List.prefix_refl _)⟩)⟩
  · dsimp only [withLsCodeLoaded] at hpost; rw [hexit_false] at hpost; exact (allowPanic_not_exited hpost).elim

private theorem pointsToBytesRO_decryptionFailed_err (a : BitVec 64) :
    (a ↦ᵣ decryptionFailedStr) =
      (a ↦₆₄ᵣ 0x6974707972636564#64) ∗ ((a + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗ ((a + 16#64) ↦₈ᵣ 0x64#8) := by
  have hsplit : decryptionFailedStr =
      [0x64#8, 0x65#8, 0x63#8, 0x72#8, 0x79#8, 0x70#8, 0x74#8, 0x69#8] ++
      ([0x6f#8, 0x6e#8, 0x20#8, 0x66#8, 0x61#8, 0x69#8, 0x6c#8, 0x65#8] ++ [0x64#8]) := by rfl_kernel
  rw [hsplit, pointsToBytesRO_append, pointsToBytesRO_append]
  change (a ↦ᵣ [0x64#8, 0x65#8, 0x63#8, 0x72#8, 0x79#8, 0x70#8, 0x74#8, 0x69#8]) ∗
    (((a + 8#64) ↦ᵣ [0x6f#8, 0x6e#8, 0x20#8, 0x66#8, 0x61#8, 0x69#8, 0x6c#8, 0x65#8]) ∗
     ((a + 8#64 + 8#64) ↦ᵣ [0x64#8])) = _
  rw [pointsToBytesRO8_eq_pointsTo64RO, pointsToBytesRO8_eq_pointsTo64RO, pointsToBytesRO_cons,
    pointsToBytesRO_nil, sepConj_emp, show a + 8#64 + 8#64 = a + 16#64 by bv_omega]
  simp only [BitVec.reduceAppend, sepConj_assoc]

private theorem intro_lsro_decryptionFailed_err [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hwp : SepWPp prog ret s
      (((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
       ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hro0 : s.mem ⊨ ((lsmpl.ρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦ᵣ decryptionFailedStr) ∗ (P ∗ R) :=
    lsro_intro_chk hcro.2 (by rfl_kernel) hm
  change s.mem ⊨ ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦ᵣ decryptionFailedStr) ∗ (P ∗ R) at hro0
  rw [pointsToBytesRO_decryptionFailed_err] at hro0
  have hro1 : s.mem ⊨ (((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
      ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗
      ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 16#64) ↦₈ᵣ 0x64#8) ∗ P) ∗ R := by
    simpa only [sepConj_assoc] using hro0
  exact SepWPp.drop_frame (P_drop := (lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 16#64) ↦₈ᵣ 0x64#8)
    (by ac_rfl) hwp R hro1 hL

open DropGlueFacts in
private theorem spe2JumpTable_placed_byte' (base : BitVec 64) (i : Nat) (b : BitVec 8)
    (heq : speJumpTable = speJumpTable.take i ++ (b :: speJumpTable.drop (i + 1)))
    (hlen : (speJumpTable.take i).length = i) :
    SatEntails (base ↦ᵣ speJumpTable) ((base + BitVec.ofNat 64 i) ↦₈ᵣ b) := by
  have h : (base ↦ᵣ speJumpTable) = (base ↦ᵣ speJumpTable.take i) ∗
      (((base + BitVec.ofNat 64 i) ↦₈ᵣ b) ∗ ((base + BitVec.ofNat 64 i + 1#64) ↦ᵣ speJumpTable.drop (i + 1))) := by
    conv_lhs => rw [heq]
    rw [pointsToBytesRO_append, pointsToBytesRO_cons, hlen]
  rw [h]; exact SatEntails.trans (SatEntails.drop_left _ _) (SatEntails.drop_right _ _)

private theorem spe2_false_elim' {prog : Program} {target_pc : BitVec 64} {s : State}
    {P Q : SepProp} {post : State → SepProp → Prop} :
    SepWP prog target_pc s (P ∗ ⌜False⌝ ∗ Q) post := by
  unfold SepWP; intro R hm
  have heq : (P ∗ ⌜False⌝ ∗ Q) ∗ R = ⌜False⌝ ∗ (P ∗ Q ∗ R) := by ac_rfl
  rw [heq, satisfies_pure_sepConj] at hm; exact False.elim hm.1

private theorem sepWP_bind_lscl [LibsignalPlacement] {prog : Program} {mid target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun s1 P1 => LibsignalCodeLoaded lsmpl s1.mem → SepWP prog target_pc s1 P1 post)) :
    SepWP prog target_pc s P post := by
  unfold SepWP; intro R hm hL; rcases h.elim hm hL with ⟨s1, hsteps, ⟨-, -, P1, hm1, hnext⟩ | ⟨hoom, hf⟩⟩
  · have hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem := ⟨hcl, hro⟩
    rcases (hnext (hcro.of_keepsFrozen hsteps.keepsFrozen).1).elim hm1 (hsteps.codeLoaded hL) with
      ⟨sf, hsteps2, ⟨hpcf, hrunf, Pf, hmf, hpost⟩ | ⟨hoom, hf⟩⟩
    · exact ⟨sf, hsteps.trans hsteps2, Or.inl ⟨hpcf, hrunf, Pf, hmf, hpost⟩⟩
    · exact ⟨sf, hsteps.trans hsteps2, Or.inr ⟨hoom, hf⟩⟩
  · exact ⟨s1, hsteps, Or.inr ⟨hoom, hf⟩⟩

set_option maxHeartbeats 1600000 in
open DropGlueFacts in
private theorem drop_spe2_placed_ok_at_of_dealloc [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok (lsProg_518 ext) (lsmpl.base 511)
      (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl (dropSpeSpec A))) := by
  have hd511_cl : subroutine_ok ((blkPC_511).rebase (blkPl_511).base ext)
      (lsρ lsRustDeallocSym) (withLsCodeLoaded lsmpl (rustDeallocSpec A)) :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_511).rebase (blkPl_511).base ext)
      (subroutine_ok_withLsCodeLoaded_of_plain hdealloc) (by decide)
  have h511 : subroutine_ok ((blkPC_511).rebase (blkPl_511).base ext) (blkPl_511).base
      (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl (dropSpeSpec A))) := by
    simp only [withLsCodeLoaded, withLsRoLoaded, dropSpeSpec]
    simp only [withLsCodeLoaded, rustDeallocSpec] at hd511_cl
    wp_init x s0; obtain ⟨a, fnName, e⟩ := x; dsimp only at *
    have hx0 : s0.readReg64 (Reg.gpr 0#5) = a := by assumption
    subst hx0
    have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
    have hro : LibsignalRoLoaded lsmpl s0.mem := by assumption
    have h_intro_jt : ∀ {P : SepProp} {post : State → SepProp → Prop},
        SepWP ((blkPC_511).rebase (blkPl_511).base ext) (s0.readReg64 (Reg.gpr 30#5)) s0
          (((lsρ spe2JumpTableSym) ↦ᵣ speJumpTable) ∗ P) post →
        SepWP ((blkPC_511).rebase (blkPl_511).base ext) (s0.readReg64 (Reg.gpr 30#5)) s0 P post := by
      intro P post h; unfold SepWP at h ⊢; intro R hm; have hR := h R; rw [sepConj_assoc] at hR
      exact hR (lsro_intro_chk hro (by rfl_kernel) hm)
    refine h_intro_jt ?_
    nth_rw 1 [stackAt_dropSpe_split s0.sp]; cells_unfold; wp_pull_exists
    cases e with
    | panic => simp only [speAt]; exact spe2_false_elim'
    | invalidState =>
      refine Getters.SepWP.weaken_pre_sat (spe_str_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidState
        1 0x8000000000000001#64 rfl (spe2JumpTable_placed_byte' (lsρ spe2JumpTableSym) 1 0x00#8 rfl rfl)
        (speAt_invalidState_expose A fnName (s0.readReg64 (Reg.gpr 0#5))) _) ?_
      wp_pull_exists; rename_i cap ptr
      by_cases hcap : cap = 0#64
      · simp only [hcap, beq_self_eq_true, ↓reduceIte, emp_sepConj]; wp_steps
        refine Getters.SepWP.weaken_pre_sat (spe_str_cap0_pre_weaken_full _ _ _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
      · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
        simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
        refine sepWP_bind_lscl hcl hro (mid := lsρ lsRustDeallocSym) ?_; wp_steps
        refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hcl1 => ?_
        refine Getters.SepWP.weaken_pre_sat (spe_tail_dealloc_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) _ cap ptr s0.sp _ _ _ _ _ _ _) ?_
        wp_apply
        refine SepWP.weaken_pre (spe_tail_dealloc_post (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_; wp_done
    | invalidMessage t r =>
      refine Getters.SepWP.weaken_pre_sat (spe_str_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.invalidMessage t r)
        24 0x8000000000000018#64 rfl (spe2JumpTable_placed_byte' (lsρ spe2JumpTableSym) 24 0x00#8 rfl rfl)
        (speAt_invalidMessage_expose A fnName (s0.readReg64 (Reg.gpr 0#5)) t r) _) ?_
      wp_pull_exists; rename_i cap ptr
      by_cases hcap : cap = 0#64
      · simp only [hcap, beq_self_eq_true, ↓reduceIte, emp_sepConj]; wp_steps
        refine Getters.SepWP.weaken_pre_sat (spe_str_cap0_pre_weaken_full _ _ _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
      · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
        simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
        refine sepWP_bind_lscl hcl hro (mid := lsρ lsRustDeallocSym) ?_; wp_steps
        refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hcl1 => ?_
        refine Getters.SepWP.weaken_pre_sat (spe_tail_dealloc_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) _ cap ptr s0.sp _ _ _ _ _ _ _) ?_
        wp_apply
        refine SepWP.weaken_pre (spe_tail_dealloc_post (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_; wp_done
    | invalidProtobufEncoding =>
      refine Getters.SepWP.weaken_pre_sat (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidProtobufEncoding
        2 0x8000000000000002#64 rfl (spe2JumpTable_placed_byte' (lsρ spe2JumpTableSym) 2 0x1b#8 rfl rfl) (SatEntails.refl _) _) ?_
      wp_steps; refine Getters.SepWP.weaken_pre_sat (spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    | ciphertextMessageTooShort n =>
      refine Getters.SepWP.weaken_pre_sat (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.ciphertextMessageTooShort n)
        3 0x8000000000000003#64 rfl (spe2JumpTable_placed_byte' (lsρ spe2JumpTableSym) 3 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40 _ _))) _) ?_
      wp_steps; refine Getters.SepWP.weaken_pre_sat (spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    | legacyCiphertextVersion v =>
      refine Getters.SepWP.weaken_pre_sat (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.legacyCiphertextVersion v)
        4 0x8000000000000004#64 rfl (spe2JumpTable_placed_byte' (lsρ spe2JumpTableSym) 4 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
      wp_steps; refine Getters.SepWP.weaken_pre_sat (spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    | unrecognizedCiphertextVersion v =>
      refine Getters.SepWP.weaken_pre_sat (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.unrecognizedCiphertextVersion v)
        5 0x8000000000000005#64 rfl (spe2JumpTable_placed_byte' (lsρ spe2JumpTableSym) 5 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
      wp_steps; refine Getters.SepWP.weaken_pre_sat (spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    | noKeyTypeIdentifier =>
      refine Getters.SepWP.weaken_pre_sat (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .noKeyTypeIdentifier
        7 0x8000000000000007#64 rfl (spe2JumpTable_placed_byte' (lsρ spe2JumpTableSym) 7 0x1b#8 rfl rfl) (SatEntails.refl _) _) ?_
      wp_steps; refine Getters.SepWP.weaken_pre_sat (spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    | badKeyType t =>
      refine Getters.SepWP.weaken_pre_sat (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.badKeyType t)
        8 0x8000000000000008#64 rfl (spe2JumpTable_placed_byte' (lsρ spe2JumpTableSym) 8 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
      wp_steps; refine Getters.SepWP.weaken_pre_sat (spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    | badKeyLength n =>
      refine Getters.SepWP.weaken_pre_sat (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.badKeyLength n)
        9 0x8000000000000009#64 rfl (spe2JumpTable_placed_byte' (lsρ spe2JumpTableSym) 9 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40 _ _))) _) ?_
      wp_steps; refine Getters.SepWP.weaken_pre_sat (spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    | invalidKeyAgreement =>
      refine Getters.SepWP.weaken_pre_sat (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidKeyAgreement
        10 0x800000000000000a#64 rfl (spe2JumpTable_placed_byte' (lsρ spe2JumpTableSym) 10 0x1b#8 rfl rfl) (SatEntails.refl _) _) ?_
      wp_steps; refine Getters.SepWP.weaken_pre_sat (spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    | invalidSessionStructure r =>
      refine Getters.SepWP.weaken_pre_sat (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.invalidSessionStructure r)
        20 0x8000000000000014#64 rfl (spe2JumpTable_placed_byte' (lsρ spe2JumpTableSym) 20 0x1b#8 rfl rfl)
        (by simp only [speAt]; exact SatEntails.sepConj_mono_right (spe_strRef_at_8_entails_40 _ _)) _) ?_
      wp_steps; refine Getters.SepWP.weaken_pre_sat (spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    | duplicatedMessage idx c =>
      refine Getters.SepWP.weaken_pre_sat (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.duplicatedMessage idx c)
        23 0x8000000000000017#64 rfl (spe2JumpTable_placed_byte' (lsρ spe2JumpTableSym) 23 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u32x2_at_8_entails_40 _ _ _))) _) ?_
      wp_steps; refine Getters.SepWP.weaken_pre_sat (spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  exact ls_subroutine_ok_of_block (callerProg := lsProg_518 ext) h511 (by decide)

theorem p3_err_dup_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr : BitVec 64)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 512) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧ s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = 0x8000000000000017#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ s1.readReg64 .x30 = dpClosureEntryM3Placed + 0x34dc#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  dsimp only [dpClosureEntryM3Placed] at hpc ⊢; wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem p3_err_nondup_a_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr errTag e1 e2 e3 e4 e5 u930 u938 u940 u948 u950 u958 : BitVec 64)
    (herr_ne_ok : errTag ≠ 0xfffffffffffffffe#64) (herr_ne_dup : errTag ≠ 0x8000000000000017#64)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 519) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x270#64) ↦₆₄ errTag) ∗ ((s.sp + 0x278#64) ↦₆₄ e1) ∗
       ((s.sp + 0x280#64) ↦₆₄ e2) ∗ ((s.sp + 0x288#64) ↦₆₄ e3) ∗ ((s.sp + 0x290#64) ↦₆₄ e4) ∗
       ((s.sp + 0x298#64) ↦₆₄ e5) ∗ ((s.sp + 0x930#64) ↦₆₄ u930) ∗ ((s.sp + 0x938#64) ↦₆₄ u938) ∗
       ((s.sp + 0x940#64) ↦₆₄ u940) ∗ ((s.sp + 0x948#64) ↦₆₄ u948) ∗ ((s.sp + 0x950#64) ↦₆₄ u950) ∗
       ((s.sp + 0x958#64) ↦₆₄ u958))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x270#64) ↦₆₄ errTag) ∗ ((s.sp + 0x278#64) ↦₆₄ e1) ∗
          ((s.sp + 0x280#64) ↦₆₄ e2) ∗ ((s.sp + 0x288#64) ↦₆₄ e3) ∗ ((s.sp + 0x290#64) ↦₆₄ e4) ∗
          ((s.sp + 0x298#64) ↦₆₄ e5) ∗ ((s.sp + 0x930#64) ↦₆₄ errTag) ∗ ((s.sp + 0x938#64) ↦₆₄ e1) ∗
          ((s.sp + 0x940#64) ↦₆₄ e2) ∗ ((s.sp + 0x948#64) ↦₆₄ e3) ∗ ((s.sp + 0x950#64) ↦₆₄ e4) ∗
          ((s.sp + 0x958#64) ↦₆₄ e5)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = s.sp + 0x3b0#64 ∧
        s1.readReg64 .x2 = 7#64 ∧ s1.readReg64 .x3 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x4 = s.sp + 0x930#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = outPtr ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0x8000000000000017#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = dpClosureEntryM3Placed + 0x2d9c#64 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond_ok := cond_ne_adds64_of_ne_neg2 herr_ne_ok
  have hcond_dup := cond_eq_subs64_of_ne_dup herr_ne_dup
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  dsimp only [dpClosureEntryM3Placed] at hpc ⊢; wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

theorem p3_err_nondup_b_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x2d9c#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (lsmpl.base 42) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = s.sp + 0x3c8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = 0#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = dpClosureEntryM3Placed + 0x2db4#64 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  dsimp only [dpClosureEntryM3Placed] at hpc ⊢; wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem p3_err_nondup_c_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (s : State) (coroPtr errsPtr errTag e1 e2 e3 e4 e5 u_e0 u_e1 u_e2 u_e3 u_e4 u_e5 : BitVec 64)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x2db4#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = 0#64) (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) :
    SepWP (lsProg_518 ext) (dpClosureEntryM3Placed + 0x2eac#64) s
      (((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ ((s.sp + 0x270#64) ↦₆₄ errTag) ∗ ((s.sp + 0x278#64) ↦₆₄ e1) ∗
       ((s.sp + 0x280#64) ↦₆₄ e2) ∗ ((s.sp + 0x288#64) ↦₆₄ e3) ∗ ((s.sp + 0x290#64) ↦₆₄ e4) ∗
       ((s.sp + 0x298#64) ↦₆₄ e5) ∗ ((errsPtr + 0x0#64) ↦₆₄ u_e0) ∗ ((errsPtr + 0x8#64) ↦₆₄ u_e1) ∗
       ((errsPtr + 0x10#64) ↦₆₄ u_e2) ∗ ((errsPtr + 0x18#64) ↦₆₄ u_e3) ∗ ((errsPtr + 0x20#64) ↦₆₄ u_e4) ∗
       ((errsPtr + 0x28#64) ↦₆₄ u_e5))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ ((s.sp + 0x270#64) ↦₆₄ errTag) ∗ ((s.sp + 0x278#64) ↦₆₄ e1) ∗
          ((s.sp + 0x280#64) ↦₆₄ e2) ∗ ((s.sp + 0x288#64) ↦₆₄ e3) ∗ ((s.sp + 0x290#64) ↦₆₄ e4) ∗
          ((s.sp + 0x298#64) ↦₆₄ e5) ∗ ((errsPtr + 0x0#64) ↦₆₄ errTag) ∗ ((errsPtr + 0x8#64) ↦₆₄ e1) ∗
          ((errsPtr + 0x10#64) ↦₆₄ e2) ∗ ((errsPtr + 0x18#64) ↦₆₄ e3) ∗ ((errsPtr + 0x20#64) ↦₆₄ e4) ∗
          ((errsPtr + 0x28#64) ↦₆₄ e5)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = 17#64 ∧
        s1.readReg64 .x1 = 1#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = 0#64 := hx21
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have herr0 : 0#64 * 0x30#64 + errsPtr = errsPtr := by bv_arith
  dsimp only [dpClosureEntryM3Placed, lsLogFilterAddr] at hpc ⊢
  wp_steps; wp_call hshim (); wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.of_eq (by ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 800000 in
private theorem p3_alloc_2eac_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s : State) (F : SepProp) (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x2eac#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = 17#64) (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (lsProg_518 ext) (dpClosureEntryM3Placed + 0x2eb0#64) s ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) 17 1 ∗ memRegion (s2.readReg64 .x0) 17 ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem)
      (P3P4.PanicOomProp s0) := by
  have hbl : SepWP (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") s emp
      (fun s1 P_f => (P_f ⊢ emp) ∧ s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = 17#64 ∧ s1.readReg64 .x1 = 1#64 ∧
        CalleeSavedPreserved s s1 ∧ s1.readReg64 .x30 = dpClosureEntryM3Placed + 0x2eb0#64) := by
    dsimp only [dpClosureEntryM3Placed] at hpc ⊢; wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm],
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, by simp_all [arm64_norm]⟩
  refine bind_sepWP_lscro_frame_err hcro hbl (emp_sepConj _).symm
    fun s1 hpc1 hrun1 hcro1 ⟨hsp1, htr1, hx0_1, hx1_1, hcs1, hlr1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hsp_align
  have hφ : (s1.readReg64 .x0).toNat = 17 ∧ (s1.readReg64 .x1).toNat = 1 ∧ LayoutOk 17 1 :=
    ⟨by rw [hx0_1]; rfl, by rw [hx1_1]; rfl, by decide, ⟨0, rfl⟩, by decide⟩
  refine call_raw_nopanic_err (spec := rustAllocSpec A) (x := (17, 1))
    (T := A.pool ∗ stackAt s.sp allocHookStack) (F := F)
    hcro1 halloc hpc1 hrun1 hsp1_al hlr1 (by dsimp only [rustAllocSpec]; rw [hsp1]) hφ (emp_sepConj _)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hcs : CalleeSavedPreserved s s2 := hcs1.trans hcs2
  dsimp only [rustAllocSpec]; rw [hsp1]
  by_cases hoom : s2.readReg64 .x0 = 0#64
  · have hoom0 : (s2.readReg64 .x0 = 0) = True := eq_true hoom
    simp only [hoom0, ↓reduceIte, P3P4.pull_pure_alloc_oom]; refine SepWPp.pure_elim fun htr2 => ?_
    have hoom_steps : SepWP (lsProg_518 ext) (lsρ lsHandleErrorSym) s2 emp
        (fun s3 P_f => (P_f ⊢ emp) ∧ s3.trace = s2.trace) := by
      have hx0_g : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      dsimp only [lsHandleErrorSym, dpClosureEntryM3Placed] at hpc2 ⊢; wp_steps
      exact SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl⟩
    refine bind_sepWP_lscro_frame_err hcro2 hoom_steps (emp_sepConj _).symm fun s3 hpc3 hrun3 _ htr3 => ?_
    have hext : (lsProg_518 ext).externAt? s3.pc = some Rust.panicked := by
      rw [hpc3]; exact (ls_externAt?_of_mem (prog := lsProg_518 ext) (i := 518) (by decide)).trans hpanic
    exact SepWPp.panic hrun3 hext fun R hm =>
      allowPanic_panicked (LibsignalTripleRatchet.allocFailedIn_of_eq
        (by simp only [Rust.panicked, htr3, htr2, htr1, htr])) hm
  · have hoom0 : (s2.readReg64 .x0 = 0) = False := eq_false hoom
    simp only [hoom0, ↓reduceIte, P3P4.pull_pure_alloc_ok]
    exact SepWPp.pure_elim fun ⟨_, htr2⟩ =>
      SepWPp.done hpc2 hrun2 ⟨Entails.of_eq (by ac_rfl), hoom, hsp2, htr2.trans htr1, hcs, hcro2⟩

theorem p3_err_nondup_d_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr dfPtr ro0 ro1 u_df0 u_df8 u_270 u_278 u_280 u_288 : BitVec 64)
    (u_df10 u_290 : BitVec 8) (hdf_nz : dfPtr ≠ 0#64)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x2eb0#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx0 : s.readReg64 .x0 = dfPtr)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (lsmpl.base 512) s
      (((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ ro0) ∗
       ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ ro1) ∗
       ((dfPtr + 0x0#64) ↦₆₄ u_df0) ∗ ((dfPtr + 0x8#64) ↦₆₄ u_df8) ∗ ((dfPtr + 0x10#64) ↦₈ u_df10) ∗
       ((s.sp + 0x270#64) ↦₆₄ u_270) ∗ ((s.sp + 0x278#64) ↦₆₄ u_278) ∗ ((s.sp + 0x280#64) ↦₆₄ u_280) ∗
       ((s.sp + 0x288#64) ↦₆₄ u_288) ∗ ((s.sp + 0x290#64) ↦₈ u_290))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ ro0) ∗
          ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ ro1) ∗
          ((dfPtr + 0x0#64) ↦₆₄ ro0) ∗ ((dfPtr + 0x8#64) ↦₆₄ ro1) ∗ ((dfPtr + 0x10#64) ↦₈ 0x64#8) ∗
          ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000018#64) ∗ ((s.sp + 0x278#64) ↦₆₄ 17#64) ∗
          ((s.sp + 0x280#64) ↦₆₄ dfPtr) ∗ ((s.sp + 0x288#64) ↦₆₄ 17#64) ∗ ((s.sp + 0x290#64) ↦₈ 3#8)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = 0x8000000000000018#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ s1.readReg64 .x30 = dpClosureEntryM3Placed + 0x34dc#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdf_beq : (dfPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hdf_nz
  have hx0' : s.readReg64 (Reg.gpr 0#5) = dfPtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  dsimp only [dpClosureEntryM3Placed, lsρ] at hpc ⊢; wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem p3_err_tail_dup_a_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr errsPtr ssCap v_27c v_284 v_290 v_298 u_250 u_258 u_370 u_378 u_384 u_38c : BitVec 64)
    (v_278 v_28c u_260 u_380 : BitVec 32) (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x34dc#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = 0x8000000000000017#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 512) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗ ((s.sp + 0x250#64) ↦₆₄ u_250) ∗ ((s.sp + 0x258#64) ↦₆₄ u_258) ∗
       ((s.sp + 0x260#64) ↦₃₂ u_260) ∗ ((s.sp + 0x278#64) ↦₃₂ v_278) ∗ ((s.sp + 0x27c#64) ↦₆₄ v_27c) ∗
       ((s.sp + 0x284#64) ↦₆₄ v_284) ∗ ((s.sp + 0x28c#64) ↦₃₂ v_28c) ∗ ((s.sp + 0x290#64) ↦₆₄ v_290) ∗
       ((s.sp + 0x298#64) ↦₆₄ v_298) ∗ ((s.sp + 0x370#64) ↦₆₄ u_370) ∗ ((s.sp + 0x378#64) ↦₆₄ u_378) ∗
       ((s.sp + 0x380#64) ↦₃₂ u_380) ∗ ((s.sp + 0x384#64) ↦₆₄ u_384) ∗ ((s.sp + 0x38c#64) ↦₆₄ u_38c))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗ ((s.sp + 0x250#64) ↦₆₄ v_27c) ∗ ((s.sp + 0x258#64) ↦₆₄ v_284) ∗
          ((s.sp + 0x260#64) ↦₃₂ v_28c) ∗ ((s.sp + 0x278#64) ↦₃₂ v_278) ∗ ((s.sp + 0x27c#64) ↦₆₄ v_27c) ∗
          ((s.sp + 0x284#64) ↦₆₄ v_284) ∗ ((s.sp + 0x28c#64) ↦₃₂ v_28c) ∗ ((s.sp + 0x290#64) ↦₆₄ v_290) ∗
          ((s.sp + 0x298#64) ↦₆₄ v_298) ∗ ((s.sp + 0x370#64) ↦₆₄ v_27c) ∗ ((s.sp + 0x378#64) ↦₆₄ v_284) ∗
          ((s.sp + 0x380#64) ↦₃₂ v_28c) ∗ ((s.sp + 0x384#64) ↦₆₄ v_290) ∗ ((s.sp + 0x38c#64) ↦₆₄ v_298)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = v_278.zeroExtend 64 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0x8000000000000017#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = dpClosureEntryM3Placed + 0x359c#64 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond_cap := cond_eq_adds64_of_ne_neg1 hcap_ne
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0x8000000000000017#64 := hx28
  dsimp only [dpClosureEntryM3Placed] at hpc ⊢; wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem p3_err_tail_nondup_a1_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr errsPtr : BitVec 64)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x34dc#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (lsmpl.base 511) s
      (((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 1#64))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 1#64)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = errsPtr ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = errsPtr ∧
        s1.readReg64 .x22 = errsPtr ∧ s1.readReg64 .x23 = 1#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = dpClosureEntryM3Placed + 0x34f4#64 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  dsimp only [dpClosureEntryM3Placed] at hpc ⊢; wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

theorem p3_err_tail_nondup_a2_placed_wp [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s : State) (coroPtr errsPtr ssCap v_27c v_284 v_290 v_298 u_250 u_258 u_370 u_378 u_384 u_38c : BitVec 64)
    (v_278 v_28c u_260 u_380 : BitVec 32) (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x34f4#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = errsPtr) (hx22 : s.readReg64 .x22 = errsPtr)
    (hx23 : s.readReg64 .x23 = 1#64) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx28 : s.readReg64 .x28 = 0x8000000000000018#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 512) s
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ A.live errsPtr 192 8 ∗ memRegion errsPtr 192 ∗
       A.pool ∗ stackAt s.sp allocHookStack ∗ ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗
       ((s.sp + 0x250#64) ↦₆₄ u_250) ∗ ((s.sp + 0x258#64) ↦₆₄ u_258) ∗ ((s.sp + 0x260#64) ↦₃₂ u_260) ∗
       ((s.sp + 0x278#64) ↦₃₂ v_278) ∗ ((s.sp + 0x27c#64) ↦₆₄ v_27c) ∗ ((s.sp + 0x284#64) ↦₆₄ v_284) ∗
       ((s.sp + 0x28c#64) ↦₃₂ v_28c) ∗ ((s.sp + 0x290#64) ↦₆₄ v_290) ∗ ((s.sp + 0x298#64) ↦₆₄ v_298) ∗
       ((s.sp + 0x370#64) ↦₆₄ u_370) ∗ ((s.sp + 0x378#64) ↦₆₄ u_378) ∗ ((s.sp + 0x380#64) ↦₃₂ u_380) ∗
       ((s.sp + 0x384#64) ↦₆₄ u_384) ∗ ((s.sp + 0x38c#64) ↦₆₄ u_38c))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ A.pool ∗ stackAt s.sp allocHookStack ∗
          ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗ ((s.sp + 0x250#64) ↦₆₄ v_27c) ∗ ((s.sp + 0x258#64) ↦₆₄ v_284) ∗
          ((s.sp + 0x260#64) ↦₃₂ v_28c) ∗ ((s.sp + 0x278#64) ↦₃₂ v_278) ∗ ((s.sp + 0x27c#64) ↦₆₄ v_27c) ∗
          ((s.sp + 0x284#64) ↦₆₄ v_284) ∗ ((s.sp + 0x28c#64) ↦₃₂ v_28c) ∗ ((s.sp + 0x290#64) ↦₆₄ v_290) ∗
          ((s.sp + 0x298#64) ↦₆₄ v_298) ∗ ((s.sp + 0x370#64) ↦₆₄ v_27c) ∗ ((s.sp + 0x378#64) ↦₆₄ v_284) ∗
          ((s.sp + 0x380#64) ↦₃₂ v_28c) ∗ ((s.sp + 0x384#64) ↦₆₄ v_290) ∗ ((s.sp + 0x38c#64) ↦₆₄ v_298)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = v_278.zeroExtend 64 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0x8000000000000018#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = dpClosureEntryM3Placed + 0x359c#64 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond_cap := cond_eq_adds64_of_ne_neg1 hcap_ne
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = errsPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = errsPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0x8000000000000018#64 := hx28
  dsimp only [dpClosureEntryM3Placed] at hpc ⊢; wp_steps; wp_call hdealloc (errsPtr, 192, 8); wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.of_eq (by ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1200000 in
theorem stageP3_err_tail_dup_prevEmpty_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 s : State) (coroPtr outPtr errsPtr w0 w1 w2 w3 w4 : BitVec 64) (b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x34dc#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x8000000000000017#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ prevSessionsEmptyAt A coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗
       ((s.sp + 0x280#64) ↦₆₄ w1) ∗ ((s.sp + 0x288#64) ↦₆₄ w2) ∗ ((s.sp + 0x290#64) ↦₆₄ w3) ∗
       ((s.sp + 0x298#64) ↦₆₄ w4) ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          words6At outPtr 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ memRegion (s.sp + 0x250#64) 20 ∗
          memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp dropSessionStructure2Stack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  refine P3P4.SepWPp.weaken_frame (sessionStateAt_unpack_head_tail A (coroPtr + 0xf8#64) recG recSt) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => ?_
  have hrepack278 := words3_repack_w32_2w64_w32 (s.sp + 0x278#64) w0 w1 w2
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack278
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion20_split_eq (s.sp + 0x250#64))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 => SepWPp.exists_elim fun u_250 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (sp370_36_err_split_eq s.sp)) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_38c => SepWPp.exists_elim fun u_384 =>
    SepWPp.exists_elim fun u_380 => SepWPp.exists_elim fun u_378 => SepWPp.exists_elim fun u_370 => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_
  have hstep1 := p3_err_tail_dup_a_placed_wp ext s coroPtr errsPtr recG.localIk.cap
    (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32) (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    w3 w4 u_250 u_258 u_370 u_378 u_384 u_38c (w0.extractLsb' 0 32) (w2.extractLsb' 32 32) u_260 u_380
    (cap_ne_noneCap_of_lt hcap_lt) hpc hrun hsp_align hx19 hx24 hx25 hx28
  refine bind_sepWP_lscro_frame_err hcro hstep1 (by sep_focus) fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx19_1, hx22_1, _, hx25_1, hx26_1, _, hx28_1, _, hx30_1, hvregs_1⟩
  have hpack_ss : ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A recG recSt ⊢ sessionStateAt A (coroPtr + 0xf8#64) recG recSt := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using sessionStateAt_pack_head_tail A (coroPtr + 0xf8#64) recG recSt hinl
  refine P3P4.SepWPp.weaken_frame hpack_ss (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (words6_entails_memRegion48 (s.sp + 0x270#64) 0x8000000000000017#64 w0 w1 w2 w3 w4) (by sep_focus) ?_
  have hfold250 : ((s.sp + 0x250#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ w2.extractLsb' 32 32) ⊢ memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      memRegion20_fold (s.sp + 0x250#64) (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32) (w2.extractLsb' 32 32)
  refine P3P4.SepWPp.weaken_frame hfold250 (by sep_focus) ?_
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1_s]; exact hsp_align
  have hx25_1' : s1.readReg64 .x25 = s1.sp + 0x210#64 := by rw [hx25_1, hsp1_s]
  have hcommon := stageP3_err_tail_common_prevEmpty_placed_ok ext hdealloc hDropSS3
    s0 s1 coroPtr outPtr 0x8000000000000017#64 w0 w1 w2 w3 w4 b_2c0 g recG recSt
    hcro1 hpc1 hrun1 hsp1_align (htr1_s.trans htr) hx0_1 hx19_1 hx22_1 hx25_1' (hx26_1.trans hx26) hx28_1 hx30_1
  rw [hsp1_s] at hcommon
  refine P3P4.SepWPp.ret_sepWPp_frame hcommon (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
  exact ⟨Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)), hspf, htrf, hcc, hcrof, hvregs_f.trans hvregs_1⟩

set_option maxHeartbeats 1200000 in
theorem stageP3_sub5_err_dup_prevEmpty_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 s : State) (coroPtr outPtr errsPtr : BitVec 64) (ratVer counter : BitVec 32) (b_2c0 : BitVec 8)
    (g : RecordGhost) (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       vecResultAt A (s.sp + 0x270#64) (.error (.duplicatedMessage ratVer counter)) ∗
       sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ prevSessionsEmptyAt A coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
       stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
          memRegion (s.sp + 0xa90#64) 344 ∗ memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ recordResultAt A outPtr (.error (.duplicatedMessage ratVer counter)) ∗
          memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
          memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗ stackAt s.sp dropSessionStructure2Stack) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  have hdecomp : vecResultAt A (s.sp + 0x270#64) (.error (.duplicatedMessage ratVer counter)) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ c : BitVec 64, words6At c 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
          speAt A (utf8 "decrypt") c (.duplicatedMessage ratVer counter)⌝ ∗
        ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗
        ((s.sp + 0x280#64) ↦₆₄ w1) ∗ ((s.sp + 0x288#64) ↦₆₄ w2) ∗
        ((s.sp + 0x290#64) ↦₆₄ w3) ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗ H := by
    have h1 := speAt_decomp6 A (utf8 "decrypt") (s.sp + 0x270#64) (.duplicatedMessage ratVer counter) (by nofun)
    dsimp only [vecResultAt, speTag, speWord] at h1 ⊢
    refine Entails.trans h1 ?_
    apply Entails.sepExists_elim; intro w0; apply Entails.sepExists_elim; intro w1
    apply Entails.sepExists_elim; intro w2; apply Entails.sepExists_elim; intro w3
    apply Entails.sepExists_elim; intro w4; apply Entails.sepExists_elim; intro H
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right H ?_)))))
    unfold words6At; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hdecomp (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 =>
    SepWPp.exists_elim fun w2 => SepWPp.exists_elim fun w3 =>
    SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun H => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜∀ c : BitVec 64, words6At c 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
      speAt A (utf8 "decrypt") c (.duplicatedMessage ratVer counter)⌝)
    (P₂ := ⌜∀ c : BitVec 64, words6At c 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
      speAt A (utf8 "decrypt") c (.duplicatedMessage ratVer counter)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun hreassemble => ?_
  have hstep1 := p3_err_dup_placed_wp ext s coroPtr outPtr hpc hrun hsp_align hx19 hx24
  refine bind_sepWP_lscro_frame_err hcro hstep1 (by sep_focus) fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx19_1, hx24_1, hx25_1, hx26_1, _, hx28_1, _, hx30_1, hvregs_1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  refine call_lscl_nopanic_err
    (x := (⟨s.sp + 0xa90#64, G₂, st₂⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ A.pool ∗ stackAt s.sp dropSessionStructure2Stack)
    hcro1 hDropSS3 hpc1 hrun1 hsp1_al hx30_1 (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp1_s])
    hx0_1 (by sep_focus) (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]; rw [hsp1_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2_s]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, _, hx28_cs2, _, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx24_2 : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_cs2, hx24_1, hsp2_s]
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hsp2_s]
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans hx26_1
  have hx28_2 : s2.readReg64 .x28 = 0x8000000000000017#64 := hx28_cs2.trans hx28_1
  have htail := stageP3_err_tail_dup_prevEmpty_placed_ok ext hdealloc hDropSS3
    s0 s2 coroPtr outPtr errsPtr w0 w1 w2 w3 w4 b_2c0 g recG recSt
    hcro2 hpc2 hrun2 hsp2_align (htr2_1.trans (htr1_s.trans htr)) hx19_2 hx24_2 hx25_2 hx26_2 hx28_2
  rw [hsp2_s] at htail
  refine P3P4.SepWPp.ret_sepWPp_frame htail (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
  have hrec : words6At outPtr 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
      recordResultAt A outPtr (.error (.duplicatedMessage ratVer counter)) := hreassemble outPtr
  exact ⟨entails_replace_sub hrec (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus)),
    hspf, htrf, hcc, hcrof, by rw [hvregs_f, hvregs_cs2, hvregs_1]⟩

set_option maxHeartbeats 1200000 in
theorem stageP3_err_tail_nondup_dec_prevEmpty_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 s : State) (coroPtr outPtr errsPtr w0 w1 w2 w3 w4 : BitVec 64)
    (e : SignalProtocolError) (_he_npan : e ≠ .panic) (b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x34dc#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x8000000000000018#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ A.live errsPtr 192 8 ∗
       speAt A (utf8 "decrypt") errsPtr e ∗ memRegion (errsPtr + 0x30#64) 144 ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ prevSessionsEmptyAt A coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗ ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000018#64) ∗
       ((s.sp + 0x278#64) ↦₆₄ w0) ∗ ((s.sp + 0x280#64) ↦₆₄ w1) ∗
       ((s.sp + 0x288#64) ↦₆₄ w2) ∗ ((s.sp + 0x290#64) ↦₆₄ w3) ∗
       ((s.sp + 0x298#64) ↦₆₄ w4) ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
       stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢ ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          words6At outPtr 0x8000000000000018#64 w0 w1 w2 w3 w4 ∗ memRegion (s.sp + 0x250#64) 20 ∗
          memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
          stackAt s.sp dropSessionStructure2Stack) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  refine P3P4.SepWPp.weaken_frame (sessionStateAt_unpack_head_tail A (coroPtr + 0xf8#64) recG recSt) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_
  have hrepack278 := words3_repack_w32_2w64_w32 (s.sp + 0x278#64) w0 w1 w2
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack278
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion20_split_eq (s.sp + 0x250#64))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 => SepWPp.exists_elim fun u_250 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (sp370_36_err_split_eq s.sp)) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_38c => SepWPp.exists_elim fun u_384 =>
    SepWPp.exists_elim fun u_380 => SepWPp.exists_elim fun u_378 => SepWPp.exists_elim fun u_370 => ?_
  have hstep1 := p3_err_tail_nondup_a1_placed_wp ext s coroPtr errsPtr hpc hrun hsp_align hx19
  refine bind_sepWP_lscro_frame_err hcro hstep1 (by sep_focus) fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx19_1, hx21_1, hx22_1, hx23_1,
    hx24_1, hx25_1, hx26_1, _, hx28_1, _, hx30_1, hvregs_1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  have hdropSpe := drop_spe2_placed_ok_at_of_dealloc ext hdealloc
  have hstack_drop : stackAt s.sp dropSessionStructure2Stack =
      memRegion (s.sp - 4192#64) 64 ∗ stackAt s.sp dropSpeStack :=
    stackAt_split_bottom s.sp dropSpeStack 64 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop) (by sep_focus) ?_
  refine call_lscl_ro_nopanic_err (spec := dropSpeSpec A) (x := (⟨errsPtr, utf8 "decrypt", e⟩ : DropSpeGhost))
    (T := speAt A (utf8 "decrypt") errsPtr e ∗ A.pool ∗ stackAt s.sp dropSpeStack)
    hcro1 hdropSpe hpc1 hrun1 hsp1_al hx30_1 (by dsimp only [dropSpeSpec]; rw [hsp1_s]) hx0_1 (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  dsimp only [dropSpeSpec]; rw [hsp1_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hjoin192 : memRegion errsPtr 48 ∗ memRegion (errsPtr + 0x30#64) 144 ⊢ memRegion errsPtr 192 := by
    rw [ProofLib.memRegion_split' (b := errsPtr) (n := 48) (k := 144) (b' := errsPtr + 0x30#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hjoin192 (by sep_focus) ?_
  have hstack_alloc : stackAt s.sp dropSpeStack =
      memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 32 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2_s]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2, hx25_cs2, hx26_cs2, _, hx28_cs2, _, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx21_2 : s2.readReg64 .x21 = errsPtr := hx21_cs2.trans hx21_1
  have hx22_2 : s2.readReg64 .x22 = errsPtr := hx22_cs2.trans hx22_1
  have hx23_2 : s2.readReg64 .x23 = 1#64 := hx23_cs2.trans hx23_1
  have hx24_2 : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_cs2, hx24_1, hx24, hsp2_s]
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hx25, hsp2_s]
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans (hx26_1.trans hx26)
  have hx28_2 : s2.readReg64 .x28 = 0x8000000000000018#64 := hx28_cs2.trans (hx28_1.trans hx28)
  have hstep3 := p3_err_tail_nondup_a2_placed_wp ext hdealloc s2 coroPtr errsPtr recG.localIk.cap
    (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32) (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    w3 w4 u_250 u_258 u_370 u_378 u_384 u_38c (w0.extractLsb' 0 32) (w2.extractLsb' 32 32) u_260 u_380
    (cap_ne_noneCap_of_lt hcap_lt) hpc2 hrun2 hsp2_align hx19_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx28_2
  rw [hsp2_s] at hstep3
  refine bind_sepWP_lscro_frame_err hcro2 hstep3 (by sep_focus) fun s3 hpc3 hrun3 hcro3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hx0_3, hx19_3, hx22_3, _, hx25_3, hx26_3, _, hx28_3, _, hx30_3, hvregs_3⟩
  have hstack_restore :
      memRegion (s.sp - 4192#64) 64 ∗ memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack ⊢
        stackAt s.sp dropSessionStructure2Stack := by rw [hstack_drop, hstack_alloc]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore (by sep_focus) ?_
  have hpack_ss : ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A recG recSt ⊢ sessionStateAt A (coroPtr + 0xf8#64) recG recSt := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using sessionStateAt_pack_head_tail A (coroPtr + 0xf8#64) recG recSt hinl
  refine P3P4.SepWPp.weaken_frame hpack_ss (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (words6_entails_memRegion48 (s.sp + 0x270#64) 0x8000000000000018#64 w0 w1 w2 w3 w4) (by sep_focus) ?_
  have hfold250 : ((s.sp + 0x250#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ w2.extractLsb' 32 32) ⊢ memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      memRegion20_fold (s.sp + 0x250#64) (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32) (w2.extractLsb' 32 32)
  refine P3P4.SepWPp.weaken_frame hfold250 (by sep_focus) ?_
  have hsp3_s : s3.sp = s.sp := hsp3_2
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3_s]; exact hsp_align
  have hx25_3' : s3.readReg64 .x25 = s3.sp + 0x210#64 := by rw [hx25_3, hsp3_s]
  have hcommon := stageP3_err_tail_common_prevEmpty_placed_ok ext hdealloc hDropSS3
    s0 s3 coroPtr outPtr 0x8000000000000018#64 w0 w1 w2 w3 w4 b_2c0 g recG recSt
    hcro3 hpc3 hrun3 hsp3_align (htr3_2.trans (htr2_1.trans (htr1_s.trans htr)))
    hx0_3 hx19_3 hx22_3 hx25_3' (hx26_3.trans hx26_2) hx28_3 hx30_3
  rw [hsp3_s] at hcommon
  refine P3P4.SepWPp.ret_sepWPp_frame hcommon (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
  exact ⟨Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)), hspf, htrf, hcc, hcrof,
    by rw [hvregs_f, hvregs_3, hvregs_cs2, hvregs_1]⟩

set_option maxHeartbeats 1200000 in
theorem stageP3_sub5_err_nondup_prevEmpty_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42) (withLsCodeLoaded lsmpl (growOneSpeSpec A)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hLogClosure : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 519) (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s : State) (coroPtr outPtr initErrsPtr : BitVec 64) (hinit_ne : initErrsPtr ≠ 0#64)
    (e : SignalProtocolError) (he_npan : e ≠ .panic) (htag_ne23 : speTag e ≠ speWord 23)
    (b_2c0 : BitVec 8) (g : RecordGhost) (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP3ErrPrePrevEmptyM3Placed A s0 s coroPtr outPtr initErrsPtr g e b_2c0 G₂ recG st₂ recSt)
      (fun sf P_f =>
        (P_f ⊢ stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr e) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  unfold stageP3ErrPrePrevEmptyM3Placed stageP3ErrPostPrevEmptyM3Placed
  have hrec_err : SessionState.recordError .preKey e = .invalidMessage .preKey .decryptionFailed :=
    recordError_preKey_of_speTag_ne_speWord23 he_npan htag_ne23
  rw [hrec_err]; refine intro_lsro_decryptionFailed_err hcro ?_
  have hdecomp : vecResultAt A (s.sp + 0x270#64) (.error e) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ c : BitVec 64, words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢ speAt A (utf8 "decrypt") c e⌝ ∗
        ((s.sp + 0x270#64) ↦₆₄ speTag e) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗
        ((s.sp + 0x280#64) ↦₆₄ w1) ∗ ((s.sp + 0x288#64) ↦₆₄ w2) ∗
        ((s.sp + 0x290#64) ↦₆₄ w3) ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗ H := by
    have h1 := speAt_decomp6 A (utf8 "decrypt") (s.sp + 0x270#64) e he_npan
    dsimp only [vecResultAt] at h1 ⊢; refine Entails.trans h1 ?_
    apply Entails.sepExists_elim; intro w0; apply Entails.sepExists_elim; intro w1
    apply Entails.sepExists_elim; intro w2; apply Entails.sepExists_elim; intro w3
    apply Entails.sepExists_elim; intro w4; apply Entails.sepExists_elim; intro H
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right H ?_)))))
    unfold words6At; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hdecomp (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 =>
    SepWPp.exists_elim fun w2 => SepWPp.exists_elim fun w3 =>
    SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun H => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜∀ c : BitVec 64, words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢ speAt A (utf8 "decrypt") c e⌝)
    (P₂ := ⌜∀ c : BitVec 64, words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢ speAt A (utf8 "decrypt") c e⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun hreassemble => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x930#64))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u930 => SepWPp.exists_elim fun u938 =>
    SepWPp.exists_elim fun u940 => SepWPp.exists_elim fun u948 =>
    SepWPp.exists_elim fun u950 => SepWPp.exists_elim fun u958 => ?_
  have hstep1 := p3_err_nondup_a_placed_wp ext s coroPtr outPtr (speTag e)
    w0 w1 w2 w3 w4 u930 u938 u940 u948 u950 u958
    (speTag_ne_ok_of_ne_panic he_npan) htag_ne23 hpc hrun hsp_align hx19 hx24
  refine bind_sepWP_lscro_frame_err hcro hstep1 (by sep_focus) fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, _, _, _, _, hx19_1, hx24_1, hx25_1, hx26_1, _, _, _, hx30_1, hvregs_1⟩
  refine P3P4.SepWPp.weaken_frame (words6_entails_memRegion48 (s.sp + 0x930#64) (speTag e) w0 w1 w2 w3 w4) (by sep_focus) ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  have hstack_log : stackAt s.sp growOneSpeStack =
      memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack :=
    stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine call_lscl_nopanic_err (spec := pqxdhLogClosurePlacedSpec) (x := ()) (φ := True)
    (T := FromRecordCallees.lsLogOff ∗ stackAt s.sp pqxdhClosureStack)
    hcro1 hLogClosure hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp1_s, pure_true, emp_sepConj]) trivial (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp1_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hstack_restore1 : memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack ⊢
      stackAt s.sp growOneSpeStack := by rw [hstack_log]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore1 (by sep_focus) ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2_s]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, _, _, _, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx24_2 : s2.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs2.trans hx24_1
  have hx25_2 : s2.readReg64 .x25 = s.sp + 0x210#64 := hx25_cs2.trans hx25_1
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans hx26_1
  have hstep3 := p3_err_nondup_b_placed_wp ext s2 coroPtr hpc2 hrun2 hsp2_align hx19_2
  rw [hsp2_s] at hstep3
  refine bind_sepWP_lscro_frame_err hcro2 hstep3 (by sep_focus) fun s3 hpc3 hrun3 hcro3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hx0_3, hx19_3, hx21_3, hx24_3, hx25_3, hx26_3, _, _, _, hx30_3, hvregs_3⟩
  have hsp3_s : s3.sp = s.sp := hsp3_2
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3_s] using hsp_align
  have htr3_0 : s3.trace = s0.trace := htr3_2.trans (htr2_1.trans (htr1_s.trans htr))
  refine call_lscl_oom_err (x := (s.sp + 0x3c8#64, 0#64, initErrsPtr, ([] : List (BitVec 8)))) (φ := True)
    (T := ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
          A.pool ∗ stackAt s.sp growOneSpeStack)
    hcro3 htr3_0 hGrow hpc3 hrun3 hsp3_al hx30_3
    (by
      rw [growOneSpe_pre_zero_eq A s3 (s.sp + 0x3c8#64) initErrsPtr hx0_3 hinit_ne, hsp3_s, pure_true, emp_sepConj]
      simp only [BitVec.add_assoc, BitVec.reduceAdd])
    trivial (by sep_focus) (hnext := fun s4 hpc4 hrun4 hsp4_3 _ hcs4 hcro4 => ?_)
  rw [growOneSpe_post_zero_eq A s3 s4 (s.sp + 0x3c8#64) initErrsPtr, hsp3_s]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun errsPtr => SepWPp.pure_elim fun htr4_3 => SepWPp.pure_elim fun _ => ?_
  have hsplit192 : memRegion errsPtr 192 = memRegion errsPtr 48 ∗ memRegion (errsPtr + 0x30#64) 144 := by
    rw [ProofLib.memRegion_split' (b := errsPtr) (n := 48) (k := 144) (b' := errsPtr + 0x30#64) rfl (by bv_omega) (by decide)]
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hsplit192) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq errsPtr)) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun e0 => SepWPp.exists_elim fun e1 =>
    SepWPp.exists_elim fun e2 => SepWPp.exists_elim fun e3 =>
    SepWPp.exists_elim fun e4 => SepWPp.exists_elim fun e5 => ?_
  have hlog_eq : FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hlog_eq) (by sep_focus) ?_
  have hsp4_s : s4.sp = s.sp := hsp4_3.trans hsp3_s
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4_s]; exact hsp_align
  rcases hcs4 with ⟨hx19_cs4, _, hx21_cs4, _, _, hx24_cs4, hx25_cs4, hx26_cs4, _, _, _, hvregs_cs4⟩
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hx19_cs4.trans hx19_3
  have hx21_4 : s4.readReg64 .x21 = 0#64 := hx21_cs4.trans hx21_3
  have hx24_4 : s4.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs4.trans (hx24_3.trans hx24_2)
  have hx25_4 : s4.readReg64 .x25 = s4.sp + 0x210#64 := by rw [hx25_cs4, hx25_3, hx25_2, hsp4_s]
  have hx26_4 : s4.readReg64 .x26 = outPtr := hx26_cs4.trans (hx26_3.trans hx26_2)
  have hstep5 := p3_err_nondup_c_placed_wp ext hshim s4 coroPtr errsPtr (speTag e)
    w0 w1 w2 w3 w4 e0 e1 e2 e3 e4 e5 hpc4 hrun4 hsp4_align hx19_4 hx21_4 hx25_4
  rw [hsp4_s] at hstep5
  refine bind_sepWP_lscro_frame_err hcro4 hstep5 (by sep_focus) fun s5 hpc5 hrun5 hcro5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5_4, htr5_4, hx0_5, hx1_5, hx19_5, hx24_5, hx25_5, hx26_5, _, _, _, hvregs_5⟩
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hlog_eq.symm) (by sep_focus) ?_
  have hsp5_s : s5.sp = s.sp := hsp5_4
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5_s]; exact hsp_align
  have htr5_0 : s5.trace = s0.trace := htr5_4.trans (htr4_3.trans htr3_0)
  have hreasm_errs :
      ((errsPtr + 0x0#64) ↦₆₄ speTag e) ∗ ((errsPtr + 0x8#64) ↦₆₄ w0) ∗
      ((errsPtr + 0x10#64) ↦₆₄ w1) ∗ ((errsPtr + 0x18#64) ↦₆₄ w2) ∗
      ((errsPtr + 0x20#64) ↦₆₄ w3) ∗ ((errsPtr + 0x28#64) ↦₆₄ w4) ∗ H ⊢
      speAt A (utf8 "decrypt") errsPtr e := by
    simpa only [words6At, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hreassemble errsPtr
  refine P3P4.SepWPp.weaken_frame hreasm_errs (by sep_focus) ?_
  have hstack_alloc : stackAt s.sp growOneSpeStack =
      memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 512 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have halloc17 := p3_alloc_2eac_placed_ok (A := A) ext halloc hpanic s0 s5
    emp hcro5 hpc5 hrun5 hsp5_align htr5_0 hx0_5 hx1_5
  rw [sepConj_emp, hsp5_s] at halloc17
  refine SepWPp.bind_sepWPp_frame_raw halloc17 (by sep_focus)
    fun s6 P_m6 hpc6 hrun6 ⟨hP6, hdf_ne, hsp6_5, htr6_5, hcs6, hcro6⟩ => ?_
  rw [sepConj_emp] at hP6
  refine P3P4.SepWPp.weaken_frame hP6 (by sep_focus) ?_
  have hstack_restore2 : memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack ⊢
      stackAt s.sp growOneSpeStack := by rw [hstack_alloc]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore2 (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion17_split_eq (s6.readReg64 .x0))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun df_10 => SepWPp.exists_elim fun df_8 => SepWPp.exists_elim fun df_0 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (cell_split_head8 (s.sp + 0x290#64) w3)) (by sep_focus) ?_
  have hsp6_s : s6.sp = s.sp := hsp6_5
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6_s]; exact hsp_align
  rcases hcs6 with ⟨hx19_cs6, _, _, _, _, hx24_cs6, hx25_cs6, hx26_cs6, _, _, _, hvregs_cs6⟩
  have hx19_6 : s6.readReg64 .x19 = coroPtr := hx19_cs6.trans hx19_5
  have hx24_6 : s6.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs6.trans (hx24_5.trans hx24_4)
  have hx25_6 : s6.readReg64 .x25 = s.sp + 0x210#64 := hx25_cs6.trans hx25_5
  have hx26_6 : s6.readReg64 .x26 = outPtr := hx26_cs6.trans (hx26_5.trans hx26_4)
  have hstep7 := p3_err_nondup_d_placed_wp ext s6 coroPtr (s6.readReg64 .x0)
    0x6974707972636564#64 0x656c696166206e6f#64 df_0 df_8 (speTag e) w0 w1 w2 df_10 (w3.extractLsb' 0 8)
    hdf_ne hpc6 hrun6 hsp6_align rfl hx19_6
  rw [hsp6_s] at hstep7
  refine bind_sepWP_lscro_frame_err hcro6 hstep7 (by sep_focus) fun s7 hpc7 hrun7 hcro7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7_6, htr7_6, hx0_7, hx19_7, hx24_7, hx25_7, hx26_7, _, hx28_7, _, hx30_7, hvregs_7⟩
  have hsp7_s : s7.sp = s.sp := hsp7_6
  have hsp7_al : s7.spAligned = true := by simpa only [State.spAligned, hsp7_s] using hsp_align
  refine SepWPp.drop_frame
    (P_drop := ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
               ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64))
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (dfPtr_words_eq_decryptionFailedStr (s6.readReg64 .x0))) (by sep_focus) ?_
  obtain ⟨w3', hw3'_unpack, hw3'_join⟩ := cell_join_head8 3#8 w3
  have hw3'_head : w3'.extractLsb' 0 8 = 3#8 := extractLsb0_8_of_unpack64_cons hw3'_unpack
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (hw3'_join (s.sp + 0x290#64))) (by sep_focus) ?_
  have hstack_drop2 : stackAt s.sp growOneSpeStack =
      memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
    stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  refine call_lscl_nopanic_err (x := (⟨s.sp + 0xa90#64, G₂, st₂⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ A.pool ∗ stackAt s.sp dropSessionStructure2Stack)
    hcro7 hDropSS3 hpc7 hrun7 hsp7_al hx30_7 (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp7_s])
    hx0_7 (by sep_focus) (hnext := fun s8 hpc8 hrun8 hsp8_7 _ hcs8 hcro8 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]; rw [hsp7_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr8_7 => ?_
  have hsp8_s : s8.sp = s.sp := hsp8_7.trans hsp7_s
  have hsp8_align : (s8.sp &&& 15#64 == 0#64) = true := by rw [hsp8_s]; exact hsp_align
  rcases hcs8 with ⟨hx19_cs8, _, _, _, _, hx24_cs8, hx25_cs8, hx26_cs8, _, hx28_cs8, _, hvregs_cs8⟩
  have hx19_8 : s8.readReg64 .x19 = coroPtr := hx19_cs8.trans hx19_7
  have hx24_8 : s8.readReg64 .x24 = s8.sp + 0x370#64 := by rw [hx24_cs8, hx24_7, hx24_6, hsp8_s]
  have hx25_8 : s8.readReg64 .x25 = s8.sp + 0x210#64 := by rw [hx25_cs8, hx25_7, hx25_6, hsp8_s]
  have hx26_8 : s8.readReg64 .x26 = outPtr := hx26_cs8.trans (hx26_7.trans hx26_6)
  have hx28_8 : s8.readReg64 .x28 = 0x8000000000000018#64 := hx28_cs8.trans hx28_7
  have htail := stageP3_err_tail_nondup_dec_prevEmpty_placed_ok ext hdealloc hDropSS3
    s0 s8 coroPtr outPtr errsPtr 17#64 (s6.readReg64 .x0) 17#64 w3' w4 e he_npan b_2c0 g recG recSt
    hcro8 hpc8 hrun8 hsp8_align (htr8_7.trans (htr7_6.trans (htr6_5.trans htr5_0)))
    hx19_8 hx24_8 hx25_8 hx26_8 hx28_8
  rw [hsp8_s] at htail
  refine P3P4.SepWPp.ret_sepWPp_frame htail (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
  have hrec := words6At_preKey_decryptionFailed_entails_recordResultAt A
    outPtr (s6.readReg64 .x0) w3' w4 hdf_ne hw3'_head
  have hstack_restore3 : memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack ⊢
      stackAt s.sp growOneSpeStack := by rw [hstack_drop2]; exact Entails.refl _
  refine ⟨?_, hspf, htrf, hcc, hcrof,
    by rw [hvregs_f, hvregs_cs8, hvregs_7, hvregs_cs6, hvregs_5, hvregs_cs4, hvregs_3, hvregs_cs2, hvregs_1]⟩
  refine Entails.sepExists_right 4#64 (Entails.sepExists_right errsPtr (Entails.sepExists_right 1#64 ?_))
  refine Entails.trans (entails_replace_sub hrec (by sep_focus) rfl) ?_
  exact entails_replace_sub hstack_restore3 (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
theorem stageP3_sub5_err_prevEmpty_placed_ok [LibsignalPlacement] :
    StageP3Sub5ErrPrevEmptyPlacedStmt := by
  intro A ext hshim halloc hdealloc _hmemcpy hGrow hDropSS3 hLogClosure hpanic
    s0 s coroPtr outPtr initErrsPtr hinit_ne e he_npan b_2c0 g G₂ recG st₂ recSt
    hcro hpc hrun hsp_align htr hx19 hx24
  by_cases htag23 : speTag e = speWord 23
  · obtain ⟨ratVer, counter, rfl⟩ := speTag_eq_speWord23_iff.mp htag23
    unfold stageP3ErrPrePrevEmptyM3Placed stageP3ErrPostPrevEmptyM3Placed
    have hstack_drop2 : stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
      stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
    rw [hstack_drop2]
    have hdup := stageP3_sub5_err_dup_prevEmpty_placed_ok ext hdealloc hDropSS3
      s0 s coroPtr outPtr initErrsPtr ratVer counter b_2c0 g G₂ recG st₂ recSt
      hcro hpc hrun hsp_align htr hx19 hx24
    refine P3P4.SepWPp.ret_sepWPp_frame hdup (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
    have herrs : ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
        ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ⊢
        ∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
          ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ errsLen) :=
      Entails.sepExists_right 0#64 (Entails.sepExists_right initErrsPtr
        (Entails.sepExists_right 0#64 (Entails.refl _)))
    dsimp only [SessionState.recordError]
    exact ⟨entails_replace_sub herrs (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus)),
      hspf, htrf, hcc, hcrof, hvregs_f⟩
  · exact stageP3_sub5_err_nondup_prevEmpty_placed_ok ext hshim halloc hdealloc
      hGrow hDropSS3 hLogClosure hpanic
      s0 s coroPtr outPtr initErrsPtr hinit_ne e he_npan htag23
      b_2c0 g G₂ recG st₂ recSt hcro hpc hrun hsp_align htr hx19 hx24

theorem stageP3Gen_prevEmpty_vregs_placed_ok_of_clone [LibsignalPlacement]
    (hClone : CloneGenVRegsPlacedStmt) : StageP3PrevEmptyVRegsM3PlacedStmt :=
  stageP3Gen_prevEmpty_vregs_placed_ok_of_parts hClone stageP3_sub5_err_prevEmpty_placed_ok

/-! ## `[LibsignalFullPlacement]` / `LibsignalFrozen` variants -/

set_option maxHeartbeats 1200000 in
theorem stageP3_sub5_err_nondup_prevEmpty_full_placed_ok [LibsignalFullPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42) (withLsCodeLoaded lsmpl (growOneSpeSpec A)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s : State) (coroPtr outPtr initErrsPtr : BitVec 64) (hinit_ne : initErrsPtr ≠ 0#64)
    (e : SignalProtocolError) (he_npan : e ≠ .panic) (htag_ne23 : speTag e ≠ speWord 23)
    (b_2c0 : BitVec 8) (g : RecordGhost) (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hfr : LibsignalFrozen lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP3ErrPrePrevEmptyM3Placed A s0 s coroPtr outPtr initErrsPtr g e b_2c0 G₂ recG st₂ recSt)
      (fun sf P_f =>
        (P_f ⊢ stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr e) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  have hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem := lscro_of_frozen hfr
  unfold stageP3ErrPrePrevEmptyM3Placed stageP3ErrPostPrevEmptyM3Placed
  have hrec_err : SessionState.recordError .preKey e = .invalidMessage .preKey .decryptionFailed :=
    recordError_preKey_of_speTag_ne_speWord23 he_npan htag_ne23
  rw [hrec_err]; refine intro_lsro_decryptionFailed_err hcro ?_
  have hdecomp : vecResultAt A (s.sp + 0x270#64) (.error e) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ c : BitVec 64, words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢ speAt A (utf8 "decrypt") c e⌝ ∗
        ((s.sp + 0x270#64) ↦₆₄ speTag e) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗
        ((s.sp + 0x280#64) ↦₆₄ w1) ∗ ((s.sp + 0x288#64) ↦₆₄ w2) ∗
        ((s.sp + 0x290#64) ↦₆₄ w3) ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗ H := by
    have h1 := speAt_decomp6 A (utf8 "decrypt") (s.sp + 0x270#64) e he_npan
    dsimp only [vecResultAt] at h1 ⊢; refine Entails.trans h1 ?_
    apply Entails.sepExists_elim; intro w0; apply Entails.sepExists_elim; intro w1
    apply Entails.sepExists_elim; intro w2; apply Entails.sepExists_elim; intro w3
    apply Entails.sepExists_elim; intro w4; apply Entails.sepExists_elim; intro H
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right H ?_)))))
    unfold words6At; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hdecomp (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 =>
    SepWPp.exists_elim fun w2 => SepWPp.exists_elim fun w3 =>
    SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun H => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜∀ c : BitVec 64, words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢ speAt A (utf8 "decrypt") c e⌝)
    (P₂ := ⌜∀ c : BitVec 64, words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢ speAt A (utf8 "decrypt") c e⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun hreassemble => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x930#64))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u930 => SepWPp.exists_elim fun u938 =>
    SepWPp.exists_elim fun u940 => SepWPp.exists_elim fun u948 =>
    SepWPp.exists_elim fun u950 => SepWPp.exists_elim fun u958 => ?_
  have hstep1 := p3_err_nondup_a_placed_wp ext s coroPtr outPtr (speTag e)
    w0 w1 w2 w3 w4 u930 u938 u940 u948 u950 u958
    (speTag_ne_ok_of_ne_panic he_npan) htag_ne23 hpc hrun hsp_align hx19 hx24
  refine bind_sepWP_lsfr_frame_ver hfr hstep1 (by sep_focus) fun s1 hpc1 hrun1 hfr1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, _, _, _, _, hx19_1, hx24_1, hx25_1, hx26_1, _, _, _, hx30_1, hvregs_1⟩
  refine P3P4.SepWPp.weaken_frame (words6_entails_memRegion48 (s.sp + 0x930#64) (speTag e) w0 w1 w2 w3 w4) (by sep_focus) ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  have hstack_log : stackAt s.sp growOneSpeStack =
      memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack :=
    stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine call_lsfr_nopanic_ver (spec := pqxdhLogClosurePlacedSpec) (x := ()) (φ := True)
    (T := FromRecordCallees.lsLogOff ∗ stackAt s.sp pqxdhClosureStack)
    hfr1 (pqxdh_log_closure_frozen_placed_ok_of_block (callerProg := lsProg_518 ext))
    hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp1_s, pure_true, emp_sepConj]) trivial (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hfr2 => ?_)
  have hcro2 : StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem := lscro_of_frozen hfr2
  dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp1_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hstack_restore1 : memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack ⊢
      stackAt s.sp growOneSpeStack := by rw [hstack_log]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore1 (by sep_focus) ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2_s]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, _, _, _, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx24_2 : s2.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs2.trans hx24_1
  have hx25_2 : s2.readReg64 .x25 = s.sp + 0x210#64 := hx25_cs2.trans hx25_1
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans hx26_1
  have hstep3 := p3_err_nondup_b_placed_wp ext s2 coroPtr hpc2 hrun2 hsp2_align hx19_2
  rw [hsp2_s] at hstep3
  refine bind_sepWP_lscro_frame_err hcro2 hstep3 (by sep_focus) fun s3 hpc3 hrun3 hcro3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hx0_3, hx19_3, hx21_3, hx24_3, hx25_3, hx26_3, _, _, _, hx30_3, hvregs_3⟩
  have hsp3_s : s3.sp = s.sp := hsp3_2
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3_s] using hsp_align
  have htr3_0 : s3.trace = s0.trace := htr3_2.trans (htr2_1.trans (htr1_s.trans htr))
  refine call_lscl_oom_err (x := (s.sp + 0x3c8#64, 0#64, initErrsPtr, ([] : List (BitVec 8)))) (φ := True)
    (T := ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
          A.pool ∗ stackAt s.sp growOneSpeStack)
    hcro3 htr3_0 hGrow hpc3 hrun3 hsp3_al hx30_3
    (by
      rw [growOneSpe_pre_zero_eq A s3 (s.sp + 0x3c8#64) initErrsPtr hx0_3 hinit_ne, hsp3_s, pure_true, emp_sepConj]
      simp only [BitVec.add_assoc, BitVec.reduceAdd])
    trivial (by sep_focus) (hnext := fun s4 hpc4 hrun4 hsp4_3 _ hcs4 hcro4 => ?_)
  rw [growOneSpe_post_zero_eq A s3 s4 (s.sp + 0x3c8#64) initErrsPtr, hsp3_s]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun errsPtr => SepWPp.pure_elim fun htr4_3 => SepWPp.pure_elim fun _ => ?_
  have hsplit192 : memRegion errsPtr 192 = memRegion errsPtr 48 ∗ memRegion (errsPtr + 0x30#64) 144 := by
    rw [ProofLib.memRegion_split' (b := errsPtr) (n := 48) (k := 144) (b' := errsPtr + 0x30#64) rfl (by bv_omega) (by decide)]
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hsplit192) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq errsPtr)) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun e0 => SepWPp.exists_elim fun e1 =>
    SepWPp.exists_elim fun e2 => SepWPp.exists_elim fun e3 =>
    SepWPp.exists_elim fun e4 => SepWPp.exists_elim fun e5 => ?_
  have hlog_eq : FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hlog_eq) (by sep_focus) ?_
  have hsp4_s : s4.sp = s.sp := hsp4_3.trans hsp3_s
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4_s]; exact hsp_align
  rcases hcs4 with ⟨hx19_cs4, _, hx21_cs4, _, _, hx24_cs4, hx25_cs4, hx26_cs4, _, _, _, hvregs_cs4⟩
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hx19_cs4.trans hx19_3
  have hx21_4 : s4.readReg64 .x21 = 0#64 := hx21_cs4.trans hx21_3
  have hx24_4 : s4.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs4.trans (hx24_3.trans hx24_2)
  have hx25_4 : s4.readReg64 .x25 = s4.sp + 0x210#64 := by rw [hx25_cs4, hx25_3, hx25_2, hsp4_s]
  have hx26_4 : s4.readReg64 .x26 = outPtr := hx26_cs4.trans (hx26_3.trans hx26_2)
  have hstep5 := p3_err_nondup_c_placed_wp ext hshim s4 coroPtr errsPtr (speTag e)
    w0 w1 w2 w3 w4 e0 e1 e2 e3 e4 e5 hpc4 hrun4 hsp4_align hx19_4 hx21_4 hx25_4
  rw [hsp4_s] at hstep5
  refine bind_sepWP_lscro_frame_err hcro4 hstep5 (by sep_focus) fun s5 hpc5 hrun5 hcro5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5_4, htr5_4, hx0_5, hx1_5, hx19_5, hx24_5, hx25_5, hx26_5, _, _, _, hvregs_5⟩
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hlog_eq.symm) (by sep_focus) ?_
  have hsp5_s : s5.sp = s.sp := hsp5_4
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5_s]; exact hsp_align
  have htr5_0 : s5.trace = s0.trace := htr5_4.trans (htr4_3.trans htr3_0)
  have hreasm_errs :
      ((errsPtr + 0x0#64) ↦₆₄ speTag e) ∗ ((errsPtr + 0x8#64) ↦₆₄ w0) ∗
      ((errsPtr + 0x10#64) ↦₆₄ w1) ∗ ((errsPtr + 0x18#64) ↦₆₄ w2) ∗
      ((errsPtr + 0x20#64) ↦₆₄ w3) ∗ ((errsPtr + 0x28#64) ↦₆₄ w4) ∗ H ⊢
      speAt A (utf8 "decrypt") errsPtr e := by
    simpa only [words6At, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hreassemble errsPtr
  refine P3P4.SepWPp.weaken_frame hreasm_errs (by sep_focus) ?_
  have hstack_alloc : stackAt s.sp growOneSpeStack =
      memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 512 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have halloc17 := p3_alloc_2eac_placed_ok (A := A) ext halloc hpanic s0 s5
    emp hcro5 hpc5 hrun5 hsp5_align htr5_0 hx0_5 hx1_5
  rw [sepConj_emp, hsp5_s] at halloc17
  refine SepWPp.bind_sepWPp_frame_raw halloc17 (by sep_focus)
    fun s6 P_m6 hpc6 hrun6 ⟨hP6, hdf_ne, hsp6_5, htr6_5, hcs6, hcro6⟩ => ?_
  rw [sepConj_emp] at hP6
  refine P3P4.SepWPp.weaken_frame hP6 (by sep_focus) ?_
  have hstack_restore2 : memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack ⊢
      stackAt s.sp growOneSpeStack := by rw [hstack_alloc]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore2 (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion17_split_eq (s6.readReg64 .x0))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun df_10 => SepWPp.exists_elim fun df_8 => SepWPp.exists_elim fun df_0 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (cell_split_head8 (s.sp + 0x290#64) w3)) (by sep_focus) ?_
  have hsp6_s : s6.sp = s.sp := hsp6_5
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6_s]; exact hsp_align
  rcases hcs6 with ⟨hx19_cs6, _, _, _, _, hx24_cs6, hx25_cs6, hx26_cs6, _, _, _, hvregs_cs6⟩
  have hx19_6 : s6.readReg64 .x19 = coroPtr := hx19_cs6.trans hx19_5
  have hx24_6 : s6.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs6.trans (hx24_5.trans hx24_4)
  have hx25_6 : s6.readReg64 .x25 = s.sp + 0x210#64 := hx25_cs6.trans hx25_5
  have hx26_6 : s6.readReg64 .x26 = outPtr := hx26_cs6.trans (hx26_5.trans hx26_4)
  have hstep7 := p3_err_nondup_d_placed_wp ext s6 coroPtr (s6.readReg64 .x0)
    0x6974707972636564#64 0x656c696166206e6f#64 df_0 df_8 (speTag e) w0 w1 w2 df_10 (w3.extractLsb' 0 8)
    hdf_ne hpc6 hrun6 hsp6_align rfl hx19_6
  rw [hsp6_s] at hstep7
  refine bind_sepWP_lscro_frame_err hcro6 hstep7 (by sep_focus) fun s7 hpc7 hrun7 hcro7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7_6, htr7_6, hx0_7, hx19_7, hx24_7, hx25_7, hx26_7, _, hx28_7, _, hx30_7, hvregs_7⟩
  have hsp7_s : s7.sp = s.sp := hsp7_6
  have hsp7_al : s7.spAligned = true := by simpa only [State.spAligned, hsp7_s] using hsp_align
  refine SepWPp.drop_frame
    (P_drop := ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
               ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64))
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (dfPtr_words_eq_decryptionFailedStr (s6.readReg64 .x0))) (by sep_focus) ?_
  obtain ⟨w3', hw3'_unpack, hw3'_join⟩ := cell_join_head8 3#8 w3
  have hw3'_head : w3'.extractLsb' 0 8 = 3#8 := extractLsb0_8_of_unpack64_cons hw3'_unpack
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (hw3'_join (s.sp + 0x290#64))) (by sep_focus) ?_
  have hstack_drop2 : stackAt s.sp growOneSpeStack =
      memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
    stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  refine call_lscl_nopanic_err (x := (⟨s.sp + 0xa90#64, G₂, st₂⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ A.pool ∗ stackAt s.sp dropSessionStructure2Stack)
    hcro7 hDropSS3 hpc7 hrun7 hsp7_al hx30_7 (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp7_s])
    hx0_7 (by sep_focus) (hnext := fun s8 hpc8 hrun8 hsp8_7 _ hcs8 hcro8 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]; rw [hsp7_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr8_7 => ?_
  have hsp8_s : s8.sp = s.sp := hsp8_7.trans hsp7_s
  have hsp8_align : (s8.sp &&& 15#64 == 0#64) = true := by rw [hsp8_s]; exact hsp_align
  rcases hcs8 with ⟨hx19_cs8, _, _, _, _, hx24_cs8, hx25_cs8, hx26_cs8, _, hx28_cs8, _, hvregs_cs8⟩
  have hx19_8 : s8.readReg64 .x19 = coroPtr := hx19_cs8.trans hx19_7
  have hx24_8 : s8.readReg64 .x24 = s8.sp + 0x370#64 := by rw [hx24_cs8, hx24_7, hx24_6, hsp8_s]
  have hx25_8 : s8.readReg64 .x25 = s8.sp + 0x210#64 := by rw [hx25_cs8, hx25_7, hx25_6, hsp8_s]
  have hx26_8 : s8.readReg64 .x26 = outPtr := hx26_cs8.trans (hx26_7.trans hx26_6)
  have hx28_8 : s8.readReg64 .x28 = 0x8000000000000018#64 := hx28_cs8.trans hx28_7
  have htail := stageP3_err_tail_nondup_dec_prevEmpty_placed_ok ext hdealloc hDropSS3
    s0 s8 coroPtr outPtr errsPtr 17#64 (s6.readReg64 .x0) 17#64 w3' w4 e he_npan b_2c0 g recG recSt
    hcro8 hpc8 hrun8 hsp8_align (htr8_7.trans (htr7_6.trans (htr6_5.trans htr5_0)))
    hx19_8 hx24_8 hx25_8 hx26_8 hx28_8
  rw [hsp8_s] at htail
  refine P3P4.SepWPp.ret_sepWPp_frame htail (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
  have hrec := words6At_preKey_decryptionFailed_entails_recordResultAt A
    outPtr (s6.readReg64 .x0) w3' w4 hdf_ne hw3'_head
  have hstack_restore3 : memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack ⊢
      stackAt s.sp growOneSpeStack := by rw [hstack_drop2]; exact Entails.refl _
  refine ⟨?_, hspf, htrf, hcc, hcrof,
    by rw [hvregs_f, hvregs_cs8, hvregs_7, hvregs_cs6, hvregs_5, hvregs_cs4, hvregs_3, hvregs_cs2, hvregs_1]⟩
  refine Entails.sepExists_right 4#64 (Entails.sepExists_right errsPtr (Entails.sepExists_right 1#64 ?_))
  refine Entails.trans (entails_replace_sub hrec (by sep_focus) rfl) ?_
  exact entails_replace_sub hstack_restore3 (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
theorem stageP3_sub5_err_prevEmpty_full_placed_ok [LibsignalFullPlacement] :
    StageP3Sub5ErrPrevEmptyFullPlacedStmt := by
  intro A ext hshim halloc hdealloc _hmemcpy hGrow hDropSS3 hpanic
    s0 s coroPtr outPtr initErrsPtr hinit_ne e he_npan b_2c0 g G₂ recG st₂ recSt
    hfr hpc hrun hsp_align htr hx19 hx24
  have hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem := lscro_of_frozen hfr
  by_cases htag23 : speTag e = speWord 23
  · obtain ⟨ratVer, counter, rfl⟩ := speTag_eq_speWord23_iff.mp htag23
    unfold stageP3ErrPrePrevEmptyM3Placed stageP3ErrPostPrevEmptyM3Placed
    have hstack_drop2 : stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
      stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
    rw [hstack_drop2]
    have hdup := stageP3_sub5_err_dup_prevEmpty_placed_ok ext hdealloc hDropSS3
      s0 s coroPtr outPtr initErrsPtr ratVer counter b_2c0 g G₂ recG st₂ recSt
      hcro hpc hrun hsp_align htr hx19 hx24
    refine P3P4.SepWPp.ret_sepWPp_frame hdup (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
    have herrs : ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
        ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ⊢
        ∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
          ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ errsLen) :=
      Entails.sepExists_right 0#64 (Entails.sepExists_right initErrsPtr
        (Entails.sepExists_right 0#64 (Entails.refl _)))
    dsimp only [SessionState.recordError]
    exact ⟨entails_replace_sub herrs (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus)),
      hspf, htrf, hcc, hcrof, hvregs_f⟩
  · exact stageP3_sub5_err_nondup_prevEmpty_full_placed_ok ext hshim halloc hdealloc
      hGrow hDropSS3 hpanic
      s0 s coroPtr outPtr initErrsPtr hinit_ne e he_npan htag23
      b_2c0 g G₂ recG st₂ recSt hfr hpc hrun hsp_align htr hx19 hx24

theorem stageP3Gen_prevEmpty_vregs_full_placed_ok_of_clone [LibsignalFullPlacement]
    (hClone : CloneGenVRegsPlacedStmt) : StageP3PrevEmptyVRegsM3FullPlacedStmt :=
  stageP3Gen_prevEmpty_vregs_full_placed_ok_of_parts hClone stageP3_sub5_err_prevEmpty_full_placed_ok

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
