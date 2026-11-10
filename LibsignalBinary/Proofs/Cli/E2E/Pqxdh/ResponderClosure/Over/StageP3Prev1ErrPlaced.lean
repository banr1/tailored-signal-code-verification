/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3Prev1ErrAPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologue
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSpe2Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenBlocks
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenBlocks2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3Prev1ErrA
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpe
import all Init.Data.String.Defs

/-!
# Placed Stage P3 Unified Substage P3.5 Error Path on 1-Element `previous_sessions`

Proves `[LibsignalPlacement]` and `[LibsignalFullPlacement]` Substage P3.5 error-path theorems
(`+0x1cd8 → s0.readReg64 .x30`) over a 1-element `previous_sessions` vector `prevVecAt [enc]`.
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

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP34
open CryptoVerification.CliHandshake.RespClosurePlaced CryptoVerification.CliHandshake.Placed
open CryptoVerification.SignalSession

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

private theorem call_lscl_oom_prev1 [LibsignalPlacement] {α : Type} {prog : Program}
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
      hnext sm hpcm hrunm hspm hsp_alm hcsm (hcro.of_keepsFrozen hsteps.keepsFrozen) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeLoaded] at hpost; rw [hpan_oom, ← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpanm, _, hpost, allowPanic_oom_of_prefix (F := F) (htr ▸ List.prefix_refl _)⟩)⟩
  · dsimp only [withLsCodeLoaded] at hpost; rw [hexit_false] at hpost; exact (allowPanic_not_exited hpost).elim

private theorem pointsToBytesRO_decryptionFailed_prev1 (a : BitVec 64) :
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

private theorem intro_lsro_decryptionFailed_prev1 [LibsignalPlacement]
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
  rw [pointsToBytesRO_decryptionFailed_prev1] at hro0
  have hro1 : s.mem ⊨ (((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
      ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗
      ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 16#64) ↦₈ᵣ 0x64#8) ∗ P) ∗ R := by
    simpa only [sepConj_assoc] using hro0
  exact SepWPp.drop_frame (P_drop := (lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 16#64) ↦₈ᵣ 0x64#8)
    (by ac_rfl) hwp R hro1 hL

set_option maxHeartbeats 800000 in
private theorem p3_alloc_2eac_prev1_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s : State) (F : SepProp) (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x2eac#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = 17#64) (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (lsProg_518 ext) (dpClosureEntryP34Placed + 0x2eb0#64) s ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) 17 1 ∗ memRegion (s2.readReg64 .x0) 17 ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem)
      (P3P4.PanicOomProp s0) := by
  have hbl : SepWP (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") s emp
      (fun s1 P_f => (P_f ⊢ emp) ∧ s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = 17#64 ∧ s1.readReg64 .x1 = 1#64 ∧
        CalleeSavedPreserved s s1 ∧ s1.readReg64 .x30 = dpClosureEntryP34Placed + 0x2eb0#64) := by
    dsimp only [dpClosureEntryP34Placed] at hpc ⊢; wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm],
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, by simp_all [arm64_norm]⟩
  refine bind_sepWP_lscro_frame hcro hbl (emp_sepConj _).symm
    fun s1 hpc1 hrun1 hcro1 ⟨hsp1, htr1, hx0_1, hx1_1, hcs1, hlr1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hsp_align
  have hφ : (s1.readReg64 .x0).toNat = 17 ∧ (s1.readReg64 .x1).toNat = 1 ∧ LayoutOk 17 1 :=
    ⟨by rw [hx0_1]; rfl, by rw [hx1_1]; rfl, by decide, ⟨0, rfl⟩, by decide⟩
  refine call_raw_nopanic_prev1 (spec := rustAllocSpec A) (x := (17, 1))
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
      dsimp only [lsHandleErrorSym, dpClosureEntryP34Placed] at hpc2 ⊢; wp_steps
      exact SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl⟩
    refine bind_sepWP_lscro_frame hcro2 hoom_steps (emp_sepConj _).symm fun s3 hpc3 hrun3 _ htr3 => ?_
    have hext : (lsProg_518 ext).externAt? s3.pc = some Rust.panicked := by
      rw [hpc3]; exact (ls_externAt?_of_mem (prog := lsProg_518 ext) (i := 518) (by decide)).trans hpanic
    exact SepWPp.panic hrun3 hext fun R hm =>
      allowPanic_panicked (LibsignalTripleRatchet.allocFailedIn_of_eq
        (by simp only [Rust.panicked, htr3, htr2, htr1, htr])) hm
  · have hoom0 : (s2.readReg64 .x0 = 0) = False := eq_false hoom
    simp only [hoom0, ↓reduceIte, P3P4.pull_pure_alloc_ok]
    exact SepWPp.pure_elim fun ⟨_, htr2⟩ =>
      SepWPp.done hpc2 hrun2 ⟨Entails.of_eq (by ac_rfl), hoom, hsp2, htr2.trans htr1, hcs, hcro2⟩

/-- Placed Substage P3.5 error-path precondition at `+0x1cd8` over a 1-element `prevVecAt [enc]`. -/
def stageP3ErrPrePrev1Placed [LibsignalPlacement] (A : RustAlloc) (s0 s : State)
    (coroPtr outPtr initErrsPtr prevCap prevPtr : BitVec 64) (enc : List (BitVec 8))
    (e : SignalProtocolError) (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8))) : SepProp :=
  ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ vecResultAt A (s.sp + 0x270#64) (.error e) ∗
  sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
  prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  FromRecordCallees.lsLogOff ∗
  memRegion outPtr 48 ∗
  memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x370#64) 36 ∗
  memRegion (s.sp + 0x930#64) 48 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
  stackAt s.sp growOneSpeStack

set_option maxHeartbeats 1200000 in
/-- Placed Substage P3.5 non-duplicate error path (`+0x1cd8 → s0.readReg64 .x30`) over a 1-element
`prevVecAt [enc]`. -/
theorem stageP3_sub5_err_nondup_prev1_placed_ok [LibsignalPlacement] {A : RustAlloc}
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
    (s0 s : State) (coroPtr outPtr initErrsPtr prevCap prevPtr : BitVec 64) (hinit_ne : initErrsPtr ≠ 0#64)
    (e : SignalProtocolError) (he_npan : e ≠ .panic) (htag_ne23 : speTag e ≠ speWord 23)
    (b_2c0 : BitVec 8) (enc : List (BitVec 8)) (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP3ErrPrePrev1Placed A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc e b_2c0 G₂ recG st₂ recSt)
      (fun sf P_f =>
        (P_f ⊢ stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr e) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  unfold stageP3ErrPrePrev1Placed stageP3ErrPostPrevEmptyM3Placed
  have hrec_err : SessionState.recordError .preKey e = .invalidMessage .preKey .decryptionFailed :=
    recordError_preKey_of_speTag_ne_speWord23 he_npan htag_ne23
  rw [hrec_err]; refine intro_lsro_decryptionFailed_prev1 hcro ?_
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
  refine bind_sepWP_lscro_frame hcro hstep1 (by sep_focus) fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, _, _, _, _, hx19_1, hx24_1, hx25_1, hx26_1, _, _, _, hx30_1, hvregs_1⟩
  refine P3P4.SepWPp.weaken_frame (words6_entails_memRegion48 (s.sp + 0x930#64) (speTag e) w0 w1 w2 w3 w4) (by sep_focus) ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  have hstack_log : stackAt s.sp growOneSpeStack =
      memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack :=
    stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine call_lscl_nopanic_prev1 (spec := pqxdhLogClosurePlacedSpec) (x := ()) (φ := True)
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
  refine bind_sepWP_lscro_frame hcro2 hstep3 (by sep_focus) fun s3 hpc3 hrun3 hcro3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hx0_3, hx19_3, hx21_3, hx24_3, hx25_3, hx26_3, _, _, _, hx30_3, hvregs_3⟩
  have hsp3_s : s3.sp = s.sp := hsp3_2
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3_s] using hsp_align
  have htr3_0 : s3.trace = s0.trace := htr3_2.trans (htr2_1.trans (htr1_s.trans htr))
  refine call_lscl_oom_prev1 (x := (s.sp + 0x3c8#64, 0#64, initErrsPtr, ([] : List (BitVec 8)))) (φ := True)
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
  refine bind_sepWP_lscro_frame hcro4 hstep5 (by sep_focus) fun s5 hpc5 hrun5 hcro5 hregs5 => ?_
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
  have halloc17 := p3_alloc_2eac_prev1_placed_ok (A := A) ext halloc hpanic s0 s5
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
  refine bind_sepWP_lscro_frame hcro6 hstep7 (by sep_focus) fun s7 hpc7 hrun7 hcro7 hregs7 => ?_
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
  refine call_lscl_nopanic_prev1 (x := (⟨s.sp + 0xa90#64, G₂, st₂⟩ : DropSessionStructureGhost))
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
  have htail := stageP3_err_tail_nondup_dec_prev1_placed_ok ext hdealloc hDropSS3
    s0 s8 coroPtr outPtr errsPtr prevCap prevPtr 17#64 (s6.readReg64 .x0) 17#64 w3' w4 e he_npan b_2c0 enc recG recSt
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
/-- Placed unified Substage P3.5 error path (`+0x1cd8 → s0.readReg64 .x30`) over a 1-element
`prevVecAt [enc]`. -/
theorem stageP3_sub5_err_prev1_placed_ok [LibsignalPlacement] {A : RustAlloc}
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
    (s0 s : State) (coroPtr outPtr initErrsPtr prevCap prevPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (e : SignalProtocolError) (he_npan : e ≠ .panic)
    (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP3ErrPrePrev1Placed A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc e b_2c0 G₂ recG st₂ recSt)
      (fun sf P_f =>
        (P_f ⊢ stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr e) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  by_cases htag23 : speTag e = speWord 23
  · obtain ⟨ratVer, counter, rfl⟩ := speTag_eq_speWord23_iff.mp htag23
    unfold stageP3ErrPrePrev1Placed stageP3ErrPostPrevEmptyM3Placed
    have hstack_drop2 : stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
      stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
    rw [hstack_drop2]
    have hdup := stageP3_sub5_err_dup_prev1_placed_ok ext hdealloc hDropSS3
      s0 s coroPtr outPtr initErrsPtr prevCap prevPtr ratVer counter b_2c0 enc G₂ recG st₂ recSt
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
  · exact stageP3_sub5_err_nondup_prev1_placed_ok ext hshim halloc hdealloc
      hGrow hDropSS3 hLogClosure hpanic
      s0 s coroPtr outPtr initErrsPtr prevCap prevPtr hinit_ne e he_npan htag23
      b_2c0 enc G₂ recG st₂ recSt hcro hpc hrun hsp_align htr hx19 hx24

/-! ## `[LibsignalFullPlacement]` / `LibsignalFrozen` Variants -/

set_option maxHeartbeats 1200000 in
theorem stageP3_sub5_err_nondup_prev1_full_placed_ok [LibsignalFullPlacement] {A : RustAlloc}
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
    (s0 s : State) (coroPtr outPtr initErrsPtr prevCap prevPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (e : SignalProtocolError) (he_npan : e ≠ .panic) (htag_ne23 : speTag e ≠ speWord 23)
    (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hfr : LibsignalFrozen lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP3ErrPrePrev1Placed A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc e b_2c0 G₂ recG st₂ recSt)
      (fun sf P_f =>
        (P_f ⊢ stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr e) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  have hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem := lscro_of_frozen hfr
  unfold stageP3ErrPrePrev1Placed stageP3ErrPostPrevEmptyM3Placed
  have hrec_err : SessionState.recordError .preKey e = .invalidMessage .preKey .decryptionFailed :=
    recordError_preKey_of_speTag_ne_speWord23 he_npan htag_ne23
  rw [hrec_err]; refine intro_lsro_decryptionFailed_prev1 hcro ?_
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
  refine bind_sepWP_lscro_frame hcro2 hstep3 (by sep_focus) fun s3 hpc3 hrun3 hcro3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hx0_3, hx19_3, hx21_3, hx24_3, hx25_3, hx26_3, _, _, _, hx30_3, hvregs_3⟩
  have hsp3_s : s3.sp = s.sp := hsp3_2
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3_s] using hsp_align
  have htr3_0 : s3.trace = s0.trace := htr3_2.trans (htr2_1.trans (htr1_s.trans htr))
  refine call_lscl_oom_prev1 (x := (s.sp + 0x3c8#64, 0#64, initErrsPtr, ([] : List (BitVec 8)))) (φ := True)
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
  refine bind_sepWP_lscro_frame hcro4 hstep5 (by sep_focus) fun s5 hpc5 hrun5 hcro5 hregs5 => ?_
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
  have halloc17 := p3_alloc_2eac_prev1_placed_ok (A := A) ext halloc hpanic s0 s5
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
  refine bind_sepWP_lscro_frame hcro6 hstep7 (by sep_focus) fun s7 hpc7 hrun7 hcro7 hregs7 => ?_
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
  refine call_lscl_nopanic_prev1 (x := (⟨s.sp + 0xa90#64, G₂, st₂⟩ : DropSessionStructureGhost))
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
  have htail := stageP3_err_tail_nondup_dec_prev1_placed_ok ext hdealloc hDropSS3
    s0 s8 coroPtr outPtr errsPtr prevCap prevPtr 17#64 (s6.readReg64 .x0) 17#64 w3' w4 e he_npan b_2c0 enc recG recSt
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
/-- `[LibsignalFullPlacement]` unified Substage P3.5 error path (`+0x1cd8 → s0.readReg64 .x30`) over
a 1-element `prevVecAt [enc]`, discharging `.rodata` from `LibsignalFrozen`. -/
theorem stageP3_sub5_err_prev1_full_placed_ok [LibsignalFullPlacement] {A : RustAlloc}
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
    (s0 s : State) (coroPtr outPtr initErrsPtr prevCap prevPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (e : SignalProtocolError) (he_npan : e ≠ .panic)
    (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hfr : LibsignalFrozen lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP3ErrPrePrev1Placed A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc e b_2c0 G₂ recG st₂ recSt)
      (fun sf P_f =>
        (P_f ⊢ stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr e) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  have hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem := lscro_of_frozen hfr
  by_cases htag23 : speTag e = speWord 23
  · obtain ⟨ratVer, counter, rfl⟩ := speTag_eq_speWord23_iff.mp htag23
    unfold stageP3ErrPrePrev1Placed stageP3ErrPostPrevEmptyM3Placed
    have hstack_drop2 : stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
      stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
    rw [hstack_drop2]
    have hdup := stageP3_sub5_err_dup_prev1_placed_ok ext hdealloc hDropSS3
      s0 s coroPtr outPtr initErrsPtr prevCap prevPtr ratVer counter b_2c0 enc G₂ recG st₂ recSt
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
  · exact stageP3_sub5_err_nondup_prev1_full_placed_ok ext hshim halloc hdealloc
      hGrow hDropSS3 hpanic
      s0 s coroPtr outPtr initErrsPtr prevCap prevPtr hinit_ne e he_npan htag23
      b_2c0 enc G₂ recG st₂ recSt hfr hpc hrun hsp_align htr hx19 hx24

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
