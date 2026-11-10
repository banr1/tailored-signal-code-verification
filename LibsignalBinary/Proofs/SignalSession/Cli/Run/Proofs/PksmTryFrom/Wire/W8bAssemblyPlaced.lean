/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssembly
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.LoopStepWPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailWPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCleanup
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ParseLemmas
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

/-!
# Relocatable `[LibsignalPlacement]` Top-Level Assembly (`pksmTryFromPlaced_ok_of_postLoop`)

Defines `PreKeyPostLoopOkWPlaced` and proves `pksmTryFromPlaced_ok_of_postLoop` on
`preKeyPlacedProg H` against `pksmTryFromSpecPlaced A`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## 1. `SepWPp` Post Combinators for `pksmTryFromSpecPlaced` -/

/-- The Err tail post (`sp`, callee-saved, `LibsignalCodeRoLoaded`, trace, `pksmErrE A fn x.ret e ∗ R`)
meets `(pksmTryFromSpecPlaced A).post` whenever `Pksm.pksmParse x.bytes = none`. -/
theorem w8b_errPost_placed [LibsignalPlacement] {A : RustAlloc}
    {x : RunCompose.PksmGhost} {s0 sf : State}
    {Pf R : SepProp} {fn : List (BitVec 8)} {e : SignalProtocolError}
    (hparse : Pksm.pksmParse x.bytes = none)
    (h : sf.sp = s0.sp ∧
      (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
      LibsignalCodeRoLoaded lsmpl sf.mem ∧ sf.trace = s0.trace ∧
      (Pf ⊢ (pksmErrE A fn x.ret e ∗ R) ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool ∗
        stackAt s0.sp preKeyTryFromStack)) :
    sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
      (Pf ⊢ (pksmTryFromSpecPlaced A).post x s0 sf) := by
  obtain ⟨hsp, hcs, _hcl, htr, hent⟩ := h
  refine ⟨hsp, hcs, Entails.trans hent ?_⟩
  dsimp only [pksmTryFromSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
  refine Entails.trans
    (sepConj_mono_left (pksmResAt_err_of_parse A fn x.ret x.bytes e R hparse)) ?_
  rw [pure_sepConj_of_true htr]
  change RunCompose.pksmResAt A x.ret (Pksm.pksmParse x.bytes) ∗
      (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool ∗ stackAt s0.sp preKeyTryFromStack ⊢
    RunCompose.pksmResAt A x.ret (Pksm.pksmParse x.bytes) ∗
      (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ stackAt s0.sp preKeyTryFromStack ∗ A.pool
  apply entails_of_eq; ac_rfl

/-- `w8b_errPost_placed` specialized to heap-free error payloads (`Pf ⊢ pksmErrE A fn x.ret e ∗ ...`). -/
theorem w8b_errPost_noHeap_placed [LibsignalPlacement] {A : RustAlloc}
    {x : RunCompose.PksmGhost} {s0 sf : State}
    {Pf : SepProp} {fn : List (BitVec 8)} {e : SignalProtocolError}
    (hparse : Pksm.pksmParse x.bytes = none)
    (h : sf.sp = s0.sp ∧
      (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
      LibsignalCodeRoLoaded lsmpl sf.mem ∧ sf.trace = s0.trace ∧
      (Pf ⊢ pksmErrE A fn x.ret e ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool ∗
        stackAt s0.sp preKeyTryFromStack)) :
    sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
      (Pf ⊢ (pksmTryFromSpecPlaced A).post x s0 sf) := by
  obtain ⟨hsp, hcs, _hcl, htr, hent⟩ := h
  refine ⟨hsp, hcs, Entails.trans hent ?_⟩
  dsimp only [pksmTryFromSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
  have herr : pksmErrE A fn x.ret e ⊢ RunCompose.pksmResAt A x.ret (Pksm.pksmParse x.bytes) := by
    simpa [sepConj_emp] using pksmResAt_err_of_parse A fn x.ret x.bytes e emp hparse
  refine Entails.trans (sepConj_mono_left herr) ?_
  rw [pure_sepConj_of_true htr]
  change RunCompose.pksmResAt A x.ret (Pksm.pksmParse x.bytes) ∗
      (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool ∗ stackAt s0.sp preKeyTryFromStack ⊢
    RunCompose.pksmResAt A x.ret (Pksm.pksmParse x.bytes) ∗
      (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ stackAt s0.sp preKeyTryFromStack ∗ A.pool
  apply entails_of_eq; ac_rfl

/-! ## 2. Post-loop interface (`+0x460`, decode Ok) -/

/-- Post-loop `Ok` continuation `+0x460 → ret` (`1120 → ret`) under `[LibsignalPlacement]`:
from the loop exit with `x24 = 0` and decoded `m` of `b1 :: bs1` (version byte `vb` in the
accepted window), `preKeyPlacedProg H` returns with `(pksmTryFromSpecPlaced A).post`. -/
def PreKeyPostLoopOkWPlaced [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks) : Prop :=
  ∀ (x : RunCompose.PksmGhost) (s0 s : State) (vb b1 : BitVec 8) (bs1 : List (BitVec 8))
    (m : ProtoPreKeySignalMessage),
    x.bytes = vb :: b1 :: bs1 → ¬ (vb >>> 4) < 3#8 → ¬ 4#8 < (vb >>> 4) →
    x.bytes.length < 2 ^ 32 →
    Pksm.decodeProto (b1 :: bs1) = some m →
    PreKeyLoopExitStatePlaced s0 (s0.sp - 608#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.ptr vb s →
    s.pc = (blkPl_111).base + 1120#64 →
    s.status = .Running →
    s.readReg64 .x24 = 0#64 →
    Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s
      (wirePreKeyOf A (s0.sp - 608#64 + 312#64) m ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 16 ∗
        memRegion (s0.sp - 608#64 + 440#64) 8 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        memRegion x.ret 248 ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗
        A.pool ∗ stackAt (s0.sp - 608#64) preKeyTryFromSubStack)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (pksmTryFromSpecPlaced A).post x s0 sf))
      (tryFromQp s0)

/-- Loop-exit glue under `[LibsignalPlacement]`: regroups `preKey_valid_to_460_placed_wpW`'s post
(+ the frame kept across `+0x000 → +0x460`) into the shape both `+0x460` continuations consume. -/
theorem w8b_loopExit_regroup_placed [LibsignalPlacement] (A : RustAlloc)
    (x : RunCompose.PksmGhost) (s0 : State) (vb b1 : BitVec 8) (bs1 : List (BitVec 8))
    (x24 : BitVec 64) (res : Option ProtoPreKeySignalMessage) (hcons : x.bytes = vb :: b1 :: bs1) :
    ((x.ptr ↦₈ vb) ∗
        preKeyLoopExitMem A (s0.sp - 608#64) (x.ptr + 1#64) (b1 :: bs1) x24 res ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0) ∗
      (memRegion x.ret 248 ∗ lsLogOff ∗ memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 - BitVec.ofNat 64 preKeyTryFromSubStack)
          (preKeyTryFromSubStack - Prost.skipFieldStackX 100)) ⊢
      (match res with
        | some m' => ⌜x24 = 0#64⌝ ∗ wirePreKeyOf A (s0.sp - 608#64 + 312#64) m'
        | none =>
          ⌜x24 ≠ 0#64⌝ ∗ decodeErrorAt A x24 ∗
            (∃∗ mErr, wirePreKeyOf A (s0.sp - 608#64 + 312#64) mErr)) ∗
      (memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 16 ∗
        memRegion (s0.sp - 608#64 + 440#64) 8 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        memRegion x.ret 248 ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗
        A.pool ∗ stackAt (s0.sp - 608#64) preKeyTryFromSubStack) := by
  have h440 := pointsTo64_entails_memRegion (s0.sp - 608#64 + 440#64) (s0.sp - 608#64 + 296#64)
  unfold preKeyLoopExitMem
  rw [hcons, stackAt_preKeyTryFromSubStack_skipField (s0.sp - 608#64)]
  simp only [pointsToBytes_cons]
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left h440))))
  apply entails_of_eq; ac_rfl

/-! ## 3. Entry → return & Top-Level `pksmTryFromPlaced_ok_of_postLoop` -/

/-- `PreKeySignalMessage::try_from` from `(blkPl_111).base` to `s0.readReg64 .x30`, every input (`< 2 ^ 32`). -/
theorem preKey_entry_to_ret_placed_wpX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hdeallocX : subroutine_ok (preKeyPlacedProg H) ((blkPl_111).ρ lsRustDeallocSym)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (rustDeallocExternSpecWithStack A extHookStack)))
    (hDropErr : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 4)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.dropDecodeErrorSpecX A)))
    (hLoopF4 : PreKeyDecodeLoopF4OkWPlaced A H)
    (hPost : PreKeyPostLoopOkWPlaced A H)
    {x : RunCompose.PksmGhost} {s0 : State}
    (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (blkPl_111).base)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = x.ptr)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s0
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248 ∗ lsLogOff ∗
        stackAt s0.sp preKeyTryFromStack ∗ A.pool)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (pksmTryFromSpecPlaced A).post x s0 sf))
      (tryFromQp s0) := by
  have hsplit : stackAt s0.sp preKeyTryFromStack =
      stackAt (s0.sp - 608#64) preKeyTryFromSubStack ∗ memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗ memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        memRegion (s0.sp - 608#64 + 512#64) 96 :=
    CryptoVerification.E2E.Pqxdh.ResponderWire.stackAt_preKeyTryFrom_split s0.sp
  rw [hsplit]
  by_cases hvalid : ∃ vb b1 bs1, x.bytes = vb :: b1 :: bs1 ∧
      ¬ (vb >>> 4) < 3#8 ∧ ¬ 4#8 < (vb >>> 4)
  · obtain ⟨vb, b1, bs1, hcons, hge3, hle4⟩ := hvalid
    rw [stackAt_preKeyTryFromSubStack_skipField (s0.sp - 608#64)]
    refine Wire.SepWPp.mono_pre
      (P' := ((x.ptr ↦ₛ x.bytes) ∗
          memRegion (s0.sp - 608#64 + 296#64) 152 ∗
          memRegion (s0.sp - 608#64 + 448#64) 64 ∗
          memRegion (s0.sp - 608#64 + 512#64) 96 ∗
          A.pool ∗ stackAt (s0.sp - 608#64) (Prost.skipFieldStackX 100)) ∗
        (memRegion x.ret 248 ∗ lsLogOff ∗ memRegion (s0.sp - 608#64) 296 ∗
          memRegion (s0.sp - 608#64 - BitVec.ofNat 64 preKeyTryFromSubStack)
            (preKeyTryFromSubStack - Prost.skipFieldStackX 100)))
      (by apply entails_of_eq; ac_rfl) ?_
    refine Wire.SepWPp.bind_frame_tryFrom
      (preKey_valid_to_460_placed_wpW hLoopF4 hcons hge3 hle4 hlt hpc hrun hsp hcl hx0 hx1 hx8) ?_
    intro s1 P1 hpc1 hrun1 ⟨hst1, hent1⟩
    refine Wire.SepWPp.mono_pre (sepConj_mono_left hent1) ?_; clear hent1
    refine Wire.SepWPp.mono_pre
      (w8b_loopExit_regroup_placed A x s0 vb b1 bs1 (s1.readReg64 .x24)
        (Pksm.decodeProto (b1 :: bs1)) hcons) ?_
    cases hdec : Pksm.decodeProto (b1 :: bs1) with
    | none =>
      have hv_ok : 0x30#8 ≤ vb ∧ vb ≤ 0x4f#8 :=
        (pksmParse_ver_ok_iff vb).mp (not_or.mpr ⟨hge3, hle4⟩)
      have hparse : Pksm.pksmParse x.bytes = none := by
        rw [hcons]; exact pksmParse_decodeNone hv_ok hdec
      simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
      refine Wire.SepWPp.exists_pre fun mErr => ?_
      refine Wire.SepWPp.pure_pre fun hx24_ne => ?_
      refine SepWPp.mono_post
        (Wire.SepWPp.mono_pre (by apply entails_of_eq; ac_rfl)
          (preKey_loopErr_460_placed_wpE (x := x) hdeallocX hDropErr hst1 hpc1 hrun1 rfl hx24_ne mErr)) ?_
      intro sf Pf _ _ hq
      exact w8b_errPost_placed hparse hq
    | some m =>
      simp only [sepConj_assoc]
      refine Wire.SepWPp.pure_pre fun hx24 => ?_
      exact hPost x s0 s1 vb b1 bs1 m hcons hge3 hle4 hlt hdec hst1 hpc1 hrun1 hx24
  · have herr : x.bytes = [] ∨ (∃ vb body, x.bytes = vb :: body ∧
        ((vb >>> 4) < 3#8 ∨ 4#8 < (vb >>> 4) ∨ body = [])) := by
      rcases hb : x.bytes with _ | ⟨vb, _ | ⟨b1, bs1⟩⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨vb, [], rfl, Or.inr (Or.inr rfl)⟩
      · refine Or.inr ⟨vb, b1 :: bs1, rfl, ?_⟩
        by_cases h3 : (vb >>> 4) < 3#8
        · exact Or.inl h3
        · by_cases h4 : 4#8 < (vb >>> 4)
          · exact Or.inr (Or.inl h4)
          · exact absurd ⟨vb, b1, bs1, hb, h3, h4⟩ hvalid
    refine Wire.SepWPp.mono_pre
      (P' := ((x.ptr ↦ₛ x.bytes) ∗
          memRegion x.ret 248 ∗
          memRegion (s0.sp - 608#64) 296 ∗
          memRegion (s0.sp - 608#64 + 296#64) 152 ∗
          memRegion (s0.sp - 608#64 + 512#64) 96) ∗
        (stackAt (s0.sp - 608#64) preKeyTryFromSubStack ∗
          memRegion (s0.sp - 608#64 + 448#64) 64 ∗ lsLogOff ∗ A.pool))
      (by apply entails_of_eq; ac_rfl) ?_
    refine Wire.SepWPp.bind_frame_tryFrom
      (preKey_earlyErr_to_504_placed_wpE (A := A) herr hlt hpc hrun hsp hcl hx0 hx1 hx8) ?_
    rintro s1 P1 hpc1 hrun1 ⟨hst1, hparse, e, hent1⟩
    refine Wire.SepWPp.mono_pre (sepConj_mono_left hent1) ?_; clear hent1
    refine SepWPp.mono_post
      (Wire.SepWPp.mono_pre (by apply entails_of_eq; ac_rfl)
        (epilogue_504_placed_w_wpX (A := A) (x := x) (R := pksmErrE A [] x.ret e) hst1 hpc1 hrun1)) ?_
    intro sf Pf _ _ hq
    exact w8b_errPost_noHeap_placed hparse hq

/-- `subroutine_ok (preKeyPlacedProg H) (blkPl_111).base (pksmTryFromSpecPlaced A)`
from the decode loop, the post-loop Ok path, and the dealloc / `DecodeError` drop contracts (`< 2 ^ 32`). -/
theorem pksmTryFromPlaced_ok_of_postLoop [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hdeallocX : subroutine_ok (preKeyPlacedProg H) ((blkPl_111).ρ lsRustDeallocSym)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (rustDeallocExternSpecWithStack A extHookStack)))
    (hDropErr : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 4)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.dropDecodeErrorSpecX A)))
    (hLoopF4 : PreKeyDecodeLoopF4OkWPlaced A H)
    (hPost : PreKeyPostLoopOkWPlaced A H) :
    subroutine_ok (preKeyPlacedProg H) (blkPl_111).base (pksmTryFromSpecPlaced A) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp hL
  obtain ⟨hcl, hpre'⟩ := LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
  dsimp only [pksmTryFromSpecPlaced] at hpre'
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx1_nat, hlt, hx8, _hsp_ge⟩, hmem⟩
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length := by
    rw [← hx1_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hmem' : s0.mem ⊨
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248 ∗ lsLogOff ∗
        stackAt s0.sp preKeyTryFromStack ∗ A.pool) ∗ R := by
    change s0.mem ⊨ (x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248 ∗ lsLogOff ∗
      stackAt s0.sp preKeyTryFromStack ∗ A.pool ∗ R at hmem
    ac_nf at hmem ⊢
  have hfull := preKey_entry_to_ret_placed_wpX hdeallocX hDropErr hLoopF4 hPost
    hlt hpc hrun hsp hcl hx0 hx1 hx8
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem' hL
  rcases hex with ⟨hpc_f, hrun_f, Pf, hmf, ⟨hsp_f, hcs_f, hent_f⟩, hvregs_f⟩ | ⟨hpan, Pf, hmf, htr_f⟩ | ⟨_, hoom⟩
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f hvregs_f⟩,
      Satisfies.mono (sepConj_mono_left hent_f) hmf⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, htr_f R hmf⟩)⟩
  · exact (allowPanic_not_exited hoom).elim

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
