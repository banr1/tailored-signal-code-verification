/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1State
public import LibsignalBinary.Proofs.Placed.PlacedCallSym
public import LibsignalBinary.Proofs.TripleRatchet.Prog
public import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ProtoReprCodeSym -- shake: keep

/-!
# Code-Symbol Fetch and `BL` Call Bridges for `EncodedLen`

Provides `[LibsignalPlacement]` dual-block instruction fetch helpers, `FrozenInv`-preserving
`SepWPpF` / `CallPinnedEncLenAtF` `BL` call bridges, and the `V1State::encoded_len` `.rodata`
jump-table `ADRP + ADD` step (`+56..+64`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000


namespace CryptoVerification
set_option maxRecDepth 2000000
gen_ls_blk 177
gen_ls_blk 179
gen_ls_blk 188
gen_ls_blk 405
gen_ls_blk 407
gen_ls_blk 414
end CryptoVerification

namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open EncodedLen

local notation "tripleRatchetProgAtExt" => CryptoVerification.LibsignalTripleRatchet.contractProg

/-- Entry-point membership covering both `libsignalSessionCode.rebase b (Rust.withPanics abs)` at
    `fn1` / `fn2` and `[LibsignalPlacement]` block programs `pc1.rebase b1 H` / `pc2.rebase b2 H`. -/
def IsDualBlockEntryP2 (fn1 fn2 : String)
    (pc1 pc2 : [LibsignalPlacement] → Program)
    (b1 b2 : [LibsignalPlacement] → BitVec 64)
    (prog : Program) (entry : BitVec 64) : Prop :=
  (∃ b abs, prog = tripleRatchetProgAtExt b abs ∧
    ((tripleRatchetProgAtExt b abs).fnAddr fn1 = entry ∨
     (tripleRatchetProgAtExt b abs).fnAddr fn2 = entry)) ∨
  (∃ (inst : LibsignalPlacement) (H : String → Option (State → State)),
    (prog = (@pc1 inst).rebase (@b1 inst) H ∧ entry = @b1 inst) ∨
    (prog = (@pc2 inst).rebase (@b2 inst) H ∧ entry = @b2 inst))

theorem dualBlockP2_fetch_entry {fn1 fn2 : String}
    {pc1 pc2 : [LibsignalPlacement] → Program}
    {b1 b2 : [LibsignalPlacement] → BitVec 64} {prog : Program} {entry : BitVec 64}
    (hfn : IsDualBlockEntryP2 fn1 fn2 pc1 pc2 b1 b2 prog entry) {ins : Instr}
    (h1 : ∀ b H, (libsignalSessionCode.rebase b H).fetch
      ((libsignalSessionCode.rebase b H).fnAddr fn1) = some ins)
    (h2 : ∀ b H, (libsignalSessionCode.rebase b H).fetch
      ((libsignalSessionCode.rebase b H).fnAddr fn2) = some ins)
    (h3 : ∀ [LibsignalPlacement] H, (pc1.rebase b1 H).fetch b1 = some ins)
    (h4 : ∀ [LibsignalPlacement] H, (pc2.rebase b2 H).fetch b2 = some ins) :
    prog.fetch entry = some ins := by
  rcases hfn with ⟨b, abs, rfl, rfl | rfl⟩ | ⟨inst, H, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact h1 b _
  · exact h2 b _
  · exact @h3 inst H
  · exact @h4 inst H

theorem dualBlockP2_fetch_add {fn1 fn2 : String}
    {pc1 pc2 : [LibsignalPlacement] → Program}
    {b1 b2 : [LibsignalPlacement] → BitVec 64} {prog : Program} {entry : BitVec 64}
    (hfn : IsDualBlockEntryP2 fn1 fn2 pc1 pc2 b1 b2 prog entry) {k : Nat} {ins : Instr}
    (h1 : ∀ b H, (libsignalSessionCode.rebase b H).fetch
      ((libsignalSessionCode.rebase b H).fnAddr fn1 + BitVec.ofNat 64 k) = some ins)
    (h2 : ∀ b H, (libsignalSessionCode.rebase b H).fetch
      ((libsignalSessionCode.rebase b H).fnAddr fn2 + BitVec.ofNat 64 k) = some ins)
    (h3 : ∀ [LibsignalPlacement] H, (pc1.rebase b1 H).fetch (b1 + BitVec.ofNat 64 k) = some ins)
    (h4 : ∀ [LibsignalPlacement] H, (pc2.rebase b2 H).fetch (b2 + BitVec.ofNat 64 k) = some ins) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with ⟨b, abs, rfl, rfl | rfl⟩ | ⟨inst, H, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact h1 b _
  · exact h2 b _
  · exact @h3 inst H
  · exact @h4 inst H

abbrev IsChunkedCt1SampledEntryP2 (prog : Program) (entry : BitVec 64) : Prop :=
  IsDualBlockEntryP2
    chunkedCt1SampledEncodedLenLocal1Name chunkedCt1SampledEncodedLenLocal2Name
    (fun [LibsignalPlacement] => blkPC_179) (fun [LibsignalPlacement] => blkPC_407)
    (fun [LibsignalPlacement] => (blkPl_179).base) (fun [LibsignalPlacement] => (blkPl_407).base)
    prog entry

abbrev IsChunkedHeaderSentEntryP2 (prog : Program) (entry : BitVec 64) : Prop :=
  IsDualBlockEntryP2
    chunkedHeaderSentEncodedLenLocal1Name chunkedHeaderSentEncodedLenLocal2Name
    (fun [LibsignalPlacement] => blkPC_188) (fun [LibsignalPlacement] => blkPC_414)
    (fun [LibsignalPlacement] => (blkPl_188).base) (fun [LibsignalPlacement] => (blkPl_414).base)
    prog entry

abbrev IsV1StateEntryP2 (prog : Program) (entry : BitVec 64) : Prop :=
  IsDualBlockEntryP2
    v1StateEncodedLenLocal1Name v1StateEncodedLenLocal2Name
    (fun [LibsignalPlacement] => blkPC_177) (fun [LibsignalPlacement] => blkPC_405)
    (fun [LibsignalPlacement] => (blkPl_177).base) (fun [LibsignalPlacement] => (blkPl_405).base)
    prog entry

/-! ## `SepWPpF`: `KeepsFrozen`-Stable Memory Invariant Threading for `SepWPp` -/

class FrozenInv (Φ : Memory → Prop) : Prop where
  keeps : ∀ {m m' : Memory}, Φ m → m.KeepsFrozen m' → Φ m'

instance instFrozenInvTrue : FrozenInv (fun _ => True) where
  keeps h _ := h

instance instFrozenInvLsCl (pl : MultiPlacement) : FrozenInv (LibsignalCodeLoaded pl) where
  keeps h hkf := h.of_keepsFrozen hkf

def SepWPpF (Φ : Memory → Prop) (prog : Program) (ret : BitVec 64) (s : State) (P : SepProp)
    (Q Qp : State → SepProp → Prop) (oom : State → SepProp := fun _ => ⌜False⌝) : Prop :=
  Φ s.mem → SepWPp prog ret s P (fun sf Pf => Φ sf.mem ∧ Q sf Pf) Qp oom

namespace SepWPpF

variable {Φ : Memory → Prop} {prog : Program} {ret : BitVec 64} {s : State} {P P' : SepProp}
  {Q Qp : State → SepProp → Prop} {oom : State → SepProp}

theorem of_sepWP [hinv : FrozenInv Φ] {mid : BitVec 64}
    (h : SepWP prog mid s P (fun sm Pm => SepWPpF Φ prog ret sm Pm Q Qp oom) oom) :
    SepWPpF Φ prog ret s P Q Qp oom := by
  intro hΦ
  exact SepWPp.seq_frozen (fun _ _ h hkf => hinv.keeps h hkf) hΦ h

theorem done (hpc : s.pc = ret) (hrun : s.status = .Running) (hq : Q s P) :
    SepWPpF Φ prog ret s P Q Qp oom := by
  intro hΦ
  exact SepWPp.done hpc hrun ⟨hΦ, hq⟩

theorem congr_pre (heq : P = P') (h : SepWPpF Φ prog ret s P' Q Qp oom) :
    SepWPpF Φ prog ret s P Q Qp oom := by
  subst heq; exact h

theorem iff_sepWPp_true :
    SepWPpF (fun _ => True) prog ret s P Q Qp oom ↔ SepWPp prog ret s P Q Qp oom := by
  unfold SepWPpF
  simp only [true_and, forall_true_left]

end SepWPpF

theorem subroutine_ok_of_sepWPpF_true {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
        SepWPpF (fun _ => True) prog (s0.readReg64 Reg.lr) s0 P
          (fun sf P_f => ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    subroutine_ok prog entry spec := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  obtain ⟨P, Fr, hm, hwp⟩ := h x R s0 hpc hrun hpre hsp
  exact ⟨P, Fr, hm, SepWPpF.iff_sepWPp_true.mp hwp⟩

theorem subroutine_ok_of_sepWPpF_lscl {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : MultiPlacement} {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
        SepWPpF (LibsignalCodeLoaded pl) prog (s0.readReg64 Reg.lr) s0 P
          (fun sf P_f => ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    subroutine_ok prog entry (withLsCodeLoaded pl spec) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  obtain ⟨hcl0, hpre'⟩ := extract_withLsCodeLoaded hpre
  obtain ⟨P, Fr, hm, hwp⟩ := h x R s0 hpc hrun hpre' hsp
  refine ⟨P, Fr, hm, ?_⟩
  have hwp0 := hwp hcl0
  intro Fr' hm' hL
  obtain ⟨sf, hsteps, hout⟩ := hwp0 Fr' hm' hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, ⟨_, hq⟩⟩ | hpan | hoom
  · exact Or.inl ⟨hpcf, hrunf, P_f, hmf, hq⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hoom)

/-! ## `CallPinnedEncLenAtF`: `BL` Call Bridge with `FrozenInv Φ` -/

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

/-- Abstracted `BL` call at offset `k` from `entry` to a pinned `encoded_len` callee with
    representation `repr`, pure model `encLen`, stack requirement `stackSz`, and `FrozenInv Φ`. -/
def CallPinnedEncLenAtF (Φ : Memory → Prop) (prog : Program) (entry : BitVec 64) (k : Nat)
    {Ghost Model : Type} (repr : Ghost → BitVec 64 → Model → SepProp)
    (encLen : Model → Nat) (stackSz : Nat) : Prop :=
  ∀ (ret : BitVec 64) (g : Ghost) (a sp : BitVec 64) (m : Model) (s : State) (F : SepProp)
    (Q Qp : State → SepProp → Prop),
    s.pc = entry + BitVec.ofNat 64 k →
    s.status = .Running →
    s.sp = sp →
    sp &&& 15#64 = 0#64 →
    s.readReg64 .x0 = a →
    encLen m < 2 ^ 64 →
    (∀ sf : State,
      sf.pc = entry + BitVec.ofNat 64 (k + 4) →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (encLen m) →
      EpochEncLenCalleeSaved s sf →
      sf.readReg64 .fp = s.readReg64 .fp →
      SepWPpF Φ prog ret sf ((repr g a m ∗ stackAt sp stackSz) ∗ F) Q Qp) →
    SepWPpF Φ prog ret s ((repr g a m ∗ stackAt sp stackSz) ∗ F) Q Qp

theorem callPinnedEncLenAtF_of_bl {Φ : Memory → Prop} [FrozenInv Φ]
    {prog : Program} {entry calleeAddr : BitVec 64} {k : Nat} {disp : BitVec 64}
    {Ghost Model : Type} {repr : Ghost → BitVec 64 → Model → SepProp}
    {encLen : Model → Nat} {stackSz : Nat} {spec : Spec (PinnedEncLenGhost Ghost Model)}
    (hspec_pre : ∀ x s, spec.pre x s =
      (⌜s.readReg64 .x0 = x.a ∧ encLen x.m < 2 ^ 64⌝ ∗ repr x.g x.a x.m ∗ stackAt s.sp stackSz))
    (hspec_post : ∀ x s0 sf, spec.post x s0 sf =
      (⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encLen x.m) ∧ sf.trace = s0.trace⌝ ∗
        repr x.g x.a x.m ∗ stackAt s0.sp stackSz))
    (hspec_panic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝)
    (hspec_exit : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝)
    (hfetch : prog.fetch (entry + BitVec.ofNat 64 k) = some (.bl disp))
    (htarget : entry + BitVec.ofNat 64 k + disp = calleeAddr)
    (hcallee : subroutine_ok prog calleeAddr spec)
    (hspec_oom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    CallPinnedEncLenAtF Φ prog entry k repr encLen stackSz := by
  intro ret g a sp m s F Q Qp hpc hrun hsp halign hx0 hbound hcont
  subst hsp
  apply SepWPpF.of_sepWP (mid := entry + BitVec.ofNat 64 (k + 4))
  wp_steps
  have hlr_eq : entry + BitVec.ofNat 64 k + 4#64 = entry + BitVec.ofNat 64 (k + 4) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  refine SepWP.call_subroutine_frame (x := ⟨a, g, m⟩) (F := F)
    (ret_pc := entry + BitVec.ofNat 64 (k + 4)) hcallee
    (by simp_all) (by simp_all)
    (by simp only [State.spAligned, beq_iff_eq]; simp_all)
    (by simp_all) ?_ ?_ ?_ ?_ (h_oom := ?_)
  · intro R hm
    rw [hspec_pre]
    simp only [sepConj_assoc, satisfies_pure_sepConj, arm64_norm]
    refine ⟨⟨by simp_all, hbound⟩, ?_⟩
    convert hm using 1
    · ac_rfl
    · rfl
  · intro R' sf _ hpan
    rw [hspec_panic, satisfies_pure_sepConj] at hpan
    exact hpan.1
  · intro R' code sf _ hex
    rw [hspec_exit, satisfies_pure_sepConj] at hex
    exact hex.1
  · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
    rw [hspec_post]
    simp only [arm64_norm] at hsp_sf ⊢
    apply SepWP.weaken_pre (P' := ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encLen m) ∧ sf.trace = s.trace⌝ ∗
        ((repr g a m ∗ stackAt s.sp stackSz) ∗ F))
    · exact Entails.of_eq (by ac_rfl)
    · apply SepWP.pure_elim
      rintro ⟨hx0_sf, htr_sf⟩
      apply SepWP.done hpc_sf hrun_sf
      have ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hv⟩ := hcs_sf
      have hcs_saved : EpochEncLenCalleeSaved s sf := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all
      have hfp_sf : sf.readReg64 .fp = s.readReg64 .fp := by
        simp_all
      exact hcont sf hpc_sf hrun_sf hsp_sf htr_sf hx0_sf hcs_saved hfp_sf
  · intro R' sf _ hoom
    rw [hspec_oom] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

theorem callPinnedEncLenAtF_of_bl_lscl [LibsignalPlacement]
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {k : Nat} {disp : BitVec 64}
    {Ghost Model : Type} {repr : Ghost → BitVec 64 → Model → SepProp}
    {encLen : Model → Nat} {stackSz : Nat} {spec : Spec (PinnedEncLenGhost Ghost Model)}
    (hspec_pre : ∀ x s, spec.pre x s =
      (⌜s.readReg64 .x0 = x.a ∧ encLen x.m < 2 ^ 64⌝ ∗ repr x.g x.a x.m ∗ stackAt s.sp stackSz))
    (hspec_post : ∀ x s0 sf, spec.post x s0 sf =
      (⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encLen x.m) ∧ sf.trace = s0.trace⌝ ∗
        repr x.g x.a x.m ∗ stackAt s0.sp stackSz))
    (hspec_panic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝)
    (hspec_exit : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝)
    (hfetch : callerProg.fetch (entry + BitVec.ofNat 64 k) = some (.bl disp))
    (htarget : entry + BitVec.ofNat 64 k + disp = lsmpl.base j)
    (hcallee : subroutine_ok calleeProg (lsmpl.base j) (withLsCodeLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide)
    (hspec_oom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) callerProg entry k repr encLen stackSz := by
  intro ret g a sp m s F Q Qp hpc hrun hsp halign hx0 hbound hcont hcl0
  subst hsp
  have hcall : subroutine_ok callerProg (lsmpl.base j) (withMemEq s.mem spec) :=
    lscall_blk_cl (callerProg := callerProg) hcallee hcl0 hi hj hj_unmut
  apply SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl0
    (mid := entry + BitVec.ofNat 64 (k + 4))
  wp_steps
  have hlr_eq : entry + BitVec.ofNat 64 k + 4#64 = entry + BitVec.ofNat 64 (k + 4) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  refine SepWP.call_subroutine_frame (x := ⟨a, g, m⟩) (F := F)
    (ret_pc := entry + BitVec.ofNat 64 (k + 4)) hcall
    (by simp_all) (by simp_all)
    (by simp only [State.spAligned, beq_iff_eq]; simp_all)
    (by simp_all) ?_ ?_ ?_ ?_ (h_oom := ?_)
  · intro R hm
    dsimp only [withMemEq]
    rw [sepConj_assoc, sepConj_left_comm (spec.pre _ _) ⌜_ = s.mem⌝, satisfies_pure_sepConj]
    refine ⟨rfl, ?_⟩
    rw [hspec_pre]
    simp only [sepConj_assoc, satisfies_pure_sepConj, arm64_norm]
    refine ⟨⟨by simp_all, hbound⟩, ?_⟩
    convert hm using 1
    · ac_rfl
    · rfl
  · intro R' sf _ hpan
    dsimp only [withMemEq] at hpan
    rw [hspec_panic, satisfies_pure_sepConj] at hpan
    exact hpan.1
  · intro R' code sf _ hex
    dsimp only [withMemEq] at hex
    rw [hspec_exit, satisfies_pure_sepConj] at hex
    exact hex.1
  · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
    dsimp only [withMemEq]
    rw [hspec_post]
    simp only [arm64_norm] at hsp_sf ⊢
    apply SepWP.weaken_pre (P' := ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encLen m) ∧ sf.trace = s.trace⌝ ∗
        ((repr g a m ∗ stackAt s.sp stackSz) ∗ F))
    · exact Entails.of_eq (by ac_rfl)
    · apply SepWP.pure_elim
      rintro ⟨hx0_sf, htr_sf⟩
      apply SepWP.done hpc_sf hrun_sf
      have ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hv⟩ := hcs_sf
      have hcs_saved : EpochEncLenCalleeSaved s sf := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all
      have hfp_sf : sf.readReg64 .fp = s.readReg64 .fp := by
        simp_all
      intro hcl_sf
      exact hcont sf hpc_sf hrun_sf hsp_sf htr_sf hx0_sf hcs_saved hfp_sf hcl_sf
  · intro R' sf _ hoom
    dsimp only [withMemEq] at hoom
    rw [hspec_oom] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

theorem callPinnedEncLenAtF_of_bl_plain [LibsignalPlacement]
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {k : Nat} {disp : BitVec 64}
    {Ghost Model : Type} {repr : Ghost → BitVec 64 → Model → SepProp}
    {encLen : Model → Nat} {stackSz : Nat} {spec : Spec (PinnedEncLenGhost Ghost Model)}
    (hspec_pre : ∀ x s, spec.pre x s =
      (⌜s.readReg64 .x0 = x.a ∧ encLen x.m < 2 ^ 64⌝ ∗ repr x.g x.a x.m ∗ stackAt s.sp stackSz))
    (hspec_post : ∀ x s0 sf, spec.post x s0 sf =
      (⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encLen x.m) ∧ sf.trace = s0.trace⌝ ∗
        repr x.g x.a x.m ∗ stackAt s0.sp stackSz))
    (hspec_panic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝)
    (hspec_exit : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝)
    (hfetch : callerProg.fetch (entry + BitVec.ofNat 64 k) = some (.bl disp))
    (htarget : entry + BitVec.ofNat 64 k + disp = lsmpl.base j)
    (hcallee : subroutine_ok calleeProg (lsmpl.base j) spec)
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide)
    (hspec_oom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) callerProg entry k repr encLen stackSz :=
  callPinnedEncLenAtF_of_bl_lscl hspec_pre hspec_post hspec_panic hspec_exit
    hfetch htarget (subroutine_ok_withLsCodeLoaded_of_plain hcallee) hi hj hj_unmut hspec_oom

/-! ## `V1State::encoded_len` Jump Table `.rodata` & `ADRP + ADD` Step (`+56..+64`) -/

abbrev v1StateJtSymLocal1 : String :=
  "libsignal_session:.rodata.<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len"

abbrev v1StateJtSymLocal2 : String :=
  "spqr:.rodata.<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len"

theorem v1StateJumpTableBytes_lsro_local1_intro {pl : MultiPlacement} {m : Memory}
    (hro : LibsignalRoLoaded pl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ (pl.ρ v1StateJtSymLocal1 ↦ᵣ v1StateJumpTableBytes) ∗ P :=
  lsro_slice_intro hro (sym := v1StateJtSymLocal1) (off := 0) (by simp) (by decide +kernel) hP

theorem v1StateJumpTableBytes_lsro_local2_intro {pl : MultiPlacement} {m : Memory}
    (hro : LibsignalRoLoaded pl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ (pl.ρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗ P :=
  lsro_slice_intro hro (sym := v1StateJtSymLocal2) (off := 0) (by simp) (by decide +kernel) hP

/-- Bundles the two-instruction step at `+56..+64` (`ADRP X9, jt; ADD X9, X9, #loOff`) loading
    `roBase` into `X9`, covering both `tripleRatchetProgAtExt b abs` and `[LibsignalPlacement]`
    relaxable `pairStep_0x38`. -/
def HasJumpTableStepP2 (prog : Program) (entry roBase : BitVec 64) : Prop :=
  ∀ (s : State) (P : SepProp) (post : State → SepProp → Prop) (oom : State → SepProp),
    s.pc = entry + 56#64 →
    s.status = .Running →
    SepWP prog (entry + 64#64) ((s.writeReg64 .x9 roBase).setPC (entry + 64#64)) P post oom →
    SepWP prog (entry + 64#64) s P post oom

theorem hasJumpTableStepP2_placed_local1 [LibsignalPlacement] (H : LibsignalHooks) :
    HasJumpTableStepP2 ((blkPC_177).rebase (blkPl_177).base H) (blkPl_177).base
      (lsρ v1StateJtSymLocal1) := by
  intro s P post oom hpc hrun hnext
  exact blkPC_177_pairStep_0x38 (blkPl_177).base H rfl hpc hrun hnext

theorem hasJumpTableStepP2_placed_local2 [LibsignalPlacement] (H : LibsignalHooks) :
    HasJumpTableStepP2 ((blkPC_405).rebase (blkPl_405).base H) (blkPl_405).base
      (lsρ v1StateJtSymLocal2) := by
  intro s P post oom hpc hrun hnext
  exact blkPC_405_pairStep_0x38 (blkPl_405).base H rfl hpc hrun hnext

/-- Bundles the `ADRP X9` (`+56`) and `ADD X9, X9, #loOff` (`+60`) instructions and their
    resolved `.rodata` jump-table base address `roBase`. -/
def HasJumpTableAddr (b : BitVec 64) (abs : String → Option (State → State))
    (entry roBase : BitVec 64) : Prop :=
  ∃ (pageOff : BitVec 64) (loOff : BitVec 12),
    (tripleRatchetProgAtExt b abs).fetch (entry + 56#64) =
      some (.adr true .x9 pageOff) ∧
    (tripleRatchetProgAtExt b abs).fetch (entry + 60#64) =
      some (.addSubImm .W64 .ADD .x9 .x9 loOff false) ∧
    ((entry + 56#64) &&& 0xfffffffffffff000#64) + pageOff + loOff.zeroExtend 64 = roBase

theorem hasJumpTableStepP2_of_addr {b : BitVec 64} {abs : String → Option (State → State)}
    {entry roBase : BitVec 64} (hjt : HasJumpTableAddr b abs entry roBase) :
    HasJumpTableStepP2 (tripleRatchetProgAtExt b abs) entry roBase := by
  rcases hjt with ⟨pageOff, loOff, hf56, hf60, hro⟩
  intro s P post oom hpc hrun hnext
  wp_steps
  exact hnext

theorem subroutine_ok_unpin_lscl {Model Ghost : Type} {prog : Program} {entry : BitVec 64}
    {pl : MultiPlacement}
    {pinnedSpec : Spec (PinnedEncLenGhost Ghost Model)}
    {unpinnedSpec : Spec (BitVec 64 × Model)}
    (hpre_eq : ∀ a m s0, unpinnedSpec.pre (a, m) s0 = ∃∗ g, pinnedSpec.pre ⟨a, g, m⟩ s0)
    (hpost_eq : ∀ a m s0 sf, unpinnedSpec.post (a, m) s0 sf = ∃∗ g, pinnedSpec.post ⟨a, g, m⟩ s0 sf)
    (hpinned_pan : ∀ x s0 sf, pinnedSpec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hpinned_ex : ∀ x code s0 sf, pinnedSpec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hpinned_oom : ∀ x s0 sf, pinnedSpec.onOom x s0 sf = ⌜False⌝ := by intros; rfl)
    (hpinned : subroutine_ok prog entry (withLsCodeLoaded pl pinnedSpec)) :
    subroutine_ok prog entry (withLsCodeLoaded pl unpinnedSpec) := by
  apply subroutine_ok_outcome_intro
  intro ⟨a, m⟩ R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [hpre_eq, sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨a, g, m⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded] at hpost ⊢
    rw [hpost_eq, sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · dsimp only [withLsCodeLoaded] at hpost
    rw [hpinned_pan, satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · dsimp only [withLsCodeLoaded] at hpost
    rw [hpinned_ex, satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · dsimp only [withLsCodeLoaded] at hpost
    rw [hpinned_oom, satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1

end CryptoVerification.SpqrV1.ProtoRepr
