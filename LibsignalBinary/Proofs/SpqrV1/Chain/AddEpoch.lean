/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpers
public import LibsignalBinary.Proofs.SpqrV1.Chain.ChainPbCodeSym
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import LibsignalBinary.Proofs.SpqrV1.Auth.SpqrAuthCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# Verification of `<spqr::chain::Chain>::add_epoch`

Proves the fixed-image (`chainAddEpoch_ok_of_contracts_x`, `chainAddEpoch_ok_ext_x`) and
relocatable `[LibsignalPlacement]` (`chainAddEpoch_placed_ok_of_contracts_x`,
`chainAddEpoch_placed_ok`) contracts for `<spqr::chain::Chain>::add_epoch` (`0x61004`, Block `368`,
148 instructions).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ChainProofs

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (toBEBytes)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open ChainAddEpochFacts
open ChainNewFacts
open NextKeyInternalFacts
open AgreeStateSimp

gen_decodes libsignalSessionCode_tree libsignalSessionBin [0x5bc0c → 0x5be5c]

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-- Registers preserved across the `b.eq 0x611fc` (`VecDeque::grow`) branch to `0x61160`. -/
@[arm64_norm, wp_norm]
def RegsAt348 (s sf : State) : Prop :=
  sf.readReg64 (.gpr 0#5) = s.readReg64 (.gpr 0#5) ∧
  sf.readReg64 (.gpr 8#5) = s.readReg64 (.gpr 8#5) ∧
  sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
  sf.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
  sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
  sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
  sf.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
  sf.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
  sf.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
  sf.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
  calleeSavedVRegs sf = calleeSavedVRegs s

theorem SepWPp.join_at_348 {prog : Program} {img : Obj.Image}
    {join_pc target_pc cap1 : BitVec 64} {s : State} {P P_join : SepProp}
    {post panic_post : State → SepProp → Prop}
    (hF : ImgCallInv img s)
    (hreach : SepWPp prog join_pc s P
      (fun sm Pm => sm.sp = s.sp ∧ RegsAt348 s sm ∧
        sm.readReg64 (.gpr 9#5) = cap1 ∧
        sm.trace = s.trace ∧ (Pm ⊢ P_join))
      panic_post)
    (hnext : ∀ sf : State, sf.pc = join_pc → sf.status = .Running →
      sf.sp = s.sp → RegsAt348 s sf → sf.readReg64 (.gpr 9#5) = cap1 → ImgCallInv img sf →
      SepWPp prog target_pc sf (⌜sf.trace = s.trace⌝ ∗ P_join) post panic_post) :
    SepWPp prog target_pc s P post panic_post := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hspm, hregm, hcapm, htrm, hent⟩ | hpan⟩ :=
    hreach R hm hL
  · have hmm' : sm.mem ⊨ (⌜sm.trace = s.trace⌝ ∗ P_join) ∗ R := by
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨htrm, Satisfies.mono (sepConj_mono_left hent) hmm⟩
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hregm hcapm (hF.of_steps hsteps) R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr hpan⟩

theorem allowPanic_addEpoch_err {hkdf : HkdfFn} {self : Chain} {epochSecret : EpochSecret}
    {Q : Prop} {s0 sf : State} {P R : SepProp}
    (herr : (Chain.addEpoch hkdf self epochSecret).isOk = false)
    (htr : (Rust.panicked sf).trace = s0.trace)
    (hm : (Rust.panicked sf).mem ⊨ P ∗ R) :
    (Rust.panicked sf).mem ⊨
      ⌜((Chain.addEpoch hkdf self epochSecret).isOk = false ∧ (Rust.panicked sf).trace = s0.trace) ∨ Q⌝ ∗
        anyHeap ∗ R := by
  rw [satisfies_pure_sepConj]
  exact ⟨Or.inl ⟨herr, htr⟩, Satisfies.mono (sepConj_mono_left (entails_anyHeap P)) hm⟩

theorem allowPanic_addEpoch_oom {P₀ : Prop} {s0 sf : State} {P R : SepProp}
    (hoom : allocFailedIn s0 (Rust.panicked sf) ∧ s0.trace <+: (Rust.panicked sf).trace)
    (hm : (Rust.panicked sf).mem ⊨ P ∗ R) :
    (Rust.panicked sf).mem ⊨
      ⌜P₀ ∨ (allocFailedIn s0 (Rust.panicked sf) ∧ s0.trace <+: (Rust.panicked sf).trace)⌝ ∗
        anyHeap ∗ R := by
  rw [satisfies_pure_sepConj]
  exact ⟨Or.inr hoom, Satisfies.mono (sepConj_mono_left (entails_anyHeap P)) hm⟩

theorem SepWP.bind_cell64 {prog : Program} {pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} (a : BitVec 64) {v : BitVec 64}
    (hf : P = (a ↦₆₄ v) ∗ F)
    (h : ∀ x : BitVec 64, SepWP prog pc s ((a ↦₆₄ x) ∗ F) post) :
    SepWP prog pc s P post := by
  rw [hf]; exact h v

theorem SepWPp.exists_left {α : Type} {prog : Program} {pc : BitVec 64} {s : State}
    {P : α → SepProp} {F : SepProp} {post panic_post : State → SepProp → Prop}
    (h : ∀ x : α, SepWPp prog pc s (P x ∗ F) post panic_post) :
    SepWPp prog pc s ((∃∗ x : α, P x) ∗ F) post panic_post := by
  intro R hm hL
  rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨x, hmx⟩
  exact h x R hmx hL

theorem SepWPp.reassoc_panic {prog : Program} {pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {Q : State → SepProp} {H R : SepProp}
    (h : SepWPp prog pc s P post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (Q sf ∗ H) ∗ R))) :
    SepWPp prog pc s P post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Q sf ∗ H ∗ R)) := by
  simpa only [sepConj_assoc] using h

open Lean Elab Tactic in
elab "wpp_call_inImage_addEpoch' " hcall:term:max a:term:max hF:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    apply (NextKeyInternalFacts.SepWPp.call_allowPanic_inImage_ret $hcall (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_inImage_addEpoch': unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; apply onPanic_addEpoch_of_trace_eq; wp_norm_lhs)
    wp_focus_close (wp_unfold_specs; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

theorem physIdx_madd_eq {head cap ptr : BitVec 64} {len : Nat}
    (hhead : head.toNat < cap.toNat) (hlen : len < cap.toNat)
    (hcap : cap.toNat * 112 < 2 ^ 63) :
    ptr + (head + BitVec.ofNat 64 len -
      if BitVec.ult (head + BitVec.ofNat 64 len) cap = true then 0#64 else cap) * 112#64 =
      ptr + BitVec.ofNat 64 (vecDequePhysIdx head.toNat cap.toNat len * 112) := by
  apply congrArg (ptr + ·)
  have hsum_lt : head.toNat + len < 18446744073709551616 := by omega
  have hlen_lt : len < 18446744073709551616 := by omega
  have hsum_toNat : (head + BitVec.ofNat 64 len).toNat = head.toNat + len := by
    simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen_lt, Nat.mod_eq_of_lt hsum_lt]
  have hult :
      BitVec.ult (head + BitVec.ofNat 64 len) cap =
        decide (head.toNat + len < cap.toNat) := by
    simp [BitVec.ult, hsum_toNat]
  rw [hult]
  unfold vecDequePhysIdx
  by_cases hlt : head.toNat + len < cap.toNat
  · simp only [hlt, decide_true, ↓reduceIte, BitVec.sub_zero]
    apply BitVec.eq_of_toNat_eq
    have hmul_lt : (head.toNat + len) * 112 < 18446744073709551616 := by omega
    simp [BitVec.toNat_mul, hsum_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmul_lt]
  · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    have hle : cap.toNat ≤ head.toNat + len := by omega
    have hsub_toNat : (head + BitVec.ofNat 64 len - cap).toNat = head.toNat + len - cap.toNat := by
      rw [BitVec.toNat_sub, hsum_toNat]
      have hcap_lt : cap.toNat < 18446744073709551616 := by omega
      omega
    have hmul_lt : (head.toNat + len - cap.toNat) * 112 < 18446744073709551616 := by omega
    simp [BitVec.toNat_mul, hsub_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmul_lt]

theorem vecDequeRingBuf_split_madd (A : RustAlloc) (cap ptr head : BitVec 64)
    (xs : List (ChainEpochGhost × ChainEpoch))
    (hlen : xs.length < cap.toNat) :
    let s := vecDequePhysIdx head.toNat cap.toNat xs.length
    let slotPtr := ptr + (head + BitVec.ofNat 64 xs.length -
      if BitVec.ult (head + BitVec.ofNat 64 xs.length) cap = true then 0#64 else cap) * 112#64
    vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) cap ptr head xs ⊢
      ∃∗ d1 : BitVec 32,
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
      ∃∗ d0 : BitVec 32,
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
      ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
        ⌜head.toNat < cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        A.live ptr (cap.toNat * 112) 8 ∗
        (slotPtr ↦₆₄ u0) ∗ ((slotPtr + 8#64) ↦₆₄ u1) ∗ ((slotPtr + 16#64) ↦₆₄ u2) ∗
        ((slotPtr + 24#64) ↦₆₄ u3) ∗ ((slotPtr + 32#64) ↦₆₄ u4) ∗ ((slotPtr + 40#64) ↦₆₄ u5) ∗
        ((slotPtr + 48#64) ↦₃₂ d0) ∗ memRegion (slotPtr + 52#64) 4 ∗
        ((slotPtr + 56#64) ↦₆₄ w0) ∗ ((slotPtr + 64#64) ↦₆₄ w1) ∗ ((slotPtr + 72#64) ↦₆₄ w2) ∗
        ((slotPtr + 80#64) ↦₆₄ w3) ∗ ((slotPtr + 88#64) ↦₆₄ w4) ∗ ((slotPtr + 96#64) ↦₆₄ w5) ∗
        ((slotPtr + 104#64) ↦₃₂ d1) ∗ memRegion (slotPtr + 108#64) 4 ∗
        vecDequeSlotsExcept (chainEpochAt A) 112 cap.toNat head.toNat ptr xs s := by
  intro s slotPtr
  refine Entails.trans (vecDequeRingBuf_split_physIdx A cap ptr head xs hlen) ?_
  refine Entails.sepExists_elim fun d1 => Entails.sepExists_elim fun w0 =>
    Entails.sepExists_elim fun w1 => Entails.sepExists_elim fun w2 =>
    Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w4 =>
    Entails.sepExists_elim fun w5 => Entails.sepExists_elim fun d0 =>
    Entails.sepExists_elim fun u0 => Entails.sepExists_elim fun u1 =>
    Entails.sepExists_elim fun u2 => Entails.sepExists_elim fun u3 =>
    Entails.sepExists_elim fun u4 => Entails.sepExists_elim fun u5 => ?_
  refine Entails.pure_left fun ⟨hhead, hcap, hptr⟩ => ?_
  have hmadd : slotPtr = ptr + BitVec.ofNat 64 (s * 112) :=
    physIdx_madd_eq hhead hlen hcap
  rw [← hmadd]
  refine Entails.sepExists_right d1 (Entails.sepExists_right w0
    (Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.sepExists_right d0
        (Entails.sepExists_right u0 (Entails.sepExists_right u1 (Entails.sepExists_right u2
          (Entails.sepExists_right u3 (Entails.sepExists_right u4
            (Entails.sepExists_right u5 ?_)))))))))))))
  exact Entails.pure_right ⟨hhead, hcap, hptr⟩ (Entails.refl _)

private theorem SepWP.join_inImage {prog : Program} {img : Obj.Image}
    {join_pc target_pc : BitVec 64} {s : State} {P P_join : SepProp}
    {post panic_post : State → SepProp → Prop}
    (hF : ImgCallInv img s)
    (hreach : SepWP prog join_pc s P
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧
        sm.trace = s.trace ∧ (Pm ⊢ P_join)))
    (hnext : ∀ sf : State, sf.pc = join_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → ImgCallInv img sf →
      SepWPp prog target_pc sf (⌜sf.trace = s.trace⌝ ∗ P_join) post panic_post) :
    SepWPp prog target_pc s P post panic_post := by
  intro R hm hL
  rcases hreach.elim hm hL with
    ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hspm, hcsm, htrm, hent⟩ | ⟨hoom, hfalse⟩⟩
  · have hmm' : sm.mem ⊨ (⌜sm.trace = s.trace⌝ ∗ P_join) ∗ R := by
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨htrm, Satisfies.mono (sepConj_mono_left hent) hmm⟩
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hF.of_steps hsteps) R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom, hfalse⟩)⟩

@[simp, arm64_norm, wp_norm]
theorem currentEpoch_add_one_eq_zero (e : BitVec 64) :
    (e + 1#64 == 0#64) = (e == 0xffffffffffffffff#64) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  bv_omega

theorem vecDequeRingBuf_split_madd_links (A : RustAlloc) (cap ptr head : BitVec 64)
    (G : ChainGhost) (self : Chain)
    (hlen_eq : G.epochs.length = self.links.length)
    (hlen : self.links.length < cap.toNat) :
    vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) cap ptr head
      (G.epochs.zip self.links) ⊢
      ∃∗ d1 : BitVec 32,
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
      ∃∗ d0 : BitVec 32,
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
      ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
        ⌜head.toNat < cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        A.live ptr (cap.toNat * 112) 8 ∗
        ((ptr + (head + BitVec.ofNat 64 self.links.length -
          if BitVec.ult (head + BitVec.ofNat 64 self.links.length) cap = true then 0#64 else cap) * 112#64) ↦₆₄ u0) ∗
        ((ptr + (head + BitVec.ofNat 64 self.links.length -
          if BitVec.ult (head + BitVec.ofNat 64 self.links.length) cap = true then 0#64 else cap) * 112#64 + 8#64) ↦₆₄ u1) ∗
        ((ptr + (head + BitVec.ofNat 64 self.links.length -
          if BitVec.ult (head + BitVec.ofNat 64 self.links.length) cap = true then 0#64 else cap) * 112#64 + 16#64) ↦₆₄ u2) ∗
        ((ptr + (head + BitVec.ofNat 64 self.links.length -
          if BitVec.ult (head + BitVec.ofNat 64 self.links.length) cap = true then 0#64 else cap) * 112#64 + 24#64) ↦₆₄ u3) ∗
        ((ptr + (head + BitVec.ofNat 64 self.links.length -
          if BitVec.ult (head + BitVec.ofNat 64 self.links.length) cap = true then 0#64 else cap) * 112#64 + 32#64) ↦₆₄ u4) ∗
        ((ptr + (head + BitVec.ofNat 64 self.links.length -
          if BitVec.ult (head + BitVec.ofNat 64 self.links.length) cap = true then 0#64 else cap) * 112#64 + 40#64) ↦₆₄ u5) ∗
        ((ptr + (head + BitVec.ofNat 64 self.links.length -
          if BitVec.ult (head + BitVec.ofNat 64 self.links.length) cap = true then 0#64 else cap) * 112#64 + 48#64) ↦₃₂ d0) ∗
        memRegion (ptr + (head + BitVec.ofNat 64 self.links.length -
          if BitVec.ult (head + BitVec.ofNat 64 self.links.length) cap = true then 0#64 else cap) * 112#64 + 52#64) 4 ∗
        ((ptr + (head + BitVec.ofNat 64 self.links.length -
          if BitVec.ult (head + BitVec.ofNat 64 self.links.length) cap = true then 0#64 else cap) * 112#64 + 56#64) ↦₆₄ w0) ∗
        ((ptr + (head + BitVec.ofNat 64 self.links.length -
          if BitVec.ult (head + BitVec.ofNat 64 self.links.length) cap = true then 0#64 else cap) * 112#64 + 64#64) ↦₆₄ w1) ∗
        ((ptr + (head + BitVec.ofNat 64 self.links.length -
          if BitVec.ult (head + BitVec.ofNat 64 self.links.length) cap = true then 0#64 else cap) * 112#64 + 72#64) ↦₆₄ w2) ∗
        ((ptr + (head + BitVec.ofNat 64 self.links.length -
          if BitVec.ult (head + BitVec.ofNat 64 self.links.length) cap = true then 0#64 else cap) * 112#64 + 80#64) ↦₆₄ w3) ∗
        ((ptr + (head + BitVec.ofNat 64 self.links.length -
          if BitVec.ult (head + BitVec.ofNat 64 self.links.length) cap = true then 0#64 else cap) * 112#64 + 88#64) ↦₆₄ w4) ∗
        ((ptr + (head + BitVec.ofNat 64 self.links.length -
          if BitVec.ult (head + BitVec.ofNat 64 self.links.length) cap = true then 0#64 else cap) * 112#64 + 96#64) ↦₆₄ w5) ∗
        ((ptr + (head + BitVec.ofNat 64 self.links.length -
          if BitVec.ult (head + BitVec.ofNat 64 self.links.length) cap = true then 0#64 else cap) * 112#64 + 104#64) ↦₃₂ d1) ∗
        memRegion (ptr + (head + BitVec.ofNat 64 self.links.length -
          if BitVec.ult (head + BitVec.ofNat 64 self.links.length) cap = true then 0#64 else cap) * 112#64 + 108#64) 4 ∗
        vecDequeSlotsExcept (chainEpochAt A) 112 cap.toNat head.toNat ptr
          (G.epochs.zip self.links) (vecDequePhysIdx head.toNat cap.toNat self.links.length) := by
  have hzip_len : (G.epochs.zip self.links).length = self.links.length := by simp [hlen_eq]
  have h := vecDequeRingBuf_split_madd A cap ptr head (G.epochs.zip self.links) (by rw [hzip_len]; exact hlen)
  dsimp only [] at h
  rw [hzip_len] at h
  exact h

theorem chainEpochDirectionAt_madd_send_intro (A : RustAlloc)
    (maddPtr slotPtr p_next p_prev : BitVec 64)
    (hmadd : maddPtr = slotPtr)
    {genr8r : List (BitVec 8)} (hgen : genr8r.length = 96) (d : Direction)
    (hnext : p_next ≠ 0#64) (hprev : p_prev ≠ 0#64) :
    (maddPtr ↦₆₄ 32#64) ∗ ((maddPtr + 8#64) ↦₆₄ p_next) ∗ ((maddPtr + 16#64) ↦₆₄ 32#64) ∗
    ((maddPtr + 24#64) ↦₆₄ 72#64) ∗ ((maddPtr + 32#64) ↦₆₄ p_prev) ∗ ((maddPtr + 40#64) ↦₆₄ 0#64) ∗
    ((maddPtr + 48#64) ↦₃₂ 0#32) ∗ memRegion (maddPtr + 52#64) 4 ∗
    A.live p_next 32 1 ∗ (p_next ↦ₛ (Chain.cedForDirection genr8r d).next) ∗
    A.live p_prev 72 1 ∗ memRegion p_prev 72 ⊢
      chainEpochDirectionAt A slotPtr
        { next := { cap := 32#64, ptr := p_next }, prev := { cap := 72#64, ptr := p_prev } }
        (Chain.cedForDirection genr8r d) := by
  subst hmadd
  exact chainEpochDirectionAt_new_intro A maddPtr p_next p_prev hgen d hnext hprev

theorem chainEpochDirectionAt_madd_recv_intro (A : RustAlloc)
    (maddPtr slotPtr p_next p_prev : BitVec 64)
    (hmadd : maddPtr = slotPtr)
    {genr8r : List (BitVec 8)} (hgen : genr8r.length = 96) (d : Direction)
    (hnext : p_next ≠ 0#64) (hprev : p_prev ≠ 0#64) :
    ((maddPtr + 56#64) ↦₆₄ 32#64) ∗ ((maddPtr + 64#64) ↦₆₄ p_next) ∗ ((maddPtr + 72#64) ↦₆₄ 32#64) ∗
    ((maddPtr + 80#64) ↦₆₄ 72#64) ∗ ((maddPtr + 88#64) ↦₆₄ p_prev) ∗ ((maddPtr + 96#64) ↦₆₄ 0#64) ∗
    ((maddPtr + 104#64) ↦₃₂ 0#32) ∗ memRegion (maddPtr + 108#64) 4 ∗
    A.live p_next 32 1 ∗ (p_next ↦ₛ (Chain.cedForDirection genr8r d).next) ∗
    A.live p_prev 72 1 ∗ memRegion p_prev 72 ⊢
      chainEpochDirectionAt A (slotPtr + 56#64)
        { next := { cap := 32#64, ptr := p_next }, prev := { cap := 72#64, ptr := p_prev } }
        (Chain.cedForDirection genr8r d) := by
  subst hmadd
  have h := chainEpochDirectionAt_new_intro A (maddPtr + 56#64) p_next p_prev hgen d hnext hprev
  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  chainAddEpoch_fnOff hkdfToSlice_fnOff vecDequeGrow_fnOff
  shim_fnOff alloc_fnOff dealloc_fnOff handleError_fnOff
  panicAddOverflow_fnOff corePanic_fnOff
  libsignalSessionCode_fnOff_0x5bc0c
  libsignalSessionCode_fnOff_0x5de8c
  libsignalSessionCode_fnOff_0x5a544
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_hook% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "alloc::raw_vec::handle_error")
  (ls_hook% "alloc::raw_vec::handle_error")
  (ls_stub% "core::panicking::panic_const::panic_const_add_overflow")
  (ls_hook% "core::panicking::panic_const::panic_const_add_overflow")
  (ls_stub% "core::panicking::panic")
  (ls_hook% "core::panicking::panic")

macro "sep_elim_exists" : tactic =>
  `(tactic| (
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    repeat' (first | (apply SepWPp.exists_elim; intro _) | (apply SepWP.exists_elim; intro _))))

theorem panic_at_ovf_addEpoch (base : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt base ext).externAt?
      ((tripleRatchetProgAtExt base ext).fnAddr chainAddEpochName +
        bv% (ls_off% "core::panicking::panic_const::panic_const_add_overflow" - 0x5bc0c)) =
      some Rust.panicked := by
  exact panic_at_sym_ext base ext chainAddEpochName panicAddOverflowName
    (num% (ls_off% "core::panicking::panic_const::panic_const_add_overflow" - 0x5bc0c))
    (by rw [chainAddEpoch_fnOff, panicAddOverflow_fnOff])
    (hp := by simp [Rust.isPanicSymbol, panicAddOverflowName])

theorem panic_at_core_addEpoch (base : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt base ext).externAt?
      ((tripleRatchetProgAtExt base ext).fnAddr chainAddEpochName +
        bv% (ls_off% "core::panicking::panic" - 0x5bc0c)) =
      some Rust.panicked := by
  exact panic_at_sym_ext base ext chainAddEpochName corePanicName
    (num% (ls_off% "core::panicking::panic" - 0x5bc0c))
    (by rw [chainAddEpoch_fnOff, corePanic_fnOff])
    (hp := by simp [Rust.isPanicSymbol, corePanicName])

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false chainAddEpochInfo_length chainEpochSize
  cmp_dir_toI32 cmp_dir_toI32_bne
  csel_cedSrcAddEpoch_dir csel_cedSrcAddEpoch_dir_bne
  csel_cedSrcAddEpoch_switch csel_cedSrcAddEpoch_switch_bne
  currentEpoch_add_one_eq_zero RegsAt348

private def hkdfToSliceAddEpochCore (hkdf : HkdfFn) (extra : Nat) : Spec HkdfToSliceGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.saltA ∧ s.readReg64 .x1 = BitVec.ofNat 64 x.salt.length ∧
      s.readReg64 .x2 = x.ikmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.ikm.length ∧
      s.readReg64 .x4 = x.infoA ∧ s.readReg64 .x5 = BitVec.ofNat 64 x.info.length ∧
      s.readReg64 .x6 = x.okmA ∧ s.readReg64 .x7 = BitVec.ofNat 64 x.okmLen ∧
      x.salt.length < 2 ^ 63 ∧ x.ikm.length < 2 ^ 63 ∧
      32 ≤ x.info.length ∧ x.info.length < 55 ∧
      (x.okmLen = 32 ∨ x.okmLen = 64 ∨ x.okmLen = 96) ∧
      (¬x.saltRO ∨ x.salt.length ≤ 64) ∧ (¬x.ikmRO ∨ x.ikm.length < 64)⌝ ∗
      bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
      bytesAt x.infoRO x.infoA x.info ∗ memRegion x.okmA x.okmLen ∗
      memRegion (s.sp - BitVec.ofNat 64 (extra + extHookStack)) extra ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜(hkdf x.salt x.ikm x.info x.okmLen).length = x.okmLen ∧ sf.trace = s0.trace⌝ ∗
      bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
      bytesAt x.infoRO x.infoA x.info ∗ (x.okmA ↦ₛ hkdf x.salt x.ikm x.info x.okmLen) ∗
      memRegion (s0.sp - BitVec.ofNat 64 (extra + extHookStack)) extra ∗ stackAt s0.sp extHookStack

private def chainAddEpochSpecCore (hkdf : HkdfFn) (A : RustAlloc) (extra : Nat) : Spec ChainAddEpochGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.selfPtr ∧ s.readReg64 .x1 = x.esPtr ∧
      (x.self.links.length < x.G.linksCap.toNat ∨
        max (2 * x.G.linksCap.toNat) 4 * chainEpochSize < 2 ^ 63)⌝ ∗
      chainAt A x.selfPtr x.G x.self ∗ epochSecretAt A x.esPtr x.esPin x.epochSecret ∗
      A.pool ∗ memRegion (s.sp - BitVec.ofNat 64 (extra + chainAddEpochStackX)) extra ∗
      stackAt s.sp chainAddEpochStackX
  post := fun x s0 sf =>
    match Chain.addEpoch hkdf x.self x.epochSecret with
    | .error _ => ⌜False⌝
    | .ok c' =>
      ⌜sf.trace = s0.trace⌝ ∗ chainRepr A x.selfPtr c' ∗ memRegion x.esPtr 32 ∗
        A.pool ∗ memRegion (s0.sp - BitVec.ofNat 64 (extra + chainAddEpochStackX)) extra ∗
        stackAt s0.sp chainAddEpochStackX
  onPanic := fun x s0 sf =>
    ⌜((Chain.addEpoch hkdf x.self x.epochSecret).isOk = false ∧ sf.trace = s0.trace) ∨
      (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)⌝ ∗ anyHeap

set_option maxHeartbeats 1600000 in
private theorem chainAddEpoch_ok_core {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)} {extra : Nat}
    (hsub_extra : ∀ sp : BitVec 64,
      sp - 192#64 - BitVec.ofNat 64 (extra + extHookStack) =
        sp - BitVec.ofNat 64 (extra + chainAddEpochStackX))
    (himg : Obj.Loads libsignalSessionImage img)
    (hhkdf : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfToSliceName)
      ((hkdfToSliceAddEpochCore hkdf extra).inImage img))
    (hgrow : VecDequeGrowOkX img A ext)
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr shimName)
      ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr allocName)
      ((rustAllocSpecWithStack A extHookStack).inImage img))
    (hdealloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr deallocName)
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr chainAddEpochName)
      ((chainAddEpochSpecCore hkdf A extra).inImage img) := by
  unfold tripleRatchetProgAtExt at *
  refine subroutine_ok_inImage_rodata1_keep (rodata_chainAddEpochInfo himg) ?_
  wpp_init x s0
  have hfn : libsignalSessionCode.fnOff chainAddEpochName = 0x5bc0c :=
    chainAddEpoch_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x5bc0c 592
  have h_hkdf := sub_ok_at_rebase (name := chainAddEpochName) (callee := hkdfToSliceName)
    (k := num% (0x5de8c - 0x5bc0c)) (by rw [chainAddEpoch_fnOff, hkdfToSlice_fnOff]) hhkdf
  have h_grow := sub_ok_at_rebase_bv (name := chainAddEpochName) (callee := vecDequeGrowName)
    (k := 0x5a544#64 - 0x5bc0c#64) (by rw [chainAddEpoch_fnOff, vecDequeGrow_fnOff]; rfl) hgrow
  have h_shim := sub_ok_at_rebase (name := chainAddEpochName) (callee := shimName)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x5bc0c))
    (by rw [chainAddEpoch_fnOff, shim_fnOff]) hshim
  have h_alloc := sub_ok_at_rebase (name := chainAddEpochName) (callee := allocName)
    (k := num% (ls_off% "__rustc::__rust_alloc" - 0x5bc0c))
    (by rw [chainAddEpoch_fnOff, alloc_fnOff]) halloc
  have h_dealloc := sub_ok_at_rebase (name := chainAddEpochName) (callee := deallocName)
    (k := num% (ls_off% "__rustc::__rust_dealloc" - 0x5bc0c))
    (by rw [chainAddEpoch_fnOff, dealloc_fnOff]) hdealloc
  have h_panic_oom := panic_at_handle_error_ext img.base ext chainAddEpochName
    (num% (ls_off% "alloc::raw_vec::handle_error" - 0x5bc0c))
    (by rw [chainAddEpoch_fnOff, handleError_fnOff])
  have h_panic_ovf := panic_at_ovf_addEpoch img.base ext
  have h_panic_core := panic_at_core_addEpoch img.base ext
  dsimp only [tripleRatchetProgAtExt] at h_panic_oom h_panic_ovf h_panic_core
  have hadrp1 : ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      chainAddEpochName + 80#64 &&&
      18446744073709547520#64) + bv% (ls_xref% 0x5bc5c 0x5bc60 - 0x5b000) =
      img.base + bv% (ls_xref% 0x5bc5c 0x5bc60) := by
    have hb := base_aligned_of_loads himg
    rw [Program.fnAddr_rebase, hfn]
    revert hb; bv_kernel
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainAddEpochName :=
    hpc.trans (by rw [Program.fnAddr_rebase, hfn])
  clear himg hhkdf hgrow hshim halloc hdealloc hfn
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      chainAddEpochName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  rcases x with ⟨selfPtr, esPtr, G, esPin, self, epochSecret⟩
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨h_2, h_1⟩
  have hheadroom :
      self.links.length < G.linksCap.toNat ∨
        max (2 * G.linksCap.toNat) 4 * chainEpochSize < 2 ^ 63 := h
  subst h_3 h_4
  refine SepWPp.rw_pre (by rw [stackAt_chainAddEpochX_split s0.sp]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP_inImage (mid := entry + 40#64) hinv0 ?_
  refine SepWP.fold (chainAt_unpack_addEpoch A (s0.readReg64 (.gpr 0#5)) G self) (by sep_focus) ?_
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hlen_eq, hlen_le, hnr_le, hnr_lt, hnr_ptr⟩
  refine SepWP.fold (epochSecretAt_unpack A (s0.readReg64 (.gpr 1#5)) esPin epochSecret) (by sep_focus) ?_
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hes_le, hes_lt, hes_ptr⟩
  have hnr_len_lt : self.nextRoot.length < 2 ^ 63 := Nat.lt_of_le_of_lt hnr_le hnr_lt
  have hes_len_lt : epochSecret.secret.length < 2 ^ 63 := Nat.lt_of_le_of_lt hes_le hes_lt
  refine SepWP.bind_cell64 (s0.sp - 72#64) (by sep_focus) fun v15 => ?_
  wp_steps
  refine SepWP.fold (Entails.of_eq (calleeSavedStackAt_def s0 v15)) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv0'
  by_cases hovf : self.currentEpoch = 0xffffffffffffffff#64
  · have herr := isOk_addEpoch_false_of_ovf hkdf self epochSecret hovf
    have hovf_beq : (self.currentEpoch == 0xffffffffffffffff#64) = true := by simp [hovf]
    wp_norm_hyp hovf_beq
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "core::panicking::panic_const::panic_const_add_overflow" - 0x5bc0c))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic_ovf) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_addEpoch_err herr (by simp only [Rust.panicked, arm64_norm]) hm
  · have hovf_beq : (self.currentEpoch == 0xffffffffffffffff#64) = false := by simp [hovf]
    have hovf_cmn := cmn_one_false_of_ne hovf
    wp_norm_hyp hovf_beq
    wp_norm_hyp hovf_cmn
    refine SepWPp.of_sepWP_inImage (mid := entry + 60#64) hinv0' ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv0''
    by_cases hep : epochSecret.epoch = self.currentEpoch + 1#64
    · rw [chain_addEpoch_eq_ok hkdf hovf hep]
      have hep_bne : (epochSecret.epoch != self.currentEpoch + 1#64) = false := by simp [hep]
      have hep_beq : (epochSecret.epoch == self.currentEpoch + 1#64) = true := by simp [hep]
      wp_norm_hyp hep_bne
      wp_norm_hyp hep_beq
      have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      have hsalt_ro : ¬false ∨ self.nextRoot.length ≤ 64 := Or.inl Bool.noConfusion
      have hikm_ro : ¬false ∨ epochSecret.secret.length < 64 := Or.inl Bool.noConfusion
      have hextra_in :
          memRegion (s0.sp - BitVec.ofNat 64 (extra + chainAddEpochStackX)) extra =
          memRegion (s0.sp - 192#64 - BitVec.ofNat 64 (extra + extHookStack)) extra := by
        rw [hsub_extra s0.sp]
      refine SepWPp.of_sepWP_inImage (mid := entry + 144#64) hinv0'' ?_
      apply SepWP.seq_inImage (mid := entry + bv% (0x5de8c - 0x5bc0c)) hinv0''
      wp_steps
      refine SepWP.fold (Entails.of_eq hextra_in) (by sep_focus) ?_
      refine SepWP.fold (cells12_192_entails_memRegion_96 s0.sp 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv1
      have ⟨hF1, hsym1⟩ := hinv1
      apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x5bc0c)) hinv1
      wp_call h_hkdf
        (⟨false, G.nextRoot.ptr, self.nextRoot,
          false, esPin.ptr, epochSecret.secret,
          true, img.base + bv% (ls_xref% 0x5bc5c 0x5bc60), chainAddEpochInfo,
          s0.sp - 192#64, 96⟩ : HkdfToSliceGhost)
      wp_steps
      have hstack_sf : stackAt (s0.sp - 192#64) extHookStack = stackAt sf.sp extHookStack := by
        rw [‹sf.sp = s0.sp - 192#64›]
      refine SepWP.fold (Entails.of_eq hextra_in.symm) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv2
      have ⟨hF2, hsym2⟩ := hinv2
      apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - 0x5bc0c)) hinv2
      wp_call h_shim ()
      wp_steps
      have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
        rw [‹sf_1.sp = sf.sp›]
      refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      rintro ⟨hF3, hsym3⟩
      wp_call h_alloc (32, 1)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv3
      by_cases hoom1 : sf_2.readReg64 (Reg.gpr 0#5) = 0
      · have hoom1_64 : sf_2.readReg64 (Reg.gpr 0#5) = 0#64 := hoom1
        wp_norm_hyp hoom1_64
        simp only [hoom1, ite_true, sepConj_assoc]
        refine SepWPp.pure_left_focus _ (by sep_focus) ?_
        intro htrace
        apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5bc0c))
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic_oom) fun hm => ?_
        simpa only [sepConj_assoc] using
          allowPanic_addEpoch_oom
            (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace,
              ‹sf_1.trace = sf.trace›, ‹sf.trace = s0.trace›])) hm
      · have hoom1_64 : sf_2.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom1
        simp only [hoom1, ite_false, sepConj_assoc]
        refine SepWPp.pure_left_focus _ (by sep_focus) ?_
        rintro ⟨hmod1, htrace1⟩
        wp_norm_hyp htrace1
        obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
          hokm_all, hokm_root, hokm_a2b, hokm_b2a⟩ :=
          exists_unpack64_of_length_96_split
            ‹List.length (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96) = 96›
        refine SepWPp.of_sepWP_inImage (mid := entry + 164#64) hinv3 ?_
        refine SepWP.fold (Entails.of_eq (hokm_sp_reframe_addEpoch s0.sp hokm_all self.dir)) (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (cedStackBothAt_def s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir)) (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (memRegion_32_cells4 (sf_2.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
        sep_elim_exists
        wp_steps
        refine SepWP.fold (Entails.of_eq (hokm_root (sf_2.readReg64 (.gpr 0#5))).symm) (by sep_focus) ?_
        have hstack_sf2 : stackAt sf_1.sp extHookStack = stackAt sf_2.sp extHookStack := by
          rw [‹sf_2.sp = sf_1.sp›]
        refine SepWP.fold (Entails.of_eq hstack_sf2) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hinv4
        refine SepWP.join_inImage (join_pc := entry + 180#64)
          (P_join :=
            ((img.base + bv% (ls_xref% 0x5bc5c 0x5bc60)) ↦ᵣ chainAddEpochInfo) ∗
            ((s0.sp - 192#64) ↦₆₄ w0) ∗ ((s0.sp - 184#64) ↦₆₄ w1) ∗
            ((s0.sp - 176#64) ↦₆₄ w2) ∗ ((s0.sp - 168#64) ↦₆₄ w3) ∗
            cedStackBothAt s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir ∗
            calleeSavedStackAt s0 v15 ∗
            (s0.readReg64 (.gpr 0#5) ↦₆₄ G.linksCap) ∗
            ((s0.readReg64 (.gpr 0#5) + 8#64) ↦₆₄ G.linksPtr) ∗
            ((s0.readReg64 (.gpr 0#5) + 16#64) ↦₆₄ G.linksHead) ∗
            ((s0.readReg64 (.gpr 0#5) + 24#64) ↦₆₄ BitVec.ofNat 64 self.links.length) ∗
            vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
              G.linksCap G.linksPtr G.linksHead (G.epochs.zip self.links) ∗
            ((s0.readReg64 (.gpr 0#5) + 32#64) ↦₆₄ G.nextRoot.cap) ∗
            ((s0.readReg64 (.gpr 0#5) + 40#64) ↦₆₄ G.nextRoot.ptr) ∗
            ((s0.readReg64 (.gpr 0#5) + 48#64) ↦₆₄ BitVec.ofNat 64 self.nextRoot.length) ∗
            ((s0.readReg64 (.gpr 0#5) + 56#64) ↦₆₄ (self.currentEpoch + 1#64)) ∗
            ((s0.readReg64 (.gpr 0#5) + 80#64) ↦₃₂ self.dir.toI32) ∗
            chainUntouchedAt (s0.readReg64 (.gpr 0#5)) self ∗
            (s0.readReg64 (.gpr 1#5) ↦₆₄ esPin.cap) ∗
            ((s0.readReg64 (.gpr 1#5) + 8#64) ↦₆₄ esPin.ptr) ∗
            ((s0.readReg64 (.gpr 1#5) + 16#64) ↦₆₄ BitVec.ofNat 64 epochSecret.secret.length) ∗
            ((s0.readReg64 (.gpr 1#5) + 24#64) ↦₆₄ epochSecret.epoch) ∗
            (esPin.ptr ↦ₛ epochSecret.secret) ∗
            vecU8Rest A esPin.cap esPin.ptr epochSecret.secret.length ∗
            A.live (sf_2.readReg64 (.gpr 0#5)) 32 1 ∗
            (sf_2.readReg64 (.gpr 0#5) ↦ₛ (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96).take 32) ∗
            A.pool ∗ stackAt sf_2.sp extHookStack ∗
            memRegion (s0.sp - BitVec.ofNat 64 (extra + chainAddEpochStackX)) extra)
          hinv4 ?_ ?_
        · by_cases hnr_cap : G.nextRoot.cap = 0#64
          · have hnr_cap_beq : (G.nextRoot.cap == 0#64) = true := by simp [hnr_cap]
            wp_norm_hyp hnr_cap_beq
            refine SepWP.fold (Entails.of_eq (vecU8Rest_eq_zero A G.nextRoot.ptr hnr_cap hnr_le)) (by sep_focus) ?_
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            refine ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_⟩
            sep_frame
          · have hnr_cap_beq : (G.nextRoot.cap == 0#64) = false := beq_false_of_ne hnr_cap
            wp_norm_hyp hnr_cap_beq
            refine SepWP.fold (vecU8Rest_nonzero_entails A G.nextRoot.ptr hnr_cap hnr_le hnr_lt) (by sep_focus) ?_
            refine SepWP.pure_left_focus _ (by sep_focus) ?_
            intro hnr_layout
            have ⟨hnr_pos, _, hnr_isize⟩ := hnr_layout
            apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - 0x5bc0c)) hinv4
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            rintro ⟨hF_nr, hsym_nr⟩
            wp_call h_dealloc (G.nextRoot.ptr, G.nextRoot.cap.toNat, 1)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, by wp_norm_goal, ?_⟩
            sep_frame
        · intro sf_nr hpc_nr hrun_nr hsp_nr hcs_nr hinv_nr
          wp_split_join hsp_nr hcs_nr
          have htr_nr : sf_nr.trace = sf_2.trace := ‹_›
          wp_norm_hyp htr_nr
          refine SepWPp.of_sepWP_inImage (mid := entry + 212#64) hinv_nr ?_
          apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x5bc0c)) hinv_nr
          wp_steps
          refine SepWP.fold (Entails.of_eq (addEpochMidFrame_def img hkdf A s0 v15 w0 w1 w2 w3 (sf_2.readReg64 (.gpr 0#5)) esPin self epochSecret)) (by sep_focus) ?_
          have hstack_nr : stackAt sf_2.sp extHookStack = stackAt sf_nr.sp extHookStack := by
            rw [‹sf_nr.sp = sf_2.sp›]
          refine SepWP.fold (Entails.of_eq hstack_nr) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hinv5
          have ⟨hF5, hsym5⟩ := hinv5
          apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - 0x5bc0c)) hinv5
          wp_call h_shim ()
          wp_steps
          have hstack_sf3 : stackAt sf_nr.sp extHookStack = stackAt sf_3.sp extHookStack := by
            rw [‹sf_3.sp = sf_nr.sp›]
          refine SepWP.fold (Entails.of_eq hstack_sf3) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          rintro ⟨hF6, hsym6⟩
          wp_call h_alloc (72, 1)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hinv6
          by_cases hoom2 : sf_4.readReg64 (Reg.gpr 0#5) = 0
          · have hoom2_64 : sf_4.readReg64 (Reg.gpr 0#5) = 0#64 := hoom2
            wp_norm_hyp hoom2_64
            simp only [hoom2, ite_true, sepConj_assoc]
            refine SepWPp.pure_left_focus _ (by sep_focus) ?_
            intro htrace2
            apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5bc0c))
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic_oom) fun hm => ?_
            simpa only [sepConj_assoc] using
              allowPanic_addEpoch_oom
                (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace2,
                  ‹sf_3.trace = sf_nr.trace›, htr_nr, htrace1,
                  ‹sf_1.trace = sf.trace›, ‹sf.trace = s0.trace›])) hm
          · have hoom2_64 : sf_4.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom2
            simp only [hoom2, ite_false, sepConj_assoc]
            refine SepWPp.pure_left_focus _ (by sep_focus) ?_
            rintro ⟨hmod2, htrace2⟩
            wp_norm_hyp htrace2
            refine SepWPp.of_sepWP_inImage (mid := entry + 236#64) hinv6 ?_
            apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x5bc0c)) hinv6
            wp_steps
            have hstack_sf4 : stackAt sf_3.sp extHookStack = stackAt sf_4.sp extHookStack := by
              rw [‹sf_4.sp = sf_3.sp›]
            refine SepWP.fold (Entails.of_eq hstack_sf4) (by sep_focus) ?_
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            intro hinv7
            have ⟨hF7, hsym7⟩ := hinv7
            apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - 0x5bc0c)) hinv7
            wp_call h_shim ()
            wp_steps
            have hstack_sf5 : stackAt sf_4.sp extHookStack = stackAt sf_5.sp extHookStack := by
              rw [‹sf_5.sp = sf_4.sp›]
            refine SepWP.fold (Entails.of_eq hstack_sf5) (by sep_focus) ?_
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            rintro ⟨hF8, hsym8⟩
            wp_call h_alloc (32, 1)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            intro hinv8
            by_cases hoom3 : sf_6.readReg64 (Reg.gpr 0#5) = 0
            · have hoom3_64 : sf_6.readReg64 (Reg.gpr 0#5) = 0#64 := hoom3
              wp_norm_hyp hoom3_64
              simp only [hoom3, ite_true, sepConj_assoc]
              refine SepWPp.pure_left_focus _ (by sep_focus) ?_
              intro htrace3
              apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5bc0c))
              wp_steps
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic_oom) fun hm => ?_
              simpa only [sepConj_assoc] using
                allowPanic_addEpoch_oom
                  (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace3,
                    ‹sf_5.trace = sf_4.trace›, htrace2,
                    ‹sf_3.trace = sf_nr.trace›, htr_nr, htrace1,
                    ‹sf_1.trace = sf.trace›, ‹sf.trace = s0.trace›])) hm
            · have hoom3_64 : sf_6.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom3
              simp only [hoom3, ite_false, sepConj_assoc]
              refine SepWPp.pure_left_focus _ (by sep_focus) ?_
              rintro ⟨hmod3, htrace3⟩
              wp_norm_hyp htrace3
              refine SepWPp.of_sepWP_inImage (mid := entry + 288#64) hinv8 ?_
              apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x5bc0c)) hinv8
              refine SepWP.fold (Entails.of_eq (cedStackBothAt_def s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir).symm) (by sep_focus) ?_
              refine SepWP.fold (Entails.of_eq (memRegion_32_cells4 (sf_6.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
              sep_elim_exists
              wp_steps
              refine SepWP.fold (Entails.of_eq (cedCells_eq_pointsToBytes hokm_a2b hokm_b2a self.dir (sf_6.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
              refine SepWP.fold (Entails.of_eq (cedStackBothAt_def s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir)) (by sep_focus) ?_
              have hstack_sf6 : stackAt sf_5.sp extHookStack = stackAt sf_6.sp extHookStack := by
                rw [‹sf_6.sp = sf_5.sp›]
              refine SepWP.fold (Entails.of_eq hstack_sf6) (by sep_focus) ?_
              apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
              intro hinv9
              have ⟨hF9, hsym9⟩ := hinv9
              apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - 0x5bc0c)) hinv9
              wp_call h_shim ()
              wp_steps
              have hstack_sf7 : stackAt sf_6.sp extHookStack = stackAt sf_7.sp extHookStack := by
                rw [‹sf_7.sp = sf_6.sp›]
              refine SepWP.fold (Entails.of_eq hstack_sf7) (by sep_focus) ?_
              apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
              rintro ⟨hF10, hsym10⟩
              wp_call h_alloc (72, 1)
              apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
              intro hinv10
              by_cases hoom4 : sf_8.readReg64 (Reg.gpr 0#5) = 0
              · have hoom4_64 : sf_8.readReg64 (Reg.gpr 0#5) = 0#64 := hoom4
                wp_norm_hyp hoom4_64
                simp only [hoom4, ite_true, sepConj_assoc]
                refine SepWPp.pure_left_focus _ (by sep_focus) ?_
                intro htrace4
                apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5bc0c))
                wp_steps
                apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
                refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic_oom) fun hm => ?_
                simpa only [sepConj_assoc] using
                  allowPanic_addEpoch_oom
                    (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace4,
                      ‹sf_7.trace = sf_6.trace›, htrace3,
                      ‹sf_5.trace = sf_4.trace›, htrace2,
                      ‹sf_3.trace = sf_nr.trace›, htr_nr, htrace1,
                      ‹sf_1.trace = sf.trace›, ‹sf.trace = s0.trace›])) hm
              · have hoom4_64 : sf_8.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom4
                simp only [hoom4, ite_false, sepConj_assoc]
                refine SepWPp.pure_left_focus _ (by sep_focus) ?_
                rintro ⟨hmod4, htrace4⟩
                wp_norm_hyp htrace4
                refine SepWPp.of_sepWP_inImage (mid := entry + 312#64) hinv10 ?_
                apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x5bc0c)) hinv10
                wp_steps
                have hstack_sf8 : stackAt sf_7.sp extHookStack = stackAt sf_8.sp extHookStack := by
                  rw [‹sf_8.sp = sf_7.sp›]
                refine SepWP.fold (Entails.of_eq hstack_sf8) (by sep_focus) ?_
                apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                intro hinv11
                have ⟨hF11, hsym11⟩ := hinv11
                apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - 0x5bc0c)) hinv11
                wp_call h_shim ()
                wp_steps
                have hstack_sf9 : stackAt sf_8.sp extHookStack = stackAt sf_9.sp extHookStack := by
                  rw [‹sf_9.sp = sf_8.sp›]
                refine SepWP.fold (Entails.of_eq hstack_sf9) (by sep_focus) ?_
                apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                rintro ⟨hF12, hsym12⟩
                wp_call h_alloc (32, 1)
                apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                intro hinv12
                by_cases hoom5 : sf_10.readReg64 (Reg.gpr 0#5) = 0
                · have hoom5_64 : sf_10.readReg64 (Reg.gpr 0#5) = 0#64 := hoom5
                  wp_norm_hyp hoom5_64
                  simp only [hoom5, ite_true, sepConj_assoc]
                  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
                  intro htrace5
                  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5bc0c))
                  wp_steps
                  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
                  refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic_oom) fun hm => ?_
                  simpa only [sepConj_assoc] using
                    allowPanic_addEpoch_oom
                      (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace5,
                        ‹sf_9.trace = sf_8.trace›, htrace4,
                        ‹sf_7.trace = sf_6.trace›, htrace3,
                        ‹sf_5.trace = sf_4.trace›, htrace2,
                        ‹sf_3.trace = sf_nr.trace›, htr_nr, htrace1,
                        ‹sf_1.trace = sf.trace›, ‹sf.trace = s0.trace›])) hm
                · have hoom5_64 : sf_10.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom5
                  simp only [hoom5, ite_false, sepConj_assoc]
                  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
                  rintro ⟨hmod5, htrace5⟩
                  wp_norm_hyp htrace5
                  refine SepWPp.of_sepWP_inImage (mid := entry + 344#64) hinv12 ?_
                  refine SepWP.fold (Entails.of_eq (cedStackBothAt_def s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir).symm) (by sep_focus) ?_
                  refine SepWP.fold (Entails.of_eq (memRegion_32_cells4 (sf_10.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
                  sep_elim_exists
                  wp_steps
                  refine SepWP.fold (Entails.of_eq (cedCells_eq_pointsToBytes hokm_a2b hokm_b2a self.dir.switch (sf_10.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
                  refine SepWP.fold (Entails.of_eq (cedStackBothAt_def s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir)) (by sep_focus) ?_
                  have hstack_sf10 : stackAt sf_9.sp extHookStack = stackAt sf_10.sp extHookStack := by
                    rw [‹sf_10.sp = sf_9.sp›]
                  refine SepWP.fold (Entails.of_eq hstack_sf10) (by sep_focus) ?_
                  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                  intro hinv13
                  let cap1 : BitVec 64 :=
                    if self.links.length = G.linksCap.toNat then newCapChainEpoch G.linksCap else G.linksCap
                  have hlen_lt_cap1 : self.links.length < cap1.toNat := by
                    dsimp only [cap1]
                    split_ifs with heq
                    · exact len_lt_newCapChainEpoch heq (Or.resolve_left hheadroom (by omega))
                    · omega
                  refine SepWPp.join_at_348 (join_pc := entry + 348#64) (cap1 := cap1)
                    (P_join :=
                      ∃∗ ptr1 : BitVec 64, ∃∗ head1 : BitVec 64,
                        addEpochMidFrame img hkdf A s0 v15 w0 w1 w2 w3 (sf_2.readReg64 (.gpr 0#5)) esPin self epochSecret ∗
                        cedStackBothAt s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir ∗
                        (s0.readReg64 (.gpr 0#5) ↦₆₄ cap1) ∗
                        ((s0.readReg64 (.gpr 0#5) + 8#64) ↦₆₄ ptr1) ∗
                        ((s0.readReg64 (.gpr 0#5) + 16#64) ↦₆₄ head1) ∗
                        ((s0.readReg64 (.gpr 0#5) + 24#64) ↦₆₄ BitVec.ofNat 64 self.links.length) ∗
                        vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
                          cap1 ptr1 head1 (G.epochs.zip self.links) ∗
                        (s0.readReg64 (.gpr 1#5) ↦₆₄ esPin.cap) ∗
                        A.live (sf_4.readReg64 (.gpr 0#5)) 72 1 ∗
                        memRegion (sf_4.readReg64 (.gpr 0#5)) 72 ∗
                        A.live (sf_6.readReg64 (.gpr 0#5)) 32 1 ∗
                        (sf_6.readReg64 (.gpr 0#5) ↦ₛ (Chain.cedForDirection (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96) self.dir).next) ∗
                        A.live (sf_8.readReg64 (.gpr 0#5)) 72 1 ∗
                        memRegion (sf_8.readReg64 (.gpr 0#5)) 72 ∗
                        A.live (sf_10.readReg64 (.gpr 0#5)) 32 1 ∗
                        (sf_10.readReg64 (.gpr 0#5) ↦ₛ (Chain.cedForDirection (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96) self.dir.switch).next) ∗
                        A.pool ∗ stackAt sf_10.sp extHookStack ∗
                        memRegion (s0.sp - BitVec.ofNat 64 (extra + chainAddEpochStackX)) extra)
                    hinv13 ?_ ?_
                  · by_cases heq_cap : self.links.length = G.linksCap.toNat
                    · have hcap1_eq : cap1 = newCapChainEpoch G.linksCap := by simp [cap1, heq_cap]
                      have hcmp_eq : (BitVec.ofNat 64 self.links.length == G.linksCap) = true := by
                        rw [heq_cap]; simp
                      wp_norm_hyp hcmp_eq
                      have hgrow_ok : max (2 * G.linksCap.toNat) 4 * chainEpochSize < 2 ^ 63 :=
                        Or.resolve_left hheadroom (by omega)
                      have hzip_eq : (G.epochs.zip self.links).length = G.linksCap.toNat := by
                        simp [hlen_eq, heq_cap]
                      refine SepWPp.of_sepWP_inImage (mid := entry + (0x5a544#64 - 0x5bc0c#64)) hinv13 ?_
                      refine SepWP.fold (vecDequeAt_fold_addEpoch A (s0.readReg64 (.gpr 0#5)) G.linksCap G.linksPtr G.linksHead G self hlen_eq) (by sep_focus) ?_
                      wp_steps
                      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                      intro hinv14
                      change subroutine_ok prog (entry + (0x5a544#64 - 0x5bc0c#64))
                        ((vecDequeGrowSpec A).inImage img) at h_grow
                      apply SepWPp.reassoc_panic
                      wpp_call_inImage_addEpoch' h_grow
                        (⟨s0.readReg64 (.gpr 0#5), G.linksCap, G.linksPtr, G.linksHead, G.epochs.zip self.links⟩ : VecDequeGrowGhost)
                        hinv14
                      refine SepWP.unfold_vecDeque_bind A (s0.readReg64 (.gpr 0#5)) (newCapChainEpoch G.linksCap) G self hlen_eq (by sep_focus) ?_
                      intro ptr1 head1
                      wp_steps
                      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                      refine ⟨by wp_norm_goal, by wp_norm_goal, by rw [hcap1_eq]; wp_norm_goal, by wp_norm_goal, ?_⟩
                      rw [hcap1_eq]
                      refine Entails.sepExists_right ptr1 (Entails.sepExists_right head1 ?_)
                      sep_frame
                    · have hcap1_eq : cap1 = G.linksCap := by simp [cap1, heq_cap]
                      have hcmp_ne : BitVec.ofNat 64 self.links.length ≠ G.linksCap :=
                        ofNat_len_ne_cap (by omega)
                      have hcmp_eq : (BitVec.ofNat 64 self.links.length == G.linksCap) = false :=
                        beq_false_of_ne hcmp_ne
                      have hcmp_sub := sub_eq_zero_false_of_ne hcmp_ne
                      have hcmp_add := add_neg_eq_zero_false_of_ne hcmp_ne
                      wp_norm_hyp hcmp_eq
                      wp_norm_hyp hcmp_sub
                      wp_norm_hyp hcmp_add
                      apply SepWPp.of_sepWP_ret
                      wp_steps
                      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                      refine ⟨by wp_norm_goal, by wp_norm_goal, by rw [hcap1_eq]; wp_norm_goal, by wp_norm_goal, ?_⟩
                      rw [hcap1_eq]
                      refine Entails.sepExists_right G.linksPtr (Entails.sepExists_right G.linksHead ?_)
                      sep_frame
                  · intro sf_348 hpc_348 hrun_348 hsp_348 hreg_348 hcap_348 hinv_348
                    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
                    intro htr_348
                    apply SepWPp.exists_elim; intro ptr1
                    apply SepWPp.exists_elim; intro head1
                    wp_split_join hsp_348 hreg_348
                    wp_norm_hyp hcap_348
                    wp_norm_hyp htr_348
                    refine SepWPp.of_sepWP_inImage (mid := entry + 428#64) hinv_348 ?_
                    refine SepWP.fold (vecDequeRingBuf_split_madd_links A cap1 ptr1 head1 G self hlen_eq hlen_lt_cap1) (by sep_focus) ?_
                    sep_elim_exists
                    refine SepWP.pure_left_focus _ (by sep_focus) ?_
                    rintro ⟨hhead1, hcap1_lt, hptr1⟩
                    wp_steps
                    have hmadd_eq := physIdx_madd_eq (ptr := ptr1) hhead1 hlen_lt_cap1 hcap1_lt
                    let slotPtr := ptr1 + BitVec.ofNat 64 (vecDequePhysIdx head1.toNat cap1.toNat self.links.length * 112)
                    refine SepWP.fold (chainEpochDirectionAt_madd_send_intro A _ slotPtr
                      (sf_6.readReg64 (.gpr 0#5)) (sf_4.readReg64 (.gpr 0#5)) hmadd_eq
                      ‹List.length (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96) = 96›
                      self.dir hoom3_64 hoom2_64) (by sep_focus) ?_
                    refine SepWP.fold (chainEpochDirectionAt_madd_recv_intro A _ slotPtr
                      (sf_10.readReg64 (.gpr 0#5)) (sf_8.readReg64 (.gpr 0#5)) hmadd_eq
                      ‹List.length (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96) = 96›
                      self.dir.switch hoom5_64 hoom4_64) (by sep_focus) ?_
                    have hlen_add1 := ofNat_len_add_one hlen_lt_cap1 hcap1_lt
                    have hlen_cell :
                        ((s0.readReg64 (.gpr 0#5) + 24#64) ↦₆₄ (BitVec.ofNat 64 self.links.length + 1#64)) =
                        ((s0.readReg64 (.gpr 0#5) + 24#64) ↦₆₄ BitVec.ofNat 64 (self.links.length + 1)) := by
                      rw [hlen_add1]
                    refine SepWP.fold (Entails.of_eq hlen_cell) (by sep_focus) ?_
                    refine SepWP.fold (Entails.of_eq (addEpochMidFrame_def img hkdf A s0 v15 w0 w1 w2 w3 (sf_2.readReg64 (.gpr 0#5)) esPin self epochSecret).symm) (by sep_focus) ?_
                    refine SepWP.fold (Entails.of_eq (calleeSavedStackAt_def s0 v15).symm) (by sep_focus) ?_
                    refine SepWP.fold (Entails.of_eq (cedStackBothAt_def s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir).symm) (by sep_focus) ?_
                    have hep_cell :
                        ((s0.readReg64 (.gpr 0#5) + 56#64) ↦₆₄ (self.currentEpoch + 1#64)) =
                        ((s0.readReg64 (.gpr 0#5) + 56#64) ↦₆₄ epochSecret.epoch) := by
                      rw [hep]
                    refine SepWP.fold (Entails.of_eq hep_cell) (by sep_focus) ?_
                    have hchain_intro := chainRepr_addEpoch_intro A hkdf
                      (s0.readReg64 (.gpr 0#5)) cap1 ptr1 head1
                      (sf_2.readReg64 (.gpr 0#5))
                      (sf_6.readReg64 (.gpr 0#5)) (sf_4.readReg64 (.gpr 0#5))
                      (sf_10.readReg64 (.gpr 0#5)) (sf_8.readReg64 (.gpr 0#5))
                      G self epochSecret hlen_eq hlen_lt_cap1 hhead1 hcap1_lt hptr1 hoom1_64
                      ‹List.length (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96) = 96›
                    dsimp only [] at hchain_intro
                    refine SepWP.fold hchain_intro (by sep_focus) ?_
                    refine SepWP.fold (cells4_entails_memRegion_32 (s0.readReg64 (.gpr 1#5))
                      esPin.cap esPin.ptr (BitVec.ofNat 64 epochSecret.secret.length) epochSecret.epoch)
                      (by sep_focus) ?_
                    refine SepWP.fold (Entails.of_eq (cedCells_reframe_addEpoch s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir).symm) (by sep_focus) ?_
                    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                    intro hinv15
                    by_cases hes_cap : esPin.cap = 0#64
                    · have hes_cap_beq : (esPin.cap == 0#64) = true := by simp [hes_cap]
                      wp_norm_hyp hes_cap_beq
                      apply SepWPp.of_sepWP_ret
                      refine SepWP.fold (Entails.of_eq (vecU8Rest_eq_zero A esPin.ptr hes_cap hes_le)) (by sep_focus) ?_
                      wp_steps
                      have hstack_348 : stackAt sf_10.sp extHookStack = stackAt (s0.sp - 192#64) extHookStack := by
                        rw [‹sf_10.sp = sf_9.sp›, ‹sf_9.sp = sf_8.sp›, ‹sf_8.sp = sf_7.sp›,
                          ‹sf_7.sp = sf_6.sp›, ‹sf_6.sp = sf_5.sp›, ‹sf_5.sp = sf_4.sp›,
                          ‹sf_4.sp = sf_3.sp›, ‹sf_3.sp = sf_nr.sp›, ‹sf_nr.sp = sf_2.sp›,
                          ‹sf_2.sp = sf_1.sp›, ‹sf_1.sp = sf.sp›, ‹sf.sp = s0.sp - 192#64›]
                      refine SepWP.fold (Entails.of_eq hstack_348) (by sep_focus) ?_
                      refine SepWP.fold (rejoin_stack_chainAddEpochX s0.sp
                        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
                        (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
                        (s0.readReg64 (.gpr 27#5)) v15
                        (s0.readReg64 (.gpr 26#5)) (s0.readReg64 (.gpr 25#5))
                        (s0.readReg64 (.gpr 24#5)) (s0.readReg64 (.gpr 23#5))
                        (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5))
                        (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5)))
                        (by sep_focus) ?_
                      wp_done
                    · have hes_cap_beq : (esPin.cap == 0#64) = false := beq_false_of_ne hes_cap
                      wp_norm_hyp hes_cap_beq
                      refine SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - 0x5bc0c)) hinv15 ?_
                      refine SepWP.fold (vecU8Rest_nonzero_entails A esPin.ptr hes_cap hes_le hes_lt) (by sep_focus) ?_
                      refine SepWP.pure_left_focus _ (by sep_focus) ?_
                      intro hes_layout
                      have ⟨hes_pos, _, hes_isize⟩ := hes_layout
                      wp_steps
                      have hstack_348 : stackAt sf_10.sp extHookStack = stackAt (s0.sp - 192#64) extHookStack := by
                        rw [‹sf_10.sp = sf_9.sp›, ‹sf_9.sp = sf_8.sp›, ‹sf_8.sp = sf_7.sp›,
                          ‹sf_7.sp = sf_6.sp›, ‹sf_6.sp = sf_5.sp›, ‹sf_5.sp = sf_4.sp›,
                          ‹sf_4.sp = sf_3.sp›, ‹sf_3.sp = sf_nr.sp›, ‹sf_nr.sp = sf_2.sp›,
                          ‹sf_2.sp = sf_1.sp›, ‹sf_1.sp = sf.sp›, ‹sf.sp = s0.sp - 192#64›]
                      refine SepWP.fold (Entails.of_eq hstack_348) (by sep_focus) ?_
                      refine SepWP.fold (rejoin_stack_chainAddEpochX s0.sp
                        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
                        (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
                        (s0.readReg64 (.gpr 27#5)) v15
                        (s0.readReg64 (.gpr 26#5)) (s0.readReg64 (.gpr 25#5))
                        (s0.readReg64 (.gpr 24#5)) (s0.readReg64 (.gpr 23#5))
                        (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5))
                        (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5)))
                        (by sep_focus) ?_
                      refine SepWP.fold (Entails.of_eq (stackAt_chainAddEpochX_top_split s0.sp)) (by sep_focus) ?_
                      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                      rintro ⟨hF16, hsym16⟩
                      apply SepWPp.of_sepWP_ret
                      wp_call h_dealloc (esPin.ptr, esPin.cap.toNat, 1)
                      refine SepWP.fold (Entails.of_eq (stackAt_chainAddEpochX_top_split s0.sp).symm) (by sep_focus) ?_
                      wp_done
    · have herr := isOk_addEpoch_false_of_epoch_ne hkdf self epochSecret hovf hep
      have hep_bne : (epochSecret.epoch != self.currentEpoch + 1#64) = true := by simp [hep]
      have hep_beq : (epochSecret.epoch == self.currentEpoch + 1#64) = false := beq_false_of_ne hep
      have hep_sub := sub_eq_zero_false_of_ne hep
      have hep_add := add_neg_eq_zero_false_of_ne hep
      wp_norm_hyp hep_bne
      wp_norm_hyp hep_beq
      wp_norm_hyp hep_sub
      wp_norm_hyp hep_add
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "core::panicking::panic" - 0x5bc0c))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic_core) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_addEpoch_err herr (by simp only [Rust.panicked, arm64_norm]) hm

theorem chainAddEpoch_ok_of_contracts_x {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hhkdf : HkdfToSliceSpqrOkX img hkdf ext)
    (hgrow : VecDequeGrowOkX img A ext)
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr shimName)
      ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr allocName)
      ((rustAllocSpecWithStack A extHookStack).inImage img))
    (hdealloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr deallocName)
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img)) :
    ChainAddEpochOkX img hkdf A ext := by
  unfold HkdfToSliceSpqrOkX at hhkdf
  have hhkdf' : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfToSliceName)
      ((hkdfToSliceAddEpochCore hkdf 0).inImage img) := by
    refine sub_ok_conseq_entails hhkdf (fun x s => ?_) (fun x s0 sf => ?_)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    · dsimp only [Spec.inImage, hkdfToSliceAddEpochCore, hkdfToSliceSpqrSpec, hkdfToSliceSpec]
      rw [ProofLib.memRegion_zero, emp_sepConj]
      refine sepConj_mono_right (Entails.pure_left fun hp => ?_)
      rcases hp with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, _, _⟩
      exact Entails.pure_right ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ (Entails.refl _)
    · dsimp only [Spec.inImage, hkdfToSliceAddEpochCore, hkdfToSliceSpqrSpec, hkdfToSliceSpec]
      rw [ProofLib.memRegion_zero, emp_sepConj]; exact Entails.refl _
  unfold ChainAddEpochOkX
  refine sub_ok_conseq_entails
    (chainAddEpoch_ok_core (fun sp => by dsimp only [extHookStack, chainAddEpochStackX]; bv_kernel)
      himg hhkdf' hgrow hshim halloc hdealloc)
    (fun x s => ?_) (fun x s0 sf => ?_) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
  · dsimp only [Spec.inImage, chainAddEpochSpecCore, chainAddEpochSpecX]
    rw [ProofLib.memRegion_zero, emp_sepConj]; exact Entails.refl _
  · dsimp only [Spec.inImage, chainAddEpochSpecCore, chainAddEpochSpecX]
    cases Chain.addEpoch hkdf x.self x.epochSecret <;>
      simp only [ProofLib.memRegion_zero, emp_sepConj] <;> exact Entails.refl _

/-- External-hook specialization of `chainAddEpoch_ok_of_contracts_x`: given `AllocContractsX`,
`HkdfToSliceSpqrOkX`, and `VecDequeGrowOkX`, `<spqr::chain::Chain>::add_epoch` meets
`(chainAddEpochSpecX hkdf A).inImage img`. -/
theorem chainAddEpoch_ok_ext_x {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hhkdf : HkdfToSliceSpqrOkX img hkdf ext)
    (hgrow : VecDequeGrowOkX img A ext)
    (hA : AllocContractsX img A ext) :
    ChainAddEpochOkX img hkdf A ext :=
  chainAddEpoch_ok_of_contracts_x himg hhkdf hgrow
    (hA.shim extHookStack (by decide) (by decide)) hA.alloc hA.dealloc

private theorem stackAt_hkdfAddEpochExt_split (sp : BitVec 64) : stackAt sp hkdfToSliceStackExt =
    memRegion (sp - BitVec.ofNat 64 (1232 + extHookStack)) 1232 ∗ stackAt sp extHookStack :=
  ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 17616) (n := 1232) (k := 16384)
    (b' := sp - 16384#64) rfl (by bv_omega) (by decide)

theorem chainAddEpoch_ok_of_contracts_ext {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hhkdf : HkdfToSliceSpqrOkExt img hkdf ext)
    (hgrow : VecDequeGrowOkX img A ext)
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr shimName)
      ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr allocName)
      ((rustAllocSpecWithStack A extHookStack).inImage img))
    (hdealloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr deallocName)
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img)) :
    ChainAddEpochOkExt img hkdf A ext := by
  unfold HkdfToSliceSpqrOkExt at hhkdf
  have hhkdf' : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfToSliceName)
      ((hkdfToSliceAddEpochCore hkdf 1232).inImage img) := by
    refine sub_ok_conseq_entails hhkdf (fun x s => ?_) (fun x s0 sf => ?_)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    · dsimp only [Spec.inImage, hkdfToSliceAddEpochCore, hkdfToSliceSpecExt]
      rw [stackAt_hkdfAddEpochExt_split s.sp]; exact Entails.of_eq (by ac_rfl)
    · dsimp only [Spec.inImage, hkdfToSliceAddEpochCore, hkdfToSliceSpecExt]
      rw [stackAt_hkdfAddEpochExt_split s0.sp]; exact Entails.of_eq (by ac_rfl)
  unfold ChainAddEpochOkExt
  refine sub_ok_conseq_entails
    (chainAddEpoch_ok_core (fun sp => by dsimp only [extHookStack, chainAddEpochStackX]; bv_kernel)
      himg hhkdf' hgrow hshim halloc hdealloc)
    (fun x s => ?_) (fun x s0 sf => ?_) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
  · dsimp only [Spec.inImage, chainAddEpochSpecCore, chainAddEpochSpecExt]
    rw [stackAt_chainAddEpochExt_eq s.sp]; exact Entails.of_eq (by ac_rfl)
  · dsimp only [Spec.inImage, chainAddEpochSpecCore, chainAddEpochSpecExt]
    cases Chain.addEpoch hkdf x.self x.epochSecret
    · exact Entails.refl _
    · rw [stackAt_chainAddEpochExt_eq s0.sp]; exact Entails.of_eq (by ac_rfl)

theorem chainAddEpoch_ok_ext_ext {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hhkdf : HkdfToSliceSpqrOkExt img hkdf ext)
    (hgrow : VecDequeGrowOkX img A ext)
    (hA : AllocContractsX img A ext) :
    ChainAddEpochOkExt img hkdf A ext :=
  chainAddEpoch_ok_of_contracts_ext himg hhkdf hgrow
    (hA.shim extHookStack (by decide) (by decide)) hA.alloc hA.dealloc

abbrev chainAddEpoch_ok_ext := @chainAddEpoch_ok_ext_ext

/-! ## Relocatable `[LibsignalPlacement]` Proof of `<spqr::chain::Chain>::add_epoch` (Block `368`) -/

theorem SepWPp.join_at_348_lsCallInv {prog : Program} {pl : Obj.MultiPlacement}
    {join_pc target_pc cap1 : BitVec 64} {s : State} {P P_join : SepProp}
    {post panic_post : State → SepProp → Prop}
    (hF : LsCallInv pl s.mem)
    (hreach : SepWPp prog join_pc s P
      (fun sm Pm => sm.sp = s.sp ∧ RegsAt348 s sm ∧
        sm.readReg64 (.gpr 9#5) = cap1 ∧
        sm.trace = s.trace ∧ (Pm ⊢ P_join))
      panic_post)
    (hnext : ∀ sf : State, sf.pc = join_pc → sf.status = .Running →
      sf.sp = s.sp → RegsAt348 s sf → sf.readReg64 (.gpr 9#5) = cap1 → LsCallInv pl sf.mem →
      SepWPp prog target_pc sf (⌜sf.trace = s.trace⌝ ∗ P_join) post panic_post) :
    SepWPp prog target_pc s P post panic_post := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hspm, hregm, hcapm, htrm, hent⟩ | hpan⟩ :=
    hreach R hm hL
  · have hmm' : sm.mem ⊨ (⌜sm.trace = s.trace⌝ ∗ P_join) ∗ R := by
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨htrm, Satisfies.mono (sepConj_mono_left hent) hmm⟩
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hregm hcapm (hF.of_steps hsteps) R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr hpan⟩

private theorem SepWP.join_lsCallInv {prog : Program} {pl : Obj.MultiPlacement}
    {join_pc target_pc : BitVec 64} {s : State} {P P_join : SepProp}
    {post panic_post : State → SepProp → Prop}
    (hF : LsCallInv pl s.mem)
    (hreach : SepWP prog join_pc s P
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧
        sm.trace = s.trace ∧ (Pm ⊢ P_join)))
    (hnext : ∀ sf : State, sf.pc = join_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LsCallInv pl sf.mem →
      SepWPp prog target_pc sf (⌜sf.trace = s.trace⌝ ∗ P_join) post panic_post) :
    SepWPp prog target_pc s P post panic_post := by
  intro R hm hL
  rcases hreach.elim hm hL with
    ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hspm, hcsm, htrm, hent⟩ | ⟨hoom, hfalse⟩⟩
  · have hmm' : sm.mem ⊨ (⌜sm.trace = s.trace⌝ ∗ P_join) ∗ R := by
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨htrm, Satisfies.mono (sepConj_mono_left hent) hmm⟩
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hF.of_steps hsteps) R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom, hfalse⟩)⟩

def addEpochMidFramePlaced [LibsignalPlacement] (hkdf : HkdfFn) (A : RustAlloc)
    (s0 : State) (v15 w0 w1 w2 w3 p_root' : BitVec 64)
    (esPin : VecPin) (self : Chain) (epochSecret : EpochSecret) : SepProp :=
  ((lsρ "spqr:.rodata..Lanon.175") ↦ᵣ chainAddEpochInfo) ∗
  ((s0.sp - 192#64) ↦₆₄ w0) ∗ ((s0.sp - 184#64) ↦₆₄ w1) ∗
  ((s0.sp - 176#64) ↦₆₄ w2) ∗ ((s0.sp - 168#64) ↦₆₄ w3) ∗
  calleeSavedStackAt s0 v15 ∗
  ((s0.readReg64 (.gpr 0#5) + 32#64) ↦₆₄ 32#64) ∗
  ((s0.readReg64 (.gpr 0#5) + 40#64) ↦₆₄ p_root') ∗
  ((s0.readReg64 (.gpr 0#5) + 48#64) ↦₆₄ 32#64) ∗
  ((s0.readReg64 (.gpr 0#5) + 56#64) ↦₆₄ (self.currentEpoch + 1#64)) ∗
  ((s0.readReg64 (.gpr 0#5) + 80#64) ↦₃₂ self.dir.toI32) ∗
  chainUntouchedAt (s0.readReg64 (.gpr 0#5)) self ∗
  ((s0.readReg64 (.gpr 1#5) + 8#64) ↦₆₄ esPin.ptr) ∗
  ((s0.readReg64 (.gpr 1#5) + 16#64) ↦₆₄ BitVec.ofNat 64 epochSecret.secret.length) ∗
  ((s0.readReg64 (.gpr 1#5) + 24#64) ↦₆₄ epochSecret.epoch) ∗
  (esPin.ptr ↦ₛ epochSecret.secret) ∗
  vecU8Rest A esPin.cap esPin.ptr epochSecret.secret.length ∗
  A.live p_root' 32 1 ∗
  (p_root' ↦ₛ (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96).take 32)

theorem addEpochMidFramePlaced_def [LibsignalPlacement] (hkdf : HkdfFn) (A : RustAlloc)
    (s0 : State) (v15 w0 w1 w2 w3 p_root' : BitVec 64)
    (esPin : VecPin) (self : Chain) (epochSecret : EpochSecret) :
    ((lsρ "spqr:.rodata..Lanon.175") ↦ᵣ chainAddEpochInfo) ∗
    ((s0.sp - 192#64) ↦₆₄ w0) ∗ ((s0.sp - 184#64) ↦₆₄ w1) ∗
    ((s0.sp - 176#64) ↦₆₄ w2) ∗ ((s0.sp - 168#64) ↦₆₄ w3) ∗
    calleeSavedStackAt s0 v15 ∗
    ((s0.readReg64 (.gpr 0#5) + 32#64) ↦₆₄ 32#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 40#64) ↦₆₄ p_root') ∗
    ((s0.readReg64 (.gpr 0#5) + 48#64) ↦₆₄ 32#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 56#64) ↦₆₄ (self.currentEpoch + 1#64)) ∗
    ((s0.readReg64 (.gpr 0#5) + 80#64) ↦₃₂ self.dir.toI32) ∗
    chainUntouchedAt (s0.readReg64 (.gpr 0#5)) self ∗
    ((s0.readReg64 (.gpr 1#5) + 8#64) ↦₆₄ esPin.ptr) ∗
    ((s0.readReg64 (.gpr 1#5) + 16#64) ↦₆₄ BitVec.ofNat 64 epochSecret.secret.length) ∗
    ((s0.readReg64 (.gpr 1#5) + 24#64) ↦₆₄ epochSecret.epoch) ∗
    (esPin.ptr ↦ₛ epochSecret.secret) ∗
    vecU8Rest A esPin.cap esPin.ptr epochSecret.secret.length ∗
    A.live p_root' 32 1 ∗
    (p_root' ↦ₛ (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96).take 32) =
    addEpochMidFramePlaced hkdf A s0 v15 w0 w1 w2 w3 p_root' esPin self epochSecret := rfl

set_option maxHeartbeats 1600000 in
/-- Relocatable `<spqr::chain::Chain>::add_epoch` (Block `368`) meets
`withLsCallInv lsmpl (chainAddEpochSpecX hkdf A)` under `[LibsignalPlacement]`. -/
theorem chainAddEpoch_placed_ok_of_contracts_x [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hhkdf : subroutine_ok ((blkPC_368).rebase (blkPl_368).base H)
      (lsmpl.base 379) (withLsCallInv lsmpl (hkdfToSliceSpqrSpec hkdf)))
    (hgrow : subroutine_ok ((blkPC_368).rebase (blkPl_368).base H)
      (lsmpl.base 353) (withLsCallInv lsmpl (vecDequeGrowSpec A)))
    (hshim : subroutine_ok ((blkPC_368).rebase (blkPl_368).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withLsCallInv lsmpl (withStack sessionShimSpec extHookStack)))
    (halloc : subroutine_ok ((blkPC_368).rebase (blkPl_368).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (withLsCallInv lsmpl (rustAllocSpecWithStack A extHookStack)))
    (hdealloc : subroutine_ok ((blkPC_368).rebase (blkPl_368).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (withLsCallInv lsmpl (rustDeallocExternSpecWithStack A extHookStack)))
    (hpan_oom : ((blkPC_368).rebase (blkPl_368).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked)
    (hpan_ovf : ((blkPC_368).rebase (blkPl_368).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow") = some Rust.panicked)
    (hpan_core : ((blkPC_368).rebase (blkPl_368).base H).externAt?
      (lsρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic") = some Rust.panicked) :
    subroutine_ok ((blkPC_368).rebase (blkPl_368).base H) (blkPl_368).base
      (withLsCallInv lsmpl (chainAddEpochSpecX hkdf A)) := by
  refine subroutine_ok_withLsCallInv_rodata1_keep rodata_chainAddEpochInfo_placed ?_
  wpp_init x s0
  rcases x with ⟨selfPtr, esPtr, G, esPin, self, epochSecret⟩
  dsimp only at *
  have hinv0 : LsCallInv lsmpl s0.mem := ⟨h_2, h_1⟩
  have hheadroom :
      self.links.length < G.linksCap.toNat ∨
        max (2 * G.linksCap.toNat) 4 * chainEpochSize < 2 ^ 63 := h
  subst h_3 h_4
  refine SepWPp.rw_pre (by rw [stackAt_chainAddEpochX_split s0.sp]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_368).base + 40#64) hinv0 ?_
  refine SepWP.fold (chainAt_unpack_addEpoch A (s0.readReg64 (.gpr 0#5)) G self) (by sep_focus) ?_
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hlen_eq, hlen_le, hnr_le, hnr_lt, hnr_ptr⟩
  refine SepWP.fold (epochSecretAt_unpack A (s0.readReg64 (.gpr 1#5)) esPin epochSecret) (by sep_focus) ?_
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hes_le, hes_lt, hes_ptr⟩
  have hnr_len_lt : self.nextRoot.length < 2 ^ 63 := Nat.lt_of_le_of_lt hnr_le hnr_lt
  have hes_len_lt : epochSecret.secret.length < 2 ^ 63 := Nat.lt_of_le_of_lt hes_le hes_lt
  refine SepWP.bind_cell64 (s0.sp - 72#64) (by sep_focus) fun v15 => ?_
  wp_steps
  refine SepWP.fold (Entails.of_eq (calleeSavedStackAt_def s0 v15)) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv0'
  by_cases hovf : self.currentEpoch = 0xffffffffffffffff#64
  · have herr := isOk_addEpoch_false_of_ovf hkdf self epochSecret hovf
    have hovf_beq : (self.currentEpoch == 0xffffffffffffffff#64) = true := by simp [hovf]
    wp_norm_hyp hovf_beq
    apply SepWPp.of_sepWP (mid := lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow")
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpan_ovf) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_addEpoch_err herr (by simp only [Rust.panicked, arm64_norm]) hm
  · have hovf_beq : (self.currentEpoch == 0xffffffffffffffff#64) = false := by simp [hovf]
    have hovf_cmn := cmn_one_false_of_ne hovf
    wp_norm_hyp hovf_beq
    wp_norm_hyp hovf_cmn
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_368).base + 60#64) hinv0' ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv0''
    by_cases hep : epochSecret.epoch = self.currentEpoch + 1#64
    · rw [chain_addEpoch_eq_ok hkdf hovf hep]
      have hep_bne : (epochSecret.epoch != self.currentEpoch + 1#64) = false := by simp [hep]
      have hep_beq : (epochSecret.epoch == self.currentEpoch + 1#64) = true := by simp [hep]
      wp_norm_hyp hep_bne
      wp_norm_hyp hep_beq
      have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_368).base + 144#64) hinv0'' ?_
      apply SepWP.seq_lsCallInv (mid := lsmpl.base 379) hinv0''
      wp_steps
      refine SepWP.fold (cells12_192_entails_memRegion_96 s0.sp 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv1
      have ⟨hF1, hsym1⟩ := hinv1
      apply SepWP.seq_lsCallInv (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") hinv1
      wp_call hhkdf
        (⟨false, G.nextRoot.ptr, self.nextRoot,
          false, esPin.ptr, epochSecret.secret,
          true, lsρ "spqr:.rodata..Lanon.175", chainAddEpochInfo,
          s0.sp - 192#64, 96⟩ : HkdfToSliceGhost)
      wp_steps
      have hstack_sf : stackAt (s0.sp - 192#64) extHookStack = stackAt sf.sp extHookStack := by
        rw [‹sf.sp = s0.sp - 192#64›]
      refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv2
      have ⟨hF2, hsym2⟩ := hinv2
      apply SepWP.seq_lsCallInv (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") hinv2
      wp_call hshim ()
      wp_steps
      have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
        rw [‹sf_1.sp = sf.sp›]
      refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      rintro ⟨hF3, hsym3⟩
      wp_call halloc (32, 1)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv3
      by_cases hoom1 : sf_2.readReg64 (Reg.gpr 0#5) = 0
      · have hoom1_64 : sf_2.readReg64 (Reg.gpr 0#5) = 0#64 := hoom1
        wp_norm_hyp hoom1_64
        simp only [hoom1, ite_true, sepConj_assoc]
        refine SepWPp.pure_left_focus _ (by sep_focus) ?_
        intro htrace
        apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpan_oom) fun hm => ?_
        simpa only [sepConj_assoc] using
          allowPanic_addEpoch_oom
            (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace,
              ‹sf_1.trace = sf.trace›, ‹sf.trace = s0.trace›])) hm
      · have hoom1_64 : sf_2.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom1
        simp only [hoom1, ite_false, sepConj_assoc]
        refine SepWPp.pure_left_focus _ (by sep_focus) ?_
        rintro ⟨hmod1, htrace1⟩
        wp_norm_hyp htrace1
        obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
          hokm_all, hokm_root, hokm_a2b, hokm_b2a⟩ :=
          exists_unpack64_of_length_96_split
            ‹List.length (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96) = 96›
        refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_368).base + 164#64) hinv3 ?_
        refine SepWP.fold (Entails.of_eq (hokm_sp_reframe_addEpoch s0.sp hokm_all self.dir)) (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (cedStackBothAt_def s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir)) (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (memRegion_32_cells4 (sf_2.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
        sep_elim_exists
        wp_steps
        refine SepWP.fold (Entails.of_eq (hokm_root (sf_2.readReg64 (.gpr 0#5))).symm) (by sep_focus) ?_
        have hstack_sf2 : stackAt sf_1.sp extHookStack = stackAt sf_2.sp extHookStack := by
          rw [‹sf_2.sp = sf_1.sp›]
        refine SepWP.fold (Entails.of_eq hstack_sf2) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hinv4
        refine SepWP.join_lsCallInv (join_pc := (blkPl_368).base + 180#64)
          (P_join :=
            ((lsρ "spqr:.rodata..Lanon.175") ↦ᵣ chainAddEpochInfo) ∗
            ((s0.sp - 192#64) ↦₆₄ w0) ∗ ((s0.sp - 184#64) ↦₆₄ w1) ∗
            ((s0.sp - 176#64) ↦₆₄ w2) ∗ ((s0.sp - 168#64) ↦₆₄ w3) ∗
            cedStackBothAt s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir ∗
            calleeSavedStackAt s0 v15 ∗
            (s0.readReg64 (.gpr 0#5) ↦₆₄ G.linksCap) ∗
            ((s0.readReg64 (.gpr 0#5) + 8#64) ↦₆₄ G.linksPtr) ∗
            ((s0.readReg64 (.gpr 0#5) + 16#64) ↦₆₄ G.linksHead) ∗
            ((s0.readReg64 (.gpr 0#5) + 24#64) ↦₆₄ BitVec.ofNat 64 self.links.length) ∗
            vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
              G.linksCap G.linksPtr G.linksHead (G.epochs.zip self.links) ∗
            ((s0.readReg64 (.gpr 0#5) + 32#64) ↦₆₄ G.nextRoot.cap) ∗
            ((s0.readReg64 (.gpr 0#5) + 40#64) ↦₆₄ G.nextRoot.ptr) ∗
            ((s0.readReg64 (.gpr 0#5) + 48#64) ↦₆₄ BitVec.ofNat 64 self.nextRoot.length) ∗
            ((s0.readReg64 (.gpr 0#5) + 56#64) ↦₆₄ (self.currentEpoch + 1#64)) ∗
            ((s0.readReg64 (.gpr 0#5) + 80#64) ↦₃₂ self.dir.toI32) ∗
            chainUntouchedAt (s0.readReg64 (.gpr 0#5)) self ∗
            (s0.readReg64 (.gpr 1#5) ↦₆₄ esPin.cap) ∗
            ((s0.readReg64 (.gpr 1#5) + 8#64) ↦₆₄ esPin.ptr) ∗
            ((s0.readReg64 (.gpr 1#5) + 16#64) ↦₆₄ BitVec.ofNat 64 epochSecret.secret.length) ∗
            ((s0.readReg64 (.gpr 1#5) + 24#64) ↦₆₄ epochSecret.epoch) ∗
            (esPin.ptr ↦ₛ epochSecret.secret) ∗
            vecU8Rest A esPin.cap esPin.ptr epochSecret.secret.length ∗
            A.live (sf_2.readReg64 (.gpr 0#5)) 32 1 ∗
            (sf_2.readReg64 (.gpr 0#5) ↦ₛ (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96).take 32) ∗
            A.pool ∗ stackAt sf_2.sp extHookStack)
          hinv4 ?_ ?_
        · by_cases hnr_cap : G.nextRoot.cap = 0#64
          · have hnr_cap_beq : (G.nextRoot.cap == 0#64) = true := by simp [hnr_cap]
            wp_norm_hyp hnr_cap_beq
            refine SepWP.fold (Entails.of_eq (vecU8Rest_eq_zero A G.nextRoot.ptr hnr_cap hnr_le)) (by sep_focus) ?_
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            refine ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_⟩
            sep_frame
          · have hnr_cap_beq : (G.nextRoot.cap == 0#64) = false := beq_false_of_ne hnr_cap
            wp_norm_hyp hnr_cap_beq
            refine SepWP.fold (vecU8Rest_nonzero_entails A G.nextRoot.ptr hnr_cap hnr_le hnr_lt) (by sep_focus) ?_
            refine SepWP.pure_left_focus _ (by sep_focus) ?_
            intro hnr_layout
            have ⟨hnr_pos, _, hnr_isize⟩ := hnr_layout
            apply SepWP.seq_lsCallInv (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") hinv4
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            rintro ⟨hF_nr, hsym_nr⟩
            wp_call hdealloc (G.nextRoot.ptr, G.nextRoot.cap.toNat, 1)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, by wp_norm_goal, ?_⟩
            sep_frame
        · intro sf_nr hpc_nr hrun_nr hsp_nr hcs_nr hinv_nr
          wp_split_join hsp_nr hcs_nr
          have htr_nr : sf_nr.trace = sf_2.trace := ‹_›
          wp_norm_hyp htr_nr
          refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_368).base + 212#64) hinv_nr ?_
          apply SepWP.seq_lsCallInv (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") hinv_nr
          wp_steps
          refine SepWP.fold (Entails.of_eq (addEpochMidFramePlaced_def hkdf A s0 v15 w0 w1 w2 w3 (sf_2.readReg64 (.gpr 0#5)) esPin self epochSecret)) (by sep_focus) ?_
          have hstack_nr : stackAt sf_2.sp extHookStack = stackAt sf_nr.sp extHookStack := by
            rw [‹sf_nr.sp = sf_2.sp›]
          refine SepWP.fold (Entails.of_eq hstack_nr) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hinv5
          have ⟨hF5, hsym5⟩ := hinv5
          apply SepWP.seq_lsCallInv (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") hinv5
          wp_call hshim ()
          wp_steps
          have hstack_sf3 : stackAt sf_nr.sp extHookStack = stackAt sf_3.sp extHookStack := by
            rw [‹sf_3.sp = sf_nr.sp›]
          refine SepWP.fold (Entails.of_eq hstack_sf3) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          rintro ⟨hF6, hsym6⟩
          wp_call halloc (72, 1)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hinv6
          by_cases hoom2 : sf_4.readReg64 (Reg.gpr 0#5) = 0
          · have hoom2_64 : sf_4.readReg64 (Reg.gpr 0#5) = 0#64 := hoom2
            wp_norm_hyp hoom2_64
            simp only [hoom2, ite_true, sepConj_assoc]
            refine SepWPp.pure_left_focus _ (by sep_focus) ?_
            intro htrace2
            apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpan_oom) fun hm => ?_
            simpa only [sepConj_assoc] using
              allowPanic_addEpoch_oom
                (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace2,
                  ‹sf_3.trace = sf_nr.trace›, htr_nr, htrace1,
                  ‹sf_1.trace = sf.trace›, ‹sf.trace = s0.trace›])) hm
          · have hoom2_64 : sf_4.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom2
            simp only [hoom2, ite_false, sepConj_assoc]
            refine SepWPp.pure_left_focus _ (by sep_focus) ?_
            rintro ⟨hmod2, htrace2⟩
            wp_norm_hyp htrace2
            refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_368).base + 236#64) hinv6 ?_
            apply SepWP.seq_lsCallInv (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") hinv6
            wp_steps
            have hstack_sf4 : stackAt sf_3.sp extHookStack = stackAt sf_4.sp extHookStack := by
              rw [‹sf_4.sp = sf_3.sp›]
            refine SepWP.fold (Entails.of_eq hstack_sf4) (by sep_focus) ?_
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            intro hinv7
            have ⟨hF7, hsym7⟩ := hinv7
            apply SepWP.seq_lsCallInv (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") hinv7
            wp_call hshim ()
            wp_steps
            have hstack_sf5 : stackAt sf_4.sp extHookStack = stackAt sf_5.sp extHookStack := by
              rw [‹sf_5.sp = sf_4.sp›]
            refine SepWP.fold (Entails.of_eq hstack_sf5) (by sep_focus) ?_
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            rintro ⟨hF8, hsym8⟩
            wp_call halloc (32, 1)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            intro hinv8
            by_cases hoom3 : sf_6.readReg64 (Reg.gpr 0#5) = 0
            · have hoom3_64 : sf_6.readReg64 (Reg.gpr 0#5) = 0#64 := hoom3
              wp_norm_hyp hoom3_64
              simp only [hoom3, ite_true, sepConj_assoc]
              refine SepWPp.pure_left_focus _ (by sep_focus) ?_
              intro htrace3
              apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
              wp_steps
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpan_oom) fun hm => ?_
              simpa only [sepConj_assoc] using
                allowPanic_addEpoch_oom
                  (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace3,
                    ‹sf_5.trace = sf_4.trace›, htrace2,
                    ‹sf_3.trace = sf_nr.trace›, htr_nr, htrace1,
                    ‹sf_1.trace = sf.trace›, ‹sf.trace = s0.trace›])) hm
            · have hoom3_64 : sf_6.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom3
              simp only [hoom3, ite_false, sepConj_assoc]
              refine SepWPp.pure_left_focus _ (by sep_focus) ?_
              rintro ⟨hmod3, htrace3⟩
              wp_norm_hyp htrace3
              refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_368).base + 288#64) hinv8 ?_
              apply SepWP.seq_lsCallInv (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") hinv8
              refine SepWP.fold (Entails.of_eq (cedStackBothAt_def s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir).symm) (by sep_focus) ?_
              refine SepWP.fold (Entails.of_eq (memRegion_32_cells4 (sf_6.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
              sep_elim_exists
              wp_steps
              refine SepWP.fold (Entails.of_eq (cedCells_eq_pointsToBytes hokm_a2b hokm_b2a self.dir (sf_6.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
              refine SepWP.fold (Entails.of_eq (cedStackBothAt_def s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir)) (by sep_focus) ?_
              have hstack_sf6 : stackAt sf_5.sp extHookStack = stackAt sf_6.sp extHookStack := by
                rw [‹sf_6.sp = sf_5.sp›]
              refine SepWP.fold (Entails.of_eq hstack_sf6) (by sep_focus) ?_
              apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
              intro hinv9
              have ⟨hF9, hsym9⟩ := hinv9
              apply SepWP.seq_lsCallInv (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") hinv9
              wp_call hshim ()
              wp_steps
              have hstack_sf7 : stackAt sf_6.sp extHookStack = stackAt sf_7.sp extHookStack := by
                rw [‹sf_7.sp = sf_6.sp›]
              refine SepWP.fold (Entails.of_eq hstack_sf7) (by sep_focus) ?_
              apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
              rintro ⟨hF10, hsym10⟩
              wp_call halloc (72, 1)
              apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
              intro hinv10
              by_cases hoom4 : sf_8.readReg64 (Reg.gpr 0#5) = 0
              · have hoom4_64 : sf_8.readReg64 (Reg.gpr 0#5) = 0#64 := hoom4
                wp_norm_hyp hoom4_64
                simp only [hoom4, ite_true, sepConj_assoc]
                refine SepWPp.pure_left_focus _ (by sep_focus) ?_
                intro htrace4
                apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
                wp_steps
                apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
                refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpan_oom) fun hm => ?_
                simpa only [sepConj_assoc] using
                  allowPanic_addEpoch_oom
                    (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace4,
                      ‹sf_7.trace = sf_6.trace›, htrace3,
                      ‹sf_5.trace = sf_4.trace›, htrace2,
                      ‹sf_3.trace = sf_nr.trace›, htr_nr, htrace1,
                      ‹sf_1.trace = sf.trace›, ‹sf.trace = s0.trace›])) hm
              · have hoom4_64 : sf_8.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom4
                simp only [hoom4, ite_false, sepConj_assoc]
                refine SepWPp.pure_left_focus _ (by sep_focus) ?_
                rintro ⟨hmod4, htrace4⟩
                wp_norm_hyp htrace4
                refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_368).base + 312#64) hinv10 ?_
                apply SepWP.seq_lsCallInv (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") hinv10
                wp_steps
                have hstack_sf8 : stackAt sf_7.sp extHookStack = stackAt sf_8.sp extHookStack := by
                  rw [‹sf_8.sp = sf_7.sp›]
                refine SepWP.fold (Entails.of_eq hstack_sf8) (by sep_focus) ?_
                apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                intro hinv11
                have ⟨hF11, hsym11⟩ := hinv11
                apply SepWP.seq_lsCallInv (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") hinv11
                wp_call hshim ()
                wp_steps
                have hstack_sf9 : stackAt sf_8.sp extHookStack = stackAt sf_9.sp extHookStack := by
                  rw [‹sf_9.sp = sf_8.sp›]
                refine SepWP.fold (Entails.of_eq hstack_sf9) (by sep_focus) ?_
                apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                rintro ⟨hF12, hsym12⟩
                wp_call halloc (32, 1)
                apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                intro hinv12
                by_cases hoom5 : sf_10.readReg64 (Reg.gpr 0#5) = 0
                · have hoom5_64 : sf_10.readReg64 (Reg.gpr 0#5) = 0#64 := hoom5
                  wp_norm_hyp hoom5_64
                  simp only [hoom5, ite_true, sepConj_assoc]
                  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
                  intro htrace5
                  apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
                  wp_steps
                  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
                  refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpan_oom) fun hm => ?_
                  simpa only [sepConj_assoc] using
                    allowPanic_addEpoch_oom
                      (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace5,
                        ‹sf_9.trace = sf_8.trace›, htrace4,
                        ‹sf_7.trace = sf_6.trace›, htrace3,
                        ‹sf_5.trace = sf_4.trace›, htrace2,
                        ‹sf_3.trace = sf_nr.trace›, htr_nr, htrace1,
                        ‹sf_1.trace = sf.trace›, ‹sf.trace = s0.trace›])) hm
                · have hoom5_64 : sf_10.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom5
                  simp only [hoom5, ite_false, sepConj_assoc]
                  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
                  rintro ⟨hmod5, htrace5⟩
                  wp_norm_hyp htrace5
                  refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_368).base + 344#64) hinv12 ?_
                  refine SepWP.fold (Entails.of_eq (cedStackBothAt_def s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir).symm) (by sep_focus) ?_
                  refine SepWP.fold (Entails.of_eq (memRegion_32_cells4 (sf_10.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
                  sep_elim_exists
                  wp_steps
                  refine SepWP.fold (Entails.of_eq (cedCells_eq_pointsToBytes hokm_a2b hokm_b2a self.dir.switch (sf_10.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
                  refine SepWP.fold (Entails.of_eq (cedStackBothAt_def s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir)) (by sep_focus) ?_
                  have hstack_sf10 : stackAt sf_9.sp extHookStack = stackAt sf_10.sp extHookStack := by
                    rw [‹sf_10.sp = sf_9.sp›]
                  refine SepWP.fold (Entails.of_eq hstack_sf10) (by sep_focus) ?_
                  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                  intro hinv13
                  let cap1 : BitVec 64 :=
                    if self.links.length = G.linksCap.toNat then newCapChainEpoch G.linksCap else G.linksCap
                  have hlen_lt_cap1 : self.links.length < cap1.toNat := by
                    dsimp only [cap1]
                    split_ifs with heq
                    · exact len_lt_newCapChainEpoch heq (Or.resolve_left hheadroom (by omega))
                    · omega
                  refine SepWPp.join_at_348_lsCallInv (join_pc := (blkPl_368).base + 348#64) (cap1 := cap1)
                    (P_join :=
                      ∃∗ ptr1 : BitVec 64, ∃∗ head1 : BitVec 64,
                        addEpochMidFramePlaced hkdf A s0 v15 w0 w1 w2 w3 (sf_2.readReg64 (.gpr 0#5)) esPin self epochSecret ∗
                        cedStackBothAt s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir ∗
                        (s0.readReg64 (.gpr 0#5) ↦₆₄ cap1) ∗
                        ((s0.readReg64 (.gpr 0#5) + 8#64) ↦₆₄ ptr1) ∗
                        ((s0.readReg64 (.gpr 0#5) + 16#64) ↦₆₄ head1) ∗
                        ((s0.readReg64 (.gpr 0#5) + 24#64) ↦₆₄ BitVec.ofNat 64 self.links.length) ∗
                        vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
                          cap1 ptr1 head1 (G.epochs.zip self.links) ∗
                        (s0.readReg64 (.gpr 1#5) ↦₆₄ esPin.cap) ∗
                        A.live (sf_4.readReg64 (.gpr 0#5)) 72 1 ∗
                        memRegion (sf_4.readReg64 (.gpr 0#5)) 72 ∗
                        A.live (sf_6.readReg64 (.gpr 0#5)) 32 1 ∗
                        (sf_6.readReg64 (.gpr 0#5) ↦ₛ (Chain.cedForDirection (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96) self.dir).next) ∗
                        A.live (sf_8.readReg64 (.gpr 0#5)) 72 1 ∗
                        memRegion (sf_8.readReg64 (.gpr 0#5)) 72 ∗
                        A.live (sf_10.readReg64 (.gpr 0#5)) 32 1 ∗
                        (sf_10.readReg64 (.gpr 0#5) ↦ₛ (Chain.cedForDirection (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96) self.dir.switch).next) ∗
                        A.pool ∗ stackAt sf_10.sp extHookStack)
                    hinv13 ?_ ?_
                  · by_cases heq_cap : self.links.length = G.linksCap.toNat
                    · have hcap1_eq : cap1 = newCapChainEpoch G.linksCap := by simp [cap1, heq_cap]
                      have hcmp_eq : (BitVec.ofNat 64 self.links.length == G.linksCap) = true := by
                        rw [heq_cap]; simp
                      wp_norm_hyp hcmp_eq
                      have hgrow_ok : max (2 * G.linksCap.toNat) 4 * chainEpochSize < 2 ^ 63 :=
                        Or.resolve_left hheadroom (by omega)
                      have hzip_eq : (G.epochs.zip self.links).length = G.linksCap.toNat := by
                        simp [hlen_eq, heq_cap]
                      refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 353) hinv13 ?_
                      refine SepWP.fold (vecDequeAt_fold_addEpoch A (s0.readReg64 (.gpr 0#5)) G.linksCap G.linksPtr G.linksHead G self hlen_eq) (by sep_focus) ?_
                      wp_steps
                      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                      intro hinv14
                      change subroutine_ok _ _ (withLsCallInv lsmpl (vecDequeGrowSpec A)) at hgrow
                      apply SepWPp.reassoc_panic
                      wpp_call_lsCallInv_addEpoch hgrow
                        (⟨s0.readReg64 (.gpr 0#5), G.linksCap, G.linksPtr, G.linksHead, G.epochs.zip self.links⟩ : VecDequeGrowGhost)
                        hinv14
                      refine SepWP.unfold_vecDeque_bind A (s0.readReg64 (.gpr 0#5)) (newCapChainEpoch G.linksCap) G self hlen_eq (by sep_focus) ?_
                      intro ptr1 head1
                      wp_steps
                      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                      refine ⟨by wp_norm_goal, by wp_norm_goal, by rw [hcap1_eq]; wp_norm_goal, by wp_norm_goal, ?_⟩
                      rw [hcap1_eq]
                      refine Entails.sepExists_right ptr1 (Entails.sepExists_right head1 ?_)
                      sep_frame
                    · have hcap1_eq : cap1 = G.linksCap := by simp [cap1, heq_cap]
                      have hcmp_ne : BitVec.ofNat 64 self.links.length ≠ G.linksCap :=
                        ofNat_len_ne_cap (by omega)
                      have hcmp_eq : (BitVec.ofNat 64 self.links.length == G.linksCap) = false :=
                        beq_false_of_ne hcmp_ne
                      have hcmp_sub := sub_eq_zero_false_of_ne hcmp_ne
                      have hcmp_add := add_neg_eq_zero_false_of_ne hcmp_ne
                      wp_norm_hyp hcmp_eq
                      wp_norm_hyp hcmp_sub
                      wp_norm_hyp hcmp_add
                      apply SepWPp.of_sepWP_ret
                      wp_steps
                      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                      refine ⟨by wp_norm_goal, by wp_norm_goal, by rw [hcap1_eq]; wp_norm_goal, by wp_norm_goal, ?_⟩
                      rw [hcap1_eq]
                      refine Entails.sepExists_right G.linksPtr (Entails.sepExists_right G.linksHead ?_)
                      sep_frame
                  · intro sf_348 hpc_348 hrun_348 hsp_348 hreg_348 hcap_348 hinv_348
                    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
                    intro htr_348
                    apply SepWPp.exists_elim; intro ptr1
                    apply SepWPp.exists_elim; intro head1
                    wp_split_join hsp_348 hreg_348
                    wp_norm_hyp hcap_348
                    wp_norm_hyp htr_348
                    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_368).base + 428#64) hinv_348 ?_
                    refine SepWP.fold (vecDequeRingBuf_split_madd_links A cap1 ptr1 head1 G self hlen_eq hlen_lt_cap1) (by sep_focus) ?_
                    sep_elim_exists
                    refine SepWP.pure_left_focus _ (by sep_focus) ?_
                    rintro ⟨hhead1, hcap1_lt, hptr1⟩
                    wp_steps
                    have hmadd_eq := physIdx_madd_eq (ptr := ptr1) hhead1 hlen_lt_cap1 hcap1_lt
                    let slotPtr := ptr1 + BitVec.ofNat 64 (vecDequePhysIdx head1.toNat cap1.toNat self.links.length * 112)
                    refine SepWP.fold (chainEpochDirectionAt_madd_send_intro A _ slotPtr
                      (sf_6.readReg64 (.gpr 0#5)) (sf_4.readReg64 (.gpr 0#5)) hmadd_eq
                      ‹List.length (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96) = 96›
                      self.dir hoom3_64 hoom2_64) (by sep_focus) ?_
                    refine SepWP.fold (chainEpochDirectionAt_madd_recv_intro A _ slotPtr
                      (sf_10.readReg64 (.gpr 0#5)) (sf_8.readReg64 (.gpr 0#5)) hmadd_eq
                      ‹List.length (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96) = 96›
                      self.dir.switch hoom5_64 hoom4_64) (by sep_focus) ?_
                    have hlen_add1 := ofNat_len_add_one hlen_lt_cap1 hcap1_lt
                    have hlen_cell :
                        ((s0.readReg64 (.gpr 0#5) + 24#64) ↦₆₄ (BitVec.ofNat 64 self.links.length + 1#64)) =
                        ((s0.readReg64 (.gpr 0#5) + 24#64) ↦₆₄ BitVec.ofNat 64 (self.links.length + 1)) := by
                      rw [hlen_add1]
                    refine SepWP.fold (Entails.of_eq hlen_cell) (by sep_focus) ?_
                    refine SepWP.fold (Entails.of_eq (addEpochMidFramePlaced_def hkdf A s0 v15 w0 w1 w2 w3 (sf_2.readReg64 (.gpr 0#5)) esPin self epochSecret).symm) (by sep_focus) ?_
                    refine SepWP.fold (Entails.of_eq (calleeSavedStackAt_def s0 v15).symm) (by sep_focus) ?_
                    refine SepWP.fold (Entails.of_eq (cedStackBothAt_def s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir).symm) (by sep_focus) ?_
                    have hep_cell :
                        ((s0.readReg64 (.gpr 0#5) + 56#64) ↦₆₄ (self.currentEpoch + 1#64)) =
                        ((s0.readReg64 (.gpr 0#5) + 56#64) ↦₆₄ epochSecret.epoch) := by
                      rw [hep]
                    refine SepWP.fold (Entails.of_eq hep_cell) (by sep_focus) ?_
                    have hchain_intro := chainRepr_addEpoch_intro A hkdf
                      (s0.readReg64 (.gpr 0#5)) cap1 ptr1 head1
                      (sf_2.readReg64 (.gpr 0#5))
                      (sf_6.readReg64 (.gpr 0#5)) (sf_4.readReg64 (.gpr 0#5))
                      (sf_10.readReg64 (.gpr 0#5)) (sf_8.readReg64 (.gpr 0#5))
                      G self epochSecret hlen_eq hlen_lt_cap1 hhead1 hcap1_lt hptr1 hoom1_64
                      ‹List.length (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96) = 96›
                    dsimp only [] at hchain_intro
                    refine SepWP.fold hchain_intro (by sep_focus) ?_
                    refine SepWP.fold (cells4_entails_memRegion_32 (s0.readReg64 (.gpr 1#5))
                      esPin.cap esPin.ptr (BitVec.ofNat 64 epochSecret.secret.length) epochSecret.epoch)
                      (by sep_focus) ?_
                    refine SepWP.fold (Entails.of_eq (cedCells_reframe_addEpoch s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir).symm) (by sep_focus) ?_
                    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                    intro hinv15
                    by_cases hes_cap : esPin.cap = 0#64
                    · have hes_cap_beq : (esPin.cap == 0#64) = true := by simp [hes_cap]
                      wp_norm_hyp hes_cap_beq
                      apply SepWPp.of_sepWP_ret
                      refine SepWP.fold (Entails.of_eq (vecU8Rest_eq_zero A esPin.ptr hes_cap hes_le)) (by sep_focus) ?_
                      wp_steps
                      have hstack_348 : stackAt sf_10.sp extHookStack = stackAt (s0.sp - 192#64) extHookStack := by
                        rw [‹sf_10.sp = sf_9.sp›, ‹sf_9.sp = sf_8.sp›, ‹sf_8.sp = sf_7.sp›,
                          ‹sf_7.sp = sf_6.sp›, ‹sf_6.sp = sf_5.sp›, ‹sf_5.sp = sf_4.sp›,
                          ‹sf_4.sp = sf_3.sp›, ‹sf_3.sp = sf_nr.sp›, ‹sf_nr.sp = sf_2.sp›,
                          ‹sf_2.sp = sf_1.sp›, ‹sf_1.sp = sf.sp›, ‹sf.sp = s0.sp - 192#64›]
                      refine SepWP.fold (Entails.of_eq hstack_348) (by sep_focus) ?_
                      refine SepWP.fold (rejoin_stack_chainAddEpochX s0.sp
                        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
                        (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
                        (s0.readReg64 (.gpr 27#5)) v15
                        (s0.readReg64 (.gpr 26#5)) (s0.readReg64 (.gpr 25#5))
                        (s0.readReg64 (.gpr 24#5)) (s0.readReg64 (.gpr 23#5))
                        (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5))
                        (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5)))
                        (by sep_focus) ?_
                      wp_done
                    · have hes_cap_beq : (esPin.cap == 0#64) = false := beq_false_of_ne hes_cap
                      wp_norm_hyp hes_cap_beq
                      refine SepWPp.of_sepWP_lsCallInv (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") hinv15 ?_
                      refine SepWP.fold (vecU8Rest_nonzero_entails A esPin.ptr hes_cap hes_le hes_lt) (by sep_focus) ?_
                      refine SepWP.pure_left_focus _ (by sep_focus) ?_
                      intro hes_layout
                      have ⟨hes_pos, _, hes_isize⟩ := hes_layout
                      wp_steps
                      have hstack_348 : stackAt sf_10.sp extHookStack = stackAt (s0.sp - 192#64) extHookStack := by
                        rw [‹sf_10.sp = sf_9.sp›, ‹sf_9.sp = sf_8.sp›, ‹sf_8.sp = sf_7.sp›,
                          ‹sf_7.sp = sf_6.sp›, ‹sf_6.sp = sf_5.sp›, ‹sf_5.sp = sf_4.sp›,
                          ‹sf_4.sp = sf_3.sp›, ‹sf_3.sp = sf_nr.sp›, ‹sf_nr.sp = sf_2.sp›,
                          ‹sf_2.sp = sf_1.sp›, ‹sf_1.sp = sf.sp›, ‹sf.sp = s0.sp - 192#64›]
                      refine SepWP.fold (Entails.of_eq hstack_348) (by sep_focus) ?_
                      refine SepWP.fold (rejoin_stack_chainAddEpochX s0.sp
                        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
                        (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
                        (s0.readReg64 (.gpr 27#5)) v15
                        (s0.readReg64 (.gpr 26#5)) (s0.readReg64 (.gpr 25#5))
                        (s0.readReg64 (.gpr 24#5)) (s0.readReg64 (.gpr 23#5))
                        (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5))
                        (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5)))
                        (by sep_focus) ?_
                      refine SepWP.fold (Entails.of_eq (stackAt_chainAddEpochX_top_split s0.sp)) (by sep_focus) ?_
                      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                      rintro ⟨hF16, hsym16⟩
                      apply SepWPp.of_sepWP_ret
                      wp_call hdealloc (esPin.ptr, esPin.cap.toNat, 1)
                      refine SepWP.fold (Entails.of_eq (stackAt_chainAddEpochX_top_split s0.sp).symm) (by sep_focus) ?_
                      wp_done
    · have herr := isOk_addEpoch_false_of_epoch_ne hkdf self epochSecret hovf hep
      have hep_bne : (epochSecret.epoch != self.currentEpoch + 1#64) = true := by simp [hep]
      have hep_beq : (epochSecret.epoch == self.currentEpoch + 1#64) = false := beq_false_of_ne hep
      have hep_sub := sub_eq_zero_false_of_ne hep
      have hep_add := add_neg_eq_zero_false_of_ne hep
      wp_norm_hyp hep_bne
      wp_norm_hyp hep_beq
      wp_norm_hyp hep_sub
      wp_norm_hyp hep_add
      apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic")
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpan_core) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_addEpoch_err herr (by simp only [Rust.panicked, arm64_norm]) hm

/-- Relocatable `<spqr::chain::Chain>::add_epoch` (Block `368`) meets
`withLsCallInv lsmpl (chainAddEpochSpecX hkdf A)` under `[LibsignalPlacement]`,
lifting plain/codeLoaded callee specs to `withLsCallInv`. -/
theorem chainAddEpoch_placed_ok [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hhkdf : subroutine_ok ((blkPC_368).rebase (blkPl_368).base H)
      (lsmpl.base 379) (hkdfToSliceSpqrSpec hkdf))
    (hgrow : subroutine_ok ((blkPC_368).rebase (blkPl_368).base H)
      (lsmpl.base 353) (withLsCodeLoaded lsmpl (vecDequeGrowSpec A)))
    (hshim : subroutine_ok ((blkPC_368).rebase (blkPl_368).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack sessionShimSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_368).rebase (blkPl_368).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack A extHookStack))
    (hdealloc : subroutine_ok ((blkPC_368).rebase (blkPl_368).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocExternSpecWithStack A extHookStack))
    (hpan_oom : ((blkPC_368).rebase (blkPl_368).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked)
    (hpan_ovf : ((blkPC_368).rebase (blkPl_368).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow") = some Rust.panicked)
    (hpan_core : ((blkPC_368).rebase (blkPl_368).base H).externAt?
      (lsρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic") = some Rust.panicked) :
    subroutine_ok ((blkPC_368).rebase (blkPl_368).base H) (blkPl_368).base
      (withLsCallInv lsmpl (chainAddEpochSpecX hkdf A)) :=
  chainAddEpoch_placed_ok_of_contracts_x
    (subroutine_ok_withLsCallInv_of_plain hhkdf)
    (subroutine_ok_withLsCallInv_of_withLsCodeLoaded hgrow)
    (subroutine_ok_withLsCallInv_of_plain hshim)
    (subroutine_ok_withLsCallInv_of_plain halloc)
    (subroutine_ok_withLsCallInv_of_plain hdealloc)
    hpan_oom hpan_ovf hpan_core

end CryptoVerification.SpqrV1.ChainProofs
