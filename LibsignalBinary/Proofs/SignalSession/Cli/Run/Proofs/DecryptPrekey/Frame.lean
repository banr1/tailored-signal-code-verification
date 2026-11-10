/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Spec
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
public import ProofLib.SepLogic.WP
import ProofLib.SepLogic.WPp

/-!
# Stack-Frame Layout Helpers for `signal_session_handshake::decrypt_prekey`

Separation-logic and 64-bit word-cell (`↦₆₄`) layout helpers for the `2144`-byte (`0x860`) stack
frame of `signal_session_handshake::decrypt_prekey`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers

open Arm64 ProofLib
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.Cli

/-! ## Word-list unpacking & arithmetic helpers -/
theorem args13_unpack {xs : List (BitVec 64)} {r0 r1 r2 r3 r4 r5 r6 r7 : BitVec 64}
    (hlen : xs.length = 13) (htake : xs.take 8 = [r0, r1, r2, r3, r4, r5, r6, r7]) :
    ∃ a8 a9 a10 a11 a12 : BitVec 64, xs.drop 8 = [a8, a9, a10, a11, a12] ∧
      xs = [r0, r1, r2, r3, r4, r5, r6, r7, a8, a9, a10, a11, a12] := by
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, _ | ⟨x7,
    _ | ⟨a8, _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> try (simp at hlen)
  injection htake with e0 htake; subst e0; injection htake with e1 htake; subst e1
  injection htake with e2 htake; subst e2; injection htake with e3 htake; subst e3
  injection htake with e4 htake; subst e4; injection htake with e5 htake; subst e5
  injection htake with e6 htake; subst e6; injection htake with e7 _; subst e7
  exact ⟨a8, a9, a10, a11, a12, rfl, rfl⟩

theorem ws6_unpack {ws : List (BitVec 64)}
    (hlen : ws.length = 6) (hhead : ws.head? ≠ some (BitVec.ofNat 64 (2 ^ 64 - 3))) :
    ∃ w0 w1 w2 w3 w4 w5 : BitVec 64,
      ws = [w0, w1, w2, w3, w4, w5] ∧ w0 ≠ BitVec.ofNat 64 (2 ^ 64 - 3) := by
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | _⟩⟩⟩⟩⟩⟩ <;> try (simp at hlen)
  refine ⟨w0, w1, w2, w3, w4, w5, rfl, fun h => ?_⟩; subst h; exact hhead rfl

theorem cmn3_ne_zero {w0 : BitVec 64} (hne : w0 ≠ BitVec.ofNat 64 (2 ^ 64 - 3)) :
    w0 + 3#64 ≠ 0#64 ∧ (w0 + 3#64 == 0#64) = false := by
  have h1 : w0 + 3#64 ≠ 0#64 := by bv_omega
  exact ⟨h1, beq_false_of_ne h1⟩

theorem fnAddr_poll_eq_add_rel (img : Obj.Image) (ext : String → Option (State → State))
    {wrapOff pollOff : Nat}
    (hwrap : libsignalSessionCode.fnOff cliDecryptPrekeyName = wrapOff)
    (hpoll : libsignalSessionCode.fnOff cliDpPollName = pollOff) :
    (tripleRatchetProgAtExt img.base ext).fnAddr cliDpPollName =
      (tripleRatchetProgAtExt img.base ext).fnAddr cliDecryptPrekeyName +
        (BitVec.ofNat 64 pollOff - BitVec.ofNat 64 wrapOff) := by
  dsimp only [tripleRatchetProgAtExt]; rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hwrap, hpoll]; bv_omega

theorem allocFailedIn_eq_of_trace_eq {s0 s1 sf : State} (htr : s1.trace = s0.trace) :
    allocFailedIn s1 sf ↔ allocFailedIn s0 sf := by simp only [allocFailedIn, htr]

/-! ## Word-list & 48-byte return slot conversions -/

theorem memRegion_48_words (a : BitVec 64) :
    memRegion a 48 =
      ∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, ∃∗ r2 : BitVec 64,
      ∃∗ r3 : BitVec 64, ∃∗ r4 : BitVec 64, ∃∗ r5 : BitVec 64,
        (a ↦₆₄ r0) ∗ ((a + 8#64) ↦₆₄ r1) ∗ ((a + 16#64) ↦₆₄ r2) ∗
        ((a + 24#64) ↦₆₄ r3) ∗ ((a + 32#64) ↦₆₄ r4) ∗ ((a + 40#64) ↦₆₄ r5) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 40) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 32) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 24) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 16) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 8) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64), ProofLib.memRegion_eight (a + 24#64),
      ProofLib.memRegion_eight (a + 32#64), ProofLib.memRegion_eight (a + 40#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.antisymm
  · refine Entails.sepExists_elim fun r5 => Entails.sepExists_elim fun r4 =>
      Entails.sepExists_elim fun r3 => Entails.sepExists_elim fun r2 =>
      Entails.sepExists_elim fun r1 => Entails.sepExists_elim fun r0 => ?_
    exact Entails.sepExists_right r0 (Entails.sepExists_right r1 (Entails.sepExists_right r2
      (Entails.sepExists_right r3 (Entails.sepExists_right r4 (Entails.sepExists_right r5
        (Entails.refl _))))))
  · refine Entails.sepExists_elim fun r0 => Entails.sepExists_elim fun r1 =>
      Entails.sepExists_elim fun r2 => Entails.sepExists_elim fun r3 =>
      Entails.sepExists_elim fun r4 => Entails.sepExists_elim fun r5 => ?_
    exact Entails.sepExists_right r5 (Entails.sepExists_right r4 (Entails.sepExists_right r3
      (Entails.sepExists_right r2 (Entails.sepExists_right r1 (Entails.sepExists_right r0
        (Entails.refl _))))))

theorem dpWords5_eq (a a8 a9 a10 a11 a12 : BitVec 64) :
    dpWordsAt a [a8, a9, a10, a11, a12] =
      (a ↦₆₄ a8) ∗ ((a + 8#64) ↦₆₄ a9) ∗ ((a + 16#64) ↦₆₄ a10) ∗
      ((a + 24#64) ↦₆₄ a11) ∗ ((a + 32#64) ↦₆₄ a12) := by
  simp only [dpWordsAt, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

theorem dpWords6_eq (a w0 w1 w2 w3 w4 w5 : BitVec 64) :
    dpWordsAt a [w0, w1, w2, w3, w4, w5] =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) := by
  simp only [dpWordsAt, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

theorem dpRetRes_pack {res : List (BitVec 64) → SepProp}
    (ret w0 w1 w2 w3 w4 w5 : BitVec 64)
    (hw0_ne : w0 ≠ BitVec.ofNat 64 (2 ^ 64 - 3)) :
    dpWordsAt ret [w0, w1, w2, w3, w4, w5] ∗ res [w0, w1, w2, w3, w4, w5] ⊢
      ∃∗ ws : List (BitVec 64),
        ⌜ws.length = 6 ∧ ws.head? ≠ some (BitVec.ofNat 64 (2 ^ 64 - 3))⌝ ∗
          dpWordsAt ret ws ∗ res ws := by
  refine Entails.sepExists_right [w0, w1, w2, w3, w4, w5] (Entails.pure_right ⟨rfl, ?_⟩ (Entails.refl _))
  intro h; injection h with h'; exact hw0_ne h'

theorem dpPost_pack {ioProp : Prop} {res : List (BitVec 64) → SepProp}
    {ret sp0 : BitVec 64} {args8 : List (BitVec 64)} {stk : Nat}
    (hio : ioProp) :
    (∃∗ ws : List (BitVec 64),
        ⌜ws.length = 6 ∧ ws.head? ≠ some (BitVec.ofNat 64 (2 ^ 64 - 3))⌝ ∗
          dpWordsAt ret ws ∗ res ws) ∗
      dpWordsAt sp0 args8 ∗ stackAt sp0 stk ⊢
    ⌜ioProp⌝ ∗
      (∃∗ ws : List (BitVec 64),
        ⌜ws.length = 6 ∧ ws.head? ≠ some (BitVec.ofNat 64 (2 ^ 64 - 3))⌝ ∗
          dpWordsAt ret ws ∗ res ws) ∗
      dpWordsAt sp0 args8 ∗ stackAt sp0 stk :=
  Entails.pure_right hio (Entails.refl _)

/-! ## Opaque caller frame bundle & fast `SepWP` existential unpackers -/

def dpCallerFrame (s0 : State) (ret : BitVec 64) (args8 : List (BitVec 64)) : SepProp :=
  dpWordsAt s0.sp args8 ∗ memRegion ret 48 ∗ memRegion (s0.sp - 56#64) 8 ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 Reg.fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

theorem dpCallerFrame_pack (s0 : State) (ret : BitVec 64) (args8 : List (BitVec 64)) :
    dpWordsAt s0.sp args8 ∗ memRegion ret 48 ∗ memRegion (s0.sp - 56#64) 8 ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 Reg.fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
    dpCallerFrame s0 ret args8 := Entails.refl _

private theorem sepWP_pull_exists_left {α : Type} {prog : Program} {tgt : BitVec 64} {s : State}
    {F : α → SepProp} {R : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x, SepWP prog tgt s (F x ∗ R) Q oom) :
    SepWP prog tgt s ((∃∗ x, F x) ∗ R) Q oom := by
  rw [sepExists_sepConj_left]; exact SepWP.exists_left h

theorem sepWP_unpack_callerFrame {prog : Program} {tgt : BitVec 64} {s s0 : State}
    {ret : BitVec 64} {args8 : List (BitVec 64)} {R : SepProp}
    {Q : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ r0 r1 r2 r3 r4 r5 : BitVec 64,
      SepWP prog tgt s
        (((ret ↦₆₄ r0) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r2) ∗
          ((ret + 24#64) ↦₆₄ r3) ∗ ((ret + 32#64) ↦₆₄ r4) ∗ ((ret + 40#64) ↦₆₄ r5)) ∗
          dpWordsAt s0.sp args8 ∗ memRegion (s0.sp - 56#64) 8 ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 Reg.fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗ R) Q oom) :
    SepWP prog tgt s (R ∗ dpCallerFrame s0 ret args8) Q oom := by
  have heq : R ∗ dpCallerFrame s0 ret args8 =
      memRegion ret 48 ∗ (dpWordsAt s0.sp args8 ∗ memRegion (s0.sp - 56#64) 8 ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 Reg.fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗ R) := by
    dsimp only [dpCallerFrame]; ac_rfl
  rw [heq, memRegion_48_words ret]
  exact sepWP_pull_exists_left fun r0 => sepWP_pull_exists_left fun r1 =>
    sepWP_pull_exists_left fun r2 => sepWP_pull_exists_left fun r3 =>
    sepWP_pull_exists_left fun r4 => sepWP_pull_exists_left (fun r5 => h r0 r1 r2 r3 r4 r5)

/-! ## Two-stage wrapper stack frame (`dpWrapFrame = 2144`) unpack & pack -/

private theorem stackAt_dp_top (sp0 : BitVec 64) {stk : Nat}
    (hge : dpWrapFrame ≤ stk) (hle : stk ≤ 2 ^ 64) :
    stackAt sp0 stk =
      stackAt (sp0 - 2144#64) (stk - dpWrapFrame) ∗ memRegion (sp0 - 2144#64) 2144 := by
  have hsum : (stk - dpWrapFrame) + 2144 = stk := by dsimp only [dpWrapFrame] at hge ⊢; omega
  conv => lhs; rw [← hsum]
  simp only [stackAt]
  rw [ProofLib.memRegion_split' (n := stk - dpWrapFrame) (k := 2144) rfl rfl (by omega)]
  have e1 : sp0 - BitVec.ofNat 64 (stk - dpWrapFrame + 2144) =
      sp0 - 2144#64 - BitVec.ofNat 64 (stk - dpWrapFrame) := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
  rw [e1, BitVec.sub_add_cancel]

theorem sepWP_with_dp_saved {prog : Program} {tgt : BitVec 64} {s : State}
    {stk : Nat} (hge : dpWrapFrame ≤ stk) (hle : stk ≤ 2 ^ 64)
    {R : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ sfp slr sx28 sx21 sx20 sx19 : BitVec 64,
      SepWP prog tgt s
        ((((s.sp - 48#64) ↦₆₄ sfp) ∗ ((s.sp - 40#64) ↦₆₄ slr) ∗
          ((s.sp - 32#64) ↦₆₄ sx28) ∗ ((s.sp - 24#64) ↦₆₄ sx21) ∗
          ((s.sp - 16#64) ↦₆₄ sx20) ∗ ((s.sp - 8#64) ↦₆₄ sx19)) ∗
          memRegion (s.sp - 2144#64) 2088 ∗ memRegion (s.sp - 56#64) 8 ∗
          stackAt (s.sp - 2144#64) (stk - dpWrapFrame) ∗ R) Q oom) :
    SepWP prog tgt s (R ∗ stackAt s.sp stk) Q oom := by
  have htop : R ∗ stackAt s.sp stk =
      memRegion (s.sp - 48#64) 48 ∗
        (memRegion (s.sp - 2144#64) 2088 ∗ memRegion (s.sp - 56#64) 8 ∗
         stackAt (s.sp - 2144#64) (stk - dpWrapFrame) ∗ R) := by
    rw [stackAt_dp_top s.sp hge hle,
        ProofLib.memRegion_split' (b := s.sp - 2144#64) (n := 2088) (k := 56) (b' := s.sp - 56#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s.sp - 56#64) (n := 8) (k := 48) (b' := s.sp - 48#64) rfl (by bv_omega) (by decide)]
    ac_rfl
  rw [htop, memRegion_48_words (s.sp - 48#64)]
  have e1 : s.sp - 48#64 + 8#64 = s.sp - 40#64 := by bv_kernel
  have e2 : s.sp - 48#64 + 16#64 = s.sp - 32#64 := by bv_kernel
  have e3 : s.sp - 48#64 + 24#64 = s.sp - 24#64 := by bv_kernel
  have e4 : s.sp - 48#64 + 32#64 = s.sp - 16#64 := by bv_kernel
  have e5 : s.sp - 48#64 + 40#64 = s.sp - 8#64 := by bv_kernel
  rw [e1, e2, e3, e4, e5]
  exact sepWP_pull_exists_left fun sfp => sepWP_pull_exists_left fun slr =>
    sepWP_pull_exists_left fun sx28 => sepWP_pull_exists_left fun sx21 =>
    sepWP_pull_exists_left fun sx20 => sepWP_pull_exists_left (fun sx19 => h sfp slr sx28 sx21 sx20 sx19)

theorem sepWP_with_dp_locals {prog : Program} {tgt : BitVec 64} {s : State}
    (sp0 : BitVec 64) {R : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 fcoins : BitVec 64)
           (fstate : BitVec 8) (cx0 cx1 cx2 : BitVec 64),
      SepWP prog tgt s
        ((((sp0 - 2144#64) ↦₆₄ f0) ∗ ((sp0 - 2136#64) ↦₆₄ f1) ∗
          ((sp0 - 2128#64) ↦₆₄ f2) ∗ ((sp0 - 2120#64) ↦₆₄ f3) ∗
          ((sp0 - 2112#64) ↦₆₄ f4) ∗ ((sp0 - 2104#64) ↦₆₄ f5) ∗
          ((sp0 - 2096#64) ↦₆₄ f6) ∗ ((sp0 - 2088#64) ↦₆₄ f7) ∗
          ((sp0 - 2080#64) ↦₆₄ f8) ∗ ((sp0 - 2072#64) ↦₆₄ f9) ∗
          ((sp0 - 2064#64) ↦₆₄ f10) ∗ ((sp0 - 2056#64) ↦₆₄ f11) ∗
          ((sp0 - 2048#64) ↦₆₄ f12) ∗ ((sp0 - 2040#64) ↦₆₄ fcoins) ∗
          memRegion (sp0 - 2032#64) 592 ∗
          ((sp0 - 1440#64) ↦₈ fstate) ∗
          memRegion (sp0 - 1439#64) 1303 ∗
          ((sp0 - 136#64) ↦₆₄ cx0) ∗ ((sp0 - 128#64) ↦₆₄ cx1) ∗
          ((sp0 - 120#64) ↦₆₄ cx2) ∗ memRegion (sp0 - 112#64) 8 ∗
          memRegion (sp0 - 104#64) 48) ∗ R) Q oom) :
    SepWP prog tgt s (memRegion (sp0 - 2144#64) 2088 ∗ R) Q oom := by
  have hsplit : memRegion (sp0 - 2144#64) 2088 ⊢
      ∃∗ f0 : BitVec 64, ∃∗ f1 : BitVec 64, ∃∗ f2 : BitVec 64, ∃∗ f3 : BitVec 64,
      ∃∗ f4 : BitVec 64, ∃∗ f5 : BitVec 64, ∃∗ f6 : BitVec 64, ∃∗ f7 : BitVec 64,
      ∃∗ f8 : BitVec 64, ∃∗ f9 : BitVec 64, ∃∗ f10 : BitVec 64, ∃∗ f11 : BitVec 64,
      ∃∗ f12 : BitVec 64, ∃∗ fcoins : BitVec 64, ∃∗ fstate : BitVec 8,
      ∃∗ cx0 : BitVec 64, ∃∗ cx1 : BitVec 64, ∃∗ cx2 : BitVec 64,
        ((sp0 - 2144#64) ↦₆₄ f0) ∗ ((sp0 - 2136#64) ↦₆₄ f1) ∗
        ((sp0 - 2128#64) ↦₆₄ f2) ∗ ((sp0 - 2120#64) ↦₆₄ f3) ∗
        ((sp0 - 2112#64) ↦₆₄ f4) ∗ ((sp0 - 2104#64) ↦₆₄ f5) ∗
        ((sp0 - 2096#64) ↦₆₄ f6) ∗ ((sp0 - 2088#64) ↦₆₄ f7) ∗
        ((sp0 - 2080#64) ↦₆₄ f8) ∗ ((sp0 - 2072#64) ↦₆₄ f9) ∗
        ((sp0 - 2064#64) ↦₆₄ f10) ∗ ((sp0 - 2056#64) ↦₆₄ f11) ∗
        ((sp0 - 2048#64) ↦₆₄ f12) ∗ ((sp0 - 2040#64) ↦₆₄ fcoins) ∗
        memRegion (sp0 - 2032#64) 592 ∗
        ((sp0 - 1440#64) ↦₈ fstate) ∗
        memRegion (sp0 - 1439#64) 1303 ∗
        ((sp0 - 136#64) ↦₆₄ cx0) ∗ ((sp0 - 128#64) ↦₆₄ cx1) ∗
        ((sp0 - 120#64) ↦₆₄ cx2) ∗ memRegion (sp0 - 112#64) 8 ∗
        memRegion (sp0 - 104#64) 48 := by
    rw [ProofLib.memRegion_split' (b := sp0 - 2144#64) (n := 8) (k := 2080) (b' := sp0 - 2136#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 2136#64) (n := 8) (k := 2072) (b' := sp0 - 2128#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 2128#64) (n := 8) (k := 2064) (b' := sp0 - 2120#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 2120#64) (n := 8) (k := 2056) (b' := sp0 - 2112#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 2112#64) (n := 8) (k := 2048) (b' := sp0 - 2104#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 2104#64) (n := 8) (k := 2040) (b' := sp0 - 2096#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 2096#64) (n := 8) (k := 2032) (b' := sp0 - 2088#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 2088#64) (n := 8) (k := 2024) (b' := sp0 - 2080#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 2080#64) (n := 8) (k := 2016) (b' := sp0 - 2072#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 2072#64) (n := 8) (k := 2008) (b' := sp0 - 2064#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 2064#64) (n := 8) (k := 2000) (b' := sp0 - 2056#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 2056#64) (n := 8) (k := 1992) (b' := sp0 - 2048#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 2048#64) (n := 8) (k := 1984) (b' := sp0 - 2040#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 2040#64) (n := 8) (k := 1976) (b' := sp0 - 2032#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 2032#64) (n := 592) (k := 1384) (b' := sp0 - 1440#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 1440#64) (n := 1) (k := 1383) (b' := sp0 - 1439#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 1439#64) (n := 1303) (k := 80) (b' := sp0 - 136#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 136#64) (n := 8) (k := 72) (b' := sp0 - 128#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 128#64) (n := 8) (k := 64) (b' := sp0 - 120#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 120#64) (n := 8) (k := 56) (b' := sp0 - 112#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 112#64) (n := 8) (k := 48) (b' := sp0 - 104#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (sp0 - 2144#64), ProofLib.memRegion_eight (sp0 - 2136#64),
        ProofLib.memRegion_eight (sp0 - 2128#64), ProofLib.memRegion_eight (sp0 - 2120#64),
        ProofLib.memRegion_eight (sp0 - 2112#64), ProofLib.memRegion_eight (sp0 - 2104#64),
        ProofLib.memRegion_eight (sp0 - 2096#64), ProofLib.memRegion_eight (sp0 - 2088#64),
        ProofLib.memRegion_eight (sp0 - 2080#64), ProofLib.memRegion_eight (sp0 - 2072#64),
        ProofLib.memRegion_eight (sp0 - 2064#64), ProofLib.memRegion_eight (sp0 - 2056#64),
        ProofLib.memRegion_eight (sp0 - 2048#64), ProofLib.memRegion_eight (sp0 - 2040#64),
        ProofLib.memRegion_one (sp0 - 1440#64),
        ProofLib.memRegion_eight (sp0 - 136#64), ProofLib.memRegion_eight (sp0 - 128#64),
        ProofLib.memRegion_eight (sp0 - 120#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun cx2 => Entails.sepExists_elim fun cx1 =>
      Entails.sepExists_elim fun cx0 => Entails.sepExists_elim fun fstate =>
      Entails.sepExists_elim fun fcoins => Entails.sepExists_elim fun f12 =>
      Entails.sepExists_elim fun f11 => Entails.sepExists_elim fun f10 =>
      Entails.sepExists_elim fun f9 => Entails.sepExists_elim fun f8 =>
      Entails.sepExists_elim fun f7 => Entails.sepExists_elim fun f6 =>
      Entails.sepExists_elim fun f5 => Entails.sepExists_elim fun f4 =>
      Entails.sepExists_elim fun f3 => Entails.sepExists_elim fun f2 =>
      Entails.sepExists_elim fun f1 => Entails.sepExists_elim fun f0 => ?_
    exact Entails.sepExists_right f0 (Entails.sepExists_right f1 (Entails.sepExists_right f2
      (Entails.sepExists_right f3 (Entails.sepExists_right f4 (Entails.sepExists_right f5
      (Entails.sepExists_right f6 (Entails.sepExists_right f7 (Entails.sepExists_right f8
      (Entails.sepExists_right f9 (Entails.sepExists_right f10 (Entails.sepExists_right f11
      (Entails.sepExists_right f12 (Entails.sepExists_right fcoins (Entails.sepExists_right fstate
      (Entails.sepExists_right cx0 (Entails.sepExists_right cx1 (Entails.sepExists_right cx2
        (Entails.refl _))))))))))))))))))
  refine SepWP.weaken_pre (sepConj_mono_left hsplit) ?_
  exact sepWP_pull_exists_left fun f0 => sepWP_pull_exists_left fun f1 =>
    sepWP_pull_exists_left fun f2 => sepWP_pull_exists_left fun f3 =>
    sepWP_pull_exists_left fun f4 => sepWP_pull_exists_left fun f5 =>
    sepWP_pull_exists_left fun f6 => sepWP_pull_exists_left fun f7 =>
    sepWP_pull_exists_left fun f8 => sepWP_pull_exists_left fun f9 =>
    sepWP_pull_exists_left fun f10 => sepWP_pull_exists_left fun f11 =>
    sepWP_pull_exists_left fun f12 => sepWP_pull_exists_left fun fcoins =>
    sepWP_pull_exists_left fun fstate => sepWP_pull_exists_left fun cx0 =>
    sepWP_pull_exists_left fun cx1 => sepWP_pull_exists_left (fun cx2 =>
      h f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 fcoins fstate cx0 cx1 cx2)

theorem dpFutStartAt_pack (sp0 : BitVec 64)
    (r0 r1 r2 r3 r4 r5 r6 r7 a8 a9 a10 a11 a12 coins : BitVec 64) :
    ((sp0 - 2144#64) ↦₆₄ r0) ∗ ((sp0 - 2136#64) ↦₆₄ r1) ∗
      ((sp0 - 2128#64) ↦₆₄ r2) ∗ ((sp0 - 2120#64) ↦₆₄ r3) ∗
      ((sp0 - 2112#64) ↦₆₄ r4) ∗ ((sp0 - 2104#64) ↦₆₄ r5) ∗
      ((sp0 - 2096#64) ↦₆₄ r6) ∗ ((sp0 - 2088#64) ↦₆₄ r7) ∗
      ((sp0 - 2080#64) ↦₆₄ a8) ∗ ((sp0 - 2072#64) ↦₆₄ a9) ∗
      ((sp0 - 2064#64) ↦₆₄ a10) ∗ ((sp0 - 2056#64) ↦₆₄ a11) ∗
      ((sp0 - 2048#64) ↦₆₄ a12) ∗ ((sp0 - 2040#64) ↦₆₄ coins) ∗
      memRegion (sp0 - 2032#64) 592 ∗
      ((sp0 - 1440#64) ↦₈ 0#8) ∗
      memRegion (sp0 - 1439#64) 1303 ⊢
    dpFutStartAt (sp0 - 2144#64) [r0, r1, r2, r3, r4, r5, r6, r7, a8, a9, a10, a11, a12] := by
  unfold dpFutStartAt
  simp (discharger := decide) only [dpWordsAt, dpFutCoinsOff, dpFutStateOff, dpFutSize,
    bv_sub_add_lit, sepConj_emp, sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right ?_))))))))))))
  exact sepConj_mono_left (Entails.sepExists_intro coins)

theorem dpCxAt_pack (sp0 wk : BitVec 64) :
    ((sp0 - 136#64) ↦₆₄ wk) ∗ ((sp0 - 128#64) ↦₆₄ wk) ∗
      ((sp0 - 120#64) ↦₆₄ 0#64) ∗ memRegion (sp0 - 112#64) 8 ⊢
    dpCxAt (sp0 - 136#64) := by
  unfold dpCxAt
  refine Entails.sepExists_right wk ?_
  simp (discharger := decide) only [bv_sub_add_lit]
  exact Entails.refl _

theorem dpFutDoneAt_eq (sp0 : BitVec 64) :
    dpFutDoneAt (sp0 - 2144#64) =
      memRegion (sp0 - 2144#64) 704 ∗
        ((sp0 - 1440#64) ↦₈ 1#8) ∗
        memRegion (sp0 - 1439#64) 1303 := by
  unfold dpFutDoneAt
  simp (discharger := decide) only [dpFutStateOff, dpFutSize, bv_sub_add_lit]

theorem stackAt_dp_epilogue (sp0 : BitVec 64) {stk : Nat}
    (hge : dpWrapFrame ≤ stk) (hle : stk ≤ 2 ^ 64)
    (w0 w1 w2 w3 w4 w5 sfp slr sx28 sx21 sx20 sx19 : BitVec 64) :
    stackAt (sp0 - 2144#64) (stk - dpWrapFrame) ∗ memRegion (sp0 - 2144#64) 704 ∗
      ((sp0 - 1440#64) ↦₈ 1#8) ∗ memRegion (sp0 - 1439#64) 1303 ∗ memRegion (sp0 - 136#64) 32 ∗
      ((sp0 - 104#64) ↦₆₄ w0) ∗ ((sp0 - 96#64) ↦₆₄ w1) ∗
      ((sp0 - 88#64) ↦₆₄ w2) ∗ ((sp0 - 80#64) ↦₆₄ w3) ∗
      ((sp0 - 72#64) ↦₆₄ w4) ∗ ((sp0 - 64#64) ↦₆₄ w5) ∗ memRegion (sp0 - 56#64) 8 ∗
      ((sp0 - 48#64) ↦₆₄ sfp) ∗ ((sp0 - 40#64) ↦₆₄ slr) ∗
      ((sp0 - 32#64) ↦₆₄ sx28) ∗ ((sp0 - 24#64) ↦₆₄ sx21) ∗
      ((sp0 - 16#64) ↦₆₄ sx20) ∗ ((sp0 - 8#64) ↦₆₄ sx19) ⊢
    stackAt sp0 stk := by
  rw [stackAt_dp_top sp0 hge hle,
      ProofLib.memRegion_split' (b := sp0 - 2144#64) (n := 704) (k := 1440) (b' := sp0 - 1440#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 1440#64) (n := 1) (k := 1439) (b' := sp0 - 1439#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 1439#64) (n := 1303) (k := 136) (b' := sp0 - 136#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 136#64) (n := 32) (k := 104) (b' := sp0 - 104#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 104#64) (n := 8) (k := 96) (b' := sp0 - 96#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 96#64) (n := 8) (k := 88) (b' := sp0 - 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 88#64) (n := 8) (k := 80) (b' := sp0 - 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 80#64) (n := 8) (k := 72) (b' := sp0 - 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 72#64) (n := 8) (k := 64) (b' := sp0 - 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 64#64) (n := 8) (k := 56) (b' := sp0 - 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 56#64) (n := 8) (k := 48) (b' := sp0 - 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 48#64) (n := 8) (k := 40) (b' := sp0 - 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 40#64) (n := 8) (k := 32) (b' := sp0 - 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 32#64) (n := 8) (k := 24) (b' := sp0 - 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 24#64) (n := 8) (k := 16) (b' := sp0 - 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 16#64) (n := 8) (k := 8) (b' := sp0 - 8#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono (ProofLib.pointsTo8_entails_memRegion _ _)
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) (sepConj_mono_right
            (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
              (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) (ProofLib.pointsTo64_entails_memRegion _ _)))))))))))))))))

end CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers
