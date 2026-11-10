/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1DropSS3A
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegUntrusted
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1DropSS3B
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Load
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Ok
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Trust
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.StageP1

/-!
# Stage P1 Untrusted-Identity Exit on Store Kits

Proves the `is_trusted_identity == Ok(false)` (TOFU mismatch) arm of Stage P1:
`stageP1_untrusted_err_ok_kit` (`entry + 0x6e4#64 → s0.readReg64 .x30`, cloning `peer`, building
`UntrustedIdentityException`, and dropping `p1LoadedRecordAt`) and full entry-to-return
`stageP1_untrusted_ok_kit`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
open CryptoVerification.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## 1. Stack Split & Region Folding Helpers -/

theorem stack_untrustedErr_to_ext (sp : BitVec 64) (hn : untrustedErrCallStack ≤ 2 ^ 64) :
    stackAt sp untrustedErrCallStack =
      memRegion (sp - BitVec.ofNat 64 untrustedErrCallStack)
        (untrustedErrCallStack - extHookStack) ∗
        stackAt sp extHookStack :=
  stackAt_split_of_le sp untrustedErrCallStack extHookStack (Nat.le_max_left _ _) hn

theorem stack_untrustedErr_to_dropSS (sp : BitVec 64) (hn : untrustedErrCallStack ≤ 2 ^ 64) :
    stackAt sp untrustedErrCallStack =
      memRegion (sp - BitVec.ofNat 64 untrustedErrCallStack)
        (untrustedErrCallStack - dropSessionStructureLocal2Stack) ∗
        stackAt sp dropSessionStructureLocal2Stack :=
  stackAt_split_of_le sp untrustedErrCallStack dropSessionStructureLocal2Stack
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn

theorem stack_untrustedErr_to_alloc (sp : BitVec 64) (hn : untrustedErrCallStack ≤ 2 ^ 64) :
    stackAt sp untrustedErrCallStack =
      memRegion (sp - BitVec.ofNat 64 untrustedErrCallStack)
        (untrustedErrCallStack - allocHookStack) ∗
        stackAt sp allocHookStack :=
  stackAt_split_of_le sp untrustedErrCallStack allocHookStack
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn

theorem stack_stageP1Untrusted_to_p1 {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) (sp : BitVec 64)
    (hn : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64) :
    stackAt sp (stageP1UntrustedCallStack kit ikit) =
      memRegion (sp - BitVec.ofNat 64 (stageP1UntrustedCallStack kit ikit))
        (stageP1UntrustedCallStack kit ikit - stageP1CallStack kit ikit) ∗
        stackAt sp (stageP1CallStack kit ikit) :=
  stackAt_split_of_le sp (stageP1UntrustedCallStack kit ikit) (stageP1CallStack kit ikit)
    (Nat.le_max_left _ _) hn

theorem stack_stageP1Untrusted_to_err {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) (sp : BitVec 64)
    (hn : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64) :
    stackAt sp (stageP1UntrustedCallStack kit ikit) =
      memRegion (sp - BitVec.ofNat 64 (stageP1UntrustedCallStack kit ikit))
        (stageP1UntrustedCallStack kit ikit - untrustedErrCallStack) ∗
        stackAt sp untrustedErrCallStack :=
  stackAt_split_of_le sp (stageP1UntrustedCallStack kit ikit) untrustedErrCallStack
    (Nat.le_max_right _ _) hn

theorem stringClone_pre_intro {A : RustAlloc} {s : State} {addrA ret : BitVec 64} {g : VecGhost}
    (hx0 : s.readReg64 .x0 = addrA) (hx8 : s.readReg64 .x8 = ret) :
    vecGhostAt A g addrA ∗ memRegion ret 24 ∗ A.pool ∗ stackAt s.sp extHookStack ⊢
      (stringCloneSpec A).pre (addrA, ret, g) s := by
  dsimp only [stringCloneSpec]
  exact Entails.pure_right ⟨hx0, hx8⟩ (Entails.refl _)

theorem cells6_eq (base : BitVec 64) :
    cells base 6 =
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
      ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
        (base ↦₆₄ u0) ∗ ((base + 8#64) ↦₆₄ u1) ∗ ((base + 16#64) ↦₆₄ u2) ∗
        ((base + 24#64) ↦₆₄ u3) ∗ ((base + 32#64) ↦₆₄ u4) ∗ ((base + 40#64) ↦₆₄ u5) := by
  dsimp only [cells]
  sep_norm

theorem cells6_fold (base w0 w1 w2 w3 w4 w5 : BitVec 64) :
    (base ↦₆₄ w0) ∗ ((base + 8#64) ↦₆₄ w1) ∗ ((base + 16#64) ↦₆₄ w2) ∗
      ((base + 24#64) ↦₆₄ w3) ∗ ((base + 32#64) ↦₆₄ w4) ∗ ((base + 40#64) ↦₆₄ w5) ⊢
      cells base 6 := by
  rw [cells6_eq base]
  exact Entails.sepExists_right w0
    (Entails.sepExists_right w1
      (Entails.sepExists_right w2
        (Entails.sepExists_right w3
          (Entails.sepExists_right w4
            (Entails.sepExists_right w5 (Entails.refl _))))))

theorem sp_a90_rejoin (sp w0 cap ptr len devWord u5 : BitVec 64) :
    ((sp + 0xa90#64) ↦₆₄ w0) ∗
      ((sp + 0xa98#64) ↦₃₂ cap.extractLsb' 0 32) ∗
      ((sp + 0xa9c#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
      ((sp + 0xaa4#64) ↦₆₄ (len.extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
      ((sp + 0xaac#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ len.extractLsb' 32 32)) ∗
      ((sp + 0xab4#64) ↦₆₄ (u5.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
      ((sp + 0xabc#64) ↦₃₂ u5.extractLsb' 32 32) ⊢
      cells (sp + 0xa90#64) 6 := by
  have h40 := (realign_40 (sp + 0xa98#64) cap ptr len devWord u5).symm
  repeat (simp only [BitVec.add_assoc] at h40); repeat (simp only [BitVec.reduceAdd] at h40)
  have h6 := cells6_fold (sp + 0xa90#64) w0 cap ptr len devWord u5
  repeat (simp only [BitVec.add_assoc] at h6); repeat (simp only [BitVec.reduceAdd] at h6)
  rw [h40]
  exact h6

theorem sp_370_rejoin (sp w0 w1 w2 w3 : BitVec 64) (d4 : BitVec 32) :
    ((sp + 0x370#64) ↦₆₄ w0) ∗ ((sp + 0x378#64) ↦₆₄ w1) ∗
      ((sp + 0x380#64) ↦₆₄ w2) ∗ ((sp + 0x388#64) ↦₆₄ w3) ∗
      ((sp + 0x390#64) ↦₃₂ d4) ⊢
      memRegion (sp + 0x370#64) 36 := by
  rw [sp370_36_split_eq sp]
  exact Entails.sepExists_right d4
    (Entails.sepExists_right w3
      (Entails.sepExists_right w2
        (Entails.sepExists_right w1
          (Entails.sepExists_right w0 (Entails.refl _)))))

theorem coro_e0_368_fold (coroPtr w0 w1 w2 : BitVec 64) :
    ((coroPtr + 0xe0#64) ↦₆₄ w0) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ w1) ∗
      ((coroPtr + 0xf0#64) ↦₆₄ w2) ∗
      memRegion (coroPtr + 0xf8#64) 344 ⊢
      memRegion (coroPtr + 0xe0#64) 368 := by
  rw [ProofLib.memRegion_split (coroPtr + 0xe0#64) 8 360 (by decide),
      ProofLib.memRegion_split (coroPtr + 0xe0#64 + 8#64) 8 352 (by decide),
      ProofLib.memRegion_split (coroPtr + 0xe0#64 + 8#64 + 8#64) 8 344 (by decide)]
  sep_norm
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)))

theorem prevVecAt_unpack (A : RustAlloc) (coroPtr prevCap prevPtr : BitVec 64) :
    vecAt A 24 8 (fun (_ : Unit) _ => emp) (coroPtr + 0xe0#64) prevCap prevPtr [] ⊢
      ⌜prevCap.toNat * 24 < 2 ^ 63⌝ ∗
      ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
      ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
      (if prevCap = 0 then emp
       else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) := by
  dsimp only [vecAt, vecHeader, vecBuf, arrayAt, List.length, Nat.zero_mul, Nat.sub_zero]
  simp only [Nat.zero_mul, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  sep_norm
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm ((coroPtr + 232#64) ↦₆₄ prevPtr),
      sepConj_pure_left_comm ((coroPtr + 224#64) ↦₆₄ prevCap)]
  apply Entails.pure_left; rintro ⟨_, hlt, _⟩
  exact Entails.pure_right hlt (Entails.refl _)

theorem pure_vecGhost_sep_split {A : RustAlloc} {φ : Prop} {g : VecGhost}
    {base : BitVec 64} {tail : SepProp} :
    ∃ R_ss : SepProp,
      (⌜φ⌝ ∗ (vecGhostAt A g base ∗ tail) ⊢
        ⌜g.cap.toNat < 2 ^ 63⌝ ∗ (base ↦₆₄ g.cap) ∗ R_ss) ∧
      ((base ↦₆₄ g.cap) ∗ R_ss ⊢
        ⌜φ⌝ ∗ (vecGhostAt A g base ∗ tail)) := by
  rw [DropSS3.vecGhostAt_eq_srkRest A g base]
  refine ⟨⌜φ⌝ ∗ ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
    DropSS3.srkRest A base g ∗ tail, ?_, ?_⟩
  · apply Entails.pure_left; intro hφ
    rw [sepConj_assoc]
    apply Entails.pure_left; intro hg
    rw [sepConj_assoc]
    exact Entails.pure_right hg.2.1
      (sepConj_mono_right (Entails.pure_right hφ (Entails.pure_right hg (Entails.refl _))))
  · rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hφ
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hg
    rw [← sepConj_assoc]
    exact Entails.pure_right hφ
      (sepConj_mono_left (Entails.pure_right hg (Entails.refl _)))

/-! ## 2. Unified `SessionRecord` Drop (`+0x3588 -> +0x359c`) & Return Epilogue (`+0x359c -> ret`) -/

set_option maxHeartbeats 1200000 in
/-- Drops `p1LoadedRecordAt Scope A coroPtr opt` across `+0x3588 -> +0x359c` over `ext` for both
`opt = none` and `opt = some r` (`currentSession = none` or `some ses`), yielding a single uniform
`previous_sessions` vector state at `coroPtr + 0xe0..0xf8` plus `memRegion (coroPtr + 0xf8#64) 344`
and preserving `calleeSavedVRegs`. -/
theorem p1_err_drop_record_core_wp {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Qp : State → SepProp → Prop}
    (hdrop_ss : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr DropSS3.dropSessionStructure3Name)
      (dropSessionStructureLocal2Spec A))
    (opt : Option (SessionRecord (List (BitVec 8))))
    (s : State) (coroPtr : BitVec 64)
    (hinv : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3588#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x359c#64) s
      (p1LoadedRecordAt Scope A coroPtr opt ∗
       A.pool ∗
       stackAt s.sp dropSessionStructureLocal2Stack)
      (fun s2 P_m =>
        (P_m ⊢
          ∃∗ prevCap : BitVec 64, ∃∗ prevPtr : BitVec 64,
            ⌜prevCap.toNat * 24 < 2 ^ 63⌝ ∗
            ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗
            ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
            ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
            (if prevCap = 0 then emp
             else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
            memRegion (coroPtr + 0xf8#64) 344 ∗
            A.pool ∗
            stackAt s.sp dropSessionStructureLocal2Stack) ∧
        s2.sp = s.sp ∧
        s2.trace = s.trace ∧
        s2.readReg64 .x19 = coroPtr ∧
        s2.readReg64 .x22 = s.readReg64 .x22 ∧
        s2.readReg64 .x25 = s.readReg64 .x25 ∧
        s2.readReg64 .x26 = s.readReg64 .x26 ∧
        s2.readReg64 .x28 = s.readReg64 .x28 ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s ∧
        ImgCallInv img s2)
      Qp := by
  cases opt with
  | none =>
    dsimp only [p1LoadedRecordAt, sessionRecordEmptyHeaderAt]
    sep_norm
    have hstep := p1_err_drop_none_vregs_wp_ext img.base ext s coroPtr hpc hrun hsp_align hx19
    refine SepWPp.ret_sepWP_steps_frame hinv hstep (by sep_focus)
      fun s2 _ _ _ hinv2 hregs2 => ?_
    rcases hregs2 with ⟨hsp2, htr2, hx19_2, hx22_2, hx25_2, hx26_2, hx28_2, _, hvregs2⟩
    refine ⟨?_, hsp2, htr2, hx19_2, hx22_2, hx25_2, hx26_2, hx28_2, hvregs2, hinv2⟩
    refine Entails.sepExists_right 0#64 (Entails.sepExists_right 8#64 ?_)
    refine Entails.pure_right (by decide) ?_
    have hite0 : (0#64 = 0) = True := eq_true rfl
    simp only [hite0, ↓reduceIte]
    sep_norm
    have hf8 :
        ((coroPtr + 248#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (coroPtr + 256#64) 336 ⊢
          memRegion (coroPtr + 248#64) 344 := by
      rw [ProofLib.memRegion_split (coroPtr + 248#64) 8 336 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (Entails.trans
        (sepConj_mono_left
          (Q := ((coroPtr + 224#64) ↦₆₄ 0#64) ∗
                ((coroPtr + 232#64) ↦₆₄ 8#64) ∗
                ((coroPtr + 240#64) ↦₆₄ 0#64) ∗
                A.pool ∗
                stackAt s.sp dropSessionStructureLocal2Stack) hf8)
        (Entails.of_eq (by ac_rfl)))
  | some r =>
    dsimp only [p1LoadedRecordAt]
    sep_norm
    refine SepWPp.exists_elim fun g => ?_
    refine SepWPp.pure_elim fun _ => ?_
    rw [sessionRecordAt_eq_vecAt_sep_curSessionAt A (coroPtr + 0xe0#64) g r]
    refine SepWPp.weaken_frame (prevVecAt_unpack A coroPtr g.prevCap g.prevPtr) (by sep_focus) ?_
    sep_norm
    refine SepWPp.pure_elim fun hprev_lt => ?_
    refine SepWPp.weaken_frame
      (Entails.refl (curSessionAt A (coroPtr + 0xf8#64) g.cur r.currentSession))
      (by sep_focus) ?_
    cases hcur_g : g.cur <;> cases hcur_r : r.currentSession
    · dsimp only [curSessionAt, noneCap]
      have hstep := p1_err_drop_none_vregs_wp_ext img.base ext s coroPtr hpc hrun hsp_align hx19
      refine SepWPp.ret_sepWP_steps_frame hinv hstep (by sep_focus)
        fun s2 _ _ _ hinv2 hregs2 => ?_
      rcases hregs2 with ⟨hsp2, htr2, hx19_2, hx22_2, hx25_2, hx26_2, hx28_2, _, hvregs2⟩
      refine ⟨?_, hsp2, htr2, hx19_2, hx22_2, hx25_2, hx26_2, hx28_2, hvregs2, hinv2⟩
      refine Entails.sepExists_right g.prevCap (Entails.sepExists_right g.prevPtr ?_)
      refine Entails.pure_right hprev_lt ?_
      have hf8 :
          ((coroPtr + 248#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (coroPtr + 256#64) 336 ⊢
            memRegion (coroPtr + 248#64) 344 := by
        rw [ProofLib.memRegion_split (coroPtr + 248#64) 8 336 (by decide)]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)
      refine Entails.trans (Entails.of_eq (by ac_rfl))
        (Entails.trans
          (sepConj_mono_left
            (Q := ((coroPtr + 224#64) ↦₆₄ g.prevCap) ∗
                  ((coroPtr + 232#64) ↦₆₄ g.prevPtr) ∗
                  ((coroPtr + 240#64) ↦₆₄ 0#64) ∗
                  (if g.prevCap = 0 then emp
                   else A.live g.prevPtr (g.prevCap.toNat * 24) 8 ∗
                     memRegion g.prevPtr (g.prevCap.toNat * 24)) ∗
                  A.pool ∗
                  stackAt s.sp dropSessionStructureLocal2Stack) hf8)
          (Entails.of_eq (by ac_rfl)))
    · dsimp only [curSessionAt]
      exact SepWPp.pure_elim False.elim
    · dsimp only [curSessionAt]
      exact SepWPp.pure_elim False.elim
    · rename_i G ses
      dsimp only [curSessionAt, sessionStateReprAt]
      sep_norm
      refine SepWPp.pure_elim fun _ => ?_
      have hss_split :
          ∃ R_ss : SepProp,
            (sessionStateAt A (coroPtr + 0xf8#64) G ses.state ⊢
              ⌜G.localIk.cap.toNat < 2 ^ 63⌝ ∗ ((coroPtr + 0xf8#64) ↦₆₄ G.localIk.cap) ∗ R_ss) ∧
            (((coroPtr + 0xf8#64) ↦₆₄ G.localIk.cap) ∗ R_ss ⊢
              sessionStateAt A (coroPtr + 0xf8#64) G ses.state) := by
        unfold sessionStateAt
        exact pure_vecGhost_sep_split
      obtain ⟨R_ss, hss_fwd, hss_bwd⟩ := hss_split
      refine SepWPp.weaken_frame hss_fwd (by sep_focus) ?_
      sep_norm
      refine SepWPp.pure_elim fun hcap_lt => ?_
      have hcap_ne : G.localIk.cap ≠ 0xffffffffffffffff#64 := by bv_omega
      have hto_call := p1_err_drop_ss_to_call_vregs_wp_ext img.base ext s coroPtr G.localIk.cap
        hcap_ne hpc hrun hsp_align hx19
      refine SepWPp.bind_sepWP_steps_frame hinv hto_call (by sep_focus)
        fun s1 _ hpc1 hrun1 hinv1 hregs1 => ?_
      rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, hx22_1, hx25_1, hx26_1, hx28_1, _, hx30_1, hvregs1⟩
      have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
      refine SepWPp.weaken_frame hss_bwd (by sep_focus) ?_
      refine SepWPp.call_nopanic_steps_frame
        (spec := dropSessionStructureLocal2Spec A)
        (x := ⟨coroPtr + 0xf8#64, G, ses.state⟩)
        (T := sessionStateAt A (coroPtr + 0xf8#64) G ses.state ∗ A.pool ∗
          stackAt s.sp dropSessionStructureLocal2Stack)
        hinv1 hdrop_ss hpc1 hrun1 hsp1_al hx30_1
        (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp1])
        hx0_1 (by sep_focus)
        (hoom_false := fun _ => rfl)
        (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hinv2 => ?_)
      dsimp only [dropSessionStructureLocal2Spec]
      rw [hsp1, sepConj_assoc]
      refine SepWPp.pure_elim fun htr2_1 => ?_
      refine SepWPp.done hpc2 hrun2 ?_
      rcases hcs2 with ⟨hx19_cs2, _, _, hx22_cs2, _, _, hx25_cs2, hx26_cs2, _, hx28_cs2, _, hvregs_cs2⟩
      refine ⟨?_, hsp2_1.trans hsp1, htr2_1.trans htr1,
        hx19_cs2.trans hx19_1, hx22_cs2.trans hx22_1,
        hx25_cs2.trans hx25_1, hx26_cs2.trans hx26_1, hx28_cs2.trans hx28_1,
        hvregs_cs2.trans hvregs1, hinv2⟩
      refine Entails.sepExists_right g.prevCap (Entails.sepExists_right g.prevPtr ?_)
      refine Entails.pure_right hprev_lt ?_
      exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

theorem p1_err_drop_record_wp {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Qp : State → SepProp → Prop}
    (hA : AllocHooks A abs)
    (opt : Option (SessionRecord (List (BitVec 8))))
    (s : State) (coroPtr : BitVec 64)
    (hinv : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3588#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x359c#64) s
      (p1LoadedRecordAt Scope A coroPtr opt ∗
       A.pool ∗
       stackAt s.sp dropSessionStructureLocal2Stack)
      (fun s2 P_m =>
        (P_m ⊢
          ∃∗ prevCap : BitVec 64, ∃∗ prevPtr : BitVec 64,
            ⌜prevCap.toNat * 24 < 2 ^ 63⌝ ∗
            ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗
            ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
            ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
            (if prevCap = 0 then emp
             else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
            memRegion (coroPtr + 0xf8#64) 344 ∗
            A.pool ∗
            stackAt s.sp dropSessionStructureLocal2Stack) ∧
        s2.sp = s.sp ∧ s2.trace = s.trace ∧
        s2.readReg64 .x19 = coroPtr ∧ s2.readReg64 .x22 = s.readReg64 .x22 ∧
        s2.readReg64 .x25 = s.readReg64 .x25 ∧ s2.readReg64 .x26 = s.readReg64 .x26 ∧
        s2.readReg64 .x28 = s.readReg64 .x28 ∧ ImgCallInv img s2)
      Qp :=
  SepWPp.mono_run
    (p1_err_drop_record_core_wp
      (DropSS3.drop_session_structure3_ok_std3 (b := img.base) (C := C) (ctl := ctl) (abs := abs) hA)
      opt s coroPtr hinv hpc hrun hsp_align hx19)
    (fun _ _ ⟨h1, h2, h3, h4, h5, h6, h7, h8, _, h9⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩)

set_option maxHeartbeats 1200000 in
/-- Executes the shared error-return tail `+0x359c -> s0.readReg64 .x30` over `ext` for both
`prevCap = 0` (`p3_err_tail_b_vregs_wp_ext`) and `prevCap ≠ 0` (`p1_err_tail_prev_dealloc_core_wp`),
preserving `calleeSavedVRegs`. -/
theorem p1_err_tail_prev_core_wp {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
          (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64))
      (rustDeallocSpec A))
    (s0 s : State) (sp coroPtr outPtr prevCap prevPtr cap ptr devWord u_278 : BitVec 64)
    (b_2c0 : BitVec 8)
    (peer : AddrGhost) (pad : List (BitVec 8))
    (hprev_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hpad : pad.length = 7)
    (hw4 : peer.device :: pad = unpack64 devWord)
    (hinv : ImgCallInv img s)
    (hsp_eq : s.sp = sp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x359c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = (cap.extractLsb' 0 32).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x800000000000000c#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       (if prevCap = 0 then emp
        else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
       memRegion (coroPtr + 0xf8#64) 344 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗ SegUntrusted.vecU8Buf A cap ptr peer.name.bytes ∗
       ((sp + 0x370#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
       ((sp + 0x378#64) ↦₆₄ ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
       ((sp + 0x380#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)) ∗
       ((sp + 0x388#64) ↦₆₄ (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
       ((sp + 0x390#64) ↦₃₂ u_278.extractLsb' 32 32) ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt sp allocHookStack)
      (fun sf P_f =>
        (P_f ⊢
          memRegion (coroPtr + 0xe0#64) 368 ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val)) ∗
          memRegion (sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt sp allocHookStack) ∧
        sf.sp = sp + 0xcd0#64 ∧ sf.trace = s.trace ∧
        ClosureCalleeSaved s0 sf ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        ImgCallInv img sf)
      Qp := by
  have hx25_s : s.readReg64 .x25 = s.sp + 0x210#64 := by rw [hsp_eq]; exact hx25
  rw [savedRegsAt_eq_sp_c70 sp s0]
  refine SepWPp.weaken_frame (memRegion_48_out_entails outPtr) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_ret0 =>
    SepWPp.exists_elim fun u_ret08 =>
    SepWPp.exists_elim fun u_ret0c =>
    SepWPp.exists_elim fun u_ret14 =>
    SepWPp.exists_elim fun u_ret1c =>
    SepWPp.exists_elim fun u_ret24 =>
    SepWPp.exists_elim fun u_ret2c => ?_
  have hzero64 : (0 : BitVec 64) = 0#64 := rfl
  rw [hzero64]
  let R_tail : SepProp :=
    ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
    ((sp + 0xc70#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp + 0xc78#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((sp + 0xc80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp + 0xc88#64) ↦₆₄ s0.readReg64 .x27) ∗
    ((sp + 0xc90#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp + 0xc98#64) ↦₆₄ s0.readReg64 .x25) ∗
    ((sp + 0xca0#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp + 0xca8#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((sp + 0xcb0#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp + 0xcb8#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((sp + 0xcc0#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp + 0xcc8#64) ↦₆₄ s0.readReg64 .x19) ∗
    A.pool ∗ stackAt sp allocHookStack
  by_cases hcap : prevCap = 0#64
  · subst hcap
    simp only [↓reduceIte]
    sep_norm
    have htail := p3_err_tail_b_vregs_wp_ext
      img.base ext s coroPtr outPtr 0x800000000000000c#64 prevPtr
      (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
      ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
      (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)
      (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)
      u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21)
      (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24)
      (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64 .x27)
      (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      (cap.extractLsb' 0 32) (u_278.extractLsb' 32 32) u_ret08 u_ret2c b_2c0
      hpc hrun hsp_align hx19 hx22 hx25_s hx26 hx28
    rw [hsp_eq] at htail
    refine SepWPp.ret_sepWP_steps_frame hinv htail (by sep_focus)
      fun sf _ _ _ hinvf hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _, hvregsf⟩
    have hcs_f : ClosureCalleeSaved s0 sf :=
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f,
        True.intro⟩
    refine ⟨?_, hspf, htrf, hcs_f, hvregsf, hinvf⟩
    have hout := untrusted_out_entails A outPtr cap ptr devWord u_278 peer pad hpad hw4
    simp only [BitVec.add_zero] at hout
    have hcoro := coro_e0_368_fold coroPtr 0#64 prevPtr 0#64
    have h370 := sp_370_rejoin sp
      (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
      ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
      (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)
      (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)
      (u_278.extractLsb' 32 32)
    refine Entails.trans (Entails.of_eq (by dsimp only [R_tail]; simp only [BitVec.add_zero]; ac_rfl))
      (Entails.trans
        (sepConj_mono hcoro (sepConj_mono hout (sepConj_mono_left (Q := R_tail) h370)))
        (Entails.of_eq (by dsimp only [R_tail]; ac_rfl)))
  · simp only [hcap, ↓reduceIte]
    have htail := p1_err_tail_prev_dealloc_core_wp img.base ext hdealloc s coroPtr outPtr
      0x800000000000000c#64 prevCap prevPtr
      (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
      ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
      (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)
      (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)
      u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21)
      (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24)
      (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64 .x27)
      (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      (cap.extractLsb' 0 32) (u_278.extractLsb' 32 32) u_ret08 u_ret2c b_2c0
      hcap hprev_lt hpc hrun hsp_align hx19 hx22 hx25_s hx26 hx28
    rw [hsp_eq] at htail
    refine SepWPp.ret_sepWP_steps_frame hinv htail (by sep_focus)
      fun sf _ _ _ hinvf hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _, hvregsf⟩
    have hcs_f : ClosureCalleeSaved s0 sf :=
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f,
        True.intro⟩
    refine ⟨?_, hspf, htrf, hcs_f, hvregsf, hinvf⟩
    have hout := untrusted_out_entails A outPtr cap ptr devWord u_278 peer pad hpad hw4
    simp only [BitVec.add_zero] at hout
    have hcoro := coro_e0_368_fold coroPtr prevCap prevPtr 0#64
    have h370 := sp_370_rejoin sp
      (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
      ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
      (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)
      (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)
      (u_278.extractLsb' 32 32)
    refine Entails.trans (Entails.of_eq (by dsimp only [R_tail]; simp only [BitVec.add_zero]; ac_rfl))
      (Entails.trans
        (sepConj_mono hcoro (sepConj_mono hout (sepConj_mono_left (Q := R_tail) h370)))
        (Entails.of_eq (by dsimp only [R_tail]; ac_rfl)))

theorem p1_err_tail_prev_wp {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (hA : AllocHooks A abs)
    (s0 s : State) (sp coroPtr outPtr prevCap prevPtr cap ptr devWord u_278 : BitVec 64)
    (b_2c0 : BitVec 8)
    (peer : AddrGhost) (pad : List (BitVec 8))
    (hprev_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hpad : pad.length = 7)
    (hw4 : peer.device :: pad = unpack64 devWord)
    (hinv : ImgCallInv img s)
    (hsp_eq : s.sp = sp)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x359c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = (cap.extractLsb' 0 32).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x800000000000000c#64) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs) (s0.readReg64 .x30) s
      (((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       (if prevCap = 0 then emp
        else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
       memRegion (coroPtr + 0xf8#64) 344 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗ SegUntrusted.vecU8Buf A cap ptr peer.name.bytes ∗
       ((sp + 0x370#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
       ((sp + 0x378#64) ↦₆₄ ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
       ((sp + 0x380#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)) ∗
       ((sp + 0x388#64) ↦₆₄ (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
       ((sp + 0x390#64) ↦₃₂ u_278.extractLsb' 32 32) ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt sp allocHookStack)
      (fun sf P_f =>
        (P_f ⊢
          memRegion (coroPtr + 0xe0#64) 368 ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val)) ∗
          memRegion (sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt sp allocHookStack) ∧
        sf.sp = sp + 0xcd0#64 ∧ sf.trace = s.trace ∧
        ClosureCalleeSaved s0 sf ∧ ImgCallInv img sf)
      Qp :=
  SepWPp.mono_run
    (p1_err_tail_prev_core_wp
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok
        (b := img.base) (C := C) (ctl := ctl) (abs := abs) hA)
      s0 s sp coroPtr outPtr prevCap prevPtr cap ptr devWord u_278 b_2c0
      peer pad hprev_lt hpad hw4 hinv hsp_eq hpc hrun hsp_align
      hx19 hx22 hx25 hx26 hx28)
    (fun _ _ ⟨h1, h2, h3, h4, _, h5⟩ => ⟨h1, h2, h3, h4, h5⟩)

/-! ## 3. Exported Kit Theorems (`stageP1_untrusted_err_ok_kit` & `stageP1_untrusted_ok_kit`) -/

set_option maxHeartbeats 2800000 in
/-- Kit-generic Stage P1 Untrusted Error Exit (`entry + 0x6e4#64 -> s0.readReg64 .x30`):
Starting immediately after `stageP1_trust_call_wp_kit` when `ans = .ok false` (`x20 = -2`,
`x23 = 0#64`), clones `peer` via `<String as Clone>::clone`, constructs
`SignalProtocolError::UntrustedIdentityException(peer.val)`, drops `p1LoadedRecordAt` for both
`opt = none` and `opt = some r`, writes `apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val))`,
and returns cleanly to `s0.readReg64 .x30` preserving `logOff img`, `kit.storeAt`,
`ikit.identityAt idStorePtr (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false))`,
`protocolAddressAt`, and `((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList)`. -/
theorem stageP1_untrusted_err_ok_kit {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {kit : SessionStoreSpec A img.base}
    {ikit : IdentityStoreSpec A img.base}
    {st : kit.StoreState} {ist : ikit.IdState}
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (opt : Option (SessionRecord (List (BitVec 8))))
    (hA : AllocHooks A abs)
    (hstack_lt : untrustedErrCallStack ≤ 2 ^ 64)
    (s0 s : State)
    (outPtr coroPtr msgPtr remoteAddrPtr sessStorePtr idStorePtr : BitVec 64)
    (b_2c0 b_390 : BitVec 8)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hinv : ImgCallInv img s)
    (hpc : s.pc =
      (tripleRatchetProgAt img.base C ctl abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x6e4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = 0xfffffffffffffffe#64)
    (hx23 : s.readReg64 .x23 = 0#64) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs) (s0.readReg64 .x30) s
      (((coroPtr + 0x330#64) ↦₆₄ remoteAddrPtr) ∗
       p1LoadedRecordAt Scope A coroPtr opt ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       memRegion (s.sp + 0x370#64) 36 ∗
       memRegion (s.sp + 0x3e0#64) 368 ∗
       cells (s.sp + 0xa90#64) 6 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗
       logOff img ∗
       kit.storeAt sessStorePtr st ∗
       ikit.identityAt idStorePtr
         (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
       protocolAddressAt A peer remoteAddrPtr ∗
       ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
       A.pool ∗
       stackAt s.sp untrustedErrCallStack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢
          ((coroPtr + 0x330#64) ↦₆₄ remoteAddrPtr) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗
          cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          memRegion (s.sp + 0x370#64) 36 ∗
          memRegion (s.sp + 0x3e0#64) 368 ∗
          cells (s.sp + 0xa90#64) 6 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val)) ∗
          logOff img ∗
          kit.storeAt sessStorePtr st ∗
          ikit.identityAt idStorePtr
            (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
          protocolAddressAt A peer remoteAddrPtr ∗
          ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
          A.pool ∗
          stackAt s.sp untrustedErrCallStack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  have hstep1 := p1_untrusted_to_clone_wp img.base C ctl abs s coroPtr remoteAddrPtr
    hpc hrun hsp_align hx19 hx20 hx23
  refine SepWPp.bind_sepWP_steps_frame hinv hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hinv1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx8_1, hx19_1, hx21_1, hx25_1, _, hx30_1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have htr1_pre : s0.trace <+: s1.trace := htr1 ▸ htr
  refine SepWPp.weaken_frame (memRegion_368_untrusted_entails s.sp) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun pad => ?_
  refine SepWPp.pure_elim fun hpad => ?_
  have haddr_eq :
      protocolAddressAt A peer remoteAddrPtr =
        vecGhostAt A peer.name remoteAddrPtr ∗
          ((remoteAddrPtr + 0x18#64) ↦₈ peer.device) ∗
          memRegion (remoteAddrPtr + 0x19#64) 7 := rfl
  refine SepWPp.weaken_frame (Entails.of_eq haddr_eq) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_ext s.sp hstack_lt))
    (by sep_focus) ?_
  have hclone := stringClone_ok_cli (A := A) (b := img.base) (C := C) (ctl := ctl) (abs := abs) hA
  refine SepWPp.call_oom_steps_frame
    (x := (remoteAddrPtr, s.sp + 0x3e0#64, peer.name))
    (P_spec := vecGhostAt A peer.name remoteAddrPtr ∗ memRegion (s.sp + 0x3e0#64) 24 ∗
      A.pool ∗ stackAt s1.sp extHookStack)
    hinv1 htr1_pre hclone hpc1 hrun1 hsp1_al hx30_1
    (stringClone_pre_intro hx0_1 hx8_1)
    (by rw [hsp1]; sep_focus)
    (fun _ => Entails.refl _)
    (hexit_false := fun _ _ => rfl)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hinv2 => ?_)
  dsimp only [stringCloneSpec]
  rw [hsp1]
  sep_norm
  refine SepWPp.pure_elim fun htr2_1 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_ext s.sp hstack_lt).symm)
    (by sep_focus) ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2_s]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, _, _, _, hx25_cs2, _, _, _, _, _⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx21_2 : s2.readReg64 .x21 = remoteAddrPtr := hx21_cs2.trans hx21_1
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hsp2_s]
  refine SepWPp.weaken_frame (vecU8_unpack_3e0 A s.sp peer.name.bytes) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun cap => SepWPp.exists_elim fun ptr => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (cells6_eq (coroPtr + 0x250#64))) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u250 => SepWPp.exists_elim fun u258 =>
    SepWPp.exists_elim fun u260 => SepWPp.exists_elim fun u268 =>
    SepWPp.exists_elim fun u270 => SepWPp.exists_elim fun u278 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (cells6_eq (s.sp + 0xa90#64))) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun ua90 => SepWPp.exists_elim fun ua98 =>
    SepWPp.exists_elim fun uaa0 => SepWPp.exists_elim fun uaa8 =>
    SepWPp.exists_elim fun uab0 => SepWPp.exists_elim fun uab8 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (sp370_36_split_eq s.sp)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u390 => SepWPp.exists_elim fun u388 =>
    SepWPp.exists_elim fun u380 => SepWPp.exists_elim fun u378 =>
    SepWPp.exists_elim fun u370 => ?_
  have hw4_ex : ∃ devWord : BitVec 64, peer.device :: pad = unpack64 devWord := by
    rcases pad with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨p4, _ | ⟨p5, _ | ⟨p6, _ | ⟨p7, _ | _⟩⟩⟩⟩⟩⟩⟩ <;>
      try simp at hpad
    exact ⟨p7 ++ p6 ++ p5 ++ p4 ++ p3 ++ p2 ++ p1 ++ peer.device,
      (unpack64_pack64 peer.device p1 p2 p3 p4 p5 p6 p7).symm⟩
  obtain ⟨devWord, hw4⟩ := hw4_ex
  have hlog_eq :
      logOff img =
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) :=
    rfl
  refine SepWPp.weaken_frame (Entails.of_eq hlog_eq) (by sep_focus) ?_
  have hstep3 := p1_untrusted_post_clone_wp img.base C ctl abs s2
    coroPtr remoteAddrPtr outPtr cap ptr (BitVec.ofNat 64 peer.name.bytes.length) devWord
    u250 u258 u260 u268 u270 u278
    ua90 ua98 uaa0 uaa8 uab0 uab8
    u370 u378 u380 u388 u390
    d0 b_390 peer pad
    hb hw4 hpc2 hrun2 hsp2_align hx19_2 hx21_2 hx25_2
  rw [hsp2_s] at hstep3
  refine SepWPp.bind_sepWP_steps_frame hinv2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hinv3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_s, htr3_2, hx19_3, hx22_3, hx25_3, hx26_3, hx28_3, _⟩
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3_s]; exact hsp_align
  refine SepWPp.weaken_frame
    (cells_3e0_entails_memRegion_368 s.sp cap ptr (BitVec.ofNat 64 peer.name.bytes.length) devWord)
    (by sep_focus) ?_
  have hc250 := cells6_fold (coroPtr + 0x250#64)
    0x800000000000000c#64 cap ptr (BitVec.ofNat 64 peer.name.bytes.length) devWord (s2.readReg64 .x27)
  repeat (simp only [BitVec.add_assoc] at hc250); repeat (simp only [BitVec.reduceAdd] at hc250)
  refine SepWPp.weaken_frame hc250 (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (sp_a90_rejoin s.sp 0x800000000000000c#64 cap ptr
      (BitVec.ofNat 64 peer.name.bytes.length) devWord (s2.readReg64 .x27))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq haddr_eq.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hlog_eq.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_dropSS s.sp hstack_lt))
    (by sep_focus) ?_
  have hdrop := p1_err_drop_record_wp (Scope := Scope) (Qp := PanicOomProp s0) hA opt s3 coroPtr
    hinv3 hpc3 hrun3 hsp3_align hx19_3
  rw [hsp3_s] at hdrop
  refine SepWPp.bind_sepWPp_steps_frame hdrop (by sep_focus)
    fun s4 _ hpc4 hrun4 hregs4 => ?_
  rcases hregs4 with ⟨hsp4_s, htr4_3, hx19_4, hx22_4, hx25_4, hx26_4, hx28_4, hinv4⟩
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4_s]; exact hsp_align
  sep_norm
  refine SepWPp.exists_elim fun prevCap => SepWPp.exists_elim fun prevPtr => ?_
  refine SepWPp.pure_elim fun hprev_lt => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_dropSS s.sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_alloc s.sp hstack_lt))
    (by sep_focus) ?_
  have hret := p1_err_tail_prev_wp (Qp := PanicOomProp s0) hA s0 s4 s.sp coroPtr outPtr
    prevCap prevPtr cap ptr devWord (s2.readReg64 .x27) b_2c0 peer pad
    hprev_lt hpad hw4 hinv4 hsp4_s hpc4 hrun4 hsp4_align
    hx19_4 (hx22_4.trans hx22_3) (hx25_4.trans hx25_3)
    (hx26_4.trans hx26_3) (hx28_4.trans hx28_3)
  refine SepWPp.bind_sepWPp_steps_frame hret (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨hspf, htrf_4, hcs_f, hinvf⟩
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_alloc s.sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf ?_
  have htr_full : sf.trace = s.trace := by
    rw [htrf_4, htr4_3, htr3_2, htr2_1, htr1]
  refine ⟨htr_full, ?_, hspf, hcs_f, hinvf.1, hinvf.2⟩
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 2800000 in
/-- Kit-generic Full Stage P1 Untrusted Composition (`entry -> s0.readReg64 .x30`):
Full Stage P1 composition for the `is_trusted_identity == Ok(false)` (TOFU mismatch) arm:
composes `p1_seg1_wp` (`entry -> img.base + kit.loadShimOff`), `stageP1_load_ok_kit`
(`img.base + kit.loadShimOff -> img.base + ikit.trustShimOff`), `stageP1_trust_call_wp_kit`
(`img.base + ikit.trustShimOff -> entry + 0x6e4#64`), and `stageP1_untrusted_err_ok_kit`
(`entry + 0x6e4#64 -> s0.readReg64 .x30`). -/
theorem stageP1_untrusted_ok_kit {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A img.base}
    {ikit : IdentityStoreSpec A img.base}
    {st : kit.StoreState} {ist : ikit.IdState}
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (hA : AllocHooks A abs)
    (hkit : SessionOnlyKitOkS kit Scope C encRecord ctl abs)
    (hikit : IdentityStoreKitOkI img ikit C ctl abs)
    (hstack_lt : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64)
    (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val)
    (hload_ok : ∀ ans, kit.loadRel st peer.val ans → ans.isOk = true)
    (htrust_false : ∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok false)
    (s0 : State)
    (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt rngPtr
     v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
    (b_390 : BitVec 8)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hinv : ImgCallInv img s0)
    (hfs : FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAt img.base C ctl abs) s0)
    (hpc : s0.pc =
      (tripleRatchetProgAt img.base C ctl abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName)
    (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsp_def : s0.sp - 0xcd0#64 = sp)
    (hx0 : s0.readReg64 .x0 = outPtr)
    (hx1 : s0.readReg64 .x1 = coroPtr)
    (hx2 : s0.readReg64 .x2 = ctxPtr) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs) (s0.readReg64 .x30) s0
      (decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr ∗
       cells (coroPtr + 0x70#64) 14 ∗
       cells (coroPtr + 0xe0#64) 4 ∗
       memRegion (coroPtr + 0x100#64) 336 ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
       cells (coroPtr + 0x2c8#64) 25 ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((coroPtr + 0x398#64) ↦₆₄ u_398) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ u_3a0) ∗
       (sp ↦₆₄ v_sp0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0xd8#64) 348 ∗
       memRegion (sp + 0x370#64) 36 ∗
       memRegion (sp + 0x3e0#64) 368 ∗
       cells (sp + 0xa90#64) 6 ∗
       cells (s0.sp - 0x60#64) 12 ∗
       memRegion outPtr 48 ∗
       ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadShimOff)) ∗
       ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + ikit.trustShimOff)) ∗
       ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗
       ((img.base + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
       ((img.base + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((img.base + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ∗
       ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
       ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
       ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
       logOff img ∗
       kit.storeAt sessStorePtr st ∗
       ikit.identityAt idStorePtr ist ∗
       protocolAddressAt A peer remoteAddrPtr ∗
       ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
       A.pool ∗
       stackAt sp (stageP1UntrustedCallStack kit ikit))
      (fun sf P_f =>
        (∃ opt : Option (SessionRecord (List (BitVec 8))),
          kit.loadRel st peer.val (.ok opt) ∧
          ikit.trustRel ist peer.val remoteIdKey .receiving (.ok false) ∧
          sf.trace = s0.trace ++ kit.loadEvs encRecord peer.val (.ok opt) ++
            ikit.trustEvs peer.val remoteIdKey .receiving (.ok false) ∧
          (P_f ⊢
            ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
              decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
                preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
                kyberStorePtr kyberStoreVt rngPtr ∗
              decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
                preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
                kyberStorePtr kyberStoreVt rngPtr ∗
              memRegion (coroPtr + 0xe0#64) 368 ∗
              cells (coroPtr + 0x250#64) 6 ∗
              ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
              processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
                spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
              ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
              cells (coroPtr + 0x398#64) 2 ∗
              (sp ↦₆₄ 0#64) ∗
              ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
              ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
              ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
              memRegion (sp + 0xd8#64) 348 ∗
              memRegion (sp + 0x370#64) 36 ∗
              memRegion (sp + 0x3e0#64) 368 ∗
              cells (sp + 0xa90#64) 6 ∗
              decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
              apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val)) ∗
              ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadShimOff)) ∗
              ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + ikit.trustShimOff)) ∗
              ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗
              ((img.base + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
              ((img.base + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
              ((img.base + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ∗
              ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
              ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
              ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
              ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
              logOff img ∗
              kit.storeAt sessStorePtr st ∗
              ikit.identityAt idStorePtr
                (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
              protocolAddressAt A peer remoteAddrPtr ∗
              ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
              A.pool ∗
              stackAt sp (stageP1UntrustedCallStack kit ikit))) ∧
        sf.sp = s0.sp ∧
        ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  have hp1_le : stageP1CallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_left _ _) hstack_lt
  have herr_le : untrustedErrCallStack ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_right _ _) hstack_lt
  have hload_le : loadCallStack kit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_left _ _) hp1_le
  have htrust_le : trustCallStack ikit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_right _ _) hp1_le
  have hsp_saved : sp + 0xcd0#64 = s0.sp := by rw [← hsp_def]; bv_omega
  have hstep1 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg1_wp
    img.base C ctl abs s0 outPtr coroPtr ctxPtr
    msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    (img.base + kit.loadShimOff) v_sp0
    hpc hrun hsp_align hx0 hx1 hx2
  rw [hsp_def] at hstep1
  refine SepWPp.bind_sepWP_steps_frame hinv hstep1 (by sep_focus)
    fun s1 hsteps01 hpc1 hrun1 hinv1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx19_1, _, _, _, _,
    hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _, hx30_1⟩
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by
    rw [hsp1, ← hsp_def]
    exact sp_sub_cd0_align_std3 hsp_align
  have hfs1 : FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAt img.base C ctl abs) s1 :=
    hfs.of_steps hsteps01 (evs := []) (by simpa using htr1) (fun _ => NoFsEv.nil)
  have hfs1_kit : FsAt kit.envOk (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAt img.base C ctl abs) s1 :=
    hfs1.mono (fun _ h => h.1) id
  rw [← hsp1] at hx24_1 hx25_1 hx28_1
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_p1 kit ikit sp hstack_lt))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_load kit ikit sp hp1_le))
    (by sep_focus) ?_
  sep_norm
  have hload := stageP1_load_ok_kit (ikit := ikit)
    peer hA hkit hload_le haddr_ss hload_ok s0 s1
    outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr idStorePtr
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr b_390
    hb hinv1 hfs1_kit hpc1 hrun1 hsp1_align htr1
    hx0_1 hx1_1 hx19_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx30_1
  rw [hsp1] at hload
  simp only [BitVec.add_assoc] at hload
  have hload_ex := SepWPp.mono_run hload fun s6 P_m h =>
    let ⟨⟨opt, hrel, htr6, hent⟩, hregs⟩ := h
    Exists.intro opt (And.intro (And.intro hrel (And.intro htr6 hregs)) hent)
  refine bind_sepWPp_exists_frame hload_ex (by sep_focus)
    fun opt s6 hsteps16 hpc6 hrun6 hregs6 => ?_
  rcases hregs6 with ⟨hrel_load, htr6, hsp6, hx0_6, hx1_6, hx2_6, hx3_6,
    hx19_6, hx21_6, hx26_6, hx27_6, _, hx30_6, hF6, hsym6⟩
  have hinv6 : ImgCallInv img s6 := ⟨hF6, hsym6⟩
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by
    rw [hsp6, ← hsp1]; exact hsp1_align
  have htr6_pre : s0.trace <+: s6.trace :=
    ⟨kit.loadEvs encRecord peer.val (.ok opt), by rw [htr6, htr1]⟩
  have hfs6 : FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAt img.base C ctl abs) s6 :=
    hfs1.of_steps hsteps16 htr6 (fun hq => hq.1.1 encRecord peer.val (.ok opt))
  have hfs6_ikit : FsAt ikit.envOk (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAt img.base C ctl abs) s6 :=
    hfs6.mono (fun _ h => h.2) id
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_load kit ikit sp hp1_le).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_trust kit ikit sp hp1_le))
    (by sep_focus) ?_
  sep_norm
  have htrust_raw := stageP1_trust_call_wp_kit (ist := ist)
    peer remoteIdKey hA hikit htrust_le haddr_id s0 s6
    outPtr coroPtr ctxPtr msgPtr remoteAddrPtr idStorePtr
    u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    hb hinv6 hfs6_ikit hpc6 hrun6 hsp6_align htr6_pre
    hx0_6 hx1_6 hx2_6 hx3_6 hx19_6 hx21_6 hx26_6 hx27_6 hx30_6
  have htrust := trust_call_wp_specialize_false htrust_false htrust_raw
  rw [hsp6] at htrust
  simp only [BitVec.add_assoc] at htrust
  refine SepWPp.bind_sepWPp_steps_frame htrust (by sep_focus)
    fun sm _ hpcm hrunm hregsm => ?_
  rcases hregsm with ⟨hrel_trust, htrm, hx20_m, hx23_m, hspm, hx19_m, _, hinvm⟩
  have hspm_align : (sm.sp &&& 15#64 == 0#64) = true := by
    rw [hspm, ← hsp6]; exact hsp6_align
  have htrm_pre : s0.trace <+: sm.trace :=
    ⟨kit.loadEvs encRecord peer.val (.ok opt) ++
       ikit.trustEvs peer.val remoteIdKey .receiving (.ok false),
     by rw [htrm, htr6, htr1, List.append_assoc]⟩
  sep_norm
  refine SepWPp.exists_elim fun v_a8 =>
    SepWPp.exists_elim fun v_b8 =>
    SepWPp.exists_elim fun v_d0 => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_trust kit ikit sp hp1_le).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_p1 kit ikit sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_err kit ikit sp hstack_lt))
    (by sep_focus) ?_
  unfold processPrekeyInnerInitAt
  sep_norm
  have herr := stageP1_untrusted_err_ok_kit
    (Scope := Scope) (kit := kit) (ikit := ikit) (st := st) (ist := ist)
    peer remoteIdKey opt hA herr_le s0 sm
    outPtr coroPtr msgPtr remoteAddrPtr sessStorePtr idStorePtr
    0#8 0#8
    hb hinvm hpcm hrunm hspm_align htrm_pre hx19_m hx20_m hx23_m
  rw [hspm, hsp_saved] at herr
  have herr_re := SepWPp.mono_run herr fun sf P_f h =>
    let ⟨htrf, hent, hregs⟩ := h
    And.intro hent (And.intro htrf hregs)
  refine SepWPp.bind_sepWPp_steps_frame herr_re (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨htrf, hspf, hcs_f, hFf, hsymf⟩
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_err kit ikit sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf ?_
  have htr_full : sf.trace = s0.trace ++ kit.loadEvs encRecord peer.val (.ok opt) ++
      ikit.trustEvs peer.val remoteIdKey .receiving (.ok false) := by
    rw [htrf, htrm, htr6, htr1]
  refine ⟨⟨opt, hrel_load, hrel_trust, htr_full, ?_⟩,
    hspf, hcs_f, hFf, hsymf⟩
  refine Entails.sepExists_right v_a8
    (Entails.sepExists_right v_b8
      (Entails.sepExists_right v_d0 ?_))
  rw [hsp_saved]
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
