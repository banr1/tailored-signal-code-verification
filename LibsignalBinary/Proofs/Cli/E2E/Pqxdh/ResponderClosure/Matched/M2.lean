/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1DropSS3A
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Aux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsB
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Stage P2 Matched-Session Unpack Helpers and Shared Error-Return Record Teardown

Defines `prevSessionsEmptyAt` (`p1LoadedRecordAt` unpack and stack split helpers) and proves the
shared error-return record teardown `closure_err_drop_record_tail_ext_ok` (`+0x3588 → s0.readReg64 .x30`
for general `g.prevCap`) along with its `AllocContractsX` generalization.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp eq_of_sep_emp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.SignalSession

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `p1LoadedRecordAt` unpack and stack split helpers -/

/-- Empty `previous_sessions` `Vec` header + optional spare capacity buffer at `coroPtr + 0xe0#64`
extracted from `sessionRecordAt A (coroPtr + 0xe0#64) g r`. -/
def prevSessionsEmptyAt (A : RustAlloc) (coroPtr : BitVec 64) (g : RecordGhost) : SepProp :=
  vecAt A 24 8 (fun (_ : Unit) _ => emp) (coroPtr + 0xe0#64) g.prevCap g.prevPtr []

theorem sessionRecordAt_some_eq_prev_sess (A : RustAlloc) (coroPtr : BitVec 64)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (hcur : r.currentSession = some sess) :
    sessionRecordAt A (coroPtr + 0xe0#64) g r ⊢
      ∃∗ recG : SessionGhost,
        ⌜g.cur = some recG⌝ ∗
        prevSessionsEmptyAt A coroPtr g ∗
        sessionStateReprAt A (coroPtr + 0xf8#64) recG sess := by
  cases hgc : g.cur with
  | none =>
    simp only [sessionRecordAt, hgc, hcur]
    apply Entails.trans (Q := ⌜False⌝ ∗ prevSessionsEmptyAt A coroPtr g)
    · unfold prevSessionsEmptyAt
      exact Entails.of_eq (by ac_rfl)
    · exact Entails.pure_left fun hf => False.elim hf
  | some recG =>
    refine Entails.sepExists_right recG (Entails.pure_right rfl ?_)
    simp only [sessionRecordAt, hgc, hcur, prevSessionsEmptyAt,
      BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.refl _

theorem prevSessionsEmptyAt_restore_record (A : RustAlloc) (coroPtr : BitVec 64)
    (g : RecordGhost) (recG : SessionGhost)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (hgc : g.cur = some recG) (hcur : r.currentSession = some sess) :
    prevSessionsEmptyAt A coroPtr g ∗ sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ⊢
      sessionRecordAt A (coroPtr + 0xe0#64) g r := by
  simp only [sessionRecordAt, hgc, hcur, prevSessionsEmptyAt,
    BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

theorem prevSessionsEmptyAt_unpack (A : RustAlloc) (coroPtr : BitVec 64) (g : RecordGhost) :
    prevSessionsEmptyAt A coroPtr g ⊢
      ⌜g.prevCap.toNat * 24 < 2 ^ 63 ∧ g.prevPtr ≠ 0#64⌝ ∗
      ((coroPtr + 0xe0#64) ↦₆₄ g.prevCap) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ g.prevPtr) ∗
      ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
      (if g.prevCap = 0#64 then emp
       else A.live g.prevPtr (g.prevCap.toNat * 24) 8 ∗
         memRegion g.prevPtr (g.prevCap.toNat * 24)) := by
  unfold prevSessionsEmptyAt vecAt vecHeader vecBuf
  dsimp only [List.length_nil, Nat.zero_mul, Nat.sub_zero]
  change
    ((coroPtr + 0xe0#64) ↦₆₄ g.prevCap ∗
      ((coroPtr + 0xe0#64 + 8#64) ↦₆₄ g.prevPtr ∗
        (coroPtr + 0xe0#64 + 16#64) ↦₆₄ 0#64)) ∗
      (⌜0 ≤ g.prevCap.toNat ∧ g.prevCap.toNat * 24 < 2 ^ 63 ∧ g.prevPtr ≠ 0#64⌝ ∗
        (if g.prevCap = 0#64 then emp
         else A.live g.prevPtr (g.prevCap.toNat * 24) 8 ∗
           arrayAt (fun (_ : Unit) _ => emp) 24 g.prevPtr [] ∗
           memRegion (g.prevPtr + 0#64) (g.prevCap.toNat * 24))) ⊢ _
  simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (Q :=
    ⌜0 ≤ g.prevCap.toNat ∧ g.prevCap.toNat * 24 < 2 ^ 63 ∧ g.prevPtr ≠ 0#64⌝ ∗
    (((coroPtr + 0xe0#64) ↦₆₄ g.prevCap) ∗
     ((coroPtr + 0xe8#64) ↦₆₄ g.prevPtr) ∗
     ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
     (if g.prevCap = 0#64 then emp
      else A.live g.prevPtr (g.prevCap.toNat * 24) 8 ∗
        arrayAt (fun (_ : Unit) _ => emp) 24 g.prevPtr [] ∗
        memRegion g.prevPtr (g.prevCap.toNat * 24)))) (Entails.of_eq (by ac_rfl)) ?_
  refine Entails.pure_left fun ⟨_, hcap, hptr⟩ => Entails.pure_right ⟨hcap, hptr⟩ ?_
  by_cases hc : g.prevCap = 0#64
  · simp only [hc, ↓reduceIte]
    exact Entails.refl _
  · simp only [hc, ↓reduceIte, arrayAt, emp_sepConj]
    exact Entails.refl _

theorem prevSessionsEmptyAt_zero (A : RustAlloc) (coroPtr : BitVec 64) (g : RecordGhost)
    (hzero : g.prevCap = 0#64) :
    prevSessionsEmptyAt A coroPtr g ⊢
      ⌜g.prevPtr ≠ 0#64⌝ ∗
      ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ g.prevPtr) ∗
      ((coroPtr + 0xf0#64) ↦₆₄ 0#64) := by
  refine Entails.trans (prevSessionsEmptyAt_unpack A coroPtr g) ?_
  simp only [hzero, ↓reduceIte, sepConj_emp]
  refine Entails.pure_left fun ⟨_, hptr⟩ => Entails.pure_right hptr (Entails.refl _)

theorem stack_root_to_promoteMatch (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - promoteMatchingSessionMatchStack) ∗
        stackAt sp promoteMatchingSessionMatchStack :=
  stackAt_split_of_le sp rootStack promoteMatchingSessionMatchStack (by decide) hn

theorem stack_root_to_alloc (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - allocHookStack) ∗
        stackAt sp allocHookStack :=
  stackAt_split_of_le sp rootStack allocHookStack (by decide) hn

theorem stack_root_to_dropSS (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - dropSessionStructureLocal2Stack) ∗
        stackAt sp dropSessionStructureLocal2Stack :=
  stackAt_split_of_le sp rootStack dropSessionStructureLocal2Stack (by decide) hn

theorem stack_root_to_growOneSpe (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
        stackAt sp growOneSpeStack :=
  stackAt_split_of_le sp rootStack growOneSpeStack (by decide) hn

theorem stack_dropSS_to_alloc (sp : BitVec 64) (hn : dropSessionStructureLocal2Stack ≤ 2 ^ 64) :
    stackAt sp dropSessionStructureLocal2Stack =
      memRegion (sp - BitVec.ofNat 64 dropSessionStructureLocal2Stack)
        (dropSessionStructureLocal2Stack - allocHookStack) ∗
        stackAt sp allocHookStack :=
  stackAt_split_of_le sp dropSessionStructureLocal2Stack allocHookStack (by decide) hn

/-! ## Shared error-return record teardown (`+0x3588 → s0.readReg64 .x30`) -/

theorem coro_e0_3w_344_entails_368 (coroPtr w0 w1 w2 : BitVec 64) :
    ((coroPtr + 0xe0#64) ↦₆₄ w0) ∗
    ((coroPtr + 0xe8#64) ↦₆₄ w1) ∗
    ((coroPtr + 0xf0#64) ↦₆₄ w2) ∗
    memRegion (coroPtr + 0xf8#64) 344 ⊢
      memRegion (coroPtr + 0xe0#64) 368 := by
  have h24 :
      ((coroPtr + 0xe0#64) ↦₆₄ w0) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ w1) ∗
      ((coroPtr + 0xf0#64) ↦₆₄ w2) ⊢
        memRegion (coroPtr + 0xe0#64) 24 := by
    rw [ProofLib.memRegion_split (coroPtr + 0xe0#64) 8 16 (by decide),
        ProofLib.memRegion_split (coroPtr + 0xe0#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
  rw [ProofLib.memRegion_split (coroPtr + 0xe0#64) 24 344 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (Q :=
    (((coroPtr + 0xe0#64) ↦₆₄ w0) ∗
     ((coroPtr + 0xe8#64) ↦₆₄ w1) ∗
     ((coroPtr + 0xf0#64) ↦₆₄ w2)) ∗
    memRegion (coroPtr + 0xf8#64) 344) (Entails.of_eq (by ac_rfl)) ?_
  exact sepConj_mono_left h24

theorem sp370_4w64_w32_entails_36 (sp w0 w1 w2 w3 : BitVec 64) (w4 : BitVec 32) :
    ((sp + 0x370#64) ↦₆₄ w0) ∗
    ((sp + 0x378#64) ↦₆₄ w1) ∗
    ((sp + 0x380#64) ↦₆₄ w2) ∗
    ((sp + 0x388#64) ↦₆₄ w3) ∗
    ((sp + 0x390#64) ↦₃₂ w4) ⊢
      memRegion (sp + 0x370#64) 36 := by
  rw [ProofLib.memRegion_split (sp + 0x370#64) 8 28 (by decide),
      ProofLib.memRegion_split (sp + 0x370#64 + 8#64) 8 20 (by decide),
      ProofLib.memRegion_split (sp + 0x370#64 + 8#64 + 8#64) 8 12 (by decide),
      ProofLib.memRegion_split (sp + 0x370#64 + 8#64 + 8#64 + 8#64) 8 4 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (pointsTo32_entails_memRegion _ _))))

private theorem cap_lt_2_63_ne_neg1 {c : BitVec 64} (hc : c.toNat < 2 ^ 63) :
    c ≠ 0xffffffffffffffff#64 := by
  bv_omega

theorem sessionStateAt_split_localIk_cap (A : RustAlloc) (ss : BitVec 64)
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8))) :
    ∃ R_ss : SepProp,
      (sessionStateAt A ss recG recSt ⊢
        ⌜recG.localIk.cap.toNat < 2 ^ 63⌝ ∗ (ss ↦₆₄ recG.localIk.cap) ∗ R_ss) ∧
      ((ss ↦₆₄ recG.localIk.cap) ∗ R_ss ⊢
        sessionStateAt A ss recG recSt) := by
  have hvg_lt : vecGhostRestAt A recG.localIk ss ⊢
      ⌜recG.localIk.cap.toNat < 2 ^ 63⌝ ∗ vecGhostRestAt A recG.localIk ss := by
    have heq : vecGhostRestAt A recG.localIk ss =
        ⌜recG.localIk.bytes.length ≤ recG.localIk.cap.toNat ∧
          recG.localIk.cap.toNat < 2 ^ 63 ∧ recG.localIk.ptr ≠ 0⌝ ∗
        (((ss + 8#64) ↦₆₄ recG.localIk.ptr) ∗
          ((ss + 16#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
          (if recG.localIk.cap = 0 then emp
           else A.live recG.localIk.ptr recG.localIk.cap.toNat 1 ∗
             (recG.localIk.ptr ↦ₛ recG.localIk.bytes) ∗
             memRegion (recG.localIk.ptr + BitVec.ofNat 64 recG.localIk.bytes.length)
               (recG.localIk.cap.toNat - recG.localIk.bytes.length))) := by
      dsimp only [vecGhostRestAt]; ac_rfl
    rw [heq]
    exact Entails.pure_left fun hm =>
      Entails.pure_right hm.2.1 (Entails.pure_right hm (Entails.refl _))
  refine ⟨sessionStateRestAt A ss recG recSt, ?_,
    Entails.of_eq (sessionStateAt_expose_cap A ss recG recSt).symm⟩
  rw [sessionStateAt_expose_cap A ss recG recSt]
  unfold sessionStateRestAt
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hvg_lt))) ?_
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1200000 in
/-- Drops `sessionStateAt A (coroPtr + 0xf8#64) recG recSt` and `prevSessionsEmptyAt A coroPtr g`
across `+0x3588 → s0.readReg64 .x30` for arbitrary `g : RecordGhost` (`g.prevCap = 0` or `≠ 0`),
writing the 48-byte `Result::Err` payload `(errTag, w_22, w_370..w_390)` into `outPtr`. -/
theorem closure_err_drop_record_tail_ext_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hA : AllocContracts img.base A ext)
    (hdrop_ss : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        DropSS3.dropSessionStructure3Name)
      (dropSessionStructureLocal2Spec A))
    (s0 s : State)
    (sp coroPtr outPtr errTag w_370 w_378 w_380 w_388 : BitVec 64)
    (w_22 w_390 : BitVec 32) (b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hinv : ImgCallInv img s)
    (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3588#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (prevSessionsEmptyAt A coroPtr g ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗
       ((sp + 0x370#64) ↦₆₄ w_370) ∗
       ((sp + 0x378#64) ↦₆₄ w_378) ∗
       ((sp + 0x380#64) ↦₆₄ w_380) ∗
       ((sp + 0x388#64) ↦₆₄ w_388) ∗
       ((sp + 0x390#64) ↦₃₂ w_390) ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        (P_f ⊢
          memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ errTag) ∗
          ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
          ((outPtr + 0xc#64) ↦₆₄ w_370) ∗
          ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗
          ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          memRegion (sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt sp dropSessionStructureLocal2Stack) ∧
        sf.sp = sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        ImgCallInv img sf)
      Qp := by
  have hdss_le : dropSessionStructureLocal2Stack ≤ 2 ^ 64 :=
    Nat.le_trans hsp_lt (Nat.le_of_lt sp.isLt)
  refine P3P4.SepWPp.weaken_frame (prevSessionsEmptyAt_unpack A coroPtr g) (by sep_focus) ?_
  sep_norm
  refine SepWPp.pure_elim fun ⟨hprev_lt, _⟩ => ?_
  obtain ⟨R_ss, hss_fwd, hss_bwd⟩ := sessionStateAt_split_localIk_cap A (coroPtr + 0xf8#64) recG recSt
  refine P3P4.SepWPp.weaken_frame hss_fwd (by sep_focus) ?_
  sep_norm
  refine SepWPp.pure_elim fun hcap_lt => ?_
  have hcap_ne : recG.localIk.cap ≠ 0xffffffffffffffff#64 := cap_lt_2_63_ne_neg1 hcap_lt
  have hto_call := p2_err_drop_ss_to_call_ext_wp img.base ext s coroPtr recG.localIk.cap
    hcap_ne hpc hrun hsp_align hx19
  refine SepWPp.bind_sepWP_steps_frame hinv hto_call (by sep_focus)
    fun s1 _ hpc1 hrun1 hinv1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hvregs1, hx0_1, hx19_1, hx22_1, hx25_1, hx26_1, hx28_1, _, hx30_1⟩
  have hsp1 : s1.sp = sp := hsp1_s.trans hsp_eq
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  refine P3P4.SepWPp.weaken_frame hss_bwd (by sep_focus) ?_
  refine SepWPp.call_nopanic_steps_frame
    (spec := dropSessionStructureLocal2Spec A)
    (x := ⟨coroPtr + 0xf8#64, recG, recSt⟩)
    (T := sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ A.pool ∗
      stackAt sp dropSessionStructureLocal2Stack)
    hinv1 hdrop_ss hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp1])
    hx0_1 (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hinv2 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  rw [hsp1, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  rcases hcs2 with ⟨hx19_cs2, _, _, hx22_cs2, _, _, hx25_cs2, hx26_cs2, _, hx28_cs2, _, hvregs_cs2⟩
  have hvregs2_s : calleeSavedVRegs s2 = calleeSavedVRegs s :=
    hvregs_cs2.trans (congrArg VRegFile.calleeSaved hvregs1)
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by
    rw [hsp2, ← hsp_eq]; exact hsp_align
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx22_2 : s2.readReg64 .x22 = w_22.zeroExtend 64 := hx22_cs2.trans (hx22_1.trans hx22)
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by
    rw [hsp2]; exact hx25_cs2.trans (hx25_1.trans hx25)
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans (hx26_1.trans hx26)
  have hx28_2 : s2.readReg64 .x28 = errTag := hx28_cs2.trans (hx28_1.trans hx28)
  rw [stack_dropSS_to_alloc sp hdss_le, savedRegsAt_eq_sp_c70 sp s0]
  refine P3P4.SepWPp.weaken_frame (memRegion_48_out_entails outPtr) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_ret0 => SepWPp.exists_elim fun u_ret08 =>
    SepWPp.exists_elim fun u_ret0c => SepWPp.exists_elim fun u_ret14 =>
    SepWPp.exists_elim fun u_ret1c => SepWPp.exists_elim fun u_ret24 =>
    SepWPp.exists_elim fun u_ret2c => ?_
  by_cases hcap : g.prevCap = 0#64
  · simp only [hcap, ↓reduceIte, emp_sepConj]
    have htail := p2_err_tail_prev_zero_ext_wp img.base ext s2 coroPtr outPtr errTag g.prevPtr
      w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      w_22 w_390 u_ret08 u_ret2c b_2c0
      hpc2 hrun2 hsp2_align hx19_2 hx22_2 hx25_2 hx26_2 hx28_2
    rw [hsp2] at htail
    refine SepWPp.ret_sepWP_steps_frame hinv2 htail (by sep_focus)
      fun sf _ _ _ hinvf hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hvregsf, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _⟩
    refine ⟨?_, hspf, htrf.trans (htr2_1.trans htr1_s),
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, True.intro⟩,
      hvregsf.trans hvregs2_s,
      hinvf⟩
    refine Entails.trans (entails_replace_sub (coro_e0_3w_344_entails_368 coroPtr 0#64 g.prevPtr 0#64)
      (by sep_focus) rfl) ?_
    exact entails_replace_sub (sp370_4w64_w32_entails_36 sp w_370 w_378 w_380 w_388 w_390)
      (by sep_focus) (eq_of_sep_emp (by sep_focus))
  · simp only [hcap, ↓reduceIte]
    have htail := p2_err_tail_prev_dealloc_ext_wp img.base ext hA s2 coroPtr outPtr errTag
      g.prevCap g.prevPtr w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      w_22 w_390 u_ret08 u_ret2c b_2c0 hcap hprev_lt
      hpc2 hrun2 hsp2_align hx19_2 hx22_2 hx25_2 hx26_2 hx28_2
    rw [hsp2] at htail
    refine SepWPp.ret_sepWP_steps_frame hinv2 htail (by sep_focus)
      fun sf _ _ _ hinvf hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hvregsf, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _⟩
    refine ⟨?_, hspf, htrf.trans (htr2_1.trans htr1_s),
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, True.intro⟩,
      hvregsf.trans hvregs2_s,
      hinvf⟩
    refine Entails.trans (entails_replace_sub (coro_e0_3w_344_entails_368 coroPtr g.prevCap g.prevPtr 0#64)
      (by sep_focus) rfl) ?_
    exact entails_replace_sub (sp370_4w64_w32_entails_36 sp w_370 w_378 w_380 w_388 w_390)
      (by sep_focus) (eq_of_sep_emp (by sep_focus))

/-! ## `AllocContractsX` generalization -/

/-- Stack-parametric `dropSessionStructureLocal2Spec` (`stk = dropSessionStructureLocal2Stack`
equals `dropSessionStructureLocal2Spec A`; `stk = 48 + Getters.dropChainStackX` covers `AllocContractsX`). -/
def dropSessionStructureLocal2SpecWithStack (stk : Nat) (A : RustAlloc) :
    Spec DropSessionStructureGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss⌝ ∗
      sessionStateAt A x.ss x.G x.st ∗ A.pool ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.ss 344 ∗ A.pool ∗ stackAt s0.sp stk

abbrev dropSessionStructureLocal2StackX : Nat := 48 + Getters.dropChainStackX

abbrev dropSessionStructureLocal2SpecX (A : RustAlloc) : Spec DropSessionStructureGhost :=
  dropSessionStructureLocal2SpecWithStack dropSessionStructureLocal2StackX A

theorem subroutine_ok_dropSS_inImage {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr DropSS3.dropSessionStructure3Name)
      (dropSessionStructureLocal2Spec A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr DropSS3.dropSessionStructure3Name)
      ((dropSessionStructureLocal2SpecWithStack dropSessionStructureLocal2Stack A).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  dsimp only [Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s0 hpc hrun hpre.2 hal fun _ hout => hout

theorem stack_root_to_dssWith (dssStack : Nat) (sp : BitVec 64)
    (hdss : dssStack ≤ rootStack) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - dssStack) ∗
        stackAt sp dssStack :=
  stackAt_split_of_le sp rootStack dssStack hdss hn

theorem stack_root_to_extHook_m2t (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - extHookStack) ∗
        stackAt sp extHookStack :=
  stackAt_split_of_le sp rootStack extHookStack (by decide) hn

set_option maxHeartbeats 1200000 in
/-- `AllocContractsX` generalization of `closure_err_drop_record_tail_ext_ok` with stack-parametric
`dropSessionStructure3` contract `(dropSessionStructureLocal2SpecWithStack dssStack A).inImage img`. -/
theorem closure_err_drop_record_tail_ext_x_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {dssStack : Nat}
    (hA : AllocContractsX img A ext)
    (hdss : dssStack ≤ rootStack := by decide)
    (hdrop_ss : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr DropSS3.dropSessionStructure3Name)
      ((dropSessionStructureLocal2SpecWithStack dssStack A).inImage img))
    (s0 s : State)
    (sp coroPtr outPtr errTag w_370 w_378 w_380 w_388 : BitVec 64)
    (w_22 w_390 : BitVec 32) (b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hinv : ImgCallInv img s)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3588#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (prevSessionsEmptyAt A coroPtr g ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗
       ((sp + 0x370#64) ↦₆₄ w_370) ∗
       ((sp + 0x378#64) ↦₆₄ w_378) ∗
       ((sp + 0x380#64) ↦₆₄ w_380) ∗
       ((sp + 0x388#64) ↦₆₄ w_388) ∗
       ((sp + 0x390#64) ↦₃₂ w_390) ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt sp rootStack)
      (fun sf P_f =>
        (P_f ⊢
          memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ errTag) ∗
          ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
          ((outPtr + 0xc#64) ↦₆₄ w_370) ∗
          ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗
          ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          memRegion (sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt sp rootStack) ∧
        sf.sp = sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        ImgCallInv img sf)
      Qp := by
  have hroot_le : rootStack ≤ 2 ^ 64 :=
    Nat.le_trans hsp_root (Nat.le_of_lt sp.isLt)
  refine P3P4.SepWPp.weaken_frame (prevSessionsEmptyAt_unpack A coroPtr g) (by sep_focus) ?_
  sep_norm
  refine SepWPp.pure_elim fun ⟨hprev_lt, _⟩ => ?_
  obtain ⟨R_ss, hss_fwd, hss_bwd⟩ := sessionStateAt_split_localIk_cap A (coroPtr + 0xf8#64) recG recSt
  refine P3P4.SepWPp.weaken_frame hss_fwd (by sep_focus) ?_
  sep_norm
  refine SepWPp.pure_elim fun hcap_lt => ?_
  have hcap_ne : recG.localIk.cap ≠ 0xffffffffffffffff#64 := cap_lt_2_63_ne_neg1 hcap_lt
  have hto_call := p2_err_drop_ss_to_call_ext_wp img.base ext s coroPtr recG.localIk.cap
    hcap_ne hpc hrun hsp_align hx19
  refine SepWPp.bind_sepWP_steps_frame hinv hto_call (by sep_focus)
    fun s1 _ hpc1 hrun1 hinv1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hvregs1, hx0_1, hx19_1, hx22_1, hx25_1, hx26_1, hx28_1, _, hx30_1⟩
  have hsp1 : s1.sp = sp := hsp1_s.trans hsp_eq
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  refine P3P4.SepWPp.weaken_frame hss_bwd (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_root_to_dssWith dssStack sp hdss hroot_le)) (by sep_focus) ?_
  refine SepWPp.call_nopanic_steps_frame
    (spec := (dropSessionStructureLocal2SpecWithStack dssStack A).inImage img)
    (x := ⟨coroPtr + 0xf8#64, recG, recSt⟩)
    (φ := img.FrozenLoaded s1 ∧ s1.symtab = img.symtab ∧ s1.readReg64 .x0 = coroPtr + 0xf8#64)
    (T := sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ A.pool ∗ stackAt sp dssStack)
    hinv1 hdrop_ss hpc1 hrun1 hsp1_al hx30_1
    (by
      dsimp only [Spec.inImage, dropSessionStructureLocal2SpecWithStack]
      rw [hsp1, ← sepConj_assoc, pure_sepConj_pure]; simp only [and_assoc])
    ⟨hinv1.1, hinv1.2, hx0_1⟩ (by sep_focus)
    (hpan_false := fun _ => by simp only [Spec.inImage]; rfl)
    (hexit_false := fun _ _ => by simp only [Spec.inImage]; rfl)
    (hoom_false := fun _ => by simp only [Spec.inImage]; rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hinv2 => ?_)
  dsimp only [Spec.inImage, dropSessionStructureLocal2SpecWithStack]
  rw [hsp1, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_root_to_dssWith dssStack sp hdss hroot_le).symm) (by sep_focus) ?_
  rcases hcs2 with ⟨hx19_cs2, _, _, hx22_cs2, _, _, hx25_cs2, hx26_cs2, _, hx28_cs2, _, hvregs_cs2⟩
  have hvregs2_s : calleeSavedVRegs s2 = calleeSavedVRegs s :=
    hvregs_cs2.trans (congrArg VRegFile.calleeSaved hvregs1)
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by
    rw [hsp2, ← hsp_eq]; exact hsp_align
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx22_2 : s2.readReg64 .x22 = w_22.zeroExtend 64 := hx22_cs2.trans (hx22_1.trans hx22)
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by
    rw [hsp2]; exact hx25_cs2.trans (hx25_1.trans hx25)
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans (hx26_1.trans hx26)
  have hx28_2 : s2.readReg64 .x28 = errTag := hx28_cs2.trans (hx28_1.trans hx28)
  rw [stack_root_to_extHook_m2t sp hroot_le, savedRegsAt_eq_sp_c70 sp s0]
  refine P3P4.SepWPp.weaken_frame (memRegion_48_out_entails outPtr) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_ret0 => SepWPp.exists_elim fun u_ret08 =>
    SepWPp.exists_elim fun u_ret0c => SepWPp.exists_elim fun u_ret14 =>
    SepWPp.exists_elim fun u_ret1c => SepWPp.exists_elim fun u_ret24 =>
    SepWPp.exists_elim fun u_ret2c => ?_
  by_cases hcap : g.prevCap = 0#64
  · simp only [hcap, ↓reduceIte, emp_sepConj]
    have htail := p2_err_tail_prev_zero_ext_wp img.base ext s2 coroPtr outPtr errTag g.prevPtr
      w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      w_22 w_390 u_ret08 u_ret2c b_2c0
      hpc2 hrun2 hsp2_align hx19_2 hx22_2 hx25_2 hx26_2 hx28_2
    rw [hsp2] at htail
    refine SepWPp.ret_sepWP_steps_frame hinv2 htail (by sep_focus)
      fun sf _ _ _ hinvf hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hvregsf, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _⟩
    refine ⟨?_, hspf, htrf.trans (htr2_1.trans htr1_s),
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, True.intro⟩,
      hvregsf.trans hvregs2_s,
      hinvf⟩
    refine Entails.trans (entails_replace_sub (coro_e0_3w_344_entails_368 coroPtr 0#64 g.prevPtr 0#64)
      (by sep_focus) rfl) ?_
    exact entails_replace_sub (sp370_4w64_w32_entails_36 sp w_370 w_378 w_380 w_388 w_390)
      (by sep_focus) (eq_of_sep_emp (by sep_focus))
  · simp only [hcap, ↓reduceIte]
    have htail := p2_err_tail_prev_dealloc_ext_x_wp hA s2 hinv2 coroPtr outPtr errTag
      g.prevCap g.prevPtr w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      w_22 w_390 u_ret08 u_ret2c b_2c0 hcap hprev_lt
      hpc2 hrun2 hsp2_align hx19_2 hx22_2 hx25_2 hx26_2 hx28_2
    rw [hsp2] at htail
    refine SepWPp.ret_sepWP_steps_frame hinv2 htail (by sep_focus)
      fun sf _ _ _ hinvf hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hvregsf, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _⟩
    refine ⟨?_, hspf, htrf.trans (htr2_1.trans htr1_s),
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, True.intro⟩,
      hvregsf.trans hvregs2_s,
      hinvf⟩
    refine Entails.trans (entails_replace_sub (coro_e0_3w_344_entails_368 coroPtr g.prevCap g.prevPtr 0#64)
      (by sep_focus) rfl) ?_
    exact entails_replace_sub (sp370_4w64_w32_entails_36 sp w_370 w_378 w_380 w_388 w_390)
      (by sep_focus) (eq_of_sep_emp (by sep_focus))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
