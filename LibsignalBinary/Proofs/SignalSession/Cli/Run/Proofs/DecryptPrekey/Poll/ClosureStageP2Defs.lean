/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSessionStructure3
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Stmt
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2a
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2b
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StoresAt
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4KyberRefused
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Poll Stage P2 and Stage P3 `Ext` Interfaces and Stack Budgets

Defines `prevSessionsEmptyAt`, Stage P2 stack budgets (`stageP2CallStack`), Path B general-`prevCap`
Stage P3 predicates (`StageP3PrevEmptyVRegsStmt`), and Path A `StageP3GenStepsVRegsStmt`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.RunProofs

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Empty `previous_sessions` Header (`prevSessionsEmptyAt`) for Path B -/

/-- Empty `previous_sessions` `Vec` header + optional spare capacity buffer at `coroPtr + 0xe0#64`
extracted from `sessionRecordAt A (coroPtr + 0xe0#64) g r`
(definitionally equal to `Matched.prevSessionsEmptyAt`). -/
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
    have hcomm :
        vecAt A 24 8 (fun (_ : Unit) _ => emp) (coroPtr + 0xe0#64) g.prevCap g.prevPtr [] ∗ ⌜False⌝ =
        ⌜False⌝ ∗ prevSessionsEmptyAt A coroPtr g := by
      unfold prevSessionsEmptyAt
      ac_rfl
    rw [hcomm]
    exact Entails.pure_left fun hf => False.elim hf
  | some recG =>
    refine Entails.sepExists_right recG (Entails.pure_right rfl ?_)
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
  have hpull :
      ((coroPtr + 0xe0#64) ↦₆₄ g.prevCap ∗
        ((coroPtr + 0xe0#64 + 8#64) ↦₆₄ g.prevPtr ∗
          (coroPtr + 0xe0#64 + 16#64) ↦₆₄ BitVec.ofNat 64 0)) ∗
      (⌜0 ≤ g.prevCap.toNat ∧ g.prevCap.toNat * 24 < 2 ^ 63 ∧ g.prevPtr ≠ 0⌝ ∗
        if g.prevCap = 0 then emp
        else A.live g.prevPtr (g.prevCap.toNat * 24) 8 ∗
          arrayAt (fun (_ : Unit) _ => emp) 24 g.prevPtr [] ∗
          memRegion (g.prevPtr + BitVec.ofNat 64 0) (g.prevCap.toNat * 24)) =
      ⌜0 ≤ g.prevCap.toNat ∧ g.prevCap.toNat * 24 < 2 ^ 63 ∧ g.prevPtr ≠ 0#64⌝ ∗
      (((coroPtr + 0xe0#64) ↦₆₄ g.prevCap) ∗
        ((coroPtr + 0xe8#64) ↦₆₄ g.prevPtr) ∗
        ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
        if g.prevCap = 0#64 then emp
        else A.live g.prevPtr (g.prevCap.toNat * 24) 8 ∗
          memRegion g.prevPtr (g.prevCap.toNat * 24)) := by
    have h0 : (0 : BitVec 64) = 0#64 := rfl
    have hof0 : BitVec.ofNat 64 0 = 0#64 := rfl
    rw [h0, hof0, BitVec.add_zero]
    dsimp only [arrayAt]
    simp only [emp_sepConj, BitVec.add_assoc, BitVec.reduceAdd]
    ac_rfl
  rw [hpull]
  exact Entails.pure_left fun ⟨_, hcap, hptr⟩ => Entails.pure_right ⟨hcap, hptr⟩ (Entails.refl _)

theorem prevSessionsEmptyAt_zero (A : RustAlloc) (coroPtr : BitVec 64) (g : RecordGhost)
    (hzero : g.prevCap = 0#64) :
    prevSessionsEmptyAt A coroPtr g ⊢
      ⌜g.prevPtr ≠ 0#64⌝ ∗
      ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ g.prevPtr) ∗
      ((coroPtr + 0xf0#64) ↦₆₄ 0#64) := by
  refine Entails.trans (prevSessionsEmptyAt_unpack A coroPtr g) ?_
  rw [hzero]
  simp only [↓reduceIte, sepConj_emp]
  exact Entails.pure_left fun ⟨_, hptr⟩ => Entails.pure_right hptr (Entails.refl _)

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
    exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) (ProofLib.pointsTo64_entails_memRegion _ _))
  have hgrp :
      ((coroPtr + 0xe0#64) ↦₆₄ w0) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ w1) ∗
      ((coroPtr + 0xf0#64) ↦₆₄ w2) ∗
      memRegion (coroPtr + 0xf8#64) 344 =
      (((coroPtr + 0xe0#64) ↦₆₄ w0) ∗
        ((coroPtr + 0xe8#64) ↦₆₄ w1) ∗
        ((coroPtr + 0xf0#64) ↦₆₄ w2)) ∗
      memRegion (coroPtr + 0xe0#64 + 24#64) 344 := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    ac_rfl
  rw [hgrp, ProofLib.memRegion_split (coroPtr + 0xe0#64) 24 344 (by decide)]
  exact sepConj_mono_left h24

theorem prevSessionsEmptyAt_restore_record (A : RustAlloc) (coroPtr : BitVec 64)
    (g : RecordGhost) (recG : SessionGhost)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (hgc : g.cur = some recG) (hcur : r.currentSession = some sess) :
    prevSessionsEmptyAt A coroPtr g ∗ sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ⊢
      sessionRecordAt A (coroPtr + 0xe0#64) g r := by
  simp only [sessionRecordAt, hgc, hcur, prevSessionsEmptyAt,
    BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

theorem opkPacked_two_lo32 (w : BitVec 64) :
    (((2#64 : BitVec 64).setWidth 32).zeroExtend 64 ||| (w <<< 32)).extractLsb' 0 32 = 2#32 := by
  bv_bits

theorem coro_298_split_two (coroPtr w : BitVec 64) :
    ((coroPtr + 0x298#64) ↦₆₄ (((2#64 : BitVec 64).setWidth 32).zeroExtend 64 ||| (w <<< 32))) ⊢
      ∃∗ hi : BitVec 32,
        ((coroPtr + 0x298#64) ↦₃₂ 2#32) ∗
        ((coroPtr + 0x29c#64) ↦₃₂ hi) := by
  let packed := (((2#64 : BitVec 64).setWidth 32).zeroExtend 64 ||| (w <<< 32))
  refine Entails.sepExists_right (packed.extractLsb' 32 32) ?_
  rw [pointsTo64_split32 (coroPtr + 0x298#64) packed, opkPacked_two_lo32 w]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

theorem coro298_two_entails_memRegion8 (coroPtr : BitVec 64) (hi : BitVec 32) :
    ((coroPtr + 0x298#64) ↦₃₂ 2#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ hi) ⊢
      memRegion (coroPtr + 0x298#64) 8 := by
  rw [← coro298_split_eq coroPtr 2#32 hi]
  exact ProofLib.pointsTo64_entails_memRegion _ _

/-! ## 2. Stage P2 Stack Budget Definitions & CLI Bounds (`stageP2CallStack`) -/

/-- Pure/unwind callee stack floor across Substages P2.1–P2.6 and error exits
(definitionally equal to `Kits.stageP2PureAndErrStack`). -/
def stageP2PureAndErrStack : Nat :=
  max (stageP2bStack + 0x700)
    (max stageP2aStack
      (max allocHookStack dropSessionStructureLocal2Stack))

/-- Unified stack budget for full fresh-session Stage P2 (`+0x0868 → +0x1778` and all 6 error
exits; definitionally equal to `Kits.stageP2CallStack`). -/
def stageP2CallStack {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b)
    (skit : IdentitySelfStoreSpec ikit) : Nat :=
  max
    (max
      (max spkKit.getShimStack (max spkKit.getPollStack stageP2PureAndErrStack))
      (max
        (max kpkKit.getShimStack (max kpkKit.getPollStack stageP2PureAndErrStack))
        (max pkKit.getShimStack (max pkKit.getPollStack stageP2PureAndErrStack))))
    (max
      (max skit.kpShimStack (max skit.kpPollStack stageP2PureAndErrStack))
      (max skit.regIdShimStack (max skit.regIdPollStack stageP2PureAndErrStack)))

theorem stageP2PureAndErrStack_le_subStack (B : RunBudgets) :
    stageP2PureAndErrStack ≤ dpClosSubStack B := by
  have h : stageP2PureAndErrStack ≤ 1048576 - 3280 := by decide
  exact Nat.le_trans h (Nat.le_add_right _ _)

theorem cliPollStageP2Stack_le_subStack (A : RustAlloc) (b : BitVec 64) (F0 : FsFiles)
    (peer : AddrGhost) (pid sid kid ksid : BitVec 32) (kbk : PublicKey) (B : RunBudgets) :
    stageP2CallStack
      (cliPollSpkKit A b F0 sid (cliKitStk B))
      (cliPollKpkKit A b F0 kid ksid kbk (cliKitStk B))
      (cliPollPkKit A b F0 pid (cliKitStk B))
      (cliPollSelfKit A b F0 peer (cliKitStk B)) ≤ dpClosSubStack B := by
  have hAll := cliKitStk_le_subStack B
  dsimp only [DpKitStk.All] at hAll
  rcases hAll with ⟨_, _, _, _, _, _, _, _, hkpS, hkpP, hregS, hregP,
    hpkS, hpkP, _, _, hspkS, hspkP, hkpkS, hkpkP, _, _⟩
  have hPure := stageP2PureAndErrStack_le_subStack B
  dsimp only [stageP2CallStack, cliPollSpkKit, cliSignedPreKeyStoreSpec,
    cliPollKpkKit, cliKpkStoreSpecFull, cliPollPkKit, cliPreKeyStoreSpec,
    cliPollSelfKit, cliIdSelfSpecFull]
  exact Nat.max_le.mpr
    ⟨Nat.max_le.mpr
      ⟨Nat.max_le.mpr ⟨hspkS, Nat.max_le.mpr ⟨hspkP, hPure⟩⟩,
       Nat.max_le.mpr
        ⟨Nat.max_le.mpr ⟨hkpkS, Nat.max_le.mpr ⟨hkpkP, hPure⟩⟩,
         Nat.max_le.mpr ⟨hpkS, Nat.max_le.mpr ⟨hpkP, hPure⟩⟩⟩⟩,
     Nat.max_le.mpr
      ⟨Nat.max_le.mpr ⟨hkpS, Nat.max_le.mpr ⟨hkpP, hPure⟩⟩,
       Nat.max_le.mpr ⟨hregS, Nat.max_le.mpr ⟨hregP, hPure⟩⟩⟩⟩

/-! ## 3. Path B General-`prevCap` Stage P3 Helper Predicates (`*PrevEmpty`) -/

/-- Path B counterpart of `stageP3Sub5ExtraPre` replacing `(coroPtr + 0xe0..0xf0)` (`prevCap = 0#64`)
with general `prevSessionsEmptyAt A coroPtr g`. -/
def stageP3Sub5ExtraPrePrevEmpty (A : RustAlloc) (s0 s : State)
    (coroPtr outPtr initErrsPtr : BitVec 64) (g : RecordGhost) (b_2c0 : BitVec 8) : SepProp :=
  ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
  ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (s.sp + 0x448#64) 240 ∗
  prevSessionsEmptyAt A coroPtr g ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x370#64) 36 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0

/-- Path B counterpart of `stageP3DispatchOkMid` at `+0x34dc#64` (`Ok pt`), preserving untouched
`prevSessionsEmptyAt A coroPtr g` into `M4`. -/
def stageP3DispatchOkMidPrevEmpty (A : RustAlloc) (b : BitVec 64) (s0 s : State)
    (coroPtr outPtr initErrsPtr ptCap ptPtr : BitVec 64) (g : RecordGhost)
    (pt : List (BitVec 8)) (b_2c0 : BitVec 8)
    (G₂ : SessionGhost) (st₂ : SessionState (List (BitVec 8))) : SepProp :=
  ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗
  ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗ ((s.sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  memRegion (s.sp + 0x290#64) 16 ∗ (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
  ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
  memRegion (s.sp + 0x3e0#64) 344 ∗ memRegion (s.sp + 0xa90#64) 344 ∗
  sessionStateAt A (coroPtr + 0xf8#64) G₂ st₂ ∗
  prevSessionsEmptyAt A coroPtr g ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
  memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
  memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack

/-- Path B counterpart of `stageP3ErrPost` at `s0.readReg64.x30` (`Err e` / `st.version ≠ msgVer`),
after `+0x3588 → x30` drops `SessionStructure` and deallocates any spare `g.prevPtr` buffer,
leaving `memRegion (coroPtr + 0xe0#64) 368`. -/
def stageP3ErrPostPrevEmpty (A : RustAlloc) (b : BitVec 64) (s0 s : State)
    (coroPtr outPtr : BitVec 64)
    (e : SignalProtocolError) : SepProp :=
  (∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
    ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
    ((s.sp + 0x3d8#64) ↦₆₄ errsLen)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ memRegion (s.sp + 0xa90#64) 344 ∗
  memRegion (coroPtr + 0xe0#64) 368 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
  recordResultAt A outPtr (.error (SessionState.recordError .preKey e)) ∗
  memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
  memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack

theorem stageP3Sub5ExtraPrePrevEmpty_zero (A : RustAlloc) (s0 s : State)
    (coroPtr outPtr initErrsPtr : BitVec 64) (g : RecordGhost) (b_2c0 : BitVec 8)
    (hzero : g.prevCap = 0#64) :
    stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr g b_2c0 ⊢
      ⌜g.prevPtr ≠ 0#64⌝ ∗ stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr g.prevPtr b_2c0 := by
  unfold stageP3Sub5ExtraPrePrevEmpty stageP3Sub5ExtraPre
  have hz := prevSessionsEmptyAt_zero A coroPtr g hzero
  have h1 :
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
        ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
        ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
        ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (s.sp + 0x448#64) 240 ∗
        prevSessionsEmptyAt A coroPtr g ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
        memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x370#64) 36 ∗
        decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0) ⊢
      prevSessionsEmptyAt A coroPtr g ∗
        (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (s.sp + 0x448#64) 240 ∗
          ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
          memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0) :=
    Entails.of_eq (by ac_rfl)
  refine Entails.trans h1 (Entails.trans (sepConj_mono_left hz) ?_)
  simp only [sepConj_assoc]
  exact Entails.pure_left fun hp => Entails.pure_right hp (Entails.of_eq (by ac_rfl))

/-- Path B Stage P3 (`+0x1778 → +0x34dc` / `s0.readReg64.x30`) over general `prevSessionsEmptyAt A coroPtr g`:
- `hOk` (`+0x34dc`) preserves `prevSessionsEmptyAt A coroPtr g` and provides
  `Steps (tripleRatchetProgAtExt img.base ext) s s'` (for `FsAt` at `+0x34dc`) + `calleeSavedVRegs`.
- `hErr` and `hVerNe` (`s0.readReg64.x30`) run `+0x3588 → x30`, dropping `SessionStructure` and
  deallocating any spare `g.prevPtr` buffer into `memRegion (coroPtr + 0xe0#64) 368`. -/
def StageP3PrevEmptyVRegsStmt : Prop :=
  ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem),
    AllocContracts img.base A ext →
    ChainClone3OkExt img.base A ext →
    SenderChainClone3OkExt img.base A ext →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (_root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img) →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        _root_.CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name)
      (dropSessionStructureLocal2Spec A) →
    Obj.Loads libsignalSessionImage img →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (rest : List (BitVec 8))
      (g : RecordGhost) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      initErrsPtr ≠ 0#64 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st →
      st.receiverChains.length < 2 ^ 32 →
      st.pqRatchetState.length < 2 ^ 32 →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = closureEntry img ext + 0x1778#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      rootStack ≤ s.sp.toNat →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat →
        ptCap.toNat < 2 ^ 63 →
        ptPtr ≠ 0#64 →
        Steps (tripleRatchetProgAtExt img.base ext) s s' →
        s'.pc = closureEntry img ext + 0x34dc#64 →
        s'.status = .Running →
        s'.sp = s.sp →
        s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr →
        s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 →
        s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr →
        s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        img.FrozenLoaded s' →
        s'.symtab = img.symtab →
        (P_s' ⊢
          stageP3DispatchOkMidPrevEmpty A img.base s0 s coroPtr outPtr initErrsPtr
            ptCap ptPtr g pt b_2c0 G' (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (Coins.coinsAfter img.base cur rest
              (decryptDraws C st msg.senderRatchetKey rest))) →
        SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt false G' →
        (genP3S5Model C K rem loc msg rest st).1 = .error e →
        e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmpty A img.base s0 s coroPtr outPtr e ∗
          genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (Coins.coinsAfter img.base cur rest
              (decryptDraws C st msg.senderRatchetKey rest))) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        img.FrozenLoaded sf →
        sf.symtab = img.symtab →
        Q sf (P_f ∗ F_frame)) →
      (∀ (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmpty A img.base s0 s coroPtr outPtr
            (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (Coins.coinsAt img.base cur rest)) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        img.FrozenLoaded sf →
        sf.symtab = img.symtab →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
        (TokenInit img ∗
          genP3Pre A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr g b_2c0 ∗
          F_frame)
        Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0)

/-- Path A counterpart of `StageP3GenVRegsStmt` adding `Steps (tripleRatchetProgAtExt img.base ext) s s'`
and spatial CPS frame `(F_frame : SepProp)` to `hOk` so `FsAt` and Stage P4 caller resources
transport cleanly from `+0x1778` to `+0x34dc` (proved unconditionally in `Poll/StageP3Steps.lean`). -/
def StageP3GenStepsVRegsStmt : Prop :=
  ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem),
    AllocContracts img.base A ext →
    ChainClone3OkExt img.base A ext →
    SenderChainClone3OkExt img.base A ext →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (_root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img) →
    Obj.Loads libsignalSessionImage img →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      initErrsPtr ≠ 0#64 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st →
      st.receiverChains.length < 2 ^ 32 →
      st.pqRatchetState.length < 2 ^ 32 →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = closureEntry img ext + 0x1778#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      rootStack ≤ s.sp.toNat →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat →
        ptCap.toNat < 2 ^ 63 →
        ptPtr ≠ 0#64 →
        Steps (tripleRatchetProgAtExt img.base ext) s s' →
        s'.pc = closureEntry img ext + 0x34dc#64 →
        s'.status = .Running →
        s'.sp = s.sp →
        s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr →
        s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 →
        s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr →
        s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        img.FrozenLoaded s' →
        s'.symtab = img.symtab →
        (P_s' ⊢
          stageP3DispatchOkMid A img.base s0 s coroPtr outPtr initErrsPtr prevStatesPtr
            ptCap ptPtr pt b_2c0 G' (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (Coins.coinsAfter img.base cur rest
              (decryptDraws C st msg.senderRatchetKey rest))) →
        SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt false G' →
        (genP3S5Model C K rem loc msg rest st).1 = .error e →
        e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPost A img.base s0 s coroPtr outPtr prevStatesPtr e ∗
          genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (Coins.coinsAfter img.base cur rest
              (decryptDraws C st msg.senderRatchetKey rest))) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        img.FrozenLoaded sf →
        sf.symtab = img.symtab →
        Q sf (P_f ∗ F_frame)) →
      (∀ (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPost A img.base s0 s coroPtr outPtr prevStatesPtr
            (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (Coins.coinsAt img.base cur rest)) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        img.FrozenLoaded sf →
        sf.symtab = img.symtab →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
        (TokenInit img ∗
          genP3Pre A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0 ∗
          F_frame)
        Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0)

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
