/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ArmsB
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Bridges
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Folds
import LibsignalBinary.Proofs.E2E.Record.Serialization.Canon
import LibsignalBinary.Proofs.E2E.RecordX.Length
import LibsignalBinary.Proofs.E2E.RecordX.LengthP
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedMatchFold
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Agree
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1OkFold
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# CLI Poll Stage P2 Over-Path (`Path C`) Spatial and Encoding Folds

Provides the `+0x0868` entry spatial unpack (`stageP2_entry_unpack_pathCOver`), `+0x1778` `Prev1`
normal-exit spatial fold (`p2OverOkPost_fold_pathCOver`), 32-bit encoded-session length bound
(`encSessionMem_clearPending_lt_32`), stack-budget bound, and `subroutine_ok` ghost-struct transport
helpers.
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

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure (decryptPrekeySavedRegsAt)

/-- Stage P3 (`+0x1778`) extra precondition on the Over-path (`Prev1`), definitionally (`rfl`) equal
to `Over.stageP3Sub5ExtraPrePrev1` (`ClosureOver.lean`). -/
def p2StageP3Sub5ExtraPrePrev1 (A : RustAlloc) (s0 s : State)
    (coroPtr outPtr initErrsPtr prevCap prevPtr : BitVec 64)
    (enc : List (BitVec 8)) (b_2c0 : BitVec 8) : SepProp :=
  ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
  ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (s.sp + 0x448#64) 240 ∗
  OverP2.prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x370#64) 36 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0

namespace OverP2Inst

open Arm64.Process ProofLib.ObjectLoad ProofLib.ProgramReflection ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.KitInst

/-! ## 1. Generic `subroutine_ok` Ghost-Struct Transport -/

/-- Transport `subroutine_ok prog fn s1` along a ghost-type reindexing `f : β → α` when
`pre`, `post`, `onPanic`, `onExit`, and `onOom` agree point-for-point (`rfl` across nominal ghost structures). -/
theorem subroutine_ok_of_spec_map {α β : Type} {prog : Program} {fn : BitVec 64}
    {s1 : Spec α} {s2 : Spec β}
    (f : β → α)
    (hpre : ∀ (y : β) (st : State), s1.pre (f y) st = s2.pre y st)
    (hpost : ∀ (y : β) (s0 sf : State), s1.post (f y) s0 sf = s2.post y s0 sf)
    (hpan : ∀ (y : β) (s0 sf : State), s1.onPanic (f y) s0 sf = s2.onPanic y s0 sf)
    (hexit : ∀ (y : β) code (s0 sf : State), s1.onExit (f y) code s0 sf = s2.onExit y code s0 sf)
    (hoom : ∀ (y : β) (s0 sf : State), s1.onOom (f y) s0 sf = s2.onOom y s0 sf)
    (hok : subroutine_ok prog fn s1) :
    subroutine_ok prog fn s2 := by
  refine subroutine_ok_outcome_intro fun y R s0 hpc hrun hm halign => ?_
  rw [← hpre y s0] at hm
  refine hok.mono_outcome (f y) R s0 hpc hrun hm halign fun sf hout => ?_
  rcases hout with ⟨hret, hcs, hp⟩ | ⟨hpanst, hpanp⟩ | ⟨code, hexst, hexp⟩ | ⟨hoomst, hoomp⟩
  · rw [hpost y s0 sf] at hp
    exact Or.inl ⟨hret, hcs, hp⟩
  · rw [hpan y s0 sf] at hpanp
    exact Or.inr (Or.inl ⟨hpanst, hpanp⟩)
  · rw [hexit y code s0 sf] at hexp
    exact Or.inr (Or.inr (Or.inl ⟨code, hexst, hexp⟩))
  · rw [hoom y s0 sf] at hoomp
    exact Or.inr (Or.inr (Or.inr ⟨hoomst, hoomp⟩))

/-- `.inImage img` corollary of `subroutine_ok_of_spec_map`. -/
theorem subroutine_ok_inImage_of_spec_map {α β : Type} {prog : Program} {fn : BitVec 64}
    {img : Obj.Image} {s1 : Spec α} {s2 : Spec β}
    (f : β → α)
    (hpre : ∀ (y : β) (st : State), s1.pre (f y) st = s2.pre y st)
    (hpost : ∀ (y : β) (s0 sf : State), s1.post (f y) s0 sf = s2.post y s0 sf)
    (hpan : ∀ (y : β) (s0 sf : State), s1.onPanic (f y) s0 sf = s2.onPanic y s0 sf)
    (hexit : ∀ (y : β) code (s0 sf : State), s1.onExit (f y) code s0 sf = s2.onExit y code s0 sf)
    (hoom : ∀ (y : β) (s0 sf : State), s1.onOom (f y) s0 sf = s2.onOom y s0 sf)
    (hok : subroutine_ok prog fn (s1.inImage img)) :
    subroutine_ok prog fn (s2.inImage img) :=
  subroutine_ok_of_spec_map f
    (fun y st => by dsimp only [Spec.inImage]; rw [hpre y st])
    (fun y s0 sf => by dsimp only [Spec.inImage]; rw [hpost y s0 sf])
    (fun y s0 sf => by dsimp only [Spec.inImage]; rw [hpan y s0 sf])
    (fun y code s0 sf => by dsimp only [Spec.inImage]; rw [hexit y code s0 sf])
    (fun y s0 sf => by dsimp only [Spec.inImage]; rw [hoom y s0 sf])
    hok

/-! ## 2. Base-Key Mismatch, Canonicality, & 32-Bit Encoded-Session Length Bound -/

theorem p2Over_serBytes_len (m : PreKeyMessageFields) :
    (5#8 :: bytesToBv8 (mkPathAHdr m).ekAPk).length = 33 := by
  dsimp only [mkPathAHdr]
  rw [bytesToBv8_vecU8 m.baseKey]
  simp [m.baseKey.toList_length]

theorem p2Over_not_sessMatchesMsg (sess : Session (List (BitVec 8)))
    (pm : PreKeySignalMessage) (m : PreKeyMessageFields) (i : SignalMessage)
    (hpm : pm = pmOfE m i) (hnot : ¬ SessMatchesPm sess pm) :
    ¬ Over.P2SessMatchesMsg sess 4#8 (5#8 :: bytesToBv8 (mkPathAHdr m).ekAPk) := by
  intro ⟨hver, hbk⟩
  apply hnot
  subst hpm
  obtain ⟨hmver, _, _, _, hbase, _, _, _⟩ := pmOfE_fields m i
  refine ⟨?_, ?_⟩
  · rw [hmver]; exact hver
  · dsimp only [PublicKey.serialize]
    rw [hbase]
    dsimp only [mkPathAHdr] at hbk
    rw [bytesToBv8_vecU8 m.baseKey] at hbk
    exact hbk

theorem sessionAt_dup_canonSession (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (s : Session (List (BitVec 8))) :
    sessionStateReprAt A ss G s ⊢
      ⌜E2E.Record.Serialization.CanonSession G s⌝ ∗ sessionStateReprAt A ss G s :=
  ProofLib.Entails.extract_heap_fact (E2E.InMem.SessionStoreImpl.canonSession_of_sessionAt A ss G s)

theorem pathAMsgRemInnerAt_dup_kyberPtr (g : PreKeyMsgGhost) (msgA : BitVec 64)
    (m : PreKeyMessageFields) (i : SignalMessage) :
    pathAMsgRemInnerAt g msgA m i ⊢
      ⌜g.kyberPtr ≠ 0#64⌝ ∗ pathAMsgRemInnerAt g msgA m i := by
  unfold pathAMsgRemInnerAt
  refine Entails.pure_left fun h => ?_
  have hne : g.kyberPtr ≠ 0#64 := h.1
  exact Entails.pure_right hne (Entails.pure_right h (Entails.refl _))

theorem canonSession_clearPending {G : SessionGhost} {s : Session (List (BitVec 8))}
    (h : E2E.Record.Serialization.CanonSession G s) :
    E2E.Record.Serialization.CanonSession (OverP2.clearPendingGhost G) (OverP2.clearPending s) := by
  obtain ⟨hl, hr, hs, hlen, hc, _hp⟩ := h
  exact ⟨hl, hr, hs, hlen, hc, trivial⟩

theorem encSessionMem_clearPending_eq {G : SessionGhost} {s : Session (List (BitVec 8))}
    (h : E2E.Record.Serialization.CanonSession G s) :
    E2E.Record.Serialization.encSessionMem
      (OverP2.clearPendingGhost G) (OverP2.clearPending s) =
      E2E.Record.encSession (OverP2.clearPending s) :=
  E2E.Record.Serialization.encSessionMem_eq_of_canon _ _ (canonSession_clearPending h)

theorem encSessionMem_clearPending_lt_32 {r : SessionRecord (List (BitVec 8))}
    {G : SessionGhost} {s : Session (List (BitVec 8))}
    (hIn : Slots.scopeIn r) (hcur : r.currentSession = some s)
    (hcanon : E2E.Record.Serialization.CanonSession G s) :
    (E2E.Record.Serialization.encSessionMem
      (OverP2.clearPendingGhost G) (OverP2.clearPending s)).length < 2 ^ 32 := by
  rw [encSessionMem_clearPending_eq hcanon]
  rcases r with ⟨curOpt⟩
  dsimp only at hcur
  subst hcur
  rcases hIn with ⟨⟨hin, hpq, hrepr⟩, s', hs', hss⟩
  injection hs' with hs_eq; subst hs_eq
  have hb_strip : E2E.RecordX.DeserializeScopeBounded
      ⟨some (Slots.PqValid.stripPq (OverP2.clearPending s))⟩ := by
    apply E2E.RecordX.deserializeScopeBounded_of_deserializeScopeP
    refine ⟨⟨?_, ?_, ?_⟩, Slots.PqValid.stripPq (OverP2.clearPending s), rfl, ?_⟩
    · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq
      have hin0 := hin s rfl
      exact ⟨hin0.1, hin0.2.1, fun k hk => by simp [OverP2.clearPending, Slots.PqValid.stripPq] at hk⟩
    · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq; rfl
    · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq
      obtain ⟨hr1, hr2, _hwf, hr4⟩ := hrepr s rfl
      exact ⟨hr1, hr2, rfl, hr4⟩
    · exact ⟨hss.1, fun p hp => by simp [OverP2.clearPending, Slots.PqValid.stripPq] at hp,
        fun k hk => by simp [OverP2.clearPending, Slots.PqValid.stripPq] at hk, hss.2.2.2⟩
  have h21 :
      (E2E.Record.encodeRecord
        ⟨some (Slots.PqValid.stripPq (OverP2.clearPending s))⟩).length < 2 ^ 21 :=
    E2E.RecordX.encodeRecord_length_lt_21_of_bounded hb_strip
  have hge :
      (E2E.Record.encSession
        (Slots.PqValid.stripPq (OverP2.clearPending s))).length ≤
        (E2E.Record.encodeRecord
          ⟨some (Slots.PqValid.stripPq (OverP2.clearPending s))⟩).length := by
    unfold E2E.Record.encodeRecord E2E.Record.msgField
    dsimp only [Option.map_some]
    exact E2E.RecordX.lenField_length_ge' 1
      (E2E.Record.encSession (Slots.PqValid.stripPq (OverP2.clearPending s)))
  have heq :
      (E2E.Record.encSession (OverP2.clearPending s)).length =
        (E2E.Record.encSession
          (Slots.PqValid.stripPq (OverP2.clearPending s))).length +
          (E2E.Record.bytesField 15
            (OverP2.clearPending s).state.pqRatchetState).length := by
    simp only [E2E.Record.encSession, Slots.PqValid.stripPq,
      show (E2E.Record.bytesField 15 []).length = 0 from rfl,
      List.length_append]
    omega
  have hb15 :
      (E2E.Record.bytesField 15
        (OverP2.clearPending s).state.pqRatchetState).length ≤
        (OverP2.clearPending s).state.pqRatchetState.length + 20 :=
    E2E.RecordX.bytesField_length_le' 15 (OverP2.clearPending s).state.pqRatchetState
  have hpq31 : (OverP2.clearPending s).state.pqRatchetState.length < 2 ^ 31 :=
    (hpq s rfl).2
  omega

/-! ## 3. Stack Budget Bound for `stageP2OverV1CallStack` -/

theorem stageP2OverV1CallStack_le_subStack {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey) (B : RunBudgets) :
    Over.stageP2OverV1CallStack
      (cliPollSpkKit A b F0 spkId (cliKitStk B))
      (cliPollKpkKit A b F0 kpkId spkId kbk (cliKitStk B))
      (cliPollPkKit A b F0 opkIdWord (cliKitStk B))
      (cliPollSelfKit A b F0 peer (cliKitStk B)) ≤ dpClosSubStack B := by
  have hv1 := stageP2V1CallStack_le_subStack (A := A) b F0 peer spkId kpkId opkIdWord kbk B
  have hoverPure : Over.stageP2OverPureAndErrStack ≤ dpClosSubStack B := by
    have h0 : Over.stageP2OverPureAndErrStack ≤ 1048576 - 3280 := by decide
    exact Nat.le_trans h0 (Nat.le_add_right _ _)
  exact Nat.max_le.mpr ⟨hv1, hoverPure⟩

/-! ## 4. Spatial Entry Unpack & `+0x1778` Success-Exit Fold (`Path C` Over) -/

private theorem pull_pure_after1 {A1 Rest : SepProp} {φ : Prop} :
    A1 ∗ (⌜φ⌝ ∗ Rest) = ⌜φ⌝ ∗ (A1 ∗ Rest) := by
  ac_rfl

private theorem pull_pure_msg_group {M1 M2 M3 Tail : SepProp} {φ : Prop} :
    (M1 ∗ M2 ∗ (⌜φ⌝ ∗ M3)) ∗ Tail = ⌜φ⌝ ∗ ((M1 ∗ M2 ∗ M3) ∗ Tail) := by
  ac_rfl

private theorem pull_pure_after7 {A1 A2 A3 A4 A5 A6 A7 Rest : SepProp} {φ : Prop} :
    A1 ∗ (A2 ∗ (A3 ∗ (A4 ∗ (A5 ∗ (A6 ∗ (A7 ∗ (⌜φ⌝ ∗ Rest))))))) =
      ⌜φ⌝ ∗ (A1 ∗ (A2 ∗ (A3 ∗ (A4 ∗ (A5 ∗ (A6 ∗ (A7 ∗ Rest))))))) := by
  ac_rfl

/-- Entry spatial unpack from `StageP2PathCOverQpanCliStmt` into `Over.stageP2OverPreAt ... pathAInnerFrame`. -/
theorem stageP2_entry_unpack_pathCOver {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (img : Obj.Image) (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (m : PreKeyMessageFields) (i : SignalMessage) (s0 : State)
    (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (hcur : r.currentSession = some sess)
    (hmsg : y.g.msg = pmOfE m i) (hfp : fp = sp + 0xc70#64)
    (hdec0 : DecPkOk₀ ⟨W.C, W.Q⟩ (fun _ => False) y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hFok : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hScope : ∀ r', Scope r' → Slots.scopeIn r') :
    stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
      (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
      (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 y.fut (some r) ∗
    preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
    protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
    coinsInstalled img y.g.coinsP y.g.coins ∗
    storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
    TokenInit img ∗
    logOff img ∗
    stackAt sp (dpClosSubStack B) ⊢
      ∃∗ g : RecordGhost, ∃∗ recG : SessionGhost, ∃∗ w : PathAEntryWords,
        ⌜Slots.scopeKit r ∧ g.cur = some recG ∧
         E2E.Record.Serialization.CanonSession recG sess ∧
         y.g.msgG.kyberPtr ≠ 0#64 ∧
         (∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)⌝ ∗
        Over.stageP2OverPreAt E2E.HooksE.A0 img
          (cliPollSpkKit E2E.HooksE.A0 img.base y.g.F m.spkId (cliKitStk B))
          (cliPollKpkKit E2E.HooksE.A0 img.base y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
          (cliPollPkKit E2E.HooksE.A0 img.base y.g.F w.opkWord (cliKitStk B))
          (cliPollIdKit E2E.HooksE.A0 img.base y.g.F y.g.peer (cliKitStk B))
          s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
          y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
          y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
          (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
          w.opkWord m.kpkId m.regId m.spkId
          StoresGhost.opened.signed StoresGhost.opened.kyber
          StoresGhost.opened.oneTime StoresGhost.opened.identity
          y.g.me y.g.peer g recG sess (dpClosSubStack B)
          (pathAInnerFrame img y m i rngPtr sp) := by
  rw [hmsg]
  rw [sepConj_comm (stageP2PostP1At _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _, ← sepConj_assoc]
  dsimp only [p1LoadedRecordAt]
  simp only [sepConj_assoc]
  refine Entails.pure_left fun hkit => ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun g => ?_
  refine Entails.trans
    (sepConj_mono_left (sessionRecordAt_some_eq_prev_sess E2E.HooksE.A0 y.fut g r sess hcur)) ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun recG => ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hgcur => ?_
  rw [sepConj_assoc]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left
      (sessionAt_dup_canonSession E2E.HooksE.A0 (y.fut + 0xf8#64) recG sess))) ?_
  simp only [sepConj_assoc]
  rw [pull_pure_after1]
  refine Entails.pure_left fun hcanon => ?_
  dsimp only [stageP2PostP1At]
  rw [coroCopyAt_eq_head3_tail11, processPrekeyInnerInitAt_eq_330_388_rem23]
  refine Entails.trans (show _ ⊢
    preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA (pmOfE m i) ∗
    (cells (y.fut + 0x398#64) 2 ∗ memRegion (y.fut + 0x250#64) 48 ∗ coroUnusedP1At y.fut) ∗
    closStackUnusedP1OkAt sp ∗
    storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
    (Poll.prevSessionsEmptyAt E2E.HooksE.A0 y.fut g ∗
      sessionStateReprAt E2E.HooksE.A0 (y.fut + 0xf8#64) recG sess ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
      ((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 0x80#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) ∗
      ((y.fut + 0x390#64) ↦₈ 0#8) ∗ ((y.fut + 0x4f2#64) ↦₈ 0#8) ∗
      (sp ↦₆₄ 0#64) ∗
      ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ v_a8) ∗ ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗
      ((sp + 0xb8#64) ↦₆₄ v_b8) ∗ ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
      memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x3e0#64) 368 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ memRegion y.out 48 ∗ E2E.HooksE.A0.pool ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      coinsInstalled img y.g.coinsP y.g.coins ∗
      TokenInit img ∗ logOff img ∗ stackAt sp (dpClosSubStack B)) by sep_frame) ?_
  refine Entails.trans (sepConj_mono (preKeyMsgAt_unpack_pathA y.g.msgG y.g.msgA m i)
    (sepConj_mono (coro_unused_split_p2v1 y.fut)
      (sepConj_mono_left (stack_unused_split_p2v1 sp fp hfp)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun u80 => Entails.sepExists_elim fun u88 =>
    Entails.sepExists_elim fun u90 => Entails.sepExists_elim fun u488 =>
    Entails.sepExists_elim fun b4b0 => Entails.sepExists_elim fun b4f1 =>
    Entails.sepExists_elim fun opkWord => ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hopkWord => ?_
  refine Entails.trans
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (pathAMsgRemInnerAt_dup_kyberPtr y.g.msgG y.g.msgA m i)))) ?_
  rw [pull_pure_msg_group]
  refine Entails.pure_left fun hctBuf_nz => ?_
  have hdec0' : DecPkOk₀ ⟨W.C, W.Q⟩ (fun _ => False) y.g.F y.g.peer.val y.g.me.val (pmOfE m i) :=
    hmsg ▸ hdec0
  have hstores := storesAt_entails_cliPollStoresKitsAt (A := E2E.HooksE.A0) img.base
    (cliKitStk B) y.g.stores StoresGhost.opened
    (cliSessInv_opened_scopeKit hScope hFok)
    (cliIdOwnInv_opened hdec0')
    (cliIdInv_opened_peer hFok)
    (cliPkInv_opened hdec0' opkWord)
    (cliSpkInv_opened hdec0' m.spkId)
    (cliKpkInvFull_opened hdec0' m.kpkId m.spkId (pmOfE m i).baseKey)
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstores)))) ?_
  have hprevEq :
      Poll.prevSessionsEmptyAt E2E.HooksE.A0 y.fut g =
        Matched.prevSessionsEmptyAt E2E.HooksE.A0 y.fut g := rfl
  refine Entails.sepExists_right g
    (Entails.sepExists_right recG
      (Entails.sepExists_right ⟨opkWord, u488, u80, u88, u90, b4b0, b4f1⟩
        (Entails.pure_right ⟨hkit, hgcur, hcanon, hctBuf_nz, hopkWord⟩ ?_)))
  exact Entails.of_eq (by
    dsimp only [cliPollStoresKitsAt, Over.stageP2OverPreAt, pathAInnerFrame]
    rw [hprevEq]
    ac_rfl)

set_option maxHeartbeats 800000 in
/-- Full Stage P2 Over-path (`Path C`) `+0x1778` normal-exit spatial fold into `hok`'s precondition
(`genP3Pre ∗ p2StageP3Sub5ExtraPrePrev1 ∗ stageP3CoroFrameAt ∗ stageP3StackFrameAt ∗ ...`). -/
theorem p2OverOkPost_fold_pathCOver {B : RunBudgets} {S : RunSem}
    (img : Obj.Image) (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 s2 : State) (sp fp rngPtr : BitVec 64)
    (recG G_bob : SessionGhost) (sess : Session (List (BitVec 8)))
    (st_bob : SessionState (List (BitVec 8)))
    (hcanon : E2E.Record.Serialization.CanonSession recG sess)
    (hmsg : y.g.msg = pmOfE m i)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (hsub : dpClosSubStack B ≤ sp.toNat)
    (hfp : fp = sp + 0xc70#64)
    (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)
    (hsp2 : s2.sp = sp) (hx19_2 : s2.readReg64 .x19 = y.fut)
    (hx27_2 : s2.readReg64 .x27 = sp + 0x370#64) :
    Over.p2OverOkPostAt E2E.HooksE.A0 img
      (cliPollSpkKit E2E.HooksE.A0 img.base y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKit E2E.HooksE.A0 img.base y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKit E2E.HooksE.A0 img.base y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKit E2E.HooksE.A0 img.base y.g.F y.g.peer (cliKitStk B))
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) recG sess G_bob st_bob
      (mkPathAHdr m) i.messageVersion 0#8 w.opkWord m.kpkId m.regId m.spkId
      StoresGhost.opened.signed StoresGhost.opened.kyber
      StoresGhost.opened.oneTime StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFrame img y m i rngPtr sp) ⊢
      ∃∗ prevCap' : BitVec 64, ∃∗ prevPtr' : BitVec 64,
        ⌜prevCap' ≠ 0#64⌝ ∗
        TokenInit img ∗
        genP3Pre E2E.HooksE.A0 img s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
          y.g.msgA y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
          G_bob st_bob y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
        p2StageP3Sub5ExtraPrePrev1 E2E.HooksE.A0 s0 s2 y.fut y.out 8#64 prevCap' prevPtr'
          (E2E.Record.encSession (OverP2.clearPending sess)) 0#8 ∗
        stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
          (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
          (y.g.stores + 0x78#64) (kyberVt img) rngPtr
          (coroOpkIdAtP4 y.fut m.opkId)
          (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
           ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
        stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRemBaseIdKeyAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
        storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
        memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) := by
  rw [hmsg]
  have hmsg_inner : (pmOfE m i).message = i := (pmOfE_fields m i).2.2.2.2.2.2.1
  rw [hmsg_inner]
  dsimp only [Over.p2OverOkPostAt, Over.prevArchived1At, pathAInnerFrame]
  rw [encSessionMem_clearPending_eq hcanon]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun prevCap' => Entails.sepExists_elim fun prevPtr' => ?_
  simp only [sepConj_assoc]
  rw [pull_pure_after7]
  refine Entails.pure_left fun hcap_ne => ?_
  refine Entails.sepExists_right prevCap' (Entails.sepExists_right prevPtr'
    (Entails.pure_right hcap_ne ?_))
  unfold genP3Pre
  rw [hsp2]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left
      (Entails.pure_right ⟨rfl, hx19_2, hx27_2, rfl⟩ (Entails.refl _))))
  unfold genP3CallFrame p2StageP3Sub5ExtraPrePrev1
  have hkpk_or : (m.kpkId.zeroExtend 64 <<< 32) ||| 1#64 = m.kpkId ++ 1#32 := by bv_bits
  rw [hsp2, hdrOpkIdBv?_mkPathAHdr m, hkpk_or]
  have hstkSub : stackAt sp (dpClosSubStack B) =
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
      (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - FromRecordChainClone.chainCloneStack) ∗
        stackAt sp FromRecordChainClone.chainCloneStack) := by
    rw [P3P4.stackAt_sub_eq sp (dpClosSubStack B) rootStack
          (by unfold rootStack dpClosSubStack; omega)
          (Nat.le_trans hsub (Nat.le_of_lt sp.isLt)),
        stackAt_root_eq_chainClone sp]
  have h270 : memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x279#64) 39 =
      memRegion (sp + 0x270#64) 48 := by
    rw [memRegion_split (sp + 0x270#64) 9 39 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h3e0 : memRegion (sp + 0x3e0#64) 368 =
      memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x402#64) 70 ∗
      memRegion (sp + 0x448#64) 240 ∗ memRegion (sp + 0x538#64) 24 := by
    rw [sp_3e0_368_eq_344_24 sp, sp_3e0_344_eq_104_240 sp,
        memRegion_split (sp + 0x3e0#64) 34 70 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    ac_rfl
  have h550 :
      cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗
      cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
      memRegion (sp + 0xa90#64) 288 ∗ memRegion (fp + 0xffffffffffffff80#64) 9 ∗
      sp550P2V1RemAt sp =
      memRegion (sp + 0x550#64) 976 ∗ memRegion (sp + 0x920#64) 6 ∗ memRegion (sp + 0x926#64) 10 ∗
      memRegion (sp + 0x930#64) 96 ∗ memRegion (sp + 0x990#64) 256 ∗
      memRegion (sp + 0xa90#64) 48 ∗ memRegion (sp + 0xac0#64) 296 ∗ memRegion (sp + 0xbe8#64) 136 := by
    rw [← sp_550_1824_split_p2v1 sp fp hfp, sp_550_1824_split_genP3 sp]
    unfold spHighGapsAt
    rw [memRegion_split (sp + 0xa90#64) 48 296 (by decide),
        memRegion_split (sp + 0x550#64) 976 16 (by decide),
        memRegion_split (sp + 0x550#64 + 976#64) 6 10 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    ac_rfl
  have hopkSlot := p2_coro_opk_slot_fold y.fut m.opkId w.opkWord hopk
  have hcoro := p2_coro_ok_fold y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
    (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
    (y.g.stores + 0x78#64) (kyberVt img) rngPtr
    (coroOpkIdAtP4 y.fut m.opkId)
    (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId))
  have hstk := stack_match_fold sp y.fut y.g.msgA y.g.peerA (m.spkId.zeroExtend 64)
  have hc := coinsInstalled_to_coinsAt img y.g.coinsP y.g.coins hcoins
  have hstores := cliPollStoresKitsAt_entails_storesAt (A := E2E.HooksE.A0) img.base
    (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
    (pid := w.opkWord) (sid := m.spkId) (kid := m.kpkId) (kbk := (pmOfE m i).baseKey)
    (cliKitStk B) y.g.stores StoresGhost.opened
  dsimp only [cliPollStoresKitsAt] at hstores
  have hmsgSlices := p2MsgFields_reassemble_slices y.g.msgG y.g.msgA m i w.opkWord hopk
  rw [hmsg_inner] at hmsgSlices
  rw [hstkSub, h3e0]
  refine Entails.trans (show _ ⊢
    coinsInstalled img y.g.coinsP y.g.coins ∗
    (((y.fut + 0x298#64) ↦₆₄ ((opkOptTag32 m.opkId).zeroExtend 64 ||| (w.opkWord.zeroExtend 64 <<< 32))) ∗
      processPrekeyActive10At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x78#64) (kyberVt img) ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
      ((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 0x80#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
      cells (y.fut + 0x250#64) 6 ∗ memRegion (y.fut + 0x280#64) 24 ∗
      (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12 ∗
      ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) ∗
      ((y.fut + 0x390#64) ↦₈ 1#8) ∗ memRegion (y.fut + 0x398#64) 96 ∗
      ((y.fut + 0x4f1#64) ↦₈ 0#8) ∗ ((y.fut + 0x4f2#64) ↦₈ 1#8) ∗
      memRegion (y.fut + 0x2c1#64) 7 ∗ memRegion (y.fut + 0x391#64) 7 ∗
      memRegion (y.fut + 0x488#64) 8 ∗ memRegion (y.fut + 0x4b0#64) 65 ∗
      memRegion (y.fut + 0x4f3#64) 5 ∗
      p2CoroScratchTailAt y.fut ∗ memRegion (y.fut + 0x782#64) 6) ∗
    ((cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗
        cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
        memRegion (sp + 0xa90#64) 288 ∗ memRegion (fp + 0xffffffffffffff80#64) 9 ∗
        sp550P2V1RemAt sp) ∗
      (sp ↦₆₄ 0#64) ∗ memRegion (sp + 0x8#64) 120 ∗
      ((sp + 0x90#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ y.g.peerA) ∗
      memRegion (sp + 0xbc#64) 4 ∗
      ((sp + 0xd0#64) ↦₆₄ m.spkId.zeroExtend 64) ∗
      memRegion (sp + 0xd8#64) 348 ∗
      memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
      memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
      spMidGapsAt sp ∗
      ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗
      ((sp + 0x3b8#64) ↦₆₄ y.g.msgA) ∗
      ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗
      memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x402#64) 70 ∗
      memRegion (sp + 0x538#64) 24) ∗
    ((cliPollSessKit E2E.HooksE.A0 img.base y.g.F Slots.scopeKit y.g.peer (cliKitStk B)).storeAt
        (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      (cliPollIdKit E2E.HooksE.A0 img.base y.g.F y.g.peer (cliKitStk B)).identityAt
        y.g.stores StoresGhost.opened.identity ∗
      (cliPollPkKit E2E.HooksE.A0 img.base y.g.F w.opkWord (cliKitStk B)).storeAt
        (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      (cliPollSpkKit E2E.HooksE.A0 img.base y.g.F m.spkId (cliKitStk B)).storeAt
        (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      (cliPollKpkKit E2E.HooksE.A0 img.base y.g.F m.kpkId m.spkId (pmOfE m i).baseKey (cliKitStk B)).storeAt
        (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub) ∗
    (p2MsgFieldsAt y.g.msgA y.g.msgG.kyberPtr (mkPathAHdr m) i.messageVersion
        w.opkWord m.kpkId m.regId m.spkId ∗
      signalMessageRestVerAt E2E.HooksE.A0 y.g.msgG.msg y.g.msgA i ∗
      pathAMsgRemInnerAt y.g.msgG y.g.msgA m i) ∗
    ((memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x279#64) 39) ∗
      TokenInit img ∗
      sessionStateAt E2E.HooksE.A0 (y.fut + 0xf8#64) G_bob st_bob ∗
      E2E.HooksE.A0.pool ∗
      stackAt sp FromRecordChainClone.chainCloneStack ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
      ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗
      ((sp + 0xb0#64) ↦₆₄ y.g.msgA) ∗
      ((sp + 0xb8#64) ↦₃₂ i.messageVersion.zeroExtend 32) ∗
      ((sp + 0x3a0#64) ↦₆₄ y.g.peerA) ∗
      ((sp + 0x3ac#64) ↦₈ 3#8) ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      logOff img ∗
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - FromRecordChainClone.chainCloneStack) ∗
      ((sp + 0x80#64) ↦₆₄ (y.fut + 0xf8#64)) ∗
      ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗
      ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
      ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗
      ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
      memRegion (sp + 0x448#64) 240 ∗
      OverP2.prevVecAt E2E.HooksE.A0 (y.fut + 0xe0#64) prevCap' prevPtr'
        [E2E.Record.encSession (OverP2.clearPending sess)] ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      memRegion y.out 48 ∗
      memRegion (sp + 0x250#64) 20 ∗
      memRegion (sp + 0x370#64) 36 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
    by sep_frame) ?_
  have hcoro' :
      ((y.fut + 0x298#64) ↦₆₄ ((opkOptTag32 m.opkId).zeroExtend 64 ||| (w.opkWord.zeroExtend 64 <<< 32))) ∗
      processPrekeyActive10At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x78#64) (kyberVt img) ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
      ((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 0x80#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
      cells (y.fut + 0x250#64) 6 ∗ memRegion (y.fut + 0x280#64) 24 ∗
      (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12 ∗
      ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) ∗
      ((y.fut + 0x390#64) ↦₈ 1#8) ∗ memRegion (y.fut + 0x398#64) 96 ∗
      ((y.fut + 0x4f1#64) ↦₈ 0#8) ∗ ((y.fut + 0x4f2#64) ↦₈ 1#8) ∗
      memRegion (y.fut + 0x2c1#64) 7 ∗ memRegion (y.fut + 0x391#64) 7 ∗
      memRegion (y.fut + 0x488#64) 8 ∗ memRegion (y.fut + 0x4b0#64) 65 ∗
      memRegion (y.fut + 0x4f3#64) 5 ∗
      p2CoroScratchTailAt y.fut ∗ memRegion (y.fut + 0x782#64) 6 ⊢
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr
        (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) := by
    refine Entails.trans (sepConj_mono_left hopkSlot) ?_
    exact Entails.trans (by sep_frame) hcoro
  have hstk' :
      (cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗
        cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
        memRegion (sp + 0xa90#64) 288 ∗ memRegion (fp + 0xffffffffffffff80#64) 9 ∗
        sp550P2V1RemAt sp) ∗
      (sp ↦₆₄ 0#64) ∗ memRegion (sp + 0x8#64) 120 ∗
      ((sp + 0x90#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ y.g.peerA) ∗
      memRegion (sp + 0xbc#64) 4 ∗
      ((sp + 0xd0#64) ↦₆₄ m.spkId.zeroExtend 64) ∗
      memRegion (sp + 0xd8#64) 348 ∗
      memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
      memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
      spMidGapsAt sp ∗
      ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗
      ((sp + 0x3b8#64) ↦₆₄ y.g.msgA) ∗
      ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗
      memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x402#64) 70 ∗
      memRegion (sp + 0x538#64) 24 ⊢
      genP3SpillAll sp ∗ memRegion (sp + 0x3e0#64) 104 ∗
      memRegion (sp + 0xa90#64) 344 ∗
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA := by
    rw [h550]
    exact Entails.trans (by sep_frame) hstk
  rw [h270]
  refine Entails.trans (sepConj_mono hc (sepConj_mono hcoro'
    (sepConj_mono hstk' (sepConj_mono hstores (sepConj_mono_left hmsgSlices))))) ?_
  sep_frame

/-! ## 5. `(P : PEParams) (A : RustAlloc)` Generalizations -/

/-- `(P : PEParams) (A : RustAlloc)` generalization of `stageP2_entry_unpack_pathCOver` into
`Over.stageP2OverPreAt A ... (pathAInnerFrameExt img y m i rngPtr sp)`. -/
theorem stageP2_entry_unpack_pathCOver_ext {P : PEParams} {A : RustAlloc}
    {B : RunBudgets} {S : RunSem}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (img : Obj.Image) (y : DpPollGhostState (dpSlotPollKState A img B S))
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (m : PreKeyMessageFields) (i : SignalMessage) (s0 : State)
    (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (hcur : r.currentSession = some sess)
    (hmsg : y.g.msg = pmOfE m i) (hfp : fp = sp + 0xc70#64)
    (hdec0 : DecPkOk₀ P (fun _ => False) y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hFok : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hScope : ∀ r', Scope r' → Slots.scopeIn r') :
    stageP2PostP1At A y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
      (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
      (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt Slots.scopeKit A y.fut (some r) ∗
    preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt A y.g.peer y.g.peerA ∗
    protocolAddressAt A y.g.me y.g.meA ∗
    coinsInstalled img y.g.coinsP y.g.coins ∗
    storesAt A y.g.stores StoresGhost.opened ∗
    TokenInit img ∗
    logOff img ∗
    stackAt sp (dpClosSubStack B) ⊢
      ∃∗ g : RecordGhost, ∃∗ recG : SessionGhost, ∃∗ w : PathAEntryWords,
        ⌜Slots.scopeKit r ∧ g.cur = some recG ∧
         E2E.Record.Serialization.CanonSession recG sess ∧
         y.g.msgG.kyberPtr ≠ 0#64 ∧
         (∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)⌝ ∗
        Over.stageP2OverPreAt A img
          (cliPollSpkKit A img.base y.g.F m.spkId (cliKitStk B))
          (cliPollKpkKit A img.base y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
          (cliPollPkKit A img.base y.g.F w.opkWord (cliKitStk B))
          (cliPollIdKit A img.base y.g.F y.g.peer (cliKitStk B))
          s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
          y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
          y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
          (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
          w.opkWord m.kpkId m.regId m.spkId
          StoresGhost.opened.signed StoresGhost.opened.kyber
          StoresGhost.opened.oneTime StoresGhost.opened.identity
          y.g.me y.g.peer g recG sess (dpClosSubStack B)
          (pathAInnerFrameExt img y m i rngPtr sp) := by
  rw [hmsg]
  rw [sepConj_comm (stageP2PostP1At _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _, ← sepConj_assoc]
  dsimp only [p1LoadedRecordAt]
  simp only [sepConj_assoc]
  refine Entails.pure_left fun hkit => ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun g => ?_
  refine Entails.trans
    (sepConj_mono_left (sessionRecordAt_some_eq_prev_sess A y.fut g r sess hcur)) ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun recG => ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hgcur => ?_
  rw [sepConj_assoc]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left
      (sessionAt_dup_canonSession A (y.fut + 0xf8#64) recG sess))) ?_
  simp only [sepConj_assoc]
  rw [pull_pure_after1]
  refine Entails.pure_left fun hcanon => ?_
  dsimp only [stageP2PostP1At]
  rw [coroCopyAt_eq_head3_tail11, processPrekeyInnerInitAt_eq_330_388_rem23]
  refine Entails.trans (show _ ⊢
    preKeyMsgAt A y.g.msgG y.g.msgA (pmOfE m i) ∗
    (cells (y.fut + 0x398#64) 2 ∗ memRegion (y.fut + 0x250#64) 48 ∗ coroUnusedP1At y.fut) ∗
    closStackUnusedP1OkAt sp ∗
    storesAt A y.g.stores StoresGhost.opened ∗
    (Poll.prevSessionsEmptyAt A y.fut g ∗
      sessionStateReprAt A (y.fut + 0xf8#64) recG sess ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
      ((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 0x80#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) ∗
      ((y.fut + 0x390#64) ↦₈ 0#8) ∗ ((y.fut + 0x4f2#64) ↦₈ 0#8) ∗
      (sp ↦₆₄ 0#64) ∗
      ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ v_a8) ∗ ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗
      ((sp + 0xb8#64) ↦₆₄ v_b8) ∗ ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
      memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x3e0#64) 368 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ memRegion y.out 48 ∗ A.pool ∗
      protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗
      coinsInstalled img y.g.coinsP y.g.coins ∗
      TokenInit img ∗ logOff img ∗ stackAt sp (dpClosSubStack B)) by sep_frame) ?_
  refine Entails.trans (sepConj_mono (preKeyMsgAt_unpack_pathA_ext A y.g.msgG y.g.msgA m i)
    (sepConj_mono (coro_unused_split_p2v1 y.fut)
      (sepConj_mono_left (stack_unused_split_p2v1 sp fp hfp)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun u80 => Entails.sepExists_elim fun u88 =>
    Entails.sepExists_elim fun u90 => Entails.sepExists_elim fun u488 =>
    Entails.sepExists_elim fun b4b0 => Entails.sepExists_elim fun b4f1 =>
    Entails.sepExists_elim fun opkWord => ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hopkWord => ?_
  refine Entails.trans
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (pathAMsgRemInnerAt_dup_kyberPtr_ext A y.g.msgG y.g.msgA m i)))) ?_
  rw [pull_pure_msg_group]
  refine Entails.pure_left fun hctBuf_nz => ?_
  have hdec0' : DecPkOk₀ P (fun _ => False) y.g.F y.g.peer.val y.g.me.val (pmOfE m i) :=
    hmsg ▸ hdec0
  have hstores := storesAt_entails_cliPollStoresKitsAt (A := A) img.base
    (cliKitStk B) y.g.stores StoresGhost.opened
    (cliSessInv_opened_scopeKit hScope hFok)
    (cliIdOwnInv_opened hdec0')
    (cliIdInv_opened_peer hFok)
    (cliPkInv_opened hdec0' opkWord)
    (cliSpkInv_opened hdec0' m.spkId)
    (cliKpkInvFull_opened hdec0' m.kpkId m.spkId (pmOfE m i).baseKey)
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstores)))) ?_
  have hprevEq :
      Poll.prevSessionsEmptyAt A y.fut g =
        Matched.prevSessionsEmptyAt A y.fut g := rfl
  refine Entails.sepExists_right g
    (Entails.sepExists_right recG
      (Entails.sepExists_right ⟨opkWord, u488, u80, u88, u90, b4b0, b4f1⟩
        (Entails.pure_right ⟨hkit, hgcur, hcanon, hctBuf_nz, hopkWord⟩ ?_)))
  exact Entails.of_eq (by
    dsimp only [cliPollStoresKitsAt, Over.stageP2OverPreAt, pathAInnerFrameExt]
    rw [hprevEq]
    ac_rfl)

set_option maxHeartbeats 800000 in
/-- `(A : RustAlloc)` generalization of `p2OverOkPost_fold_pathCOver`. -/
theorem p2OverOkPost_fold_pathCOver_ext {A : RustAlloc} {B : RunBudgets} {S : RunSem}
    (img : Obj.Image) (y : DpPollGhostState (dpSlotPollKState A img B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 s2 : State) (sp fp rngPtr : BitVec 64)
    (recG G_bob : SessionGhost) (sess : Session (List (BitVec 8)))
    (st_bob : SessionState (List (BitVec 8)))
    (hcanon : E2E.Record.Serialization.CanonSession recG sess)
    (hmsg : y.g.msg = pmOfE m i)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (hsub : dpClosSubStack B ≤ sp.toNat)
    (hfp : fp = sp + 0xc70#64)
    (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)
    (hsp2 : s2.sp = sp) (hx19_2 : s2.readReg64 .x19 = y.fut)
    (hx27_2 : s2.readReg64 .x27 = sp + 0x370#64) :
    Over.p2OverOkPostAt A img
      (cliPollSpkKit A img.base y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKit A img.base y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKit A img.base y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKit A img.base y.g.F y.g.peer (cliKitStk B))
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) recG sess G_bob st_bob
      (mkPathAHdr m) i.messageVersion 0#8 w.opkWord m.kpkId m.regId m.spkId
      StoresGhost.opened.signed StoresGhost.opened.kyber
      StoresGhost.opened.oneTime StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFrameExt img y m i rngPtr sp) ⊢
      ∃∗ prevCap' : BitVec 64, ∃∗ prevPtr' : BitVec 64,
        ⌜prevCap' ≠ 0#64⌝ ∗
        TokenInit img ∗
        genP3Pre A img s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
          y.g.msgA y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
          G_bob st_bob y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
        p2StageP3Sub5ExtraPrePrev1 A s0 s2 y.fut y.out 8#64 prevCap' prevPtr'
          (E2E.Record.encSession (OverP2.clearPending sess)) 0#8 ∗
        stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
          (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
          (y.g.stores + 0x78#64) (kyberVt img) rngPtr
          (coroOpkIdAtP4 y.fut m.opkId)
          (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
           ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
        stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRemBaseIdKeyAt A y.g.msgG y.g.msgA y.g.msg ∗
        storesAt A y.g.stores StoresGhost.opened ∗
        memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) := by
  rw [hmsg]
  have hmsg_inner : (pmOfE m i).message = i := (pmOfE_fields m i).2.2.2.2.2.2.1
  rw [hmsg_inner]
  dsimp only [Over.p2OverOkPostAt, Over.prevArchived1At, pathAInnerFrameExt]
  rw [encSessionMem_clearPending_eq hcanon]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun prevCap' => Entails.sepExists_elim fun prevPtr' => ?_
  simp only [sepConj_assoc]
  rw [pull_pure_after7]
  refine Entails.pure_left fun hcap_ne => ?_
  refine Entails.sepExists_right prevCap' (Entails.sepExists_right prevPtr'
    (Entails.pure_right hcap_ne ?_))
  unfold genP3Pre
  rw [hsp2]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left
      (Entails.pure_right ⟨rfl, hx19_2, hx27_2, rfl⟩ (Entails.refl _))))
  unfold genP3CallFrame p2StageP3Sub5ExtraPrePrev1
  have hkpk_or : (m.kpkId.zeroExtend 64 <<< 32) ||| 1#64 = m.kpkId ++ 1#32 := by bv_bits
  rw [hsp2, hdrOpkIdBv?_mkPathAHdr m, hkpk_or]
  have hstkSub : stackAt sp (dpClosSubStack B) =
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
      (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - FromRecordChainClone.chainCloneStack) ∗
        stackAt sp FromRecordChainClone.chainCloneStack) := by
    rw [P3P4.stackAt_sub_eq sp (dpClosSubStack B) rootStack
          (by unfold rootStack dpClosSubStack; omega)
          (Nat.le_trans hsub (Nat.le_of_lt sp.isLt)),
        stackAt_root_eq_chainClone sp]
  have h270 : memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x279#64) 39 =
      memRegion (sp + 0x270#64) 48 := by
    rw [memRegion_split (sp + 0x270#64) 9 39 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h3e0 : memRegion (sp + 0x3e0#64) 368 =
      memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x402#64) 70 ∗
      memRegion (sp + 0x448#64) 240 ∗ memRegion (sp + 0x538#64) 24 := by
    rw [sp_3e0_368_eq_344_24 sp, sp_3e0_344_eq_104_240 sp,
        memRegion_split (sp + 0x3e0#64) 34 70 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    ac_rfl
  have h550 :
      cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗
      cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
      memRegion (sp + 0xa90#64) 288 ∗ memRegion (fp + 0xffffffffffffff80#64) 9 ∗
      sp550P2V1RemAt sp =
      memRegion (sp + 0x550#64) 976 ∗ memRegion (sp + 0x920#64) 6 ∗ memRegion (sp + 0x926#64) 10 ∗
      memRegion (sp + 0x930#64) 96 ∗ memRegion (sp + 0x990#64) 256 ∗
      memRegion (sp + 0xa90#64) 48 ∗ memRegion (sp + 0xac0#64) 296 ∗ memRegion (sp + 0xbe8#64) 136 := by
    rw [← sp_550_1824_split_p2v1 sp fp hfp, sp_550_1824_split_genP3 sp]
    unfold spHighGapsAt
    rw [memRegion_split (sp + 0xa90#64) 48 296 (by decide),
        memRegion_split (sp + 0x550#64) 976 16 (by decide),
        memRegion_split (sp + 0x550#64 + 976#64) 6 10 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    ac_rfl
  have hopkSlot := p2_coro_opk_slot_fold y.fut m.opkId w.opkWord hopk
  have hcoro := p2_coro_ok_fold y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
    (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
    (y.g.stores + 0x78#64) (kyberVt img) rngPtr
    (coroOpkIdAtP4 y.fut m.opkId)
    (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId))
  have hstk := stack_match_fold sp y.fut y.g.msgA y.g.peerA (m.spkId.zeroExtend 64)
  have hc := coinsInstalled_to_coinsAt img y.g.coinsP y.g.coins hcoins
  have hstores := cliPollStoresKitsAt_entails_storesAt (A := A) img.base
    (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
    (pid := w.opkWord) (sid := m.spkId) (kid := m.kpkId) (kbk := (pmOfE m i).baseKey)
    (cliKitStk B) y.g.stores StoresGhost.opened
  dsimp only [cliPollStoresKitsAt] at hstores
  have hmsgSlices := p2MsgFields_reassemble_slices_ext A y.g.msgG y.g.msgA m i w.opkWord hopk
  rw [hmsg_inner] at hmsgSlices
  rw [hstkSub, h3e0]
  refine Entails.trans (show _ ⊢
    coinsInstalled img y.g.coinsP y.g.coins ∗
    (((y.fut + 0x298#64) ↦₆₄ ((opkOptTag32 m.opkId).zeroExtend 64 ||| (w.opkWord.zeroExtend 64 <<< 32))) ∗
      processPrekeyActive10At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x78#64) (kyberVt img) ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
      ((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 0x80#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
      cells (y.fut + 0x250#64) 6 ∗ memRegion (y.fut + 0x280#64) 24 ∗
      (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12 ∗
      ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) ∗
      ((y.fut + 0x390#64) ↦₈ 1#8) ∗ memRegion (y.fut + 0x398#64) 96 ∗
      ((y.fut + 0x4f1#64) ↦₈ 0#8) ∗ ((y.fut + 0x4f2#64) ↦₈ 1#8) ∗
      memRegion (y.fut + 0x2c1#64) 7 ∗ memRegion (y.fut + 0x391#64) 7 ∗
      memRegion (y.fut + 0x488#64) 8 ∗ memRegion (y.fut + 0x4b0#64) 65 ∗
      memRegion (y.fut + 0x4f3#64) 5 ∗
      p2CoroScratchTailAt y.fut ∗ memRegion (y.fut + 0x782#64) 6) ∗
    ((cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗
        cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
        memRegion (sp + 0xa90#64) 288 ∗ memRegion (fp + 0xffffffffffffff80#64) 9 ∗
        sp550P2V1RemAt sp) ∗
      (sp ↦₆₄ 0#64) ∗ memRegion (sp + 0x8#64) 120 ∗
      ((sp + 0x90#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ y.g.peerA) ∗
      memRegion (sp + 0xbc#64) 4 ∗
      ((sp + 0xd0#64) ↦₆₄ m.spkId.zeroExtend 64) ∗
      memRegion (sp + 0xd8#64) 348 ∗
      memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
      memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
      spMidGapsAt sp ∗
      ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗
      ((sp + 0x3b8#64) ↦₆₄ y.g.msgA) ∗
      ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗
      memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x402#64) 70 ∗
      memRegion (sp + 0x538#64) 24) ∗
    ((cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer (cliKitStk B)).storeAt
        (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      (cliPollIdKit A img.base y.g.F y.g.peer (cliKitStk B)).identityAt
        y.g.stores StoresGhost.opened.identity ∗
      (cliPollPkKit A img.base y.g.F w.opkWord (cliKitStk B)).storeAt
        (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      (cliPollSpkKit A img.base y.g.F m.spkId (cliKitStk B)).storeAt
        (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      (cliPollKpkKit A img.base y.g.F m.kpkId m.spkId (pmOfE m i).baseKey (cliKitStk B)).storeAt
        (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A (y.g.stores + 0x118#64) StoresGhost.opened.pub) ∗
    (p2MsgFieldsAt y.g.msgA y.g.msgG.kyberPtr (mkPathAHdr m) i.messageVersion
        w.opkWord m.kpkId m.regId m.spkId ∗
      signalMessageRestVerAt A y.g.msgG.msg y.g.msgA i ∗
      pathAMsgRemInnerAtExt A y.g.msgG y.g.msgA m i) ∗
    ((memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x279#64) 39) ∗
      TokenInit img ∗
      sessionStateAt A (y.fut + 0xf8#64) G_bob st_bob ∗
      A.pool ∗
      stackAt sp FromRecordChainClone.chainCloneStack ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
      ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗
      ((sp + 0xb0#64) ↦₆₄ y.g.msgA) ∗
      ((sp + 0xb8#64) ↦₃₂ i.messageVersion.zeroExtend 32) ∗
      ((sp + 0x3a0#64) ↦₆₄ y.g.peerA) ∗
      ((sp + 0x3ac#64) ↦₈ 3#8) ∗
      protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗
      logOff img ∗
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - FromRecordChainClone.chainCloneStack) ∗
      ((sp + 0x80#64) ↦₆₄ (y.fut + 0xf8#64)) ∗
      ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗
      ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
      ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗
      ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
      memRegion (sp + 0x448#64) 240 ∗
      OverP2.prevVecAt A (y.fut + 0xe0#64) prevCap' prevPtr'
        [E2E.Record.encSession (OverP2.clearPending sess)] ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      memRegion y.out 48 ∗
      memRegion (sp + 0x250#64) 20 ∗
      memRegion (sp + 0x370#64) 36 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
    by sep_frame) ?_
  have hcoro' :
      ((y.fut + 0x298#64) ↦₆₄ ((opkOptTag32 m.opkId).zeroExtend 64 ||| (w.opkWord.zeroExtend 64 <<< 32))) ∗
      processPrekeyActive10At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x78#64) (kyberVt img) ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
      ((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 0x80#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
      cells (y.fut + 0x250#64) 6 ∗ memRegion (y.fut + 0x280#64) 24 ∗
      (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12 ∗
      ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) ∗
      ((y.fut + 0x390#64) ↦₈ 1#8) ∗ memRegion (y.fut + 0x398#64) 96 ∗
      ((y.fut + 0x4f1#64) ↦₈ 0#8) ∗ ((y.fut + 0x4f2#64) ↦₈ 1#8) ∗
      memRegion (y.fut + 0x2c1#64) 7 ∗ memRegion (y.fut + 0x391#64) 7 ∗
      memRegion (y.fut + 0x488#64) 8 ∗ memRegion (y.fut + 0x4b0#64) 65 ∗
      memRegion (y.fut + 0x4f3#64) 5 ∗
      p2CoroScratchTailAt y.fut ∗ memRegion (y.fut + 0x782#64) 6 ⊢
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr
        (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) := by
    refine Entails.trans (sepConj_mono_left hopkSlot) ?_
    exact Entails.trans (by sep_frame) hcoro
  have hstk' :
      (cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗
        cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
        memRegion (sp + 0xa90#64) 288 ∗ memRegion (fp + 0xffffffffffffff80#64) 9 ∗
        sp550P2V1RemAt sp) ∗
      (sp ↦₆₄ 0#64) ∗ memRegion (sp + 0x8#64) 120 ∗
      ((sp + 0x90#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ y.g.peerA) ∗
      memRegion (sp + 0xbc#64) 4 ∗
      ((sp + 0xd0#64) ↦₆₄ m.spkId.zeroExtend 64) ∗
      memRegion (sp + 0xd8#64) 348 ∗
      memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
      memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
      spMidGapsAt sp ∗
      ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗
      ((sp + 0x3b8#64) ↦₆₄ y.g.msgA) ∗
      ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗
      memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x402#64) 70 ∗
      memRegion (sp + 0x538#64) 24 ⊢
      genP3SpillAll sp ∗ memRegion (sp + 0x3e0#64) 104 ∗
      memRegion (sp + 0xa90#64) 344 ∗
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA := by
    rw [h550]
    exact Entails.trans (by sep_frame) hstk
  rw [h270]
  refine Entails.trans (sepConj_mono hc (sepConj_mono hcoro'
    (sepConj_mono hstk' (sepConj_mono hstores (sepConj_mono_left hmsgSlices))))) ?_
  sep_frame

end OverP2Inst
end CryptoVerification.SignalSession.Cli.RunProofs.Poll
