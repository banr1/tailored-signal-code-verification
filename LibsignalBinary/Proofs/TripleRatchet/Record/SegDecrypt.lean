/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.FetchDecrypt
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatch
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Record

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

namespace SegDecryptFacts

namespace SegDecryptRegReadSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

end SegDecryptRegReadSimp

open SegDecryptRegReadSimp

/-! ## `SegDecrypt` (`+0x69c → +0x1e8c / +0x850`): `try_decrypt_with_state` + 3-way dispatch -/

/-- Outcome bridge for `SegDecrypt`: a `SepWPp` to `target` whose normal postcondition establishes
either `JState` or `FState` and whose panic postcondition establishes `recordDecryptSpec.onPanic`
yields the existential `Steps` conclusion of `SegDecryptSpec`. -/
theorem seg_of_sepWPp_JF {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    {img : Obj.Image} {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {target : BitVec 64} {P : SepProp}
    (hm : s.mem ⊨ P ∗ R)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem)
    (hwp : SepWPp (tripleRatchetProgAtExt img.base ext) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        JState C A ctl uuidTryParse S img x R s0 sf ∨ FState C A ctl uuidTryParse S img x R s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (recordDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R))) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (JState C A ctl uuidTryParse S img x R s0 s' ∨ FState C A ctl uuidTryParse S img x R s0 s' ∨
        regionOutcome (recordDecryptSpec C A ctl uuidTryParse S img) (recordRegionExit img) x R s0 s') := by
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hJF⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩
  · rcases hJF hmf with hJ | hF
    · exact ⟨sf, hsteps, Or.inl hJ⟩
    · exact ⟨sf, hsteps, Or.inr (Or.inl hF)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hpan, hqp hmf⟩))⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem seg_of_sepWPp_JFQF {Q : List (BitVec 8) → Prop} {F : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    {img : Obj.Image} {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {target : BitVec 64} {P : SepProp}
    (hm : s.mem ⊨ P ∗ R)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem)
    (hwp : SepWPp (tripleRatchetProgAtExt img.base ext) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        JState C A ctl uuidTryParse S img x (F ∗ R) s0 sf ∨
          FState C A ctl uuidTryParse S img x (F ∗ R) s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (recordDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R))) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (JState C A ctl uuidTryParse S img x (F ∗ R) s0 s' ∨
        FState C A ctl uuidTryParse S img x (F ∗ R) s0 s' ∨
        regionOutcome (recordDecryptSpecQF Q F C A ctl uuidTryParse S img)
          (recordRegionExit img) x R s0 s') := by
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hJF⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩
  · rcases hJF hmf with hJ | hF
    · exact ⟨sf, hsteps, Or.inl hJ⟩
    · exact ⟨sf, hsteps, Or.inr (Or.inl hF)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hpan, hqp hmf⟩))⟩
  · exact (not_satisfies_false_sepConj hoom).elim

/-- `try_decrypt_with_state` panic entailment into `recordDecryptSpec.onPanic`. -/
theorem tryDecrypt_onPanic_entails {C : Crypto} {S : SpqrModel}
    {x : RecordDecryptGhost} {G₁ : SessionGhost}
    {s0 s sf : State} {F : SepProp} {sp : BitVec 64}
    (heq : x.st.version.toNat = x.msg.messageVersion.toNat)
    (htr : s.trace = s0.trace) :
    (⌜(((mkTryDecryptGhost sp x G₁).model C S uuidTryParse).1 = .error .panic ∨
        S.recvPanics (mkTryDecryptGhost sp x G₁).st.pqRatchetState
          (mkTryDecryptGhost sp x G₁).msg.pqRatchet ∨
        allocFailedIn s sf) ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜((x.model C S uuidTryParse).1 = .error .panic ∨
        (x.st.version.toNat = x.msg.messageVersion.toNat ∧
          S.recvPanics x.st.pqRatchetState x.msg.pqRatchet) ∨
        allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨hpan, hpref⟩ => ?_
  unfold allocFailedIn at hpan ⊢
  rw [htr] at hpan hpref
  refine Entails.pure_right ⟨?_, hpref⟩ (entails_anyHeap _)
  rcases hpan with hmod | hrecv | halloc
  · exact Or.inl (model_panic_of_tryDecrypt_panic C S sp x G₁ heq hmod)
  · exact Or.inr (Or.inl ⟨heq, hrecv⟩)
  · exact Or.inr (Or.inr halloc)

def isDupErr : SignalProtocolError → Bool
  | .duplicatedMessage _ _ => true
  | _ => false

def decryptTarget (entry : BitVec 64) (res : Except SignalProtocolError (List (BitVec 8))) :
    BitVec 64 :=
  match res with
  | .ok _ => entry + bv% (7820)
  | .error e => if isDupErr e then entry + bv% (7820) else entry + bv% (2128)

theorem adrp_1732_eq_logFilterAddr {img : Obj.Image}
    (hloads : Obj.Loads libsignalSessionImage img)
    {entry : BitVec 64} (hentry : entry = img.base + bv% (ls_off% "session_message_decrypt_signal")) :
    ((entry + bv% (1732) &&& bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent as prost::message::Message>::encoded_len [local#1]" + 56))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) =
      CryptoVerification.LibsignalSession.logFilterAddr img := by
  have hbal := ProofLib.base_aligned_of_loads hloads
  rw [hentry, BitVec.add_assoc img.base, adrp_page_of_aligned hbal,
    CryptoVerification.LibsignalSession.logFilterAddr]
  have hmask : ((238988#64 + 1732#64 : BitVec 64) &&& bv% (2 ^ 64 - 4096)) = 237568#64 := rfl
  rw [hmask]
  bv_omega

theorem logOff_eq_at_1732 {img : Obj.Image}
    (hloads : Obj.Loads libsignalSessionImage img)
    {entry : BitVec 64} (hentry : entry = img.base + bv% (ls_off% "session_message_decrypt_signal")) :
    logOff img =
      ((((entry + bv% (1732) &&& bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent as prost::message::Message>::encoded_len [local#1]" + 56))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096)) ↦₆₄ 0#64) := by
  unfold logOff
  rw [adrp_1732_eq_logFilterAddr hloads hentry]

theorem stackAt_root_split_set (sp : BitVec 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - setSessionStateStack) ∗
        stackAt sp setSessionStateStack :=
  stackAt_split_bottom sp setSessionStateStack (rootStack - setSessionStateStack) (by decide)

theorem setStack_to_rootStack (sp : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - setSessionStateStack) ∗
      stackAt sp setSessionStateStack ⊢
    stackAt sp rootStack := by
  rw [← stackAt_root_split_set sp]
  exact Entails.refl _

theorem memRegion_5f0_split344 (sp : BitVec 64) :
    memRegion (sp + 1520#64) 1712 =
      memRegion (sp + 1520#64) 344 ∗ memRegion (sp + 1864#64) 1368 := by
  rw [show (1712 : Nat) = 344 + 1368 from rfl,
    memRegion_split (sp + 1520#64) 344 1368 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_5f0_join344 (sp : BitVec 64) :
    memRegion (sp + 1520#64) 344 ∗ memRegion (sp + 1864#64) 1368 ⊢
      memRegion (sp + 1520#64) 1712 := by
  rw [← memRegion_5f0_split344 sp]
  exact Entails.refl _

theorem errsAt_nil_exists_intro (A : RustAlloc) (sp : BitVec 64) :
    errsAt A (sp + 1496#64) [] ⊢ ∃∗ errs : List RecErr, errsAt A (sp + 0x5d8#64) errs :=
  Entails.sepExists_right [] (Entails.refl _)

theorem sessionStateAt_ok_exists_intro (A : RustAlloc) (p : BitVec 64)
    (G G' : SessionGhost) (st' : SessionState (List (BitVec 8)))
    (hrel : G.AfterRecordDecrypt G') :
    sessionStateAt A p G' st' ⊢
      ∃∗ G'' : SessionGhost, ⌜G.AfterRecordDecrypt G''⌝ ∗ sessionStateAt A p G'' st' :=
  Entails.sepExists_right G' (Entails.pure_right hrel (Entails.refl _))

theorem tapeAfter_tryDecrypt_entails (C : Crypto) (ctl sp : BitVec 64)
    (x : RecordDecryptGhost) (G₁ : SessionGhost)
    (heq : x.st.version.toNat = x.msg.messageVersion.toNat) :
    tapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ⊢
      tapeAfter ctl x.cur x.rest (x.draws C) := by
  rw [draws_eq_tryDecrypt_of_version_eq C sp x G₁ heq]
  exact Entails.refl _

theorem stackAt_root_split_dropLocal2 (sp : BitVec 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - dropSessionStructureLocal2Stack) ∗
        stackAt sp dropSessionStructureLocal2Stack :=
  stackAt_split_bottom sp dropSessionStructureLocal2Stack
    (rootStack - dropSessionStructureLocal2Stack) (by decide)

theorem dropLocal2Stack_to_rootStack (sp : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - dropSessionStructureLocal2Stack) ∗
      stackAt sp dropSessionStructureLocal2Stack ⊢
    stackAt sp rootStack := by
  rw [← stackAt_root_split_dropLocal2 sp]
  exact Entails.refl _

theorem eq_duplicatedMessage_of_isDupErr {e : SignalProtocolError} (h : isDupErr e = true) :
    ∃ i c, e = .duplicatedMessage i c := by
  cases e <;> simp [isDupErr] at h ⊢

theorem speTag_add2_ne_zero {e : SignalProtocolError} (hne : e ≠ .panic) :
    speTag e + 2#64 ≠ 0#64 := by
  cases e <;> first | exact absurd rfl hne | (dsimp [speTag, speWord]; decide)

theorem speTag_ne_speWord23_of_not_isDupErr {e : SignalProtocolError}
    (hdup : isDupErr e = false) :
    speTag e ≠ 9223372036854775831#64 := by
  intro h
  obtain ⟨i, c, rfl⟩ := speTag_eq_speWord23_iff.mp h
  exact Bool.noConfusion hdup

theorem memRegion_5f0_split_b40 (sp : BitVec 64) :
    memRegion (sp + 1520#64) 1712 =
      memRegion (sp + 1520#64) 1360 ∗ memRegion (sp + 2880#64) 48 ∗
        memRegion (sp + 2928#64) 304 := by
  rw [show (1712 : Nat) = 1360 + (48 + 304) from rfl,
    memRegion_split (sp + 1520#64) 1360 (48 + 304) (by decide),
    memRegion_split (sp + 1520#64 + BitVec.ofNat 64 1360) 48 304 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, ← sepConj_assoc]

theorem words6_b40_to_memRegion (sp : BitVec 64) (v0 v1 v2 v3 v4 v5 : BitVec 64) :
    memRegion (sp + 1520#64) 1360 ∗
    ((sp + 2880#64) ↦₆₄ v0) ∗ ((sp + 2888#64) ↦₆₄ v1) ∗
    ((sp + 2896#64) ↦₆₄ v2) ∗ ((sp + 2904#64) ↦₆₄ v3) ∗
    ((sp + 2912#64) ↦₆₄ v4) ∗ ((sp + 2920#64) ↦₆₄ v5) ∗
    memRegion (sp + 2928#64) 304 ⊢
    memRegion (sp + 1520#64) 1712 := by
  rw [memRegion_5f0_split_b40 sp]
  refine sepConj_mono_right ?_
  simpa only [words6At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
    sepConj_mono_left (Q := memRegion (sp + 2928#64) 304)
      (words6At_entails_memRegion (sp + 2880#64) v0 v1 v2 v3 v4 v5)

theorem words6_4b0_to_memRegion (sp : BitVec 64) (v0 v1 v2 v3 v4 v5 : BitVec 64) :
    ((sp + 1200#64) ↦₆₄ v0) ∗ ((sp + 1208#64) ↦₆₄ v1) ∗
    ((sp + 1216#64) ↦₆₄ v2) ∗ ((sp + 1224#64) ↦₆₄ v3) ∗
    ((sp + 1232#64) ↦₆₄ v4) ∗ ((sp + 1240#64) ↦₆₄ v5) ⊢
    memRegion (sp + 1200#64) 48 := by
  simpa only [words6At, BitVec.add_assoc, BitVec.reduceAdd, ← sepConj_assoc] using
    words6At_entails_memRegion (sp + 1200#64) v0 v1 v2 v3 v4 v5

theorem spe_errsAt_entails (A : RustAlloc) (sp p : BitVec 64)
    (e : SignalProtocolError) (tag w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp)
    (hp : p ≠ 0)
    (hreassemble :
      ((p ↦₆₄ tag) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ∗
       ((p + 24#64) ↦₆₄ w3) ∗ ((p + 32#64) ↦₆₄ w4) ∗ ((p + 40#64) ↦₆₄ w5) ∗ H) ⊢
        speAt A (utf8 "decrypt") p e) :
    ((sp + 1496#64) ↦₆₄ 4#64) ∗ ((sp + 1504#64) ↦₆₄ p) ∗ ((sp + 1512#64) ↦₆₄ 1#64) ∗
    A.live p 192 8 ∗
    (p ↦₆₄ tag) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ∗
    ((p + 24#64) ↦₆₄ w3) ∗ ((p + 32#64) ↦₆₄ w4) ∗ ((p + 40#64) ↦₆₄ w5) ∗
    H ∗ memRegion (p + 48#64) 144 ⊢
    ∃∗ r : RecErr, errsAt A (sp + 0x5d8#64) [r] := by
  refine Entails.trans ?_ (errsAt_singleton_intro A sp p (.spe e) hp)
  dsimp only [recErrAt]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
  simpa only [sepConj_assoc] using sepConj_mono_left (Q := memRegion (p + 48#64) 144) hreassemble

end SegDecryptFacts

open SegDecryptFacts

attribute [local irreducible] Program.fetch Program.externAt?

/-- Calls `try_decrypt_with_state` at `+0x6b4` (restricted to PQ states meeting `Q` with frame `F`)
and dispatches `Ok` and `Err(DuplicatedMessage)` to `JState` and non-duplicate errors to `FState`. -/
theorem segDecrypt_ok_extQF {Q : List (BitVec 8) → Prop} {F : SepProp} {img : Obj.Image}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hhooks : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (htry : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName)
      (tryDecryptSpecQF' Q F C A ctl uuidTryParse S img))
    (hset : FromRecordCallees.SetSessionStateOkExt img.base A ext)
    (hdrop : FromRecordCallees.DropSessionStructureLocal2OkExt img.base A ext)
    (hgrow : FromRecordCallees.GrowOneSpeOkExt img.base A ext)
    (hclosure : FromRecordCallees.LogClosureOkExt img ext)
    (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State)
    (_hQ : Q x.st.pqRatchetState)
    (hV : VState A ctl img x G₁ (F ∗ R) s0 s) (hsp_bound : rootStack ≤ s0.sp.toNat)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (JState C A ctl uuidTryParse S img x (F ∗ R) s0 s' ∨
        FState C A ctl uuidTryParse S img x (F ∗ R) s0 s' ∨
        regionOutcome (recordDecryptSpecQF Q F C A ctl uuidTryParse S img)
          (recordRegionExit img) x R s0 s') := by
  rcases hV with ⟨hpc, ⟨hrun, hsp, hsp_align, hx29, htr, hfrozen, hsym, hvregs⟩,
    ⟨hrem_ne, hseeds, hrc_len⟩, hclone, heq, hmem⟩
  have hentry := entryOf_eq_tripleRatchetProgAtExt ext hloads msgDecryptName
  unfold recVPC at hpc
  rw [hentry] at hpc
  have hfn := libsignalSessionCode_fnOff_sym_3a4a8
  have htry_rel :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr msgDecryptName +
          bv% (2 ^ 64 + (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") - (ls_off% "session_message_decrypt_signal")))
        (tryDecryptSpecQF' Q F C A ctl uuidTryParse S img) := by
    have h1 : libsignalSessionCode.fnOff tryDecryptName = num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") :=
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
    have h2 : (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr msgDecryptName +
        bv% (2 ^ 64 + (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") - (ls_off% "session_message_decrypt_signal")) =
        (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName := by
      simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn, h1]
      bv_omega
    rw [h2]
    exact htry
  have hmemcpy_rel :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr msgDecryptName +
          bv% (ls_off% "memcpy" - ls_off% "session_message_decrypt_signal"))
        sessionMemcpyRegionSpec :=
    hhooks.session_memcpy_region_ok_at msgDecryptName (num% (ls_off% "memcpy" - ls_off% "session_message_decrypt_signal"))
      (by fnoff_eq)
  have hset_rel :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr msgDecryptName +
          bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state") - (ls_off% "session_message_decrypt_signal")))
        (setSessionStateSpec A) := by
    have h1 : libsignalSessionCode.fnOff setSessionStateName = num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state") :=
      (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::set_session_state")
    have h2 : (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr msgDecryptName +
        bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state") - (ls_off% "session_message_decrypt_signal")) =
        (tripleRatchetProgAtExt img.base ext).fnAddr setSessionStateName := by
      simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn, h1]
      bv_omega
    rw [h2]
    exact hset
  have hdrop_rel :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr msgDecryptName +
          bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#2]") - (ls_off% "session_message_decrypt_signal")))
        (dropSessionStructureLocal2Spec A) := by
    have h1 : libsignalSessionCode.fnOff dropSessionStructureLocal2Name = num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#2]") :=
      (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#2]")
    have h2 : (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr msgDecryptName +
        bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#2]") - (ls_off% "session_message_decrypt_signal")) =
        (tripleRatchetProgAtExt img.base ext).fnAddr dropSessionStructureLocal2Name := by
      simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn, h1]
      bv_omega
    rw [h2]
    exact hdrop
  have hclosure_rel :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr msgDecryptName +
          bv% (2 ^ 64 + (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_session::HookRng>::{closure#0}") - (ls_off% "session_message_decrypt_signal")))
        ((logClosureSpec img).inImage img) := by
    have h1 : libsignalSessionCode.fnOff logClosureName = num% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_session::HookRng>::{closure#0}") :=
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_session::HookRng>::{closure#0}")
    have h2 : (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr msgDecryptName +
        bv% (2 ^ 64 + (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_session::HookRng>::{closure#0}") - (ls_off% "session_message_decrypt_signal")) =
        (tripleRatchetProgAtExt img.base ext).fnAddr logClosureName := by
      simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn, h1]
      bv_omega
    rw [h2]
    exact hclosure
  have hgrow_rel :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr msgDecryptName +
          bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one") - (ls_off% "session_message_decrypt_signal")))
        (growOneSpeSpec A) := by
    have h1 : libsignalSessionCode.fnOff growOneSpeName = num% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one") :=
      (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one")
    have h2 : (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr msgDecryptName +
        bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one") - (ls_off% "session_message_decrypt_signal")) =
        (tripleRatchetProgAtExt img.base ext).fnAddr growOneSpeName := by
      simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn, h1]
      bv_omega
    rw [h2]
    exact hgrow
  have hFPC : recFPC img = (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr msgDecryptName + 2128#64 := by
    unfold recFPC
    rw [hentry]
  have hJPC : recJPC img = (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr msgDecryptName + 7820#64 := by
    unfold recJPC
    rw [hentry]
  have hlog1732 : logOff img =
      (((((libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr msgDecryptName + 1732#64 &&&
        bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent as prost::message::Message>::encoded_len [local#1]" + 56))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096)) ↦₆₄ 0#64) :=
    logOff_eq_at_1732 hloads (by rw [Program.fnAddr_rebase, hfn])
  have hlog1732' :
      (((((libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr msgDecryptName + 1732#64 &&&
        bv% (2 ^ 64 - 4096)) + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256 - page% (ls_off% "<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent as prost::message::Message>::encoded_len [local#1]" + 56))) ↦₆₄ 0#64) : SepProp) ⊢
        logOff img := by
    rw [hlog1732]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.refl _
  segDecrypt_rec_fetches img.base (Rust.withPanics ext) hfn 1692 64
  segDecrypt_rec_fetches img.base (Rust.withPanics ext) hfn 1984 36
  segDecrypt_rec_fetches img.base (Rust.withPanics ext) hfn 5948 156
  segDecrypt_rec_fetches img.base (Rust.withPanics ext) hfn 7812 8
  change s.pc = (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr msgDecryptName + 1692#64 at hpc
  clear hentry hfn htry hset hdrop hgrow hclosure hloads
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr msgDecryptName = entry
  examples_hide_fetches
  have hsp0 : s0.sp = s.sp := hsp.symm
  clear hsp
  rw [hsp0] at hsp_bound hmem
  unfold recFrame at hmem
  simp only [← sepConj_assoc] at hmem
  have hF0 : FrozenInv img s := ⟨hfrozen, hsym⟩
  apply seg_of_sepWPp_JFQF hmem hL
    (target := decryptTarget entry ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).1)
  apply segDecrypt_of_sepWP_frozen hF0 (mid := entry + bv% (2 ^ 64 + (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") - (ls_off% "session_message_decrypt_signal")))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF1
  have hsp_bound1 : rootStack ≤
      ((((((((s.writeReg64 (Reg.gpr 2#5) x.remA).writeReg64
              (Reg.gpr 3#5) x.locA).writeReg64
            (Reg.gpr 4#5) x.msgA).writeReg64
          (Reg.gpr 0#5) (s.sp + 1200#64)).writeReg64
        (Reg.gpr 1#5) (s.sp + 3232#64)).writeReg64
      (Reg.gpr 5#5) 2#64).writeReg64
    (Reg.gpr 6#5) 0#64).writeReg64 (Reg.gpr 30#5) (entry + bv% (1720)) |>.setPC
      (entry + bv% (2 ^ 64 + (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") - (ls_off% "session_message_decrypt_signal")))).sp.toNat := hsp_bound
  segDecrypt_wpp_call_frozen htry_rel
    ({ ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
       rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
       msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
       cur := x.cur, rest := x.rest : TryDecryptGhost }) hF1
    (tryDecrypt_onPanic_entails heq (by simp only [wp_norm, arm64_norm, htr]))
  apply SepWPp.exists_elim
  intro G₂
  apply SepWPp.pure_elim
  rintro ⟨⟨hnpan, htr_sf⟩, hdec⟩
  have hmk :
      ({ ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
         rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
         msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
         cur := x.cur, rest := x.rest : TryDecryptGhost }) = mkTryDecryptGhost s.sp x G₁ := rfl
  rw [hmk] at hnpan hdec ⊢
  rcases hres : ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).1 with e | pt
  · -- Error branch
    dsimp only [decryptTarget, vecResultAt]
    have he_npan : e ≠ .panic := fun h => hnpan (h ▸ hres)
    cases hdup : isDupErr e
    · -- Non-duplicate error -> FState
      have htag_ne23 : speTag e ≠ speWord 23 := speTag_ne_speWord23_of_not_isDupErr hdup
      have hmodel_err : x.model C S uuidTryParse =
          (.error (.invalidMessage .whisper .decryptionFailed), x.st) := by
        rw [model_err_of_tryDecrypt_err C S s.sp x G₁ heq (Prod.ext hres rfl),
          recordError_of_speTag_ne_speWord23 he_npan htag_ne23]
      have hmodel_err1 : (x.model C S uuidTryParse).1 =
          .error (.invalidMessage .whisper .decryptionFailed) := congrArg Prod.fst hmodel_err
      have htag_add2 : speTag e + 2#64 ≠ 0#64 := speTag_add2_ne_zero he_npan
      have htag_ne23' : speTag e ≠ 9223372036854775831#64 := htag_ne23
      apply segDecrypt_of_sepWP_frozen hF_sf (mid := entry + bv% (2 ^ 64 + (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_session::HookRng>::{closure#0}") - (ls_off% "session_message_decrypt_signal")))
      refine segDecrypt_replace_pre
        (speAt_decomp6 A (utf8 "decrypt") (s.sp + 1200#64) e he_npan) (by sep_focus) ?_
      rw [memRegion_5f0_split_b40 s.sp, memRegion48_eq_words6At (s.sp + 2880#64),
        stackAt_root_split_closure s.sp, errsAt_nil_unfold A s.sp]
      unfold words6At
      segDecrypt_wp_extract_exists
      rename_i u0 u1 u2 u3 u4 u5 w1 w2 w3 w4 w5 H hreassemble
      generalize htag_def : speTag e = tag at htag_add2 htag_ne23' hreassemble ⊢
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF2
      segDecrypt_wpp_call_frozen hclosure_rel () hF2 noPanic_onPanic_entails
      apply segDecrypt_of_sepWP_frozen hF_sf_1 (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one") - (ls_off% "session_message_decrypt_signal")))
      segDecrypt_wp_extract_exists
      rename_i htr_cl
      rw [hsp_sf]
      refine segDecrypt_replace_pre (closureStack_to_growStack s.sp) (by sep_focus) ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF3
      segDecrypt_wpp_call_frozen hgrow_rel (s.sp + 0x5d8#64, 0#64, 8#64, []) hF3
        (grow_onPanic_entails (by simp only [wp_norm, arm64_norm, htr_cl, htr_sf, htr]))
      apply segDecrypt_of_sepWP_ret_frozen hF_sf_2
      segDecrypt_wp_extract_exists
      rename_i p' hp'
      rw [memRegion_192_split48 p', memRegion48_eq_words6At p']
      unfold words6At
      segDecrypt_wp_extract_exists
      wp_steps
      rw [hsp_sf_1, hsp_sf]
      refine segDecrypt_replace_pre
        (spe_errsAt_entails A s.sp p' e tag w1 w2 w3 w4 w5 H hp'.2 (hreassemble p'))
        (by sep_focus) ?_
      refine segDecrypt_replace_pre (words6_4b0_to_memRegion s.sp tag w1 w2 w3 w4 w5) (by sep_focus) ?_
      refine segDecrypt_replace_pre (words6_b40_to_memRegion s.sp tag w1 w2 w3 w4 w5) (by sep_focus) ?_
      refine segDecrypt_replace_pre (growStack_to_rootStack s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre
        (sessionStateAt_exists_intro A (s.sp + 3232#64) G₂
          ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2) (by sep_focus) ?_
      refine segDecrypt_replace_pre (tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF4 hmf
      right
      refine ⟨by rw [hFPC]; wp_norm_lhs, ?_, hmodel_err1, ?_⟩
      · refine ⟨by wp_norm_lhs,
                by simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf, hsp0],
                by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf]; exact hsp_align,
                by simp only [wp_norm, arm64_norm, hcs_sf_2, hcs_sf_1, hcs_sf]; exact hx29,
                by simp only [wp_norm, arm64_norm, hp'.1, htr_cl, htr_sf, htr],
                hF4.1, hF4.2,
                by simp only [wp_norm, arm64_norm, hvregs_3, hvregs_2, hvregs_1, hvregs]⟩
      · unfold recFrame
        rw [hsp0]
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf
    · -- Duplicate error -> JState
      obtain ⟨i, c, rfl⟩ := eq_duplicatedMessage_of_isDupErr hdup
      have hmodel_dup : x.model C S uuidTryParse = (.error (.duplicatedMessage i c), x.st) :=
        model_err_of_tryDecrypt_err C S s.sp x G₁ heq (Prod.ext hres rfl)
      have hmodel_dup1 : (x.model C S uuidTryParse).1 = .error (.duplicatedMessage i c) :=
        congrArg Prod.fst hmodel_dup
      apply segDecrypt_of_sepWP_frozen hF_sf (mid := entry + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#2]") - (ls_off% "session_message_decrypt_signal")))
      dsimp only [speAt]
      rw [stackAt_root_split_dropLocal2 s.sp]
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF2
      segDecrypt_wpp_call_frozen hdrop_rel
        ({ ss := s.sp + 3232#64, G := G₂,
           st := ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 : DropSessionStructureGhost })
        hF2 noPanic_onPanic_entails
      apply segDecrypt_of_sepWP_ret_frozen hF_sf_1
      segDecrypt_wp_extract_exists
      rename_i htr_drop
      rw [hsp_sf]
      refine segDecrypt_replace_pre (dropLocal2Stack_to_rootStack s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre (errsAt_nil_exists_intro A s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre (tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF3 hmf
      left
      refine ⟨by rw [hJPC]; wp_norm_lhs, ?_, by rw [hmodel_dup1]; nofun,
        by simp only [wp_norm, arm64_norm, h_17, hsp0],
        by simp only [wp_norm, arm64_norm, h_18],
        by rw [hmodel_dup1]; dsimp only [recordResultTag, speWord]; wp_norm_lhs, ?_⟩
      · refine ⟨by wp_norm_lhs,
                by simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf, hsp0],
                by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf]; exact hsp_align,
                by simp only [wp_norm, arm64_norm, hcs_sf_1, hcs_sf]; exact hx29,
                by simp only [wp_norm, arm64_norm, htr_drop, htr_sf, htr],
                hF3.1, hF3.2,
                by simp only [wp_norm, arm64_norm, hvregs_2, hvregs_1, hvregs]⟩
      · unfold recFrame
        rw [hsp0, hmodel_dup1]
        dsimp only [recordResultAt, vecResultAt, speAt]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf
  · -- Ok branch
    dsimp only [decryptTarget, vecResultAt]
    have hmodel_ok : x.model C S uuidTryParse =
        (.ok pt, ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2) :=
      model_ok_of_tryDecrypt_ok C S s.sp x G₁ heq (Prod.ext hres rfl)
    have hmodel_ok1 : (x.model C S uuidTryParse).1 = .ok pt := by rw [hmodel_ok]
    have hmodel_ok2 : (x.model C S uuidTryParse).2 =
        ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 := by rw [hmodel_ok]
    rw [hres] at hdec
    have hrel : x.G.AfterRecordDecrypt G₂ := recordOkRel_of_clone_dec hclone hdec
    apply segDecrypt_of_sepWP_frozen hF_sf (mid := entry + bv% (ls_off% "memcpy" - ls_off% "session_message_decrypt_signal"))
    rw [sessionStateAt_eq_inline_sep_heap A (s.sp + 3232#64) G₂
      ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2,
      memRegion_5f0_split344 s.sp, stackAt_root_split_set s.sp, hlog1732]
    segDecrypt_wp_extract_exists
    rename_i bs hbs
    rw [← hbs.1]
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF2
    segDecrypt_wpp_call_frozen hmemcpy_rel (s.sp + 1520#64, s.sp + 3232#64, bs) hF2
      noPanic_onPanic_entails
    apply segDecrypt_of_sepWP_frozen hF_sf_1 (mid := entry + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state") - (ls_off% "session_message_decrypt_signal")))
    segDecrypt_wp_extract_exists
    rename_i hmc
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF3
    segDecrypt_wpp_call_frozen hset_rel
      ({ record := s.sp + 288#64, src := s.sp + 1520#64,
         cur := some (x.G, x.st), bs := bs : SetSessionStateGhost }) hF3
      noPanic_onPanic_entails
    apply segDecrypt_of_sepWP_ret_frozen hF_sf_2
    segDecrypt_wp_extract_exists
    rename_i htr_set
    wp_steps
    rw [hsp_sf_1, hsp_sf]
    refine segDecrypt_replace_pre
      (sessionStateAt_move_bytes_twice A (s.sp + 3232#64) (s.sp + 1520#64) (s.sp + 312#64)
        G₂ ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 hbs.2) (by sep_focus) ?_
    refine segDecrypt_replace_pre (memRegion_5f0_join344 s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre (setStack_to_rootStack s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre hlog1732' (by sep_focus) ?_
    refine segDecrypt_replace_pre
      (sessionStateAt_ok_exists_intro A (s.sp + 312#64) x.G G₂
        ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 hrel) (by sep_focus) ?_
    refine segDecrypt_replace_pre (errsAt_nil_exists_intro A s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre (tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF4 hmf
    left
    refine ⟨by rw [hJPC]; wp_norm_lhs, ?_, by rw [hmodel_ok1]; nofun,
      by simp only [wp_norm, arm64_norm, h_27, h_17, hsp0],
      by simp only [wp_norm, arm64_norm, h_28, h_18],
      by rw [hmodel_ok1]; dsimp only [recordResultTag, okTagVec]; wp_norm_lhs, ?_⟩
    · refine ⟨by wp_norm_lhs,
              by simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf, hsp0],
              by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf]; exact hsp_align,
              by simp only [wp_norm, arm64_norm, hcs_sf_2, hcs_sf_1, hcs_sf]; exact hx29,
              by simp only [wp_norm, arm64_norm, htr_set, hmc.2, htr_sf, htr],
              hF4.1, hF4.2,
              by simp only [wp_norm, arm64_norm, hvregs_3, hvregs_2, hvregs_1, hvregs]⟩
    · unfold recFrame
      rw [hsp0, hmodel_ok1, hmodel_ok2]
      dsimp only [recordResultAt, vecResultAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf

/-- `segDecrypt_ok_extQF` on `tripleRatchetProgAt img.base C ctl abs` for every `Q` and `F`. -/
theorem segDecrypt_okQF {Q : List (BitVec 8) → Prop} {F : SepProp} {img : Obj.Image} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {abs : String → Option (State → State)} :
    SegDecryptSpecQF Q F img C A ctl uuidTryParse S abs :=
  fun hloads hhooks htry hset hdrop hgrow hclosure x G₁ R s0 s hQ =>
    segDecrypt_ok_extQF hloads (Stage2Contracts.of_tripleRatchetProgAt' hhooks) htry
      hset hdrop hgrow hclosure x G₁ R s0 s hQ

/-- `segDecrypt_ok_extQF` at `F := emp`. -/
theorem segDecrypt_ok_extQ {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {ext : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hhooks : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (htry : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName)
      ((tryDecryptSpec C A ctl uuidTryParse S img).restrictPre (Q ·.st.pqRatchetState)))
    (hset : FromRecordCallees.SetSessionStateOkExt img.base A ext)
    (hdrop : FromRecordCallees.DropSessionStructureLocal2OkExt img.base A ext)
    (hgrow : FromRecordCallees.GrowOneSpeOkExt img.base A ext)
    (hclosure : FromRecordCallees.LogClosureOkExt img ext)
    (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State)
    (hQ : Q x.st.pqRatchetState)
    (hV : VState A ctl img x G₁ R s0 s) (hsp_bound : rootStack ≤ s0.sp.toNat)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (JState C A ctl uuidTryParse S img x R s0 s' ∨ FState C A ctl uuidTryParse S img x R s0 s' ∨
        regionOutcome (recordDecryptSpec C A ctl uuidTryParse S img) (recordRegionExit img) x R s0 s') := by
  have hV' : VState A ctl img x G₁ (emp ∗ R) s0 s := by simpa only [emp_sepConj] using hV
  obtain ⟨s', hsteps, hJ | hF | ⟨hpc, hrun, hvregs, hpost⟩ | ⟨hpan, hqp⟩⟩ :=
    segDecrypt_ok_extQF hloads hhooks (subroutine_ok_tryDecryptSpecQF'_emp htry)
      hset hdrop hgrow hclosure x G₁ R s0 s hQ hV' hsp_bound hL
  · rw [emp_sepConj] at hJ
    exact ⟨s', hsteps, Or.inl hJ⟩
  · rw [emp_sepConj] at hF
    exact ⟨s', hsteps, Or.inr (Or.inl hF)⟩
  · dsimp only [recordDecryptSpecQF] at hpost
    rw [emp_sepConj] at hpost
    exact ⟨s', hsteps, Or.inr (Or.inr (Or.inl ⟨hpc, hrun, hvregs, hpost⟩))⟩
  · exact ⟨s', hsteps, Or.inr (Or.inr (Or.inr ⟨hpan, hqp⟩))⟩

/-- `segDecrypt_ok_extQ` at `Q := fun _ => True`, with the unrestricted `try_decrypt` contract. -/
theorem segDecrypt_ok_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)} :
    SegDecryptSpecExt img C A ctl uuidTryParse S ext :=
  fun hloads hhooks htry hset hdrop hgrow hclosure x G₁ R s0 s =>
    segDecrypt_ok_extQ (Q := fun _ => True) hloads hhooks (Spec.subroutine_ok_restrictPre _ htry)
      hset hdrop hgrow hclosure x G₁ R s0 s trivial

/-- `segDecrypt_ok_extQ` on `tripleRatchetProgAt img.base C ctl abs` (`ext := tripleRatchetExterns C ctl abs`),
for every `Q`. -/
theorem segDecrypt_ok {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {abs : String → Option (State → State)} :
    SegDecryptSpec Q img C A ctl uuidTryParse S abs :=
  fun hloads hhooks htry hset hdrop hgrow hclosure x G₁ R s0 s hQ =>
    segDecrypt_ok_extQ hloads (Stage2Contracts.of_tripleRatchetProgAt' hhooks) htry
      hset hdrop hgrow hclosure x G₁ R s0 s hQ

/-! ## Relocatable `[LibsignalPlacement]` `segDecrypt_placed_ok` -/

theorem seg_of_sepWPp_JF_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {target : BitVec 64} {P : SepProp}
    (hm : s.mem ⊨ P ∗ R)
    (hL : ((blkPC_197).rebase (blkPl_197).base H).CodeLoaded s.mem)
    (hwp : SepWPp ((blkPC_197).rebase (blkPl_197).base H) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        JStatePlaced C A ctl uuidTryParse S x R s0 sf ∨ FStatePlaced C A ctl uuidTryParse S x R s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (recordDecryptPlacedSpec C A ctl uuidTryParse S).onPanic x s0 sf ∗ R))) :
    ∃ s', Steps ((blkPC_197).rebase (blkPl_197).base H) s s' ∧
      (JStatePlaced C A ctl uuidTryParse S x R s0 s' ∨ FStatePlaced C A ctl uuidTryParse S x R s0 s' ∨
        regionOutcome (recordDecryptPlacedSpec C A ctl uuidTryParse S) recExitPlaced x R s0 s') := by
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hJF⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩
  · rcases hJF hmf with hJ | hF
    · exact ⟨sf, hsteps, Or.inl hJ⟩
    · exact ⟨sf, hsteps, Or.inr (Or.inl hF)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hpan, hqp hmf⟩))⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem segDecrypt_placed_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)} :
    SegDecryptPlacedSpec C A ctl uuidTryParse S H := by
  intro hmemcpy_sat htry_rel hset_rel hdrop_rel hgrow_rel hclosure_rel x G₁ R s0 s hV hsp_bound hL
  rcases hV with ⟨hpc, ⟨hrun, hsp, hsp_align, hx29, htr, hfl, hvregs⟩,
    ⟨hrem_ne, hseeds, hrc_len⟩, hclone, heq, hmem⟩
  dsimp only [recVPCPlaced] at hpc
  have hmemcpy_rel := ls_hook_ok_226 (by decide) hmemcpy_sat
  have hsp0 : s0.sp = s.sp := hsp.symm
  clear hsp
  rw [hsp0] at hsp_bound hmem
  unfold recFramePlaced at hmem
  simp only [← sepConj_assoc] at hmem
  apply seg_of_sepWPp_JF_placed hmem hL
    (target := decryptTarget (blkPl_197).base ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).1)
  apply segDecrypt_of_sepWP_placed hfl (mid := lsmpl.base 131)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF1
  have hsp_bound1 : rootStack ≤
      ((((((((s.writeReg64 (Reg.gpr 2#5) x.remA).writeReg64
              (Reg.gpr 3#5) x.locA).writeReg64
            (Reg.gpr 4#5) x.msgA).writeReg64
          (Reg.gpr 0#5) (s.sp + 1200#64)).writeReg64
        (Reg.gpr 1#5) (s.sp + 3232#64)).writeReg64
      (Reg.gpr 5#5) 2#64).writeReg64
    (Reg.gpr 6#5) 0#64).writeReg64 (Reg.gpr 30#5) ((blkPl_197).base + bv% (1720)) |>.setPC
      (lsmpl.base 131)).sp.toNat := hsp_bound
  segDecrypt_wpp_call_placed htry_rel
    ({ ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
       rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
       msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
       cur := x.cur, rest := x.rest : TryDecryptGhost }) hF1
    (tryDecrypt_onPanic_entails heq (by simp only [wp_norm, arm64_norm, htr]))
  apply SepWPp.exists_elim
  intro G₂
  apply SepWPp.pure_elim
  rintro ⟨⟨hnpan, htr_sf⟩, hdec⟩
  have hmk :
      ({ ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
         rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
         msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
         cur := x.cur, rest := x.rest : TryDecryptGhost }) = mkTryDecryptGhost s.sp x G₁ := rfl
  rw [hmk] at hnpan hdec ⊢
  rcases hres : ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).1 with e | pt
  · -- Error branch
    dsimp only [decryptTarget, vecResultAt]
    have he_npan : e ≠ .panic := fun h => hnpan (h ▸ hres)
    cases hdup : isDupErr e
    · -- Non-duplicate error -> FStatePlaced
      have htag_ne23 : speTag e ≠ speWord 23 := speTag_ne_speWord23_of_not_isDupErr hdup
      have hmodel_err : x.model C S uuidTryParse =
          (.error (.invalidMessage .whisper .decryptionFailed), x.st) := by
        rw [model_err_of_tryDecrypt_err C S s.sp x G₁ heq (Prod.ext hres rfl),
          recordError_of_speTag_ne_speWord23 he_npan htag_ne23]
      have hmodel_err1 : (x.model C S uuidTryParse).1 =
          .error (.invalidMessage .whisper .decryptionFailed) := congrArg Prod.fst hmodel_err
      have htag_add2 : speTag e + 2#64 ≠ 0#64 := speTag_add2_ne_zero he_npan
      have htag_ne23' : speTag e ≠ 9223372036854775831#64 := htag_ne23
      apply segDecrypt_of_sepWP_placed hF_sf (mid := lsmpl.base 159)
      refine segDecrypt_replace_pre
        (speAt_decomp6 A (utf8 "decrypt") (s.sp + 1200#64) e he_npan) (by sep_focus) ?_
      rw [memRegion_5f0_split_b40 s.sp, memRegion48_eq_words6At (s.sp + 2880#64),
        stackAt_root_split_closure s.sp, errsAt_nil_unfold A s.sp]
      unfold words6At
      segDecrypt_wp_extract_exists
      rename_i u0 u1 u2 u3 u4 u5 w1 w2 w3 w4 w5 H_spe hreassemble
      generalize htag_def : speTag e = tag at htag_add2 htag_ne23' hreassemble ⊢
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF2
      segDecrypt_wpp_call_placed hclosure_rel () hF2 noPanic_onPanic_entails
      apply segDecrypt_of_sepWP_placed hF_sf_1 (mid := lsmpl.base 42)
      segDecrypt_wp_extract_exists
      rename_i htr_cl
      rw [hsp_sf]
      refine segDecrypt_replace_pre (closureStack_to_growStack s.sp) (by sep_focus) ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF3
      segDecrypt_wpp_call_placed hgrow_rel (s.sp + 0x5d8#64, 0#64, 8#64, []) hF3
        (grow_onPanic_entails (by simp only [wp_norm, arm64_norm, htr_cl, htr_sf, htr]))
      apply segDecrypt_of_sepWP_placed hF_sf_2 (mid := (blkPl_197).base + 2128#64)
      segDecrypt_wp_extract_exists
      rename_i p' hp'
      rw [memRegion_192_split48 p', memRegion48_eq_words6At p']
      unfold words6At
      segDecrypt_wp_extract_exists
      wp_steps
      rw [hsp_sf_1, hsp_sf]
      refine segDecrypt_replace_pre
        (spe_errsAt_entails A s.sp p' e tag w1 w2 w3 w4 w5 H_spe hp'.2 (hreassemble p'))
        (by sep_focus) ?_
      refine segDecrypt_replace_pre (words6_4b0_to_memRegion s.sp tag w1 w2 w3 w4 w5) (by sep_focus) ?_
      refine segDecrypt_replace_pre (words6_b40_to_memRegion s.sp tag w1 w2 w3 w4 w5) (by sep_focus) ?_
      refine segDecrypt_replace_pre (growStack_to_rootStack s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre
        (sessionStateAt_exists_intro A (s.sp + 3232#64) G₂
          ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2) (by sep_focus) ?_
      refine segDecrypt_replace_pre (tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF4
      apply segDecrypt_of_sepWP_ret_placed hF4
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro _ hmf
      right
      refine ⟨by dsimp only [recFPCPlaced]; wp_norm_lhs, ?_, hmodel_err1, ?_⟩
      · refine ⟨by wp_norm_lhs,
                by simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf, hsp0],
                by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf]; exact hsp_align,
                by simp only [wp_norm, arm64_norm, hcs_sf_2, hcs_sf_1, hcs_sf]; exact hx29,
                by simp only [wp_norm, arm64_norm, hp'.1, htr_cl, htr_sf, htr],
                hF4,
                by simp only [wp_norm, arm64_norm, hvregs_3, hvregs_2, hvregs_1, hvregs]⟩
      · unfold recFramePlaced
        rw [hsp0]
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf
    · -- Duplicate error -> JStatePlaced
      obtain ⟨i, c, rfl⟩ := eq_duplicatedMessage_of_isDupErr hdup
      have hmodel_dup : x.model C S uuidTryParse = (.error (.duplicatedMessage i c), x.st) :=
        model_err_of_tryDecrypt_err C S s.sp x G₁ heq (Prod.ext hres rfl)
      have hmodel_dup1 : (x.model C S uuidTryParse).1 = .error (.duplicatedMessage i c) :=
        congrArg Prod.fst hmodel_dup
      apply segDecrypt_of_sepWP_placed hF_sf (mid := lsmpl.base 139)
      dsimp only [speAt]
      rw [stackAt_root_split_dropLocal2 s.sp]
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF2
      segDecrypt_wpp_call_placed hdrop_rel
        ({ ss := s.sp + 3232#64, G := G₂,
           st := ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 : DropSessionStructureGhost })
        hF2 noPanic_onPanic_entails
      apply segDecrypt_of_sepWP_ret_placed hF_sf_1
      segDecrypt_wp_extract_exists
      rename_i htr_drop
      rw [hsp_sf]
      refine segDecrypt_replace_pre (dropLocal2Stack_to_rootStack s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre (errsAt_nil_exists_intro A s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre (tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF3 hmf
      left
      refine ⟨by dsimp only [recJPCPlaced]; wp_norm_lhs, ?_, by rw [hmodel_dup1]; nofun,
        by simp only [wp_norm, arm64_norm, h_17, hsp0],
        by simp only [wp_norm, arm64_norm, h_18],
        by rw [hmodel_dup1]; dsimp only [recordResultTag, speWord]; wp_norm_lhs, ?_⟩
      · refine ⟨by wp_norm_lhs,
                by simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf, hsp0],
                by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf]; exact hsp_align,
                by simp only [wp_norm, arm64_norm, hcs_sf_1, hcs_sf]; exact hx29,
                by simp only [wp_norm, arm64_norm, htr_drop, htr_sf, htr],
                hF3,
                by simp only [wp_norm, arm64_norm, hvregs_2, hvregs_1, hvregs]⟩
      · unfold recFramePlaced
        rw [hsp0, hmodel_dup1]
        dsimp only [recordResultAt, vecResultAt, speAt]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf
  · -- Ok branch
    dsimp only [decryptTarget, vecResultAt]
    have hmodel_ok : x.model C S uuidTryParse =
        (.ok pt, ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2) :=
      model_ok_of_tryDecrypt_ok C S s.sp x G₁ heq (Prod.ext hres rfl)
    have hmodel_ok1 : (x.model C S uuidTryParse).1 = .ok pt := by rw [hmodel_ok]
    have hmodel_ok2 : (x.model C S uuidTryParse).2 =
        ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 := by rw [hmodel_ok]
    rw [hres] at hdec
    have hrel : x.G.AfterRecordDecrypt G₂ := recordOkRel_of_clone_dec hclone hdec
    apply segDecrypt_of_sepWP_placed hF_sf (mid := lsmpl.ρ "memcpy")
    rw [sessionStateAt_eq_inline_sep_heap A (s.sp + 3232#64) G₂
      ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2,
      memRegion_5f0_split344 s.sp, stackAt_root_split_set s.sp]
    unfold FromRecordCallees.lsLogOff
    segDecrypt_wp_extract_exists
    rename_i bs hbs
    rw [← hbs.1]
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF2
    segDecrypt_wpp_call_placed hmemcpy_rel (s.sp + 1520#64, s.sp + 3232#64, bs) hF2
      noPanic_onPanic_entails
    apply segDecrypt_of_sepWP_placed hF_sf_1 (mid := lsmpl.base 48)
    segDecrypt_wp_extract_exists
    rename_i hmc
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF3
    segDecrypt_wpp_call_placed hset_rel
      ({ record := s.sp + 288#64, src := s.sp + 1520#64,
         cur := some (x.G, x.st), bs := bs : SetSessionStateGhost }) hF3
      noPanic_onPanic_entails
    apply segDecrypt_of_sepWP_ret_placed hF_sf_2
    segDecrypt_wp_extract_exists
    rename_i htr_set
    wp_steps
    rw [hsp_sf_1, hsp_sf]
    refine segDecrypt_replace_pre
      (sessionStateAt_move_bytes_twice A (s.sp + 3232#64) (s.sp + 1520#64) (s.sp + 312#64)
        G₂ ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 hbs.2) (by sep_focus) ?_
    refine segDecrypt_replace_pre (memRegion_5f0_join344 s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre (setStack_to_rootStack s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre
      (sessionStateAt_ok_exists_intro A (s.sp + 312#64) x.G G₂
        ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 hrel) (by sep_focus) ?_
    refine segDecrypt_replace_pre (errsAt_nil_exists_intro A s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre (tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF4 hmf
    left
    refine ⟨by dsimp only [recJPCPlaced]; wp_norm_lhs, ?_, by rw [hmodel_ok1]; nofun,
      by simp only [wp_norm, arm64_norm, h_27, h_17, hsp0],
      by simp only [wp_norm, arm64_norm, h_28, h_18],
      by rw [hmodel_ok1]; dsimp only [recordResultTag, okTagVec]; wp_norm_lhs, ?_⟩
    · refine ⟨by wp_norm_lhs,
              by simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf, hsp0],
              by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf]; exact hsp_align,
              by simp only [wp_norm, arm64_norm, hcs_sf_2, hcs_sf_1, hcs_sf]; exact hx29,
              by simp only [wp_norm, arm64_norm, htr_set, hmc.2, htr_sf, htr],
              hF4,
              by simp only [wp_norm, arm64_norm, hvregs_3, hvregs_2, hvregs_1, hvregs]⟩
    · unfold recFramePlaced FromRecordCallees.lsLogOff
      rw [hsp0, hmodel_ok1, hmodel_ok2]
      dsimp only [recordResultAt, vecResultAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf

end CryptoVerification.LibsignalTripleRatchet.Record
