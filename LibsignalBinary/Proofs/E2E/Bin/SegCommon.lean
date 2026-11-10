/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Bin.OpenSegs
import LibsignalBinary.Proofs.E2E.StoreNew.RoData
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import ProofLib.SepLogic.WPp

/-!
# Shared Segment Helpers for `session_send`, `session_recv`, and `open`
-/

@[expose] public section

namespace CryptoVerification.E2E.Bin

set_option warningAsError false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open Arm64 ProofLib ProofLib.ObjectLoad CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Callee-saved registers `x19..x24`, `x28`, `x29`, and `x30` spilled at `s0.sp - 0x50#64 .. s0.sp`
in both `session_send` and `session_recv` (`s0.sp - 0x38#64` is an unused 8-byte padding slot). -/
def sendRecvSavedRegsAt (s0 : State) : SepProp :=
  ((s0.sp - 0x50#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 0x48#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((s0.sp - 0x40#64) ↦₆₄ s0.readReg64 .x28) ∗ memRegion (s0.sp - 0x38#64) 8 ∗
  ((s0.sp - 0x30#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 0x28#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 0x20#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 0x18#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 .x19)

abbrev sendRecvSavedUninitAt (sp0 : BitVec 64) : SepProp :=
  (∃∗ v0 : BitVec 64, (sp0 - 0x50#64) ↦₆₄ v0) ∗ (∃∗ v1 : BitVec 64, (sp0 - 0x48#64) ↦₆₄ v1) ∗
  (∃∗ v2 : BitVec 64, (sp0 - 0x40#64) ↦₆₄ v2) ∗ memRegion (sp0 - 0x38#64) 8 ∗
  (∃∗ v3 : BitVec 64, (sp0 - 0x30#64) ↦₆₄ v3) ∗ (∃∗ v4 : BitVec 64, (sp0 - 0x28#64) ↦₆₄ v4) ∗
  (∃∗ v5 : BitVec 64, (sp0 - 0x20#64) ↦₆₄ v5) ∗ (∃∗ v6 : BitVec 64, (sp0 - 0x18#64) ↦₆₄ v6) ∗
  (∃∗ v7 : BitVec 64, (sp0 - 0x10#64) ↦₆₄ v7) ∗ (∃∗ v8 : BitVec 64, (sp0 - 0x08#64) ↦₆₄ v8)

theorem anyHeap_absorb_right (P : SepProp) : anyHeap ∗ P ⊢ anyHeap := by
  exact ProofLib.entails_anyHeap _

theorem entails_anyHeap_sepConj (P R : SepProp) : P ∗ R ⊢ anyHeap ∗ R :=
  sepConj_mono_left (entails_anyHeap P)

theorem recordCanonical_length_pos {bs : List (BitVec 8)} {s : Session (List (BitVec 8))}
    (h : RecordCanonical bs s) : 0 < bs.length := by
  rcases h with ⟨rfl, _⟩
  simp only [encodeRecord, CryptoVerification.E2E.Record.encodeRecord,
    CryptoVerification.E2E.Record.msgField, CryptoVerification.E2E.Record.lenField,
    Option.map_some, List.length_append]
  have : 0 < (encodeKey 1 WireType.lengthDelimited).length := by decide
  omega

theorem reg_nz_of_toNat_pos {w : BitVec 64} {n : Nat} (h1 : w.toNat = n) (h2 : 0 < n) :
    (w == 0#64) = false :=
  beq_eq_false_iff_ne.mpr (by bv_omega)

theorem tapeAt_entails_tapeAfter (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    tapeAt ctl cur rest ⊢ ∃∗ draws : Nat, tapeAfter ctl cur rest draws := by
  refine Entails.sepExists_right 0 ?_
  dsimp only [tapeAfter, tapeAt]
  refine Entails.pure_left fun _ => ?_
  simp only [Nat.sub_zero, BitVec.add_zero]
  exact Entails.refl _

theorem spAligned_of_sp_eq {s1 s2 : State} (hal : s1.spAligned = true) (hsp : s2.sp = s1.sp) :
    s2.spAligned = true := by
  unfold State.spAligned at hal ⊢; rw [hsp]; exact hal

theorem sepWP_to_segExit {α : Type} {prog : Program} {spec : Spec α} {g : α} {R : SepProp}
    {s0 s : State} {next : State → Prop} {target_pc : BitVec 64} {P F : SepProp}
    {post : State → SepProp → Prop} (hpre : s.mem ⊨ P ∗ F) (hwp : SepWP prog target_pc s P post)
    (hpost : ∀ sf P_f, Steps prog s sf → sf.pc = target_pc → sf.status = .Running →
      sf.mem ⊨ P_f ∗ F → post sf P_f → next sf ∨ SubroutineOutcome spec g R s0 sf) :
    SegExit prog spec g R s0 s next := by
  intro hL
  obtain ⟨sf, hsteps, ⟨hpc, hrunf, P_f, hmf, hpostf⟩ | ⟨_, hoom⟩⟩ := SepWP.elim hwp hpre hL
  · exact ⟨sf, hsteps, hpost sf P_f hsteps hpc hrunf hmf hpostf⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem segExit_trans {α : Type} {prog : Program} {spec : Spec α} {g : α} {R : SepProp}
    {s0 s : State} {mid next : State → Prop}
    (h1 : SegExit prog spec g R s0 s mid) (h2 : ∀ s', mid s' → SegExit prog spec g R s0 s' next) :
    SegExit prog spec g R s0 s next := by
  intro hL
  obtain ⟨s1, hst1, hmid | hout⟩ := h1 hL
  · obtain ⟨s2, hst2, hnext⟩ := h2 s1 hmid (hst1.codeLoaded hL)
    exact ⟨s2, Steps.trans hst1 hst2, hnext⟩
  · exact ⟨s1, hst1, Or.inr hout⟩

theorem segExit_of_subroutine_ok {α β : Type} {prog : Program} {spec : Spec α} {g : α} {R : SepProp}
    {calleeEntry : BitVec 64} {calleeSpec : Spec β} {gc : β} {Rc : SepProp}
    {s0 s1 : State} {next : State → Prop}
    (hCallee : subroutine_ok prog calleeEntry calleeSpec)
    (hpc : s1.pc = calleeEntry) (hrun : s1.status = .Running) (hal : s1.spAligned = true)
    (hpre : s1.mem ⊨ calleeSpec.pre gc s1 ∗ Rc)
    (hpost : ∀ s2, Steps prog s1 s2 →
      (Returned s1 s2 ∧ CallingConventionPreserved s1 s2 ∧ s2.mem ⊨ calleeSpec.post gc s1 s2 ∗ Rc) →
      next s2 ∨ SubroutineOutcome spec g R s0 s2)
    (hpanic : ∀ s2, s2.status = .Panicked → s2.mem ⊨ calleeSpec.onPanic gc s1 s2 ∗ Rc →
      next s2 ∨ SubroutineOutcome spec g R s0 s2)
    (hexit : ∀ code s2, s2.mem ⊨ calleeSpec.onExit gc code s1 s2 ∗ Rc →
      s2.mem ⊨ spec.onExit g code s0 s2 ∗ R)
    (hoom : ∀ s2, s2.status = .OutOfMemory → s2.mem ⊨ calleeSpec.onOom gc s1 s2 ∗ Rc →
      next s2 ∨ SubroutineOutcome spec g R s0 s2 := by
        intro _ _ h; exact (not_satisfies_false_sepConj h).elim) :
    SegExit prog spec g R s0 s1 next := by
  intro hL
  obtain ⟨s2, hst, hout, -⟩ := hCallee.no_fault_before_outcome gc Rc s1 hpc hrun hpre hal hL
  refine ⟨s2, hst, ?_⟩
  rcases hout with hok | ⟨hpan, hmp⟩ | ⟨code, hex, hme⟩ | ⟨hoom_st, hmo⟩
  · exact hpost s2 hst hok
  · exact hpanic s2 hpan hmp
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨code, hex, hexit code s2 hme⟩)))
  · exact hoom s2 hoom_st hmo

theorem allocFailedIn_of_trace_eq {s0 s1 sf : State} (htr : s1.trace = s0.trace)
    (h : allocFailedIn s1 sf ∧ s1.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  unfold allocFailedIn at h ⊢; rwa [htr] at h

theorem sepWP_to_segExit_tripleRatchetProgAt {α : Type} {C : Crypto} {ctl : BitVec 64}
    {img : Obj.Image} {abs : String → Option (State → State)}
    {spec : Spec α} {g : α} {R : SepProp}
    {s0 s : State} {next : State → Prop} {target_pc : BitVec 64} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hloads : Obj.Loads libsignalSessionImage img) (hpre : s.mem ⊨ P ∗ F)
    (hwp : SepWP (tripleRatchetProgAt img.base C ctl abs) target_pc s P post)
    (hpost : ∀ sf P_f, Steps (tripleRatchetProgAt img.base C ctl abs) s sf →
      sf.pc = target_pc → sf.status = .Running →
      sf.mem ⊨ P_f ∗ F → post sf P_f → next sf ∨ SubroutineOutcome spec g R s0 sf) :
    SegExit (binProg img C ctl abs) spec g R s0 s next := by
  rw [binProg, tripleRatchetProg_eq_tripleRatchetProgAt hloads]; exact sepWP_to_segExit hpre hwp hpost

theorem cap_add_one_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false :=
  beq_eq_false_iff_ne.mpr (by bv_omega)

theorem callAt_head_word {A : RustAlloc} {img : Obj.Image} {callPtr : BitVec 64}
    {role : Role} {sess : Session (List (BitVec 8))} {m : Memory} {F : SepProp}
    (hm : m ⊨ callAt A img callPtr role sess ∗ F) :
    ∃ (w : BitVec 64) (R_call : SepProp),
      (w + 1#64 == 0#64) = false ∧ m ⊨ (callPtr ↦₆₄ w) ∗ (R_call ∗ F) ∧
      ((callPtr ↦₆₄ w) ∗ R_call ⊢ callAt A img callPtr role sess) := by
  dsimp only [callAt] at hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨gMe, hm⟩ := hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨gPeer, hm⟩ := hm
  let R_me : SepProp :=
    ((callPtr + 8#64) ↦₆₄ gMe.name.ptr) ∗ ((callPtr + 16#64) ↦₆₄ BitVec.ofNat 64 gMe.name.bytes.length) ∗
    ⌜gMe.name.bytes.length ≤ gMe.name.cap.toNat ∧ gMe.name.cap.toNat < 2 ^ 63 ∧ gMe.name.ptr ≠ 0#64⌝ ∗
    (if gMe.name.cap = 0#64 then emp
     else A.live gMe.name.ptr gMe.name.cap.toNat 1 ∗ (gMe.name.ptr ↦ₛ gMe.name.bytes) ∗
       memRegion (gMe.name.ptr + BitVec.ofNat 64 gMe.name.bytes.length) (gMe.name.cap.toNat - gMe.name.bytes.length)) ∗
    ((callPtr + asm64% addrDeviceOff) ↦₈ gMe.device) ∗
    memRegion (callPtr + asm64% (addrDeviceOff + 1)) (asm% (protocolAddressSize - (addrDeviceOff + 1)))
  have hvec : protocolAddressAt A gMe callPtr = (callPtr ↦₆₄ gMe.name.cap) ∗ R_me := by
    dsimp only [protocolAddressAt, vecGhostAt, vecU8At, vecHeader, R_me]; ac_rfl
  let R_call : SepProp :=
    ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
      gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36⌝ ∗ R_me ∗
    protocolAddressAt A gPeer (callPtr + 0x20#64) ∗
    inMemSessionStoreAt A img (callPtr + 0x40#64) role.peer (some sess) ∗
    inMemIdentityStoreAt A img (callPtr + 0x70#64) role (some role.peer.idKey)
  have hm1 : m ⊨ (callPtr ↦₆₄ gMe.name.cap) ∗ (R_call ∗ F) := by
    rw [hvec] at hm; exact Satisfies.of_eq hm (by dsimp only [R_call]; ac_rfl)
  have hcap : gMe.name.cap.toNat < 2 ^ 63 := by
    have hm2 : m ⊨ ⌜gMe.name.bytes.length ≤ gMe.name.cap.toNat ∧ gMe.name.cap.toNat < 2 ^ 63 ∧ gMe.name.ptr ≠ 0#64⌝ ∗
      ((callPtr ↦₆₄ gMe.name.cap) ∗ ((callPtr + 8#64) ↦₆₄ gMe.name.ptr) ∗
       ((callPtr + 16#64) ↦₆₄ BitVec.ofNat 64 gMe.name.bytes.length) ∗
       (if gMe.name.cap = 0#64 then emp
        else A.live gMe.name.ptr gMe.name.cap.toNat 1 ∗ (gMe.name.ptr ↦ₛ gMe.name.bytes) ∗
          memRegion (gMe.name.ptr + BitVec.ofNat 64 gMe.name.bytes.length) (gMe.name.cap.toNat - gMe.name.bytes.length)) ∗
       ((callPtr + asm64% addrDeviceOff) ↦₈ gMe.device) ∗
       memRegion (callPtr + asm64% (addrDeviceOff + 1)) (asm% (protocolAddressSize - (addrDeviceOff + 1))) ∗
       ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
         gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36⌝ ∗
       protocolAddressAt A gPeer (callPtr + 0x20#64) ∗
       inMemSessionStoreAt A img (callPtr + 0x40#64) role.peer (some sess) ∗
       inMemIdentityStoreAt A img (callPtr + 0x70#64) role (some role.peer.idKey) ∗ F) :=
      Satisfies.of_eq hm1 (by dsimp only [R_call, R_me]; ac_rfl)
    rw [satisfies_pure_sepConj] at hm2; exact hm2.1.2.1
  refine ⟨gMe.name.cap, R_call, cap_add_one_beq_zero_false hcap, hm1, ?_⟩
  dsimp only [callAt]
  refine Entails.sepExists_right gMe (Entails.sepExists_right gPeer ?_)
  have h1 : (callPtr ↦₆₄ gMe.name.cap) ∗ R_call =
      ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
        gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36⌝ ∗
      protocolAddressAt A gMe callPtr ∗ protocolAddressAt A gPeer (callPtr + 0x20#64) ∗
      inMemSessionStoreAt A img (callPtr + 0x40#64) role.peer (some sess) ∗
      inMemIdentityStoreAt A img (callPtr + 0x70#64) role (some role.peer.idKey) := by
    rw [hvec]; dsimp only [R_call]; ac_rfl
  rw [h1]; exact Entails.refl _

def words64At : BitVec 64 → List (BitVec 64) → SepProp
  | _, [] => emp
  | a, w :: ws => (a ↦₆₄ w) ∗ words64At (a + 8#64) ws

theorem words64At_append (xs ys : List (BitVec 64)) (a : BitVec 64) :
    words64At a (xs ++ ys) =
      words64At a xs ∗ words64At (a + BitVec.ofNat 64 (8 * xs.length)) ys := by
  induction xs generalizing a with
  | nil => simp [words64At]
  | cons w xs ih =>
    have ha : a + 8#64 + BitVec.ofNat 64 (8 * xs.length) =
        a + BitVec.ofNat 64 (8 * (w :: xs).length) := by
      simp only [List.length_cons]; bv_omega
    simp only [List.cons_append, words64At, ih (a + 8#64), ha, sepConj_assoc]

theorem words64At_entails_memRegion (ws : List (BitVec 64)) (a : BitVec 64)
    (hbound : 8 * ws.length ≤ 2 ^ 64) :
    words64At a ws ⊢ memRegion a (8 * ws.length) := by
  induction ws generalizing a with
  | nil =>
    simp [words64At, ProofLib.memRegion_zero]
    exact Entails.refl _
  | cons w ws ih =>
    simp only [words64At, List.length_cons] at hbound ⊢
    rw [show 8 * (ws.length + 1) = 8 + 8 * ws.length by omega,
        ProofLib.memRegion_split a 8 (8 * ws.length) (by omega), StoreNew.memRegion_eight a]
    exact sepConj_mono (Entails.sepExists_right w (Entails.refl _))
      (ih (a + 8#64) (by omega))

theorem memRegion_eq_exists_words64At (n : Nat) (a : BitVec 64) (hbound : 8 * n ≤ 2 ^ 64) :
    ∀ m R, (m ⊨ memRegion a (8 * n) ∗ R) →
      ∃ ws : List (BitVec 64), ws.length = n ∧ (m ⊨ words64At a ws ∗ R) := by
  induction n generalizing a with
  | zero =>
    intro m R hm
    rw [Nat.mul_zero, ProofLib.memRegion_zero] at hm
    exact ⟨[], rfl, hm⟩
  | succ n ih =>
    intro m R hm
    rw [show 8 * (n + 1) = 8 + 8 * n by omega,
        ProofLib.memRegion_split a 8 (8 * n) (by omega), StoreNew.memRegion_eight a,
        sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hm
    obtain ⟨w, hm⟩ := hm
    have hm1 : m ⊨ memRegion (a + 8#64) (8 * n) ∗ ((a ↦₆₄ w) ∗ R) :=
      Satisfies.of_eq hm (by ac_rfl)
    obtain ⟨ws, hlen, hm2⟩ := ih (a + 8#64) (by omega) m ((a ↦₆₄ w) ∗ R) hm1
    refine ⟨w :: ws, by simp [hlen], ?_⟩
    dsimp only [words64At]
    exact Satisfies.of_eq hm2 (by ac_rfl)

theorem words64At_drop_succ {a : BitVec 64} {i : Nat} {ws : List (BitVec 64)}
    (h : i < ws.length) :
    words64At a (ws.drop i) =
      (a ↦₆₄ ws.getD i 0#64) ∗ words64At (a + 8#64) (ws.drop (i + 1)) := by
  induction i generalizing a ws with
  | zero =>
    cases ws with
    | nil => simp at h
    | cons w ws' => rfl
  | succ i ih =>
    cases ws with
    | nil => simp at h
    | cons w ws' =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at h
      exact ih h

theorem words64At_drop_eq_emp {a : BitVec 64} {i : Nat} {ws : List (BitVec 64)}
    (h : ws.length ≤ i) :
    words64At a (ws.drop i) = emp := by
  rw [List.drop_eq_nil_of_le h, words64At]

theorem words64At_29 (a : BitVec 64) {ws : List (BitVec 64)} (h : ws.length = 29) :
    words64At a ws =
      (a ↦₆₄ ws.getD 0 0#64) ∗ ((a + 0x08#64) ↦₆₄ ws.getD 1 0#64) ∗
      ((a + 0x10#64) ↦₆₄ ws.getD 2 0#64) ∗ ((a + 0x18#64) ↦₆₄ ws.getD 3 0#64) ∗
      ((a + 0x20#64) ↦₆₄ ws.getD 4 0#64) ∗ ((a + 0x28#64) ↦₆₄ ws.getD 5 0#64) ∗
      ((a + 0x30#64) ↦₆₄ ws.getD 6 0#64) ∗ ((a + 0x38#64) ↦₆₄ ws.getD 7 0#64) ∗
      ((a + 0x40#64) ↦₆₄ ws.getD 8 0#64) ∗ ((a + 0x48#64) ↦₆₄ ws.getD 9 0#64) ∗
      ((a + 0x50#64) ↦₆₄ ws.getD 10 0#64) ∗ ((a + 0x58#64) ↦₆₄ ws.getD 11 0#64) ∗
      ((a + 0x60#64) ↦₆₄ ws.getD 12 0#64) ∗ ((a + 0x68#64) ↦₆₄ ws.getD 13 0#64) ∗
      ((a + 0x70#64) ↦₆₄ ws.getD 14 0#64) ∗ ((a + 0x78#64) ↦₆₄ ws.getD 15 0#64) ∗
      ((a + 0x80#64) ↦₆₄ ws.getD 16 0#64) ∗ ((a + 0x88#64) ↦₆₄ ws.getD 17 0#64) ∗
      ((a + 0x90#64) ↦₆₄ ws.getD 18 0#64) ∗ ((a + 0x98#64) ↦₆₄ ws.getD 19 0#64) ∗
      ((a + 0xa0#64) ↦₆₄ ws.getD 20 0#64) ∗ ((a + 0xa8#64) ↦₆₄ ws.getD 21 0#64) ∗
      ((a + 0xb0#64) ↦₆₄ ws.getD 22 0#64) ∗ ((a + 0xb8#64) ↦₆₄ ws.getD 23 0#64) ∗
      ((a + 0xc0#64) ↦₆₄ ws.getD 24 0#64) ∗ ((a + 0xc8#64) ↦₆₄ ws.getD 25 0#64) ∗
      ((a + 0xd0#64) ↦₆₄ ws.getD 26 0#64) ∗ ((a + 0xd8#64) ↦₆₄ ws.getD 27 0#64) ∗
      ((a + 0xe0#64) ↦₆₄ ws.getD 28 0#64) := by
  conv => lhs; rw [← @List.drop_zero _ ws]
  repeat rw [words64At_drop_succ (by omega)]
  rw [words64At_drop_eq_emp (by omega)]
  simp only [sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

theorem word32_memRegion4_detach {a : BitVec 64} {w32 : BitVec 32} {m : Memory} {R : SepProp}
    (hm : m ⊨ (a ↦₃₂ w32) ∗ memRegion (a + 4#64) 4 ∗ R) :
    ∃ w : BitVec 64,
      (m ⊨ (a ↦₆₄ w) ∗ R) ∧
      (∀ d : BitVec 64, (d ↦₆₄ w) ⊢ (d ↦₃₂ w32) ∗ memRegion (d + 4#64) 4) := by
  rw [ProofLib.memRegion_four (a + 4#64)] at hm
  have hm1 : m ⊨ (∃∗ v : BitVec 32, (a + 4#64) ↦₃₂ v) ∗ ((a ↦₃₂ w32) ∗ R) :=
    Satisfies.of_eq hm (by ac_rfl)
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm1
  obtain ⟨hi, hm1⟩ := hm1
  refine ⟨hi ++ w32, ?_, fun d => ?_⟩
  · rw [← pointsTo32_pair a w32 hi]
    exact Satisfies.of_eq hm1 (by ac_rfl)
  · rw [← pointsTo32_pair d w32 hi, ProofLib.memRegion_four (d + 4#64)]
    exact sepConj_mono_right (Entails.sepExists_right hi (Entails.refl _))

theorem byte8_memRegion7_detach {a : BitVec 64} {b : BitVec 8} {m : Memory} {R : SepProp}
    (hm : m ⊨ (a ↦₈ b) ∗ memRegion (a + 1#64) 7 ∗ R) :
    ∃ w : BitVec 64,
      (m ⊨ (a ↦₆₄ w) ∗ R) ∧
      (∀ d : BitVec 64, (d ↦₆₄ w) ⊢ (d ↦₈ b) ∗ memRegion (d + 1#64) 7) := by
  have hsplit : ∀ d : BitVec 64,
      memRegion (d + 1#64) 7 =
        (∃∗ b1 : BitVec 8, (d + 1#64) ↦₈ b1) ∗
        (∃∗ h1 : BitVec 16, (d + 2#64) ↦₁₆ h1) ∗
        (∃∗ hi : BitVec 32, (d + 4#64) ↦₃₂ hi) := by
    intro d
    rw [memRegion_split' (b := d + 1#64) (b' := d + 2#64) (N := 7) (n := 1) (k := 6) (by decide) (by bv_lin) (by decide),
        memRegion_split' (b := d + 2#64) (b' := d + 4#64) (N := 6) (n := 2) (k := 4) (by decide) (by bv_lin) (by decide),
        ProofLib.memRegion_one, ProofLib.memRegion_two, ProofLib.memRegion_four]
  rw [hsplit a] at hm
  have hm1 : m ⊨ (∃∗ b1 : BitVec 8, (a + 1#64) ↦₈ b1) ∗
      ((∃∗ h1 : BitVec 16, (a + 2#64) ↦₁₆ h1) ∗
       (∃∗ hi : BitVec 32, (a + 4#64) ↦₃₂ hi) ∗ (a ↦₈ b) ∗ R) :=
    Satisfies.of_eq hm (by ac_rfl)
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm1; obtain ⟨b1, hm1⟩ := hm1
  have hm2 : m ⊨ (∃∗ h1 : BitVec 16, (a + 2#64) ↦₁₆ h1) ∗
      ((∃∗ hi : BitVec 32, (a + 4#64) ↦₃₂ hi) ∗ (a ↦₈ b) ∗ ((a + 1#64) ↦₈ b1) ∗ R) :=
    Satisfies.of_eq hm1 (by ac_rfl)
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm2; obtain ⟨h1, hm2⟩ := hm2
  have hm3 : m ⊨ (∃∗ hi : BitVec 32, (a + 4#64) ↦₃₂ hi) ∗
      ((a ↦₈ b) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₁₆ h1) ∗ R) :=
    Satisfies.of_eq hm2 (by ac_rfl)
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm3; obtain ⟨hi, hm3⟩ := hm3
  have hmerge : ∀ d : BitVec 64,
      (d ↦₈ b) ∗ ((d + 1#64) ↦₈ b1) ∗ ((d + 2#64) ↦₁₆ h1) ∗ ((d + 4#64) ↦₃₂ hi) =
        (d ↦₆₄ (hi ++ (h1 ++ (b1 ++ b)))) := by
    intro d
    rw [← sepConj_assoc, ← sepConj_assoc, pointsTo8_pair d b b1,
        pointsTo16_pair d (b1 ++ b) h1, pointsTo32_pair d (h1 ++ (b1 ++ b)) hi]
  refine ⟨hi ++ (h1 ++ (b1 ++ b)), ?_, fun d => ?_⟩
  · rw [← hmerge a]
    exact Satisfies.of_eq hm3 (by ac_rfl)
  · rw [← hmerge d, hsplit d]
    exact sepConj_mono_right (sepConj_mono (Entails.sepExists_right b1 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right h1 (Entails.refl _))
        (Entails.sepExists_right hi (Entails.refl _))))

theorem pointsToBytes_eq_words64At (n : Nat) :
    ∀ (bs : List (BitVec 8)), bs.length = 8 * n →
      ∃ ws : List (BitVec 64), ws.length = n ∧ ∀ a : BitVec 64, (a ↦ₛ bs) = words64At a ws := by
  induction n with
  | zero =>
    intro bs hlen
    rw [Nat.mul_zero, List.length_eq_zero_iff] at hlen; subst hlen
    exact ⟨[], rfl, fun a => by rw [pointsToBytes_nil, words64At]⟩
  | succ n ih =>
    intro bs hlen
    have htake : (bs.take 8).length = 8 := by simp [hlen]
    have hdrop : (bs.drop 8).length = 8 * n := by simp [hlen]; omega
    obtain ⟨w, hw⟩ := exists_unpack64_of_length_8 (bs := bs.take 8) htake
    obtain ⟨ws, hws, heq⟩ := ih (bs.drop 8) hdrop
    refine ⟨w :: ws, by simp [hws], fun a => ?_⟩
    conv => lhs; rw [← List.take_append_drop 8 bs]
    rw [pointsToBytes_append]
    have ha : a + BitVec.ofNat 64 (bs.take 8).length = a + 8#64 := by rw [htake]
    rw [ha, heq (a + 8#64), words64At, hw, ← pointsTo64_eq_pointsToBytes]

theorem protocolAddressAt_detach {A : RustAlloc} {g : AddrGhost} {a : BitVec 64}
    {m : Memory} {R : SepProp}
    (hm : m ⊨ protocolAddressAt A g a ∗ R) :
    ∃ (ws : List (BitVec 64)) (H : SepProp),
      ws.length = 4 ∧
      (m ⊨ words64At a ws ∗ H ∗ R) ∧
      (∀ d : BitVec 64, words64At d ws ∗ H ⊢ protocolAddressAt A g d) := by
  let H : SepProp :=
    ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0#64⌝ ∗
    (if g.name.cap = 0#64 then emp
     else A.live g.name.ptr g.name.cap.toNat 1 ∗ (g.name.ptr ↦ₛ g.name.bytes) ∗
       memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length) (g.name.cap.toNat - g.name.bytes.length))
  have hpa : ∀ d : BitVec 64,
      protocolAddressAt A g d =
        (d ↦₆₄ g.name.cap) ∗ ((d + 8#64) ↦₆₄ g.name.ptr) ∗
        ((d + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
        (((d + 24#64) ↦₈ g.device) ∗ memRegion (d + 24#64 + 1#64) 7) ∗ H := by
    intro d
    dsimp only [protocolAddressAt, vecGhostAt, vecU8At, vecHeader, H]
    rw [show d + 24#64 + 1#64 = d + 25#64 by bv_lin]
    ac_rfl
  rw [hpa a] at hm
  have hm1 : m ⊨ ((a + 24#64) ↦₈ g.device) ∗ memRegion (a + 24#64 + 1#64) 7 ∗
      (((a ↦₆₄ g.name.cap) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗ H) ∗ R) :=
    Satisfies.of_eq hm (by ac_rfl)
  obtain ⟨w3, hm2, hw3⟩ := byte8_memRegion7_detach hm1
  refine ⟨[g.name.cap, g.name.ptr, BitVec.ofNat 64 g.name.bytes.length, w3], H, rfl, ?_, ?_⟩
  · dsimp only [words64At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
    exact Satisfies.of_eq hm2 (by ac_rfl)
  · intro d
    dsimp only [words64At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
    rw [hpa d]
    have hsplit :
        ((d ↦₆₄ g.name.cap) ∗ ((d + 8#64) ↦₆₄ g.name.ptr) ∗
         ((d + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗ ((d + 24#64) ↦₆₄ w3)) ∗ H =
        (d ↦₆₄ g.name.cap) ∗ ((d + 8#64) ↦₆₄ g.name.ptr) ∗
        ((d + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
        ((d + 24#64) ↦₆₄ w3) ∗ H := by ac_rfl
    rw [hsplit]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (hw3 (d + 24#64)))))

theorem table4SingleAt_detach {A : RustAlloc} {stride : Nat} {mp k0 k1 : BitVec 64}
    {k : Nat} {peerName : List (BitVec 8)} {peerDev : BitVec 8}
    {entryAt : BitVec 64 → SepProp} {m : Memory} {R : SepProp}
    (hm : m ⊨ InMem.HashbrownBin.table4SingleAt A stride mp k0 k1 k peerName peerDev entryAt ∗ R) :
    ∃ (ws : List (BitVec 64)) (H : SepProp),
      ws.length = 6 ∧
      (m ⊨ words64At mp ws ∗ H ∗ R) ∧
      (∀ d : BitVec 64,
        words64At d ws ∗ H ⊢ InMem.HashbrownBin.table4SingleAt A stride d k0 k1 k peerName peerDev entryAt) := by
  dsimp only [InMem.HashbrownBin.table4SingleAt, InMem.HashbrownBin.table4At] at hm
  let cbs := InMem.HashbrownModel.singleCtrl4 k (InMem.HashbrownModel.h2Tag (InMem.SipHashModel.hashAddrBv k0 k1 peerName peerDev))
  have hm1 : m ⊨ (∃∗ ctrl : BitVec 64,
      ⌜ctrl ≠ 0#64 ∧ ctrl.toNat % 8 = 0 ∧
        4 * stride ≤ ctrl.toNat ∧ ctrl.toNat + 12 < 2 ^ 64 ∧
        ([k].length = 4 → 2#64 = 0#64) ∧
        InMem.HashbrownModel.CtrlMirrorInv 3#64 cbs ∧ InMem.HashbrownModel.FullBucketsInv 3#64 cbs [k]⌝ ∗
      (mp ↦₆₄ ctrl) ∗
      ((mp + asm64% AsmConstants.tableMaskOff) ↦₆₄ 3#64) ∗
      ((mp + asm64% AsmConstants.tableGrowthLeftOff) ↦₆₄ 2#64) ∗
      ((mp + asm64% AsmConstants.tableItemsOff) ↦₆₄ BitVec.ofNat 64 [k].length) ∗
      ((mp + asm64% AsmConstants.tableHasherOff) ↦₆₄ k0) ∗
      ((mp + asm64% AsmConstants.tableHasherOff + 8#64) ↦₆₄ k1) ∗
      A.live (ctrl - BitVec.ofNat 64 (4 * stride))
        (InMem.HashbrownBin.tableAllocSize 4 stride) (asm% AsmConstants.hashbrownTableAlign) ∗
      (ctrl ↦ₛ cbs) ∗
      arrayAt
        (fun i a => if i ∈ [k] then entryAt a else memRegion a stride) stride
        (ctrl - BitVec.ofNat 64 (4 * stride)) (List.range 4).reverse) ∗ (⌜k < 4⌝ ∗ R) :=
    Satisfies.of_eq hm (by dsimp only [cbs]; ac_rfl)
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm1
  obtain ⟨ctrl, hm1⟩ := hm1
  let H : SepProp :=
    ⌜k < 4⌝ ∗
    ⌜ctrl ≠ 0#64 ∧ ctrl.toNat % 8 = 0 ∧
      4 * stride ≤ ctrl.toNat ∧ ctrl.toNat + 12 < 2 ^ 64 ∧
      ([k].length = 4 → 2#64 = 0#64) ∧
      InMem.HashbrownModel.CtrlMirrorInv 3#64 cbs ∧ InMem.HashbrownModel.FullBucketsInv 3#64 cbs [k]⌝ ∗
    A.live (ctrl - BitVec.ofNat 64 (4 * stride))
      (InMem.HashbrownBin.tableAllocSize 4 stride) (asm% AsmConstants.hashbrownTableAlign) ∗
    (ctrl ↦ₛ cbs) ∗
    arrayAt
      (fun i a => if i ∈ [k] then entryAt a else memRegion a stride) stride
      (ctrl - BitVec.ofNat 64 (4 * stride)) (List.range 4).reverse
  refine ⟨[ctrl, 3#64, 2#64, BitVec.ofNat 64 [k].length, k0, k1], H, rfl, ?_, ?_⟩
  · dsimp only [words64At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
    exact Satisfies.of_eq hm1 (by dsimp only [H, cbs]; ac_rfl)
  · intro d
    dsimp only [InMem.HashbrownBin.table4SingleAt, InMem.HashbrownBin.table4At, words64At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
    rw [sepExists_sepConj_right]
    refine Entails.sepExists_right ctrl ?_
    exact Entails.of_eq (by dsimp only [H, cbs]; ac_rfl)

theorem inMemSessionStoreAt_detach {A : RustAlloc} {img : Obj.Image} {mp : BitVec 64}
    {peer : Role} {s : Session (List (BitVec 8))} {m : Memory} {R : SepProp}
    (hm : m ⊨ inMemSessionStoreAt A img mp peer (some s) ∗ R) :
    ∃ (ws : List (BitVec 64)) (H : SepProp),
      ws.length = 6 ∧
      (m ⊨ words64At mp ws ∗ H ∗ R) ∧
      (∀ d : BitVec 64, words64At d ws ∗ H ⊢ inMemSessionStoreAt A img d peer (some s)) := by
  dsimp only [inMemSessionStoreAt] at hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨k0, hm⟩ := hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨k1, hm⟩ := hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨idx, hm⟩ := hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨gAddr, hm⟩ := hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨G, hm⟩ := hm
  let entryAt : BitVec 64 → SepProp := fun a =>
    protocolAddressAt A gAddr a ∗
    sessionRecordAt A (a + asm64% InMem.HashbrownBin.sessionBucketValueOff) ⟨0#64, 8#64, some G⟩ ⟨some s⟩
  have hm1 : m ⊨ InMem.HashbrownBin.table4SingleAt A InMem.HashbrownBin.sessionBucketStride mp k0 k1 idx peer.nameBytes 1#8 entryAt ∗
      (⌜gAddr.val = peer.addrVal ∧ BinCanonSession G s⌝ ∗ R) :=
    Satisfies.of_eq hm (by dsimp only [entryAt]; ac_rfl)
  obtain ⟨ws, H_tbl, hlen, hm2, htbl⟩ := table4SingleAt_detach hm1
  refine ⟨ws, ⌜gAddr.val = peer.addrVal ∧ BinCanonSession G s⌝ ∗ H_tbl, hlen,
    Satisfies.of_eq hm2 (by ac_rfl), fun d => ?_⟩
  dsimp only [inMemSessionStoreAt]
  refine Entails.sepExists_right k0 (Entails.sepExists_right k1
    (Entails.sepExists_right idx (Entails.sepExists_right gAddr (Entails.sepExists_right G ?_))))
  rw [show words64At d ws ∗ (⌜gAddr.val = peer.addrVal ∧ BinCanonSession G s⌝ ∗ H_tbl) =
      ⌜gAddr.val = peer.addrVal ∧ BinCanonSession G s⌝ ∗ (words64At d ws ∗ H_tbl) by ac_rfl]
  exact sepConj_mono_right (htbl d)

theorem inMemIdentityStoreAt_detach {A : RustAlloc} {img : Obj.Image} {mp : BitVec 64}
    {me : Role} {ik : IdentityKey} {m : Memory} {R : SepProp}
    (hm : m ⊨ inMemIdentityStoreAt A img mp me (some ik) ∗ R) :
    ∃ (ws : List (BitVec 64)) (H : SepProp),
      ws.length = 15 ∧
      (m ⊨ words64At mp ws ∗ H ∗ R) ∧
      (∀ d : BitVec 64, words64At d ws ∗ H ⊢ inMemIdentityStoreAt A img d me (some ik)) := by
  dsimp only [inMemIdentityStoreAt] at hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨k0, hm⟩ := hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨k1, hm⟩ := hm
  have hm1 : m ⊨ (∃∗ idx : Nat, ∃∗ gAddr : AddrGhost,
      ⌜gAddr.val = me.peer.addrVal⌝ ∗
      InMem.HashbrownBin.table4SingleAt A InMem.HashbrownBin.identityBucketStride mp k0 k1 idx me.peer.nameBytes 1#8
        (InMem.HashbrownBin.identityBucketEntryAt A gAddr ik.publicKey.bytes.toList)) ∗
      (((mp + 48#64) ↦ₛ me.keyPairBytes) ∗ ((mp + 112#64) ↦₃₂ 0#32) ∗ memRegion (mp + 116#64) 4 ∗ R) :=
    Satisfies.of_eq hm (by ac_rfl)
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm1; obtain ⟨idx, hm1⟩ := hm1
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm1; obtain ⟨gAddr, hm1⟩ := hm1
  have hm2 : m ⊨ InMem.HashbrownBin.table4SingleAt A InMem.HashbrownBin.identityBucketStride mp k0 k1 idx me.peer.nameBytes 1#8
      (InMem.HashbrownBin.identityBucketEntryAt A gAddr ik.publicKey.bytes.toList) ∗
      (⌜gAddr.val = me.peer.addrVal⌝ ∗ ((mp + 48#64) ↦ₛ me.keyPairBytes) ∗
       ((mp + 112#64) ↦₃₂ 0#32) ∗ memRegion (mp + 116#64) 4 ∗ R) :=
    Satisfies.of_eq hm1 (by ac_rfl)
  obtain ⟨ws0, H_tbl, hlen0, hm3, htbl⟩ := table4SingleAt_detach hm2
  have hkp_len : me.keyPairBytes.length = 8 * 8 := by cases me <;> decide
  obtain ⟨ws1, hlen1, hkp_eq⟩ := pointsToBytes_eq_words64At 8 me.keyPairBytes hkp_len
  have hm4 : m ⊨ ((mp + 112#64) ↦₃₂ 0#32) ∗ memRegion (mp + 112#64 + 4#64) 4 ∗
      (words64At mp ws0 ∗ ((mp + 48#64) ↦ₛ me.keyPairBytes) ∗ ⌜gAddr.val = me.peer.addrVal⌝ ∗ H_tbl ∗ R) := by
    rw [show mp + 112#64 + 4#64 = mp + 116#64 by bv_lin]
    exact Satisfies.of_eq hm3 (by ac_rfl)
  obtain ⟨w_last, hm5, hw_last⟩ := word32_memRegion4_detach hm4
  have hcomb : ∀ d : BitVec 64,
      words64At d (ws0 ++ (ws1 ++ [w_last])) =
        words64At d ws0 ∗ ((d + 48#64) ↦ₛ me.keyPairBytes) ∗ ((d + 112#64) ↦₆₄ w_last) := by
    intro d
    rw [words64At_append ws0 (ws1 ++ [w_last]) d,
        words64At_append ws1 [w_last] (d + BitVec.ofNat 64 (8 * ws0.length)),
        hlen0, hlen1,
        show d + BitVec.ofNat 64 (8 * 6) = d + 48#64 by bv_lin,
        show d + 48#64 + BitVec.ofNat 64 (8 * 8) = d + 112#64 by bv_lin,
        ← hkp_eq (d + 48#64)]
    dsimp only [words64At]
    simp only [sepConj_emp]
  refine ⟨ws0 ++ (ws1 ++ [w_last]), ⌜gAddr.val = me.peer.addrVal⌝ ∗ H_tbl,
    by simp [hlen0, hlen1], ?_, fun d => ?_⟩
  · rw [hcomb mp]
    exact Satisfies.of_eq hm5 (by ac_rfl)
  · dsimp only [inMemIdentityStoreAt]
    refine Entails.sepExists_right k0 (Entails.sepExists_right k1 ?_)
    rw [hcomb d,
        show (words64At d ws0 ∗ ((d + 48#64) ↦ₛ me.keyPairBytes) ∗ ((d + 112#64) ↦₆₄ w_last)) ∗
          (⌜gAddr.val = me.peer.addrVal⌝ ∗ H_tbl) =
          ((d + 48#64) ↦ₛ me.keyPairBytes) ∗ (((d + 112#64) ↦₆₄ w_last) ∗
          (⌜gAddr.val = me.peer.addrVal⌝ ∗ (words64At d ws0 ∗ H_tbl))) by ac_rfl,
        show ((d + 48#64) ↦ₛ me.keyPairBytes) ∗ ((d + 112#64) ↦₃₂ 0#32) ∗ memRegion (d + 116#64) 4 ∗
          (∃∗ idx : Nat, ∃∗ gAddr : AddrGhost,
            ⌜gAddr.val = me.peer.addrVal⌝ ∗
            InMem.HashbrownBin.table4SingleAt A InMem.HashbrownBin.identityBucketStride d k0 k1 idx me.peer.nameBytes 1#8
              (InMem.HashbrownBin.identityBucketEntryAt A gAddr ik.publicKey.bytes.toList)) =
          ((d + 48#64) ↦ₛ me.keyPairBytes) ∗
          ((((d + 112#64) ↦₃₂ 0#32) ∗ memRegion (d + 112#64 + 4#64) 4) ∗
           (∃∗ idx : Nat, ∃∗ gAddr : AddrGhost,
             ⌜gAddr.val = me.peer.addrVal⌝ ∗
             InMem.HashbrownBin.table4SingleAt A InMem.HashbrownBin.identityBucketStride d k0 k1 idx me.peer.nameBytes 1#8
               (InMem.HashbrownBin.identityBucketEntryAt A gAddr ik.publicKey.bytes.toList))) by
          rw [show d + 112#64 + 4#64 = d + 116#64 by bv_lin]; ac_rfl]
    refine sepConj_mono_right (sepConj_mono (hw_last (d + 112#64)) ?_)
    refine Entails.sepExists_right idx (Entails.sepExists_right gAddr ?_)
    exact sepConj_mono_right (htbl d)

theorem callAt_detach {A : RustAlloc} {img : Obj.Image} {ptr : BitVec 64}
    {role : Role} {s : Session (List (BitVec 8))} {m : Memory} {R : SepProp}
    (hm : m ⊨ callAt A img ptr role s ∗ R) :
    ∃ (bws : List (BitVec 64)) (H : SepProp),
      bws.length = 29 ∧
      (m ⊨ words64At ptr bws ∗ H ∗ R) ∧
      (∀ d : BitVec 64, words64At d bws ∗ H ⊢ callAt A img d role s) := by
  dsimp only [callAt] at hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨gMe, hm⟩ := hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨gPeer, hm⟩ := hm
  have hm1 : m ⊨ protocolAddressAt A gMe ptr ∗
      (protocolAddressAt A gPeer (ptr + 0x20#64) ∗
       inMemSessionStoreAt A img (ptr + 0x40#64) role.peer (some s) ∗
       inMemIdentityStoreAt A img (ptr + 0x70#64) role (some role.peer.idKey) ∗
       ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
         gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36⌝ ∗ R) :=
    Satisfies.of_eq hm (by ac_rfl)
  obtain ⟨ws0, H0, hlen0, hm2, h0⟩ := protocolAddressAt_detach hm1
  have hm3 : m ⊨ protocolAddressAt A gPeer (ptr + 0x20#64) ∗
      (inMemSessionStoreAt A img (ptr + 0x40#64) role.peer (some s) ∗
       inMemIdentityStoreAt A img (ptr + 0x70#64) role (some role.peer.idKey) ∗
       words64At ptr ws0 ∗ H0 ∗
       ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
         gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36⌝ ∗ R) :=
    Satisfies.of_eq hm2 (by ac_rfl)
  obtain ⟨ws1, H1, hlen1, hm4, h1⟩ := protocolAddressAt_detach hm3
  have hm5 : m ⊨ inMemSessionStoreAt A img (ptr + 0x40#64) role.peer (some s) ∗
      (inMemIdentityStoreAt A img (ptr + 0x70#64) role (some role.peer.idKey) ∗
       words64At ptr ws0 ∗ words64At (ptr + 0x20#64) ws1 ∗ H0 ∗ H1 ∗
       ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
         gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36⌝ ∗ R) :=
    Satisfies.of_eq hm4 (by ac_rfl)
  obtain ⟨ws2, H2, hlen2, hm6, h2⟩ := inMemSessionStoreAt_detach hm5
  have hm7 : m ⊨ inMemIdentityStoreAt A img (ptr + 0x70#64) role (some role.peer.idKey) ∗
      (words64At ptr ws0 ∗ words64At (ptr + 0x20#64) ws1 ∗
       words64At (ptr + 0x40#64) ws2 ∗ H0 ∗ H1 ∗ H2 ∗
       ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
         gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36⌝ ∗ R) :=
    Satisfies.of_eq hm6 (by ac_rfl)
  obtain ⟨ws3, H3, hlen3, hm8, h3⟩ := inMemIdentityStoreAt_detach hm7
  have hcomb : ∀ d : BitVec 64,
      words64At d (ws0 ++ (ws1 ++ (ws2 ++ ws3))) =
        words64At d ws0 ∗ words64At (d + 0x20#64) ws1 ∗
        words64At (d + 0x40#64) ws2 ∗ words64At (d + 0x70#64) ws3 := by
    intro d
    rw [words64At_append ws0 (ws1 ++ (ws2 ++ ws3)) d,
        words64At_append ws1 (ws2 ++ ws3) (d + BitVec.ofNat 64 (8 * ws0.length)),
        words64At_append ws2 ws3 (d + BitVec.ofNat 64 (8 * ws0.length) + BitVec.ofNat 64 (8 * ws1.length)),
        hlen0, hlen1, hlen2,
        show d + BitVec.ofNat 64 (8 * 4) = d + 0x20#64 by bv_lin,
        show d + 0x20#64 + BitVec.ofNat 64 (8 * 4) = d + 0x40#64 by bv_lin,
        show d + 0x40#64 + BitVec.ofNat 64 (8 * 6) = d + 0x70#64 by bv_lin]
  let H_all : SepProp :=
    ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
      gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36⌝ ∗
    H0 ∗ H1 ∗ H2 ∗ H3
  refine ⟨ws0 ++ (ws1 ++ (ws2 ++ ws3)), H_all, by simp [hlen0, hlen1, hlen2, hlen3], ?_, fun d => ?_⟩
  · rw [hcomb ptr]
    exact Satisfies.of_eq hm8 (by dsimp only [H_all]; ac_rfl)
  · dsimp only [callAt]
    refine Entails.sepExists_right gMe (Entails.sepExists_right gPeer ?_)
    rw [hcomb d,
        show (words64At d ws0 ∗ words64At (d + 0x20#64) ws1 ∗
          words64At (d + 0x40#64) ws2 ∗ words64At (d + 0x70#64) ws3) ∗ H_all =
          ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
            gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36⌝ ∗
          (words64At d ws0 ∗ H0) ∗ (words64At (d + 0x20#64) ws1 ∗ H1) ∗
          (words64At (d + 0x40#64) ws2 ∗ H2) ∗ (words64At (d + 0x70#64) ws3 ∗ H3) by
            dsimp only [H_all]; ac_rfl]
    exact sepConj_mono_right (sepConj_mono (h0 d)
      (sepConj_mono (h1 (d + 0x20#64))
        (sepConj_mono (h2 (d + 0x40#64)) (h3 (d + 0x70#64)))))

theorem pointsToBytes_csinc_ptr {x19 x20 ptPtr : BitVec 64} {bs : List (BitVec 8)}
    (hx19 : x19.toNat = bs.length) (hx20 : x20 = ptPtr) :
    ((if x19 != 0#64 then x20 else 1#64) ↦ₛ bs) = (ptPtr ↦ₛ bs) := by
  cases bs with
  | nil => simp [pointsToBytes_nil]
  | cons b bs' =>
    have hne : (x19 != 0#64) = true := bne_iff_ne.mpr (by simp at hx19; bv_omega)
    simp only [hne, ↓reduceIte, hx20]

protected theorem conditionHolds_hi_addsPState64 (x y : BitVec 64) :
    ConditionHolds .HI (addsPState64 x y) = (BitVec.ult (x + y) x && (x + y != 0#64)) :=
  ProofLib.conditionHolds_hi_addsPState64 x y

theorem pointsToBytes_entails_memRegion (a : BitVec 64) (bs : List (BitVec 8)) (n : Nat)
    (hlen : bs.length = n) (hn : n ≤ 2 ^ 64) :
    (a ↦ₛ bs) ⊢ memRegion a n :=
  let _ := hn; hlen ▸ ProofLib.pointsToBytes_entails_memRegion a bs

theorem sessionRecordAt_detach (A : RustAlloc) (r : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) :
    sessionRecordAt A r ⟨0#64, 8#64, some G⟩ ⟨some sess⟩ ⊢ memRegion r 0x170 ∗ anyHeap := by
  rw [sessionRecordAt_eq_word0_sep_tail_sep_heap A r G sess]
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; rintro ⟨hlen, _⟩
  have htail : (unpack64 8#64 ++ unpack64 0#64 ++ bs).length = 360 := by
    simp [hlen]
  have h0 := pointsTo64_entails_memRegion r 0#64
  have h1 := pointsToBytes_entails_memRegion (r + 8#64) (unpack64 8#64 ++ unpack64 0#64 ++ bs) 360
    htail (by decide)
  have h2 := entails_anyHeap (sessionRecordHeap A G sess)
  rw [memRegion_split' (b := r) (b' := r + 8#64) (N := 0x170) (n := 8) (k := 360)
        (by decide) rfl (by decide),
      sepConj_assoc]
  exact sepConj_mono h0 (sepConj_mono h1 h2)

theorem encodeVarintAux_length_le :
    ∀ (k : Nat) (v : BitVec 64), (encodeVarintAux k v).length ≤ k
  | 0, _ => by simp [encodeVarintAux]
  | k + 1, v => by
    unfold encodeVarintAux
    split
    · simp
    · have ih := encodeVarintAux_length_le k (v >>> 7)
      simp only [List.length_cons]
      omega

theorem encodeRecord_some_length_bounds {G : SessionGhost} {s : Session (List (BitVec 8))}
    (hG : BinCanonSession G s) :
    0 < (encodeRecord ⟨some s⟩).length ∧ (encodeRecord ⟨some s⟩).length < 11 + 2 ^ 62 := by
  have hs_len : (encodeSession s).length < 2 ^ 62 := hG.2.2.2.2.2.2.2.2.2.2.2
  have hvar_le : (encodeVarint (BitVec.ofNat 64 (encodeSession s).length)).length ≤ 10 :=
    encodeVarintAux_length_le 10 _
  have hkey_len : (encodeKey 1 .lengthDelimited).length = 1 := by decide
  change 0 < (Record.lenField 1 (encodeSession s)).length ∧
    (Record.lenField 1 (encodeSession s)).length < 11 + 2 ^ 62
  unfold Record.lenField
  simp only [List.length_append, hkey_len]
  omega

theorem tbnz_bit63_of_lt {x : BitVec 64} (h : x.toNat < 2 ^ 63) :
    ((x >>> 63#64) &&& 1#64 == 0#64) = true ∧
    x.getLsbD 63 = false := by
  have h1 : (x >>> 63#64) &&& 1#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    change (x >>> 63#64).toNat &&& 1 = 0
    have hshr : (x >>> 63#64).toNat = x.toNat / 2 ^ 63 := by
      change (x.toNat >>> (63#64).toNat) = x.toNat / 2 ^ 63
      exact Nat.shiftRight_eq_div_pow x.toNat 63
    rw [hshr, Nat.div_eq_of_lt h]
    rfl
  refine ⟨by rw [h1]; rfl, ?_⟩
  rw [BitVec.getLsbD_eq_getElem (by decide)]
  change x.toNat.testBit 63 = false
  exact Nat.testBit_lt_two_pow h

theorem memRegion_pack_split (ptr : BitVec 64) (ls lm : Nat)
    (htot : 16 + ls + lm < 2 ^ 63) :
    memRegion ptr (16 + ls + lm) =
      (∃∗ u0 : BitVec 64, ptr ↦₆₄ u0) ∗
      (∃∗ u1 : BitVec 64, (ptr + 8#64) ↦₆₄ u1) ∗
      memRegion (ptr + 16#64) ls ∗
      memRegion (ptr + BitVec.ofNat 64 (16 + ls)) lm := by
  rw [memRegion_split' (b := ptr) (b' := ptr + 8#64) (N := 16 + ls + lm) (n := 8) (k := 8 + ls + lm)
        (by omega) rfl (by omega),
      memRegion_split' (b := ptr + 8#64) (b' := ptr + 16#64) (N := 8 + ls + lm) (n := 8) (k := ls + lm)
        (by omega) (by bv_lin) (by omega),
      memRegion_split' (b := ptr + 16#64) (b' := ptr + BitVec.ofNat 64 (16 + ls)) (N := ls + lm) (n := ls) (k := lm)
        (by omega) (by rw [BitVec.ofNat_add, BitVec.add_assoc]) (by omega),
      ProofLib.memRegion_eight ptr,
      ProofLib.memRegion_eight (ptr + 8#64)]

theorem packedOutAt_intro (A : RustAlloc) (ptr : BitVec 64)
    (stateBytes msgBytes : List (BitVec 8))
    (hptr : ptr ≠ 0#64)
    (htot : 16 + stateBytes.length + msgBytes.length < 2 ^ 63) :
    A.live ptr (16 + stateBytes.length + msgBytes.length) 1 ∗
    (ptr ↦₆₄ BitVec.ofNat 64 stateBytes.length) ∗
    ((ptr + 8#64) ↦₆₄ BitVec.ofNat 64 msgBytes.length) ∗
    ((ptr + 16#64) ↦ₛ stateBytes) ∗
    ((ptr + BitVec.ofNat 64 (16 + stateBytes.length)) ↦ₛ msgBytes) ⊢
      packedOutAt A ptr stateBytes msgBytes := by
  dsimp only [packedOutAt]
  exact Entails.pure_right ⟨hptr, htot⟩ (Entails.refl _)

theorem packedOutAt_intro_nil (A : RustAlloc) (ptr : BitVec 64)
    (stateBytes : List (BitVec 8))
    (hptr : ptr ≠ 0#64)
    (htot : 16 + stateBytes.length + 0 < 2 ^ 63) :
    A.live ptr (16 + stateBytes.length + 0) 1 ∗
    (ptr ↦₆₄ BitVec.ofNat 64 stateBytes.length) ∗
    ((ptr + 8#64) ↦₆₄ 0#64) ∗
    ((ptr + 16#64) ↦ₛ stateBytes) ⊢
      packedOutAt A ptr stateBytes [] := by
  have h := packedOutAt_intro A ptr stateBytes [] hptr htot
  simpa only [List.length_nil, pointsToBytes_nil, sepConj_emp] using h

theorem layoutOk_pack (ls lm : Nat) (htot : 16 + ls + lm < 2 ^ 63) :
    LayoutOk (16 + ls + lm) 1 :=
  ⟨by omega, ⟨0, rfl⟩, by omega⟩

theorem bv_ofNat_ne_zero_of_pos_lt {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro h
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at h1
  omega

end CryptoVerification.E2E.Bin
