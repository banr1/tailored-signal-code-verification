/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLen
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymA
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymB
public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Base stepping, stack, and slice helpers for `SessionStructure::encode_raw` (`0x4d38`)

Callee offset resolution, 80-byte stack frame splitting (`encodeRawSubStack`), `PanicAllocPost`
composition combinators, `vecU8At` append lemmas, and subroutine call wrappers for
`do_reserve_and_handle`, `encode_varint`, `memcpy`, and `encode::<Chain>`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.Serialization.EncodeRawAux

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Separation-logic focus helpers -/

theorem entails_of_sep_focus {P Q : SepProp} (h : P = Q ∗ emp) : P ⊢ Q :=
  Entails.of_eq (by rw [h, sepConj_emp])

theorem satisfies_of_sep_focus {m : Memory} {P Q : SepProp} (hm : m ⊨ P) (h : P = Q ∗ emp) :
    m ⊨ Q := by
  rwa [h, sepConj_emp] at hm

theorem not_satisfies_false_sepConj2 {m : Memory} {R : SepProp} (h : m ⊨ ⌜False⌝ ∗ R) : False := by
  rw [satisfies_pure_sepConj] at h
  exact h.1

/-! ## Callee offset resolution on `tripleRatchetProgAt` -/

theorem fnAddr_encraw_add_eq {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {target : String} {off : BitVec 64}
    (h : BitVec.ofNat 64 (libsignalSessionCode.fnOff encodeRawName) + off =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff target) := by
      fnoff_eq) :
    (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + off =
      (tripleRatchetProgAt b C ctl abs).fnAddr target := by
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, BitVec.add_assoc, h]

theorem encraw_encodeVarint_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hEV : Prost.EncodeVarintOk b C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      (encodeVarintSpec A) := by
  rw [fnAddr_encraw_add_eq (target := encodeVarintName)]
  exact hEV

theorem encraw_doReserve_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      (doReserveSpec A) := by
  rw [fnAddr_encraw_add_eq (target := doReserveName)]
  exact hDR

theorem encraw_encodeChain_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hEC : OkAt b C ctl abs encodeChainName (encodeChainSpec A)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      (encodeChainSpec A) := by
  rw [fnAddr_encraw_add_eq (target := encodeChainName)]
  exact hEC

theorem encraw_memcpy_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>"))
      framelessMemcpySpec :=
  hook_ok_at_raw (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>") (k := num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")) rfl (by decide)
    (ls_hook% "memcpy") ⟨hookMemcpy, rfl, framelessMemcpy_hookOk⟩

/-! ## Stack frame splitting -/

/-- Callee stack budget below `sp0 - 80#64` inside `encode_raw`. -/
abbrev encodeRawSubStack : Nat :=
  Prost.encodeVarintStack + doReserveStack + encodeChainStack

theorem encraw_stackAt_split_bottom (sp : BitVec 64) (n d : Nat) (h : n + d ≤ 2 ^ 64) :
    stackAt sp (n + d) = memRegion (sp - BitVec.ofNat 64 (n + d)) d ∗ stackAt sp n := by
  simp only [stackAt]
  rw [show n + d = d + n by omega,
    memRegion_split' (n := d) (k := n) (by omega) rfl (by omega)]
  congr 2
  rw [BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 d), ← BitVec.sub_sub,
    BitVec.sub_add_cancel]

theorem encraw_stackAt_split_bottom' (sp : BitVec 64) (N n d : Nat) (hN : N = n + d := by decide)
    (h : n + d ≤ 2 ^ 64 := by decide) :
    stackAt sp N = memRegion (sp - BitVec.ofNat 64 N) d ∗ stackAt sp n :=
  hN ▸ encraw_stackAt_split_bottom sp n d h

theorem encraw_stackAt_split_top (sp : BitVec 64) (n d : Nat) (h : n + d ≤ 2 ^ 64) :
    stackAt sp (n + d) = stackAt (sp - BitVec.ofNat 64 d) n ∗ memRegion (sp - BitVec.ofNat 64 d) d := by
  simp only [stackAt]
  rw [memRegion_split' (n := n) (k := d) rfl rfl h]
  have e1 : sp - BitVec.ofNat 64 (n + d) = sp - BitVec.ofNat 64 d - BitVec.ofNat 64 n := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
  have e2 : sp - BitVec.ofNat 64 (n + d) + BitVec.ofNat 64 n = sp - BitVec.ofNat 64 d := by
    rw [e1, BitVec.sub_add_cancel]
  rw [e2, e1]

/-- Saved registers and scratch slot in the 80-byte frame of `encode_raw`. -/
def encRawSavedRegs (sp0 : BitVec 64) (s0 : State) (v56 : BitVec 64) : SepProp :=
  ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp0 - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp0 - 56#64) ↦₆₄ v56) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

theorem stackAt_encodeRawStack_split (sp0 : BitVec 64) :
    stackAt sp0 encodeRawStack =
      stackAt (sp0 - 80#64) encodeRawSubStack ∗
      cells (sp0 - 80#64) 10 := by
  have htop := encraw_stackAt_split_top sp0 encodeRawSubStack 80 (by decide)
  change stackAt sp0 encodeRawStack =
    stackAt (sp0 - 80#64) encodeRawSubStack ∗ memRegion (sp0 - 80#64) 80 at htop
  rw [htop, show (80 : Nat) = 8 * 10 by rfl,
      LibsignalTripleRatchet.memRegion_cells (sp0 - 80#64) 10 (by decide)]

theorem stackAt_encodeRawStack_unfold (sp0 : BitVec 64) :
    stackAt sp0 encodeRawStack =
      ∃∗ v80 : BitVec 64, ∃∗ v72 : BitVec 64, ∃∗ v64 : BitVec 64,
      ∃∗ v56 : BitVec 64, ∃∗ v48 : BitVec 64, ∃∗ v40 : BitVec 64,
      ∃∗ v32 : BitVec 64, ∃∗ v24 : BitVec 64, ∃∗ v16 : BitVec 64,
      ∃∗ v8 : BitVec 64,
        ((sp0 - 80#64) ↦₆₄ v80) ∗ ((sp0 - 72#64) ↦₆₄ v72) ∗
        ((sp0 - 64#64) ↦₆₄ v64) ∗ ((sp0 - 56#64) ↦₆₄ v56) ∗
        ((sp0 - 48#64) ↦₆₄ v48) ∗ ((sp0 - 40#64) ↦₆₄ v40) ∗
        ((sp0 - 32#64) ↦₆₄ v32) ∗ ((sp0 - 24#64) ↦₆₄ v24) ∗
        ((sp0 - 16#64) ↦₆₄ v16) ∗ ((sp0 - 8#64) ↦₆₄ v8) ∗
        stackAt (sp0 - 80#64) encodeRawSubStack := by
  rw [stackAt_encodeRawStack_split sp0, sepConj_comm]
  simp only [cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    show sp0 - 80#64 + 8#64 = sp0 - 72#64 by bv_lin,
    show sp0 - 72#64 + 8#64 = sp0 - 64#64 by bv_lin,
    show sp0 - 64#64 + 8#64 = sp0 - 56#64 by bv_lin,
    show sp0 - 56#64 + 8#64 = sp0 - 48#64 by bv_lin,
    show sp0 - 48#64 + 8#64 = sp0 - 40#64 by bv_lin,
    show sp0 - 40#64 + 8#64 = sp0 - 32#64 by bv_lin,
    show sp0 - 32#64 + 8#64 = sp0 - 24#64 by bv_lin,
    show sp0 - 24#64 + 8#64 = sp0 - 16#64 by bv_lin,
    show sp0 - 16#64 + 8#64 = sp0 - 8#64 by bv_lin,
    sepConj_assoc]

theorem encRawSavedRegs_entails_frame (sp0 : BitVec 64) (s0 : State) (v56 : BitVec 64) :
    stackAt (sp0 - 80#64) encodeRawSubStack ∗ encRawSavedRegs sp0 s0 v56 ⊢
      stackAt sp0 encodeRawStack := by
  rw [stackAt_encodeRawStack_split sp0]
  unfold encRawSavedRegs
  simp only [cells, sepConj_emp, ← sepExists_sepConj_left,
    show sp0 - 80#64 + 8#64 = sp0 - 72#64 by bv_lin,
    show sp0 - 72#64 + 8#64 = sp0 - 64#64 by bv_lin,
    show sp0 - 64#64 + 8#64 = sp0 - 56#64 by bv_lin,
    show sp0 - 56#64 + 8#64 = sp0 - 48#64 by bv_lin,
    show sp0 - 48#64 + 8#64 = sp0 - 40#64 by bv_lin,
    show sp0 - 40#64 + 8#64 = sp0 - 32#64 by bv_lin,
    show sp0 - 32#64 + 8#64 = sp0 - 24#64 by bv_lin,
    show sp0 - 24#64 + 8#64 = sp0 - 16#64 by bv_lin,
    show sp0 - 16#64 + 8#64 = sp0 - 8#64 by bv_lin]
  refine sepConj_mono_right ?_
  refine sepConj_mono (Entails.sepExists_intro _) ?_
  refine sepConj_mono (Entails.sepExists_intro _) ?_
  refine sepConj_mono (Entails.sepExists_intro _) ?_
  refine sepConj_mono (Entails.sepExists_intro _) ?_
  refine sepConj_mono (Entails.sepExists_intro _) ?_
  refine sepConj_mono (Entails.sepExists_intro _) ?_
  refine sepConj_mono (Entails.sepExists_intro _) ?_
  refine sepConj_mono (Entails.sepExists_intro _) ?_
  refine sepConj_mono (Entails.sepExists_intro _) ?_
  exact Entails.sepExists_intro _

theorem stackAt_sub_to_encodeVarint_er (sp : BitVec 64) :
    stackAt sp encodeRawSubStack =
      memRegion (sp - 17104#64) 12848 ∗ stackAt sp Prost.encodeVarintStack :=
  encraw_stackAt_split_bottom' sp encodeRawSubStack Prost.encodeVarintStack 12848

theorem stackAt_sub_to_doReserve_er (sp : BitVec 64) :
    stackAt sp encodeRawSubStack =
      memRegion (sp - 17104#64) 12896 ∗ stackAt sp doReserveStack :=
  encraw_stackAt_split_bottom' sp encodeRawSubStack doReserveStack 12896

theorem stackAt_sub_to_encodeChain (sp : BitVec 64) :
    stackAt sp encodeRawSubStack =
      memRegion (sp - 17104#64) 8464 ∗ stackAt sp encodeChainStack :=
  encraw_stackAt_split_bottom' sp encodeRawSubStack encodeChainStack 8464

/-! ## `SepWPp` composition with `PanicAllocPost` -/

def PanicAllocPost (s0 : State) : State → SepProp → Prop :=
  fun sf P_f => ∀ R, (sf.mem ⊨ P_f ∗ R) →
    (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)

theorem panicAllocPost_of_eq {s0 sf : State} {P_f : SepProp}
    (h : allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) :
    PanicAllocPost s0 sf P_f :=
  fun _ hm => allowPanic_panicked h hm

theorem encraw_seq_wpp {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P1 F P2 : SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (htr : s.trace = s0.trace)
    (h1 : SepWPp prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2)) (PanicAllocPost s))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φ sm →
      SepWPp prog ret sm (P2 ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨hpan_s, P_m, hmm, hp⟩ | hoom⟩ :=
    h1 (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · have hm' : sm.mem ⊨ (P_m ∗ F) ∗ R := by rw [sepConj_assoc]; exact hmm
    have halloc := hp (F ∗ R) hmm
    rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr] using halloc.1
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_s, P_m ∗ F, hm', hpan sm (P_m ∗ F) halloc0⟩)⟩
  · exact (not_satisfies_false_sepConj hoom.2).elim

theorem encraw_seq_wpp' {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (htr : s.trace = s0.trace)
    (h1 : SepWPp prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)) (PanicAllocPost s))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φ sm →
      SepWPp prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨hpan_s, P_m, hmm, hp⟩ | hoom⟩ :=
    h1 (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · have hm' : sm.mem ⊨ (P_m ∗ F) ∗ R := by rw [sepConj_assoc]; exact hmm
    have halloc := hp (F ∗ R) hmm
    rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr] using halloc.1
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_s, P_m ∗ F, hm', hpan sm (P_m ∗ F) halloc0⟩)⟩
  · exact (not_satisfies_false_sepConj hoom.2).elim

/-! ## `vecU8At` append helpers -/

theorem vecU8At_eq_of_pos_er (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < cap.toNat) :
    vecU8At A v cap ptr bs =
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  have hne : cap ≠ 0#64 := by
    intro h; subst h; simp at hpos
  simp [vecU8At, vecHeader, hne, sepConj_assoc]

theorem pointsToBytes_append_singleton (ptr : BitVec 64) (bs : List (BitVec 8)) (b : BitVec 8) :
    ((ptr ↦ₛ bs) ∗ ((ptr + BitVec.ofNat 64 bs.length) ↦₈ b)) = (ptr ↦ₛ (bs ++ [b])) := by
  rw [pointsToBytes_append, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

theorem memRegion_split_one (a : BitVec 64) (n : Nat) (h1 : 1 ≤ n) (hn : n ≤ 2 ^ 64) :
    memRegion a n = (∃∗ b : BitVec 8, a ↦₈ b) ∗ memRegion (a + 1#64) (n - 1) := by
  rw [memRegion_split' (n := 1) (k := n - 1) (by omega) rfl hn, memRegion_one]

theorem vecU8At_expose_one (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hlt : bs.length < cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    vecU8At A v cap ptr bs =
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        (∃∗ b0 : BitVec 8, (ptr + BitVec.ofNat 64 bs.length) ↦₈ b0) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length + 1#64) (cap.toNat - bs.length - 1)) := by
  have hpure : (bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64) = True :=
    eq_true ⟨by omega, hcap, hptr⟩
  rw [vecU8At_eq_of_pos_er A v cap ptr bs (by omega), hpure, pure_true, emp_sepConj,
      memRegion_split_one (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)
        (by omega) (by omega)]

theorem vecU8At_pack_one (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (b : BitVec 8) (hlt : bs.length < cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ (BitVec.ofNat 64 bs.length + 1#64)) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      ((ptr + BitVec.ofNat 64 bs.length) ↦₈ b) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length + 1#64) (cap.toNat - bs.length - 1)) =
    vecU8At A v cap ptr (bs ++ [b]) := by
  rw [vecU8At_eq_of_pos_er A v cap ptr (bs ++ [b]) (by omega)]
  have hlen : (bs ++ [b]).length = bs.length + 1 := by simp
  have hbv : BitVec.ofNat 64 (bs.length + 1) = BitVec.ofNat 64 bs.length + 1#64 := by
    simp [BitVec.ofNat_add]
  have hadd : ptr + (BitVec.ofNat 64 bs.length + 1#64) =
      ptr + BitVec.ofNat 64 bs.length + 1#64 := (BitVec.add_assoc ptr _ 1#64).symm
  have hsub : cap.toNat - (bs.length + 1) = cap.toNat - bs.length - 1 := by omega
  have hpure : (bs.length + 1 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64) = True :=
    eq_true ⟨by omega, hcap, hptr⟩
  rw [hlen, hbv, hadd, hsub, ← pointsToBytes_append_singleton, hpure, pure_true, emp_sepConj]
  ac_rfl

theorem vecU8At_expose_slice (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (n : Nat)
    (hle : bs.length + n ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0#64) (hn_pos : 0 < n) :
    vecU8At A v cap ptr bs =
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) n ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 n)
          (cap.toNat - bs.length - n)) := by
  have hpure : (bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64) = True :=
    eq_true ⟨by omega, hcap, hptr⟩
  rw [vecU8At_eq_of_pos_er A v cap ptr bs (by omega), hpure, pure_true, emp_sepConj,
      memRegion_split' (b := ptr + BitVec.ofNat 64 bs.length)
        (b' := ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 n)
        (n := n) (k := cap.toNat - bs.length - n)
        (by omega) rfl (by omega)]

theorem vecU8At_pack_slice (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs payload : List (BitVec 8))
    (hle : bs.length + payload.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64) (hne : payload ≠ []) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ (BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ payload) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)
        (cap.toNat - bs.length - payload.length)) =
    vecU8At A v cap ptr (bs ++ payload) := by
  have hpos : 0 < payload.length := List.length_pos_of_ne_nil hne
  rw [vecU8At_eq_of_pos_er A v cap ptr (bs ++ payload) (by omega)]
  have hlen : (bs ++ payload).length = bs.length + payload.length := List.length_append
  have hbv : BitVec.ofNat 64 (bs.length + payload.length) =
      BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length := by
    simp [BitVec.ofNat_add]
  have hadd : ptr + (BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length) =
      ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length := (BitVec.add_assoc ptr _ _).symm
  have hsub : cap.toNat - (bs.length + payload.length) =
      cap.toNat - bs.length - payload.length := by omega
  have hpure : (bs.length + payload.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64) = True :=
    eq_true ⟨hle, hcap, hptr⟩
  rw [hlen, hbv, hadd, hsub, pointsToBytes_append, hpure, pure_true, emp_sepConj]
  ac_rfl

theorem sepWPp_extract_vecU8At_bounds {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {v cap ptr : BitVec 64} {bs : List (BitVec 8)} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfocus : P = vecU8At A v cap ptr bs ∗ F := by sep_focus)
    (h : bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0#64 →
      SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ (vecU8At A v cap ptr bs ∗ F) ∗ R := hfocus ▸ hm
  rw [vecU8At_eq_header_sep_buf, sepConj_assoc, sepConj_assoc] at hm'
  have hm_buf : s.mem ⊨ vecU8Buf A cap ptr bs ∗
      (vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ F ∗ R) := by
    convert hm' using 1; ac_rfl
  obtain ⟨hle, hcap, hptr⟩ := vecU8Buf_bounds hm_buf
  exact h hle hcap hptr R hm hL

/-! ## Little-endian byte decompositions -/

theorem leBytes_4_eq (v : BitVec 32) :
    leBytes 4 v.toNat =
      [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8] := by
  dsimp [leBytes, List.range, List.range.loop]
  refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩⟩ <;>
    apply BitVec.eq_of_toNat_eq <;> simp

theorem leBytes_8_eq (v : BitVec 64) :
    leBytes 8 v.toNat =
      [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8,
       v.extractLsb' 32 8, v.extractLsb' 40 8, v.extractLsb' 48 8, v.extractLsb' 56 8] := by
  dsimp [leBytes, List.range, List.range.loop]
  refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_,
    List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_,
      List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    apply BitVec.eq_of_toNat_eq <;> simp

set_option allowUnsafeReducibility true in
attribute [local semireducible] pointsTo32 pointsTo64 in
theorem pointsToBytes_leBytes_4 (a : BitVec 64) (v : BitVec 32) :
    (a ↦ₛ leBytes 4 v.toNat) = (a ↦₃₂ v) := by
  rw [leBytes_4_eq]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, pointsTo32]
  have h0 : a = a + 0#64 := (BitVec.add_zero a).symm
  have h2 : a + 1#64 + 1#64 = a + 2#64 := by bv_lin
  have h3 : a + 2#64 + 1#64 = a + 3#64 := by bv_lin
  rw [h2, h3]
  conv_lhs => arg 1; arg 1; rw [h0]

set_option allowUnsafeReducibility true in
attribute [local semireducible] pointsTo64 in
theorem pointsToBytes_leBytes_8 (a : BitVec 64) (v : BitVec 64) :
    (a ↦ₛ leBytes 8 v.toNat) = (a ↦₆₄ v) := by
  rw [leBytes_8_eq]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, pointsTo64]
  have h0 : a = a + 0#64 := (BitVec.add_zero a).symm
  have h2 : a + 1#64 + 1#64 = a + 2#64 := by bv_lin
  have h3 : a + 2#64 + 1#64 = a + 3#64 := by bv_lin
  have h4 : a + 3#64 + 1#64 = a + 4#64 := by bv_lin
  have h5 : a + 4#64 + 1#64 = a + 5#64 := by bv_lin
  have h6 : a + 5#64 + 1#64 = a + 6#64 := by bv_lin
  have h7 : a + 6#64 + 1#64 = a + 7#64 := by bv_lin
  rw [h2, h3, h4, h5, h6, h7]
  conv_lhs => arg 1; arg 1; rw [h0]

theorem regIds_eq_append {bs : List (BitVec 8)} {rId lId : BitVec 32}
    (hlen : bs.length = 8)
    (hr : bs.take 4 = leBytes 4 rId.toNat)
    (hl : (bs.drop 4).take 4 = leBytes 4 lId.toNat) :
    bs = leBytes 4 rId.toNat ++ leBytes 4 lId.toNat := by
  have hd : bs.drop 4 = (bs.drop 4).take 4 := by
    rw [List.take_of_length_le (by simp [hlen])]
  calc bs = bs.take 4 ++ bs.drop 4 := (List.take_append_drop 4 bs).symm
    _ = leBytes 4 rId.toNat ++ leBytes 4 lId.toNat := by rw [hr, hd, hl]

theorem pointsToBytes_regIds_eq (ss : BitVec 64) {bs : List (BitVec 8)} {rId lId : BitVec 32}
    (hlen : bs.length = 8)
    (hr : bs.take 4 = leBytes 4 rId.toNat)
    (hl : (bs.drop 4).take 4 = leBytes 4 lId.toNat) :
    ((ss + 0x150#64) ↦ₛ bs) =
      ((ss + 0x150#64) ↦₃₂ rId) ∗ ((ss + 0x154#64) ↦₃₂ lId) := by
  rw [regIds_eq_append hlen hr hl, pointsToBytes_append]
  have hlen4 : (leBytes 4 rId.toNat).length = 4 := by simp [leBytes]
  have hadd : ss + 0x150#64 + 4#64 = ss + 0x154#64 := by bv_lin
  rw [hlen4, show BitVec.ofNat 64 4 = 4#64 by rfl, hadd,
      pointsToBytes_leBytes_4, pointsToBytes_leBytes_4]

theorem chainAt_eq_protoChainAt_er (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    chainAt A gc a =
      (⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗ protoChainAt A gc a) := by
  simp only [chainAt, protoChainAt, pure_sepConj_pure_assoc]
  congr 2
  exact propext ⟨fun ⟨h1, h2, h3, h4, h5⟩ => ⟨⟨h4, h5⟩, h1, h2, h3⟩,
    fun ⟨⟨h4, h5⟩, h1, h2, h3⟩ => ⟨h1, h2, h3, h4, h5⟩⟩

theorem optSenderChainAt_some_eq_chainAt_er (A : RustAlloc) (a : BitVec 64)
    (g : SenderChainGhost) (sc : SenderChain) :
    optSenderChainAt A a (some g) (some sc) =
      (⌜g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
        g.srk.bytes.length = 33⌝ ∗
       protoChainAt A (senderGhostAsChain g, senderAsChain sc) a) := by
  simp only [optSenderChainAt, protoChainAt, senderGhostAsChain, senderAsChain,
    List.length_nil, maxMessageKeys, List.zip_nil_left, pure_sepConj_pure_assoc]
  congr 2
  apply propext
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h2, h3, h4⟩, h1, by decide, trivial⟩
  · rintro ⟨⟨h2, h3, h4⟩, h1, _, _⟩
    exact ⟨h1, h2, h3, h4⟩

/-! ## `PendingPreKey` and `PendingKyberPreKey` tail decompositions -/

theorem optU32Rel_take4_eq {bs : List (BitVec 8)} {opt : Option (BitVec 32)}
    (h : OptU32Rel bs opt) :
    bs.take 4 = leBytes 4 (optU32Tag opt).toNat := by
  cases opt with
  | none =>
    have heq : ([0#8, 0#8, 0#8, 0#8] : List (BitVec 8)) = leBytes 4 (0#32).toNat := by decide
    exact h.trans heq
  | some v =>
    have heq : ([1#8, 0#8, 0#8, 0#8] : List (BitVec 8)) = leBytes 4 (1#32).toNat := by decide
    exact h.1.trans heq

theorem pending_tail_eq {bs : List (BitVec 8)} {p : PendingPreKey}
    (hopt : OptU32Rel bs p.preKeyId)
    (hts : (bs.drop 8).take 8 = leBytes 8 p.timestamp.toNat)
    (hspk : (bs.drop 16).take 4 = leBytes 4 p.signedPreKeyId.toNat) :
    bs = leBytes 4 (optU32Tag p.preKeyId).toNat ++
      (bs.drop 4).take 4 ++
      leBytes 8 p.timestamp.toNat ++
      leBytes 4 p.signedPreKeyId.toNat ++
      bs.drop 20 := by
  have h1 : bs = bs.take 4 ++ bs.drop 4 := (List.take_append_drop 4 bs).symm
  have h2 : bs.drop 4 = (bs.drop 4).take 4 ++ (bs.drop 4).drop 4 :=
    (List.take_append_drop 4 (bs.drop 4)).symm
  have h3 : bs.drop 8 = (bs.drop 8).take 8 ++ (bs.drop 8).drop 8 :=
    (List.take_append_drop 8 (bs.drop 8)).symm
  have h4 : bs.drop 16 = (bs.drop 16).take 4 ++ (bs.drop 16).drop 4 :=
    (List.take_append_drop 4 (bs.drop 16)).symm
  simp only [List.drop_drop, Nat.reduceAdd] at h2 h3 h4
  rw [optU32Rel_take4_eq hopt] at h1
  rw [hts] at h3
  rw [hspk] at h4
  rw [h4] at h3
  rw [h3] at h2
  rw [h2] at h1
  simpa only [List.append_assoc] using h1

theorem pointsToBytes_pending_tail_eq (ss : BitVec 64) {bs : List (BitVec 8)} {p : PendingPreKey}
    (hlen : bs.length = 24)
    (hopt : OptU32Rel bs p.preKeyId)
    (hts : (bs.drop 8).take 8 = leBytes 8 p.timestamp.toNat)
    (hspk : (bs.drop 16).take 4 = leBytes 4 p.signedPreKeyId.toNat) :
    ((ss + 0x110#64) ↦ₛ bs) =
      ((ss + 0x110#64) ↦₃₂ optU32Tag p.preKeyId) ∗
      ((ss + 0x114#64) ↦ₛ (bs.drop 4).take 4) ∗
      ((ss + 0x118#64) ↦₆₄ p.timestamp) ∗
      ((ss + 0x120#64) ↦₃₂ p.signedPreKeyId) ∗
      ((ss + 0x124#64) ↦ₛ bs.drop 20) := by
  conv_lhs => rw [pending_tail_eq hopt hts hspk]
  have hl1 : (leBytes 4 (optU32Tag p.preKeyId).toNat).length = 4 := by simp [leBytes]
  have hl2 : ((bs.drop 4).take 4).length = 4 := by simp [hlen]
  have hl3 : (leBytes 8 p.timestamp.toNat).length = 8 := by simp [leBytes]
  have hl4 : (leBytes 4 p.signedPreKeyId.toNat).length = 4 := by simp [leBytes]
  simp only [pointsToBytes_append, List.length_append, hl1, hl2, hl3, hl4, Nat.reduceAdd,
    show ss + 0x110#64 + 4#64 = ss + 0x114#64 by bv_lin,
    show ss + 0x110#64 + 8#64 = ss + 0x118#64 by bv_lin,
    show ss + 0x110#64 + 16#64 = ss + 0x120#64 by bv_lin,
    show ss + 0x110#64 + 20#64 = ss + 0x124#64 by bv_lin,
    pointsToBytes_leBytes_4, pointsToBytes_leBytes_8, sepConj_assoc]

theorem kyber_tail_eq {bs : List (BitVec 8)} {k : PendingKyberPreKey}
    (hpk : bs.take 4 = leBytes 4 k.preKeyId.toNat) :
    bs = leBytes 4 k.preKeyId.toNat ++ bs.drop 4 := by
  rw [← hpk, List.take_append_drop]

theorem pointsToBytes_kyber_tail_eq (ss : BitVec 64) {bs : List (BitVec 8)} {k : PendingKyberPreKey}
    (hpk : bs.take 4 = leBytes 4 k.preKeyId.toNat) :
    ((ss + 0x140#64) ↦ₛ bs) =
      ((ss + 0x140#64) ↦₃₂ k.preKeyId) ∗ ((ss + 0x144#64) ↦ₛ bs.drop 4) := by
  conv_lhs => rw [kyber_tail_eq hpk]
  have hl1 : (leBytes 4 k.preKeyId.toNat).length = 4 := by simp [leBytes]
  rw [pointsToBytes_append, hl1, show BitVec.ofNat 64 4 = 4#64 by rfl,
      show ss + 0x140#64 + 4#64 = ss + 0x144#64 by bv_lin,
      pointsToBytes_leBytes_4]

/-! ## Subroutine call wrappers -/

theorem reserveCap_bounds_add {cap len add : Nat}
    (hcap_le : cap ≤ len + add) (hlen_lt : len + add < 2 ^ 62) :
    reserveCap cap len add + 1 ≤ 2 ^ 63 ∧
    len + add ≤ (BitVec.ofNat 64 (reserveCap cap len add)).toNat ∧
    (BitVec.ofNat 64 (reserveCap cap len add)).toNat < 2 ^ 63 := by
  unfold reserveCap
  have hmax : max (max (len + add) (2 * cap)) 8 < 2 ^ 63 := by omega
  have htoNat : (BitVec.ofNat 64 (max (max (len + add) (2 * cap)) 8)).toNat =
      max (max (len + add) (2 * cap)) 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [htoNat]
  omega

theorem encraw_call_doReserve {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (sp0 v cap ptr ret_pc : BitVec 64) (bs : List (BitVec 8)) (add : Nat)
    (hcap_le : cap.toNat ≤ bs.length + add)
    (hlen_lt : bs.length + add < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = bs.length)
    (hx2 : (s.readReg64 .x2).toNat = add)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hP : P = (vecU8At A v cap ptr bs ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      bs.length + add ≤ newCap.toNat →
      newCap.toNat < 2 ^ 63 →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((vecU8At A v newCap p' bs ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  have hcall := encraw_doReserve_ok hDR
  obtain ⟨hres_bound, hnew_ge, hnew_lt⟩ := reserveCap_bounds_add hcap_le hlen_lt
  refine SepWPp.call (x := DoReserveCall.mk v cap ptr bs add)
    (F := memRegion (sp0 - 80#64 - 17104#64) 12896 ∗ F)
    hcall hpc hrun halign hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_doReserve_er (sp0 - 80#64)] at hm
    simp only [doReserveSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hres_bound⟩, ?_⟩
    apply satisfies_of_sep_focus hm
    sep_focus
  · intro _ _ _ _ hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ R' hm
    simp only [doReserveSpec, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [doReserveSpec, hsp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun p' => ?_
    refine SepWPp.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_ (hnext sm (BitVec.ofNat 64 (reserveCap cap.toNat bs.length add)) p'
      hpcm hrunm hspm htrm' hcsm hnew_ge hnew_lt)
    rw [stackAt_sub_to_doReserve_er (sp0 - 80#64)]
    exact entails_of_sep_focus (by sep_focus)

theorem encraw_call_encodeVarint {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hEV : Prost.EncodeVarintOk b C A ctl abs)
    (sp0 val v cap ptr ret_pc : BitVec 64) (bs : List (BitVec 8))
    (hlen_lt : bs.length + 10 < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hP : P = (vecU8At A v cap ptr bs ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((vecU8At A v cap' ptr' (bs ++ encodeVarint val) ∗ A.pool ∗
          stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  have hcall := encraw_encodeVarint_ok hEV
  refine SepWPp.call (x := ⟨val, v, cap, ptr, bs⟩)
    (F := memRegion (sp0 - 80#64 - 17104#64) 12848 ∗ F)
    hcall hpc hrun halign hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_encodeVarint_er (sp0 - 80#64)] at hm
    simp only [encodeVarintSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, Or.inr hlen_lt⟩, ?_⟩
    apply satisfies_of_sep_focus hm
    sep_focus
  · intro _ _ _ _ hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ R' hm
    simp only [encodeVarintSpec, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [encodeVarintSpec, hsp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => ?_
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.pure_elim fun _ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm' hcsm)
    rw [stackAt_sub_to_encodeVarint_er (sp0 - 80#64)]
    exact entails_of_sep_focus (by sep_focus)

theorem encraw_call_memcpy {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (v cap ptr srcPtr ret_pc : BitVec 64) (bs payload : List (BitVec 8))
    (hle : bs.length + payload.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0#64)
    (hne : payload ≠ [])
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>"))
    (hrun : s.status = .Running)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = ptr + BitVec.ofNat 64 bs.length)
    (hx1 : s.readReg64 .x1 = srcPtr)
    (hx2 : (s.readReg64 .x2).toNat = payload.length)
    (hP : P = (vecU8At A v cap ptr bs ∗ (srcPtr ↦ₛ payload)) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ payload) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)
            (cap.toNat - bs.length - payload.length) ∗
          (srcPtr ↦ₛ payload)) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  have hcall := encraw_memcpy_ok (b := b) (C := C) (ctl := ctl) (abs := abs)
  have hpos : 0 < payload.length := List.length_pos_of_ne_nil hne
  refine SepWPp.call (x := (ptr + BitVec.ofNat 64 bs.length, srcPtr, payload))
    (F := ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
           A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)
             (cap.toNat - bs.length - payload.length)) ∗ F)
    hcall hpc hrun halign hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, vecU8At_expose_slice A v cap ptr bs payload.length hle hcap hptr hpos] at hm
    simp only [framelessMemcpySpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    apply satisfies_of_sep_focus hm
    sep_focus
  · intro _ _ _ _ hm
    exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm
    simp only [framelessMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact False.elim hm.1
  · intro sm hpcm hrunm hspm hcsm
    simp only [framelessMemcpySpec, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm' hcsm)
    exact entails_of_sep_focus (by sep_focus)

theorem encraw_call_protoEncodeChain {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hEC : OkAt b C ctl abs encodeChainName (encodeChainSpec A))
    (tag : Nat) (sp0 a v cap ptr ret_pc : BitVec 64)
    (gc : ChainGhost × ReceiverChain) (bs : List (BitVec 8))
    (htag : tag = 6 ∨ tag = 7)
    (hlen_lt : bs.length + (lenField tag (encChainMem gc)).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 tag)
    (hx1 : s.readReg64 .x1 = a)
    (hx2 : s.readReg64 .x2 = v)
    (hP : P = (protoChainAt A gc a ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((protoChainAt A gc a ∗ vecU8At A v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  have hcall := encraw_encodeChain_ok hEC
  refine SepWPp.call (x := ⟨tag, a, gc, v, cap, ptr, bs⟩)
    (F := memRegion (sp0 - 80#64 - 17104#64) 8464 ∗ F)
    hcall hpc hrun halign hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_encodeChain (sp0 - 80#64)] at hm
    simp only [encodeChainSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, htag, hlen_lt⟩, ?_⟩
    apply satisfies_of_sep_focus hm
    sep_focus
  · intro _ _ _ _ hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ R' hm
    simp only [encodeChainSpec, allocPanic, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [encodeChainSpec, hsp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => ?_
    refine SepWPp.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm' hcsm)
    rw [stackAt_sub_to_encodeChain (sp0 - 80#64)]
    exact entails_of_sep_focus (by sep_focus)

theorem encraw_call_encodeChain {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hEC : OkAt b C ctl abs encodeChainName (encodeChainSpec A))
    (tag : Nat) (sp0 a v cap ptr ret_pc : BitVec 64)
    (gc : ChainGhost × ReceiverChain) (bs : List (BitVec 8))
    (htag : tag = 6 ∨ tag = 7)
    (hlen_lt : bs.length + (lenField tag (encChainMem gc)).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 tag)
    (hx1 : s.readReg64 .x1 = a)
    (hx2 : s.readReg64 .x2 = v)
    (hP : P = (chainAt A gc a ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((chainAt A gc a ∗ vecU8At A v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  have hP' : P = (protoChainAt A gc a ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStack) ∗
      (⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗ F) := by
    rw [hP, chainAt_eq_protoChainAt_er A gc a]; ac_rfl
  refine encraw_call_protoEncodeChain hEC tag sp0 a v cap ptr ret_pc gc bs htag hlen_lt
    hpc hrun hsp halign htr hlr hx0 hx1 hx2 hP' ?_
  intro sm cap' ptr' hpcm hrunm hspm htrm hcsm
  have hPostEq :
      ((protoChainAt A gc a ∗ vecU8At A v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
        A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
        (⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗ F)) =
      ((chainAt A gc a ∗ vecU8At A v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
        A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F) := by
    rw [chainAt_eq_protoChainAt_er A gc a]; ac_rfl
  rw [hPostEq]
  exact hnext sm cap' ptr' hpcm hrunm hspm htrm hcsm

/-! ## Register preservation and protobuf field rewrites -/

@[arm64_norm]
theorem and_self_true : (True ∧ True) = True := and_self True

def EncRawUpperSaved (s0 s : State) : Prop :=
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  (s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)

theorem EncRawUpperSaved.refl (s : State) : EncRawUpperSaved s s :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem EncRawUpperSaved.trans {s0 s1 s2 : State}
    (h1 : EncRawUpperSaved s0 s1) (h2 : EncRawUpperSaved s1 s2) :
    EncRawUpperSaved s0 s2 := by
  reg_chain

theorem EncRawUpperSaved.of_calleeSavedPreserved {s1 s2 : State}
    (h : CalleeSavedPreserved s1 s2) : EncRawUpperSaved s1 s2 := by
  reg_chain

theorem sp_sub_80_spAligned {sp0 : BitVec 64} {s : State}
    (hsp0 : sp0 &&& 15#64 = 0#64) (hsp : s.sp = sp0 - 80#64) :
    s.spAligned = true := by
  simp only [State.spAligned, hsp, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat hsp0
  simp only [BitVec.toNat_and, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.and_two_pow_sub_one_eq_mod _ 4] at h1 ⊢
  omega

theorem bv32_beq_zero_false {w : BitVec 32} (hne : w ≠ 0#32) :
    (w == 0#32) = false :=
  beq_eq_false_iff_ne.mpr hne

theorem bv64_beq_zero_false {w : BitVec 64} (hne : w ≠ 0#64) :
    (w == 0#64) = false :=
  beq_eq_false_iff_ne.mpr hne

theorem ofNat64_len_beq_zero_false {bs : List (BitVec 8)} (hne : bs ≠ []) (hlt : bs.length < 2 ^ 63) :
    (BitVec.ofNat 64 bs.length == 0#64) = false := by
  have hpos : 0 < bs.length := List.length_pos_of_ne_nil hne
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
  change bs.length = 0 at h1
  omega

theorem cap_sub_len_ult_false {cap : BitVec 64} {len add : Nat}
    (hle : len + add ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) :
    BitVec.ult (cap - BitVec.ofNat 64 len) (BitVec.ofNat 64 add) = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]
  have hlen_mod : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hadd_mod : (BitVec.ofNat 64 add).toNat = add := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : (cap - BitVec.ofNat 64 len).toNat = cap.toNat - len := by
    rw [BitVec.toNat_sub_of_le]
    · rw [hlen_mod]
    · rw [BitVec.le_def, hlen_mod]; omega
  rw [hsub, hadd_mod]
  omega

theorem cap_sub_len_ult_true {cap : BitVec 64} {len add : Nat}
    (hlen_le : len ≤ cap.toNat) (hlt : cap.toNat < len + add)
    (hcap : cap.toNat < 2 ^ 63) (hadd : add < 2 ^ 63) :
    BitVec.ult (cap - BitVec.ofNat 64 len) (BitVec.ofNat 64 add) = true := by
  rw [BitVec.ult_eq_decide, decide_eq_true_eq]
  have hlen_mod : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hadd_mod : (BitVec.ofNat 64 add).toNat = add := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : (cap - BitVec.ofNat 64 len).toNat = cap.toNat - len := by
    rw [BitVec.toNat_sub_of_le]
    · rw [hlen_mod]
    · rw [BitVec.le_def, hlen_mod]; omega
  rw [hsub, hadd_mod]
  omega

theorem bv_len_add_slice_er (bs payload : List (BitVec 8)) :
    BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length =
      BitVec.ofNat 64 (bs ++ payload).length := by
  simp only [List.length_append, BitVec.ofNat_add]

theorem uint32Field_zero (tag : Nat) : uint32Field tag 0#32 = [] := rfl

theorem uint32Field_ne_zero {tag : Nat} {v : BitVec 32} {k : BitVec 8}
    (hne : v ≠ 0#32) (hk : encodeKey tag .varint = [k] := by decide) :
    uint32Field tag v = [k] ++ encodeVarint (BitVec.zeroExtend 64 v) := by
  have hne' : v ≠ 0 := hne
  simp only [uint32Field, hne', ↓reduceIte, hk]

theorem uint64Field_zero (tag : Nat) : uint64Field tag 0#64 = [] := rfl

theorem uint64Field_ne_zero {tag : Nat} {v : BitVec 64} {k : BitVec 8}
    (hne : v ≠ 0#64) (hk : encodeKey tag .varint = [k] := by decide) :
    uint64Field tag v = [k] ++ encodeVarint v := by
  have hne' : v ≠ 0 := hne
  simp only [uint64Field, hne', ↓reduceIte, hk]

theorem int32Field_zero (tag : Nat) : int32Field tag 0#32 = [] := rfl

theorem int32Field_ne_zero {tag : Nat} {v : BitVec 32} {k : BitVec 8}
    (hne : v ≠ 0#32) (hk : encodeKey tag .varint = [k] := by decide) :
    int32Field tag v = [k] ++ encodeVarint (BitVec.signExtend 64 v) := by
  have hne' : v ≠ 0 := hne
  simp only [int32Field, hne', ↓reduceIte, hk]

theorem optUint32Field_none (tag : Nat) : optUint32Field tag none = [] := rfl

theorem optUint32Field_some {tag : Nat} (v : BitVec 32) {k : BitVec 8}
    (hk : encodeKey tag .varint = [k] := by decide) :
    optUint32Field tag (some v) = [k] ++ encodeVarint (BitVec.zeroExtend 64 v) := by
  simp only [optUint32Field, hk]

theorem bytesField_nil (tag : Nat) : bytesField tag [] = [] := rfl

theorem bytesField_ne_nil {tag : Nat} {bs : List (BitVec 8)} {k : BitVec 8}
    (hne : bs ≠ []) (hk : encodeKey tag .lengthDelimited = [k] := by decide) :
    bytesField tag bs = [k] ++ encodeVarint (BitVec.ofNat 64 bs.length) ++ bs := by
  simp only [bytesField, hne, ↓reduceIte, lenField, hk]

theorem bytesField_ne_nil_length {tag : Nat} {bs : List (BitVec 8)}
    (hne : bs ≠ []) (hk : (encodeKey tag .lengthDelimited).length = 1 := by decide) :
    (bytesField tag bs).length = 1 + (encodeVarint (BitVec.ofNat 64 bs.length)).length + bs.length := by
  simp only [bytesField, hne, ↓reduceIte, lenField, List.length_append, hk]

theorem uint32Field_ne_zero_length {tag : Nat} {v : BitVec 32}
    (hne : v ≠ 0#32) (hk : (encodeKey tag .varint).length = 1 := by decide) :
    (uint32Field tag v).length = 1 + (encodeVarint (BitVec.zeroExtend 64 v)).length := by
  have hne' : v ≠ 0 := hne
  simp only [uint32Field, hne', ↓reduceIte, List.length_append, hk]

/-! ## Relocatable `[LibsignalPlacement]` helpers (block `14`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

/-- Lifts a `SepWP` basic block into `SepWPp` while preserving `LibsignalCodeLoaded`. -/
theorem sepWPp_of_sepWP_lscl_er {prog : Program} {pl : MultiPlacement} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (sepWP_mono_lscl hcl h fun _ _ _ _ hclm hnext => hnext hclm)

/-- Steps a `withLsCodeLoaded` subroutine call inside `SepWPp`. -/
theorem sepWPp_call_lscl_er {α : Type} {prog : Program} {pl : MultiPlacement}
    {ret entry ret_pc : BitVec 64} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hcl : LibsignalCodeLoaded pl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → LibsignalCodeLoaded pl sf.mem →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q Qp := by
  let spec_cl : Spec α :=
    { pre := (withLsCodeLoaded pl spec).pre
      post := fun y s0 sf => ⌜LibsignalCodeLoaded pl sf.mem⌝ ∗ spec.post y s0 sf
      onPanic := spec.onPanic
      onExit := spec.onExit
      onOom := spec.onOom }
  have hcall_cl : subroutine_ok prog entry spec_cl := by
    refine subroutine_ok.of_codeLoaded fun y R s0 hpc0 hrun0 hpre0 hsp0 hL0 => ?_
    have hcl0 : LibsignalCodeLoaded pl s0.mem := (extract_withLsCodeLoaded hpre0).1
    obtain ⟨sf, hsteps, hout, _⟩ :=
      hcall.no_fault_before_outcome y R s0 hpc0 hrun0 hpre0 hsp0 hL0
    refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
    rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom'
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsCodeLoaded] at hpost; dsimp only [spec_cl]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hcl0.of_keepsFrozen hsteps.keepsFrozen, hpost⟩
    · exact Or.inr (Or.inl hpan)
    · exact Or.inr (Or.inr (Or.inl hex))
    · exact Or.inr (Or.inr (Or.inr hoom'))
  refine SepWPp.call (x := x) (F := F) hcall_cl hpc hrun hsp hlr
    (fun R hm => by
      dsimp only [spec_cl, withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hcl, hpre R hm⟩)
    hexit hpanic
    (fun sm hpcm hrunm hspm hcsm => by
      dsimp only [spec_cl]; rw [sepConj_assoc]
      exact ProofLib.SepWPp.pure_elim fun hclm => hnext sm hpcm hrunm hspm hclm hcsm)
    (fun sm R' _ hpost => by
      dsimp only [spec_cl] at hpost; rw [hoom sm] at hpost
      exact (not_satisfies_false_sepConj hpost).elim)

theorem encraw_call_doReserve_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (sp0 v cap ptr ret_pc : BitVec 64) (bs : List (BitVec 8)) (add : Nat)
    (hcap_le : cap.toNat ≤ bs.length + add)
    (hlen_lt : bs.length + add < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 13)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = bs.length)
    (hx2 : (s.readReg64 .x2).toNat = add)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hP : P = (vecU8At A v cap ptr bs ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      bs.length + add ≤ newCap.toNat →
      newCap.toNat < 2 ^ 63 →
      SepWPp (lsProg_14 H) ret sm
        ((vecU8At A v newCap p' bs ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hcall : subroutine_ok (lsProg_14 H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_14 H) hDR
  obtain ⟨hres_bound, hnew_ge, hnew_lt⟩ := reserveCap_bounds_add hcap_le hlen_lt
  refine sepWPp_call_lscl_er (x := DoReserveCall.mk v cap ptr bs add)
    (F := memRegion (sp0 - 80#64 - 17104#64) 12896 ∗ F)
    hcall hpc hrun halign hcl hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_doReserve_er (sp0 - 80#64)] at hm
    simp only [doReserveSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hres_bound⟩, ?_⟩
    apply satisfies_of_sep_focus hm
    sep_focus
  · intro _ _ _ _ hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ R' hm
    simp only [doReserveSpec, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hclm hcsm
    rw [hsp] at hspm
    simp only [doReserveSpec, hsp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun p' => ?_
    refine SepWPp.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_ (hnext sm (BitVec.ofNat 64 (reserveCap cap.toNat bs.length add)) p'
      hpcm hrunm hclm hspm htrm' hcsm hnew_ge hnew_lt)
    rw [stackAt_sub_to_doReserve_er (sp0 - 80#64)]
    exact entails_of_sep_focus (by sep_focus)

theorem encraw_call_encodeVarint_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hEV : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (sp0 val v cap ptr ret_pc : BitVec 64) (bs : List (BitVec 8))
    (hlen_lt : bs.length + 10 < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 10)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hP : P = (vecU8At A v cap ptr bs ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPp (lsProg_14 H) ret sm
        ((vecU8At A v cap' ptr' (bs ++ encodeVarint val) ∗ A.pool ∗
          stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hcall : subroutine_ok (lsProg_14 H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_14 H) hEV
  refine sepWPp_call_lscl_er (x := ⟨val, v, cap, ptr, bs⟩)
    (F := memRegion (sp0 - 80#64 - 17104#64) 12848 ∗ F)
    hcall hpc hrun halign hcl hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_encodeVarint_er (sp0 - 80#64)] at hm
    simp only [encodeVarintSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, Or.inr hlen_lt⟩, ?_⟩
    apply satisfies_of_sep_focus hm
    sep_focus
  · intro _ _ _ _ hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ R' hm
    simp only [encodeVarintSpec, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hclm hcsm
    rw [hsp] at hspm
    simp only [encodeVarintSpec, hsp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => ?_
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.pure_elim fun _ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hclm hspm htrm' hcsm)
    rw [stackAt_sub_to_encodeVarint_er (sp0 - 80#64)]
    exact entails_of_sep_focus (by sep_focus)

theorem encraw_call_memcpy_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (v cap ptr srcPtr ret_pc : BitVec 64) (bs payload : List (BitVec 8))
    (hle : bs.length + payload.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0#64)
    (hne : payload ≠ [])
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsρ lsMemcpySym)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = ptr + BitVec.ofNat 64 bs.length)
    (hx1 : s.readReg64 .x1 = srcPtr)
    (hx2 : (s.readReg64 .x2).toNat = payload.length)
    (hP : P = (vecU8At A v cap ptr bs ∗ (srcPtr ↦ₛ payload)) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = s.sp →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPp (lsProg_14 H) ret sm
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ payload) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)
            (cap.toNat - bs.length - payload.length) ∗
          (srcPtr ↦ₛ payload)) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hcall : subroutine_ok (lsProg_14 H) (lsρ lsMemcpySym)
      (withLsCodeLoaded lsmpl framelessMemcpySpec) :=
    subroutine_ok_withLsCodeLoaded_of_plain (ls_hook_ok_of_mem (prog := lsProg_14 H) hmc)
  have hpos : 0 < payload.length := List.length_pos_of_ne_nil hne
  refine sepWPp_call_lscl_er (x := (ptr + BitVec.ofNat 64 bs.length, srcPtr, payload))
    (F := ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
           A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)
             (cap.toNat - bs.length - payload.length)) ∗ F)
    hcall hpc hrun halign hcl hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, vecU8At_expose_slice A v cap ptr bs payload.length hle hcap hptr hpos] at hm
    simp only [framelessMemcpySpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    apply satisfies_of_sep_focus hm
    sep_focus
  · intro _ _ _ _ hm
    exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm
    simp only [framelessMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact False.elim hm.1
  · intro sm hpcm hrunm hspm hclm hcsm
    simp only [framelessMemcpySpec, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hclm hspm htrm' hcsm)
    exact entails_of_sep_focus (by sep_focus)

theorem encraw_call_protoEncodeChain_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hEC : subroutine_ok (lsProg_12 H) (blkPl_12).base
      (withLsCodeLoaded lsmpl (encodeChainSpec A)))
    (tag : Nat) (sp0 a v cap ptr ret_pc : BitVec 64)
    (gc : ChainGhost × ReceiverChain) (bs : List (BitVec 8))
    (htag : tag = 6 ∨ tag = 7)
    (hlen_lt : bs.length + (lenField tag (encChainMem gc)).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 12)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 tag)
    (hx1 : s.readReg64 .x1 = a)
    (hx2 : s.readReg64 .x2 = v)
    (hP : P = (protoChainAt A gc a ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPp (lsProg_14 H) ret sm
        ((protoChainAt A gc a ∗ vecU8At A v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hcall : subroutine_ok (lsProg_14 H) (blkPl_12).base
      (withLsCodeLoaded lsmpl (encodeChainSpec A)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_14 H) hEC
  refine sepWPp_call_lscl_er (x := ⟨tag, a, gc, v, cap, ptr, bs⟩)
    (F := memRegion (sp0 - 80#64 - 17104#64) 8464 ∗ F)
    hcall hpc hrun halign hcl hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_encodeChain (sp0 - 80#64)] at hm
    simp only [encodeChainSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, htag, hlen_lt⟩, ?_⟩
    apply satisfies_of_sep_focus hm
    sep_focus
  · intro _ _ _ _ hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ R' hm
    simp only [encodeChainSpec, allocPanic, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hclm hcsm
    rw [hsp] at hspm
    simp only [encodeChainSpec, hsp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => ?_
    refine SepWPp.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hclm hspm htrm' hcsm)
    rw [stackAt_sub_to_encodeChain (sp0 - 80#64)]
    exact entails_of_sep_focus (by sep_focus)

theorem encraw_call_encodeChain_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hEC : subroutine_ok (lsProg_12 H) (blkPl_12).base
      (withLsCodeLoaded lsmpl (encodeChainSpec A)))
    (tag : Nat) (sp0 a v cap ptr ret_pc : BitVec 64)
    (gc : ChainGhost × ReceiverChain) (bs : List (BitVec 8))
    (htag : tag = 6 ∨ tag = 7)
    (hlen_lt : bs.length + (lenField tag (encChainMem gc)).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 12)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 tag)
    (hx1 : s.readReg64 .x1 = a)
    (hx2 : s.readReg64 .x2 = v)
    (hP : P = (chainAt A gc a ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPp (lsProg_14 H) ret sm
        ((chainAt A gc a ∗ vecU8At A v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hP' : P = (protoChainAt A gc a ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStack) ∗
      (⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗ F) := by
    rw [hP, chainAt_eq_protoChainAt_er A gc a]; ac_rfl
  refine encraw_call_protoEncodeChain_placed hEC tag sp0 a v cap ptr ret_pc gc bs htag hlen_lt
    hpc hrun hcl hsp halign htr hlr hx0 hx1 hx2 hP' ?_
  intro sm cap' ptr' hpcm hrunm hclm hspm htrm hcsm
  have hPostEq :
      ((protoChainAt A gc a ∗ vecU8At A v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
        A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
        (⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗ F)) =
      ((chainAt A gc a ∗ vecU8At A v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
        A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F) := by
    rw [chainAt_eq_protoChainAt_er A gc a]; ac_rfl
  rw [hPostEq]
  exact hnext sm cap' ptr' hpcm hrunm hclm hspm htrm hcsm

end Placed

end CryptoVerification.E2E.Record.Serialization.EncodeRawAux
