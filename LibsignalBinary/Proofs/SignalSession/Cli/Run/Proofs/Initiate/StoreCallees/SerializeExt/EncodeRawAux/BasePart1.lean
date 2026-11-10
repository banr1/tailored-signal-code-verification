/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLen
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.WPX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# Base Helpers for `SessionStructure::encode_raw`

Callee address resolution (`encode_varint`, `do_reserve_and_handle`, `encode::<Chain>`, `memcpy`),
`80`-byte stack frame splits, `SepWPpX` panic composition, `vecU8At` byte/slice-append helpers,
and reusable call combinators.
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.Prost hiding vecU8Buf vecU8At_eq_header_sep_buf
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Separation-logic focus and pure helpers -/

theorem entails_of_sep_focus {P Q : SepProp} (h : P = Q ∗ emp) : P ⊢ Q :=
  Entails.of_eq (by rw [h, sepConj_emp])

theorem satisfies_of_sep_focus {m : Memory} {P Q : SepProp} (hm : m ⊨ P) (h : P = Q ∗ emp) :
    m ⊨ Q := by
  rwa [h, sepConj_emp] at hm

theorem not_satisfies_false_sepConj2 {m : Memory} {R : SepProp} (h : m ⊨ ⌜False⌝ ∗ R) : False := by
  rw [satisfies_pure_sepConj] at h
  exact h.1

/-! ## 2. Callee Address Lemmas from `encodeRawName` -/

theorem fnAddr_encraw_add_eq {img : Obj.Image} {ext : String → Option (State → State)}
    {target : String} {off : BitVec 64}
    (h : BitVec.ofNat 64 (libsignalSessionCode.fnOff encodeRawName) + off =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff target)) :
    (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + off =
      (tripleRatchetProgAtExt img.base ext).fnAddr target := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, BitVec.add_assoc, h]

theorem encraw_encodeVarint_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hEV : Prost.EncodeVarintOkExtX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      ((encodeVarintSpecX A).inImage img) := by
  rw [fnAddr_encraw_add_eq (target := encodeVarintName) (by
    rw [(ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>"),
        (ls_lemma% fnOff "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]")]
    decide)]
  exact hEV

theorem encraw_doReserve_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      ((doReserveSpecX A).inImage img) := by
  rw [fnAddr_encraw_add_eq (target := doReserveName) (by
    rw [(ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>"),
        (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]")]
    decide)]
  exact hDR

theorem encraw_encodeChain_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hEC : OkAtX img ext encodeChainName (encodeChainSpecX A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      ((encodeChainSpecX A).inImage img) := by
  rw [fnAddr_encraw_add_eq (target := encodeChainName) (by
    rw [(ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>"),
        (ls_lemma% fnOff "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")]
    decide)]
  exact hEC

/-! ## 3. Stack frame splitting (`encodeRawStackX = 80 + encodeRawSubStack`) -/

/-- Callee stack budget below `sp0 - 80#64` inside `encode_raw`. -/
abbrev encodeRawSubStack : Nat :=
  Prost.encodeVarintStackX + doReserveStackX + encodeChainStackX

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

/-- Saved registers and unused slot `[sp + 0x18]` in the 80-byte frame of `encode_raw`. -/
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

theorem stackAt_encodeRawStackX_split (sp0 : BitVec 64) :
    stackAt sp0 encodeRawStackX =
      stackAt (sp0 - 80#64) encodeRawSubStack ∗
      cells (sp0 - 80#64) 10 := by
  have htop := encraw_stackAt_split_top sp0 encodeRawSubStack 80 (by decide)
  change stackAt sp0 encodeRawStackX =
    stackAt (sp0 - 80#64) encodeRawSubStack ∗ memRegion (sp0 - 80#64) 80 at htop
  rw [htop, show (80 : Nat) = 8 * 10 by rfl,
      LibsignalTripleRatchet.memRegion_cells (sp0 - 80#64) 10 (by decide)]

theorem stackAt_encodeRawStackX_unfold (sp0 : BitVec 64) :
    stackAt sp0 encodeRawStackX =
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
  rw [stackAt_encodeRawStackX_split sp0, sepConj_comm]
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
      stackAt sp0 encodeRawStackX := by
  rw [stackAt_encodeRawStackX_split sp0]
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
      memRegion (sp - BitVec.ofNat 64 encodeRawSubStack)
        (encodeRawSubStack - Prost.encodeVarintStackX) ∗
      stackAt sp Prost.encodeVarintStackX :=
  encraw_stackAt_split_bottom' sp encodeRawSubStack Prost.encodeVarintStackX
    (encodeRawSubStack - Prost.encodeVarintStackX)

theorem stackAt_sub_to_doReserve_er (sp : BitVec 64) :
    stackAt sp encodeRawSubStack =
      memRegion (sp - BitVec.ofNat 64 encodeRawSubStack)
        (encodeRawSubStack - doReserveStackX) ∗
      stackAt sp doReserveStackX :=
  encraw_stackAt_split_bottom' sp encodeRawSubStack doReserveStackX
    (encodeRawSubStack - doReserveStackX)

theorem stackAt_sub_to_encodeChain (sp : BitVec 64) :
    stackAt sp encodeRawSubStack =
      memRegion (sp - BitVec.ofNat 64 encodeRawSubStack)
        (encodeRawSubStack - encodeChainStackX) ∗
      stackAt sp encodeChainStackX :=
  encraw_stackAt_split_bottom' sp encodeRawSubStack encodeChainStackX
    (encodeRawSubStack - encodeChainStackX)

theorem stackAt_sub_to_memcpy_er (sp : BitVec 64) :
    stackAt sp encodeRawSubStack =
      memRegion (sp - BitVec.ofNat 64 encodeRawSubStack)
        (encodeRawSubStack - extHookStack) ∗
      stackAt sp extHookStack :=
  encraw_stackAt_split_bottom' sp encodeRawSubStack extHookStack
    (encodeRawSubStack - extHookStack)

/-! ## 4. `SepWPpX` composition helpers with `PanicAllocPost` -/

def PanicAllocPost (s0 : State) : State → SepProp → Prop :=
  fun sf P_f => ∀ R, (sf.mem ⊨ P_f ∗ R) →
    (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)

theorem panicAllocPost_of_eq {s0 sf : State} {P_f : SepProp}
    (h : allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) :
    PanicAllocPost s0 sf P_f :=
  fun _ hm => allowPanic_panicked h hm

theorem encraw_seq_wpp {img : Obj.Image} {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P1 F P2 : SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (htr : s.trace = s0.trace)
    (h1 : SepWPpX img prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2)) (PanicAllocPost s))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φ sm →
      SepWPpX img prog ret sm (P2 ∗ F) Q Qp) :
    SepWPpX img prog ret s P Q Qp := by
  intro hinv R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hinv_m, hφ, hent⟩ | ⟨hpan_s, P_m, hmm, hp⟩ | hoom⟩ :=
    h1 hinv (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm hφ hinv_m R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · have hm' : sm.mem ⊨ (P_m ∗ F) ∗ R := by rw [sepConj_assoc]; exact hmm
    have halloc := hp (F ∗ R) hmm
    rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr] using halloc.1
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_s, P_m ∗ F, hm', hpan sm (P_m ∗ F) halloc0⟩)⟩
  · exact (not_satisfies_false_sepConj hoom.2).elim

theorem encraw_seq_wpp' {img : Obj.Image} {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (htr : s.trace = s0.trace)
    (h1 : SepWPpX img prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)) (PanicAllocPost s))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φ sm →
      SepWPpX img prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPpX img prog ret s P Q Qp := by
  intro hinv R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hinv_m, hφ, hent⟩ | ⟨hpan_s, P_m, hmm, hp⟩ | hoom⟩ :=
    h1 hinv (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm hφ hinv_m R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · have hm' : sm.mem ⊨ (P_m ∗ F) ∗ R := by rw [sepConj_assoc]; exact hmm
    have halloc := hp (F ∗ R) hmm
    rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr] using halloc.1
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_s, P_m ∗ F, hm', hpan sm (P_m ∗ F) halloc0⟩)⟩
  · exact (not_satisfies_false_sepConj hoom.2).elim

/-! ## 5. `vecU8At` byte-append and slice-append helpers -/

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

/-- Extract pure bounds `bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64` from `vecU8At`. -/
theorem sepWPp_extract_vecU8At_bounds {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {v cap ptr : BitVec 64} {bs : List (BitVec 8)} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfocus : P = vecU8At A v cap ptr bs ∗ F := by sep_focus)
    (h : bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0#64 →
      SepWPpX img prog ret s P Q Qp) :
    SepWPpX img prog ret s P Q Qp := by
  intro hinv R hm hL
  have hm' : s.mem ⊨ (vecU8At A v cap ptr bs ∗ F) ∗ R := hfocus ▸ hm
  rw [vecU8At_eq_header_sep_buf, sepConj_assoc, sepConj_assoc] at hm'
  have hm_buf : s.mem ⊨ vecU8Buf A cap ptr bs ∗
      (vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ F ∗ R) := by
    convert hm' using 1; ac_rfl
  obtain ⟨hle, hcap, hptr⟩ := vecU8Buf_bounds hm_buf
  exact h hle hcap hptr hinv R hm hL

/-! ## 6. `leBytes` to `pointsTo32` / `pointsTo64` equalities -/

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

theorem pointsToBytes_leBytes_4 (a : BitVec 64) (v : BitVec 32) :
    (a ↦ₛ leBytes 4 v.toNat) = (a ↦₃₂ v) := by
  rw [leBytes_4_eq]
  unfold pointsTo32
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  have h0 : a = a + 0#64 := (BitVec.add_zero a).symm
  have h2 : a + 1#64 + 1#64 = a + 2#64 := by bv_lin
  have h3 : a + 2#64 + 1#64 = a + 3#64 := by bv_lin
  rw [h2, h3]
  conv_lhs => arg 1; arg 1; rw [h0]

theorem pointsToBytes_leBytes_8 (a : BitVec 64) (v : BitVec 64) :
    (a ↦ₛ leBytes 8 v.toNat) = (a ↦₆₄ v) := by
  rw [leBytes_8_eq]
  unfold pointsTo64
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
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

/-! ## 7. Tail decompositions for `PendingPreKey` (`optTailVecAt 48`) and `PendingKyberPreKey` (`optTailVecAt 32`) -/

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

/-! ## 8. Reusable `SepWPpX.call` wrappers for `do_reserve_and_handle`, `encode_varint`, `memcpy`, `encode::<Chain>` -/

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

/-- Execute a `bl do_reserve_and_handle` call inside `encode_raw` when `s.sp = sp0 - 80#64`. -/
theorem encraw_call_doReserve {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (sp0 v cap ptr ret_pc : BitVec 64) (bs : List (BitVec 8)) (add : Nat)
    (hcap_le : cap.toNat ≤ bs.length + add)
    (hlen_lt : bs.length + add < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
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
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A v newCap p' bs ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hcall := encraw_doReserve_ok hDR
  obtain ⟨hres_bound, hnew_ge, hnew_lt⟩ := reserveCap_bounds_add hcap_le hlen_lt
  refine SepWPpX.call (x := DoReserveCall.mk v cap ptr bs add)
    (F := memRegion (sp0 - 80#64 - BitVec.ofNat 64 encodeRawSubStack)
            (encodeRawSubStack - doReserveStackX) ∗ F)
    hcall hpc hrun halign hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_doReserve_er (sp0 - 80#64)] at hm
    simp only [doReserveSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hres_bound⟩, ?_⟩
    apply satisfies_of_sep_focus hm
    sep_focus
  · intro _ _ _ _ hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ R' hm
    simp only [doReserveSpecX, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [doReserveSpecX, hsp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpX.exists_elim fun p' => ?_
    refine SepWPpX.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPpX.weaken_pre ?_ (hnext sm (BitVec.ofNat 64 (reserveCap cap.toNat bs.length add)) p'
      hpcm hrunm hspm htrm' hcsm hnew_ge hnew_lt)
    rw [stackAt_sub_to_doReserve_er (sp0 - 80#64)]
    exact entails_of_sep_focus (by sep_focus)

/-- Execute a `bl encode_varint` call inside `encode_raw` when `s.sp = sp0 - 80#64`. -/
theorem encraw_call_encodeVarint {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hEV : Prost.EncodeVarintOkExtX img A ext)
    (sp0 val v cap ptr ret_pc : BitVec 64) (bs : List (BitVec 8))
    (hlen_lt : bs.length + 10 < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
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
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A v cap' ptr' (bs ++ encodeVarint val) ∗ A.pool ∗
          stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hcall := encraw_encodeVarint_ok hEV
  refine SepWPpX.call (x := ⟨val, v, cap, ptr, bs⟩)
    (F := memRegion (sp0 - 80#64 - BitVec.ofNat 64 encodeRawSubStack)
            (encodeRawSubStack - Prost.encodeVarintStackX) ∗ F)
    hcall hpc hrun halign hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_encodeVarint_er (sp0 - 80#64)] at hm
    simp only [encodeVarintSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, Or.inr hlen_lt⟩, ?_⟩
    apply satisfies_of_sep_focus hm
    sep_focus
  · intro _ _ _ _ hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ R' hm
    simp only [encodeVarintSpecX, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [encodeVarintSpecX, hsp, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpX.exists_elim fun cap' => SepWPpX.exists_elim fun ptr' => ?_
    refine SepWPpX.pure_elim fun htrm => ?_
    refine SepWPpX.pure_elim fun _ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPpX.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm' hcsm)
    rw [stackAt_sub_to_encodeVarint_er (sp0 - 80#64)]
    exact entails_of_sep_focus (by sep_focus)

/-- Execute a `bl memcpy` call inside `encode_raw` to copy `payload` into `vecU8At A v cap ptr bs`. -/
theorem encraw_call_memcpy {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (v cap ptr srcPtr ret_pc : BitVec 64) (bs payload : List (BitVec 8))
    (hle : bs.length + payload.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0#64)
    (hne : payload ≠ [])
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    {stkSp : BitVec 64} {F_rest : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>"))
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
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ payload) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)
            (cap.toNat - bs.length - payload.length) ∗
          (srcPtr ↦ₛ payload)) ∗ F)
        Q (PanicAllocPost s0))
    (hF : F = stackAt stkSp encodeRawSubStack ∗ F_rest := by sep_focus)
    (hsp_stk : s.sp = stkSp := by simp only [wp_norm, arm64_norm, *]) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hcall := hA.session_memcpy_ok_at encodeRawName
    (num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>"))
    (hk := by
      rw [(ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>"),
          (ls_stub% "memcpy")])
  have hpos : 0 < payload.length := List.length_pos_of_ne_nil hne
  refine SepWPpX.call (x := (ptr + BitVec.ofNat 64 bs.length, srcPtr, payload))
    (F := ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
           A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)
             (cap.toNat - bs.length - payload.length) ∗
           memRegion (stkSp - BitVec.ofNat 64 encodeRawSubStack)
             (encodeRawSubStack - extHookStack)) ∗ F_rest)
    hcall hpc hrun halign hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, hF, ← hsp_stk, stackAt_sub_to_memcpy_er s.sp,
        vecU8At_expose_slice A v cap ptr bs payload.length hle hcap hptr hpos] at hm
    simp only [sessionMemcpySpec, libcMemcpySpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    apply satisfies_of_sep_focus hm
    sep_focus
  · intro _ _ _ _ hm
    exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm
    simp only [sessionMemcpySpec, libcMemcpySpec, sepConj_assoc] at hm
    exact False.elim (not_satisfies_false_sepConj hm)
  · intro sm hpcm hrunm hspm hcsm
    simp only [sessionMemcpySpec, libcMemcpySpec, sepConj_assoc]
    refine SepWPpX.pure_elim fun ⟨_, htrm⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPpX.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm' hcsm)
    rw [hF, ← hsp_stk, stackAt_sub_to_memcpy_er s.sp]
    exact entails_of_sep_focus (by sep_focus)

/-- Execute a `bl encode::<Chain>` call inside `encode_raw` on `protoChainAt` when `s.sp = sp0 - 80#64`. -/
theorem encraw_call_protoEncodeChain {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hEC : OkAtX img ext encodeChainName (encodeChainSpecX A))
    (tag : Nat) (sp0 a v cap ptr ret_pc : BitVec 64)
    (gc : ChainGhost × ReceiverChain) (bs : List (BitVec 8))
    (htag : tag = 6 ∨ tag = 7)
    (hlen_lt : bs.length + (lenField tag (encChainMem gc)).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
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
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((protoChainAt A gc a ∗ vecU8At A v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hcall := encraw_encodeChain_ok hEC
  refine SepWPpX.call (x := ⟨tag, a, gc, v, cap, ptr, bs⟩)
    (F := memRegion (sp0 - 80#64 - BitVec.ofNat 64 encodeRawSubStack)
            (encodeRawSubStack - encodeChainStackX) ∗ F)
    hcall hpc hrun halign hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_encodeChain (sp0 - 80#64)] at hm
    simp only [encodeChainSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, htag, hlen_lt⟩, ?_⟩
    apply satisfies_of_sep_focus hm
    sep_focus
  · intro _ _ _ _ hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ R' hm
    simp only [encodeChainSpecX, allocPanic, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [encodeChainSpecX, hsp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpX.exists_elim fun cap' => SepWPpX.exists_elim fun ptr' => ?_
    refine SepWPpX.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPpX.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm' hcsm)
    rw [stackAt_sub_to_encodeChain (sp0 - 80#64)]
    exact entails_of_sep_focus (by sep_focus)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
