/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCallees
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.StringCloneFlatX
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.Fetches
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.ModelAndLayout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Stage 1 Callee Wrappers and Shared Error Epilogue

Provides stack-frame split/merge lemmas, `SpeOwned` error payload builders, direct `BL` callee
wrappers at residual stack `stk - cliInitiateFrame`, and the shared Stage 1 error epilogue
(`0x0350 → ret`) for `signal_session_handshake::initiate`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.E2E
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open Stage1Norm

/-! ## Stack split/merge and `SpeOwned` payload builders -/

theorem stackAt_sub_split_local (sp : BitVec 64) {sub full : Nat}
    (hle : sub ≤ full) (hfull : full ≤ 2 ^ 64) :
    stackAt sp full =
      memRegion (sp - BitVec.ofNat 64 full) (full - sub) ∗ stackAt sp sub := by
  have h := stackAt_split_bottom sp sub (full - sub) (by omega)
  rwa [Nat.add_sub_of_le hle] at h

theorem stackAt_entry_split (s0 : State) {stk : Nat}
    (hge : cliInitiateFrame ≤ stk) (hle : stk ≤ 2 ^ 63) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    stackAt s0.sp stk =
      stackAt fsp (stk - cliInitiateFrame) ∗
        memRegion fsp initLocalsSize ∗
        memRegion (s0.sp - 0x60#64) 0x60 := by
  intro fsp
  have h1 : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cliInitiateFrame) ∗
        stackAt s0.sp cliInitiateFrame :=
    stackAt_sub_split_local s0.sp hge (by omega)
  have hbot : memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cliInitiateFrame) =
      stackAt fsp (stk - cliInitiateFrame) := by
    unfold stackAt
    have haddr : s0.sp - BitVec.ofNat 64 stk =
        fsp - BitVec.ofNat 64 (stk - cliInitiateFrame) := by
      dsimp only [fsp]
      have hd : BitVec.ofNat 64 cliInitiateFrame + BitVec.ofNat 64 (stk - cliInitiateFrame) =
          BitVec.ofNat 64 stk := by
        rw [← BitVec.ofNat_add, Nat.add_sub_cancel' hge]
      rw [← hd]
      exact (BitVec.sub_sub s0.sp _ _).symm
    rw [haddr]
  have htop : stackAt s0.sp cliInitiateFrame =
      memRegion fsp initLocalsSize ∗ memRegion (s0.sp - 0x60#64) 0x60 := by
    unfold stackAt
    change memRegion fsp (initLocalsSize + 0x60) = _
    rw [memRegion_split fsp initLocalsSize 0x60 (by decide)]
    have hfp : fsp + BitVec.ofNat 64 initLocalsSize = s0.sp - 0x60#64 := by
      dsimp only [fsp]
      change (s0.sp - 7408#64) + 7312#64 = s0.sp - 96#64
      bv_omega
    rw [hfp]
  rw [h1, hbot, htop]

theorem memRegion_saved_split (b : BitVec 64) :
    memRegion b 0x60 =
      ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64,
      ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        ((b + 0x00#64) ↦₆₄ w0) ∗ ((b + 0x08#64) ↦₆₄ w1) ∗
        ((b + 0x10#64) ↦₆₄ w2) ∗ ((b + 0x18#64) ↦₆₄ w3) ∗
        ((b + 0x20#64) ↦₆₄ w4) ∗ ((b + 0x28#64) ↦₆₄ w5) ∗
        ((b + 0x30#64) ↦₆₄ w6) ∗ ((b + 0x38#64) ↦₆₄ w7) ∗
        ((b + 0x40#64) ↦₆₄ w8) ∗ ((b + 0x48#64) ↦₆₄ w9) ∗
        ((b + 0x50#64) ↦₆₄ w10) ∗ ((b + 0x58#64) ↦₆₄ w11) := by
  have split8 : ∀ a n, n ≥ 8 → n ≤ 96 →
      memRegion a n = (∃∗ w : BitVec 64, a ↦₆₄ w) ∗ memRegion (a + 8#64) (n - 8) := by
    intro a n hge _hle
    have hn : n = 8 + (n - 8) := by omega
    conv_lhs => rw [hn]
    rw [memRegion_split a 8 (n - 8) (by omega), ProofLib.memRegion_eight]
  rw [split8 b 96 (by decide) (by decide),
      split8 _ 88 (by decide) (by decide),
      split8 _ 80 (by decide) (by decide),
      split8 _ 72 (by decide) (by decide),
      split8 _ 64 (by decide) (by decide),
      split8 _ 56 (by decide) (by decide),
      split8 _ 48 (by decide) (by decide),
      split8 _ 40 (by decide) (by decide),
      split8 _ 32 (by decide) (by decide),
      split8 _ 24 (by decide) (by decide),
      split8 _ 16 (by decide) (by decide),
      ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero,
    sepExists_sepConj_left, sepExists_sepConj_right]

theorem initSaved_entails_memRegion (s0 : State) :
    initSaved s0 ⊢ memRegion (s0.sp - 0x60#64) 0x60 := by
  unfold initSaved
  dsimp only
  rw [memRegion_saved_split (s0.sp - 0x60#64)]
  sep_frame

theorem memRegion_48_words (a : BitVec 64) :
    memRegion a 48 =
      ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
        ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) := by
  have split8 : ∀ p n, n ≥ 8 → n ≤ 48 →
      memRegion p n = (∃∗ w : BitVec 64, p ↦₆₄ w) ∗ memRegion (p + 8#64) (n - 8) := by
    intro p n hge _hle
    have hn : n = 8 + (n - 8) := by omega
    conv_lhs => rw [hn]
    rw [memRegion_split p 8 (n - 8) (by omega), ProofLib.memRegion_eight]
  rw [split8 a 48 (by decide) (by decide),
      split8 _ 40 (by decide) (by decide),
      split8 _ 32 (by decide) (by decide),
      split8 _ 24 (by decide) (by decide),
      split8 _ 16 (by decide) (by decide),
      ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]

abbrev stage1Err : Except (ApiError AddrVal Unit) Unit :=
  .error (.untrustedIdentity ⟨[], 0#8⟩)

theorem words_to_plain11_initResAt (A : RustAlloc) (r w0 w1 w2 w3 w4 w5 : BitVec 64)
    (hw0 : w0 = speWord 11) :
    (r ↦₆₄ w0) ∗ ((r + 8#64) ↦₆₄ w1) ∗ ((r + 16#64) ↦₆₄ w2) ∗
      ((r + 24#64) ↦₆₄ w3) ∗ ((r + 32#64) ↦₆₄ w4) ∗ ((r + 40#64) ↦₆₄ w5) ⊢
      initResAt A r stage1Err := by
  subst hw0
  have h11 : RunDrop.PlainSpeTag 11 := by decide
  change _ ⊢ ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A r k
  refine Entails.sepExists_right (RunDrop.SpeOwned.plain 11 h11) ?_
  dsimp only [RunDrop.speOwnedAt]
  have htail :
      ((r + 8#64) ↦₆₄ w1) ∗ ((r + 16#64) ↦₆₄ w2) ∗
        ((r + 24#64) ↦₆₄ w3) ∗ ((r + 32#64) ↦₆₄ w4) ∗ ((r + 40#64) ↦₆₄ w5) ⊢
        memRegion (r + 8#64) 40 := by
    have split8 : ∀ p n, n ≥ 8 → n ≤ 40 →
        memRegion p n = (∃∗ w : BitVec 64, p ↦₆₄ w) ∗ memRegion (p + 8#64) (n - 8) := by
      intro p n hge _hle
      have hn : n = 8 + (n - 8) := by omega
      conv_lhs => rw [hn]
      rw [memRegion_split p 8 (n - 8) (by omega), ProofLib.memRegion_eight]
    rw [split8 (r + 8#64) 40 (by decide) (by decide),
        split8 _ 32 (by decide) (by decide),
        split8 _ 24 (by decide) (by decide),
        split8 _ 16 (by decide) (by decide),
        ProofLib.memRegion_eight]
    simp only [BitVec.add_assoc, BitVec.reduceAdd,
      sepExists_sepConj_left, sepExists_sepConj_right]
    sep_frame
  exact sepConj_mono_right htail

theorem pointsTo64_low_byte_entails (p w : BitVec 64) :
    (p ↦₆₄ w) ⊢ (p ↦₈ BitVec.extractLsb' 0 8 w) ∗ memRegion (p + 1#64) 7 := by
  have hlen1 : ([BitVec.extractLsb' 0 8 w]).length = 1 := rfl
  have hlen7 : ((unpack64 w).drop 1).length = 7 := by simp [unpack64_length]
  have hhead : (unpack64 w).take 1 = [BitVec.extractLsb' 0 8 w] := by
    simp [unpack64]
  rw [pointsTo64_eq_pointsToBytes, ← List.take_append_drop 1 (unpack64 w),
      pointsToBytes_append, hhead, hlen1]
  have h1 : (p ↦ₛ [BitVec.extractLsb' 0 8 w]) = (p ↦₈ BitVec.extractLsb' 0 8 w) := by
    rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  rw [h1]
  refine sepConj_mono_right ?_
  have hr := pointsToBytes_entails_memRegion (p + 1#64) ((unpack64 w).drop 1)
  rwa [hlen7] at hr

def stage1VecBuf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8_unpack_words (A : RustAlloc) (p : BitVec 64) (bs : List (BitVec 8)) :
    RustHeap.vecU8 A p bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (p ↦₆₄ cap) ∗ ((p + 8#64) ↦₆₄ ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        stage1VecBuf A cap ptr bs := by
  unfold RustHeap.vecU8 vecU8At vecHeader stage1VecBuf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  exact Entails.of_eq (by ac_rfl)

theorem stage1VecBuf_to_vecU8 (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      stage1VecBuf A cap ptr bs) ⊢ RustHeap.vecU8 A v bs := by
  unfold RustHeap.vecU8 vecU8At vecHeader stage1VecBuf
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  exact Entails.of_eq (by ac_rfl)

theorem words_to_untrusted_initResAt (A : RustAlloc) (r : BitVec 64) (addr : AddrVal)
    (w0 cap ptr len w4 w5 : BitVec 64)
    (hw0 : w0 = speWord speUntrustedIdentity)
    (hlen : len = BitVec.ofNat 64 addr.name.length)
    (hdev : BitVec.extractLsb' 0 8 w4 = addr.device) :
    (r ↦₆₄ w0) ∗ ((r + 8#64) ↦₆₄ cap) ∗ ((r + 16#64) ↦₆₄ ptr) ∗
      ((r + 24#64) ↦₆₄ len) ∗ ((r + 32#64) ↦₆₄ w4) ∗ ((r + 40#64) ↦₆₄ w5) ∗
      stage1VecBuf A cap ptr addr.name ⊢
      initResAt A r stage1Err := by
  subst hw0; subst hlen
  change _ ⊢ ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A r k
  refine Entails.sepExists_right (RunDrop.SpeOwned.untrustedIdentity addr) ?_
  dsimp only [RunDrop.speOwnedAt, apiErrAt, addrCloneAt]
  have hv :
      ((r + 8#64) ↦₆₄ cap) ∗ ((r + 16#64) ↦₆₄ ptr) ∗
        ((r + 24#64) ↦₆₄ BitVec.ofNat 64 addr.name.length) ∗
        stage1VecBuf A cap ptr addr.name ⊢ RustHeap.vecU8 A (r + 8#64) addr.name := by
    have h0 := stage1VecBuf_to_vecU8 A (r + 8#64) cap ptr addr.name
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h0
  have hw4 : ((r + 32#64) ↦₆₄ w4) ⊢ ((r + 32#64) ↦₈ addr.device) ∗ memRegion (r + 33#64) 7 := by
    have h := pointsTo64_low_byte_entails (r + 32#64) w4
    rw [hdev] at h
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  have hw5 : ((r + 40#64) ↦₆₄ w5) ⊢ memRegion (r + 40#64) 8 :=
    pointsTo64_entails_memRegion (r + 40#64) w5
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have rearrange :
      (r ↦₆₄ speWord speUntrustedIdentity) ∗ ((r + 8#64) ↦₆₄ cap) ∗ ((r + 16#64) ↦₆₄ ptr) ∗
        ((r + 24#64) ↦₆₄ BitVec.ofNat 64 addr.name.length) ∗
        ((r + 32#64) ↦₆₄ w4) ∗ ((r + 40#64) ↦₆₄ w5) ∗ stage1VecBuf A cap ptr addr.name =
      (r ↦₆₄ speWord speUntrustedIdentity) ∗
        (((r + 8#64) ↦₆₄ cap) ∗ ((r + 16#64) ↦₆₄ ptr) ∗
          ((r + 24#64) ↦₆₄ BitVec.ofNat 64 addr.name.length) ∗ stage1VecBuf A cap ptr addr.name) ∗
        ((r + 32#64) ↦₆₄ w4) ∗ ((r + 40#64) ↦₆₄ w5) := by ac_rfl
  rw [rearrange]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono hv (sepConj_mono hw4 hw5))) ?_
  sep_frame

/-! ## Direct `BL` callee wrappers at residual stack `stk - cliInitiateFrame` -/

theorem fnAddr_add_rel_init {b : BitVec 64} {ext : String → Option (State → State)}
    (n1 n2 : String) {k : Nat}
    (hk : libsignalSessionCode.fnOff n1 + k = libsignalSessionCode.fnOff n2) :
    (tripleRatchetProgAtExt b ext).fnAddr n1 + BitVec.ofNat 64 k =
      (tripleRatchetProgAtExt b ext).fnAddr n2 := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, hk]

theorem lift_stack_inImage_ext {α : Type} {prog : Program} {img : Obj.Image}
    {e : BitVec 64} {spec : Nat → Spec α} {sub full : Nat}
    (hsub : subroutine_ok prog e ((spec sub).inImage img))
    (_hle : sub ≤ full) (_hhi : full ≤ 2 ^ 64)
    (hpreEq : ∀ x s, (spec full).pre x s =
      memRegion (s.sp - BitVec.ofNat 64 full) (full - sub) ∗ (spec sub).pre x s)
    (hpostEq : ∀ x s0 sf, (spec full).post x s0 sf =
      memRegion (s0.sp - BitVec.ofNat 64 full) (full - sub) ∗ (spec sub).post x s0 sf)
    (hpanEq : ∀ x s0 sf, (spec sub).onPanic x s0 sf ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap)
    (hpanFull : ∀ x s0 sf,
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ⊢ (spec full).onPanic x s0 sf)
    (hexit : ∀ x c s0 sf, (spec sub).onExit x c s0 sf = ⌜False⌝)
    (hoom : ∀ x s0 sf, (spec sub).onOom x s0 sf = ⌜False⌝) :
    subroutine_ok prog e ((spec full).inImage img) := by
  apply subroutine_ok_outcome_intro
  intro gx R s0 hpc hrun hpre hsp
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ (spec full).pre gx s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  rw [hpreEq gx s0] at hpre
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 full) (full - sub)
  have hpre0 : s0.mem ⊨ ((spec sub).inImage img).pre gx s0 ∗ (stkRem ∗ R) := by
    refine satisfies_inImage_pre hinv ?_
    dsimp only [stkRem]
    convert hpre using 1; ac_rfl
  refine (hsub.to_outcome gx (stkRem ∗ R) s0 hpc hrun hpre0 hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨c, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change sf.mem ⊨ (spec full).post gx s0 sf ∗ R
    change sf.mem ⊨ (spec sub).post gx s0 sf ∗ (stkRem ∗ R) at hq
    rw [hpostEq gx s0 sf]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    change sf.mem ⊨ (spec sub).onPanic gx s0 sf ∗ (stkRem ∗ R) at hq
    change sf.mem ⊨ (spec full).onPanic gx s0 sf ∗ R
    have h1 : (spec sub).onPanic gx s0 sf ∗ stkRem ⊢ (spec full).onPanic gx s0 sf := by
      refine Entails.trans (sepConj_mono_left (hpanEq gx s0 sf)) ?_
      rw [sepConj_assoc]
      exact Entails.trans (sepConj_mono_right (entails_anyHeap _)) (hpanFull gx s0 sf)
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left h1) hq
  · change sf.mem ⊨ (spec sub).onExit gx c s0 sf ∗ (stkRem ∗ R) at hq
    rw [hexit] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · change sf.mem ⊨ (spec sub).onOom gx s0 sf ∗ (stkRem ∗ R) at hq
    rw [hoom] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem lift_stack_inImage {α : Type} {img : Obj.Image} {W : CliHooks}
    {e : BitVec 64} {spec : Nat → Spec α} {sub full : Nat}
    (hsub : subroutine_ok (initProg img W) e ((spec sub).inImage img))
    (hle : sub ≤ full) (hhi : full ≤ 2 ^ 64)
    (hpreEq : ∀ x s, (spec full).pre x s =
      memRegion (s.sp - BitVec.ofNat 64 full) (full - sub) ∗ (spec sub).pre x s)
    (hpostEq : ∀ x s0 sf, (spec full).post x s0 sf =
      memRegion (s0.sp - BitVec.ofNat 64 full) (full - sub) ∗ (spec sub).post x s0 sf)
    (hpanEq : ∀ x s0 sf, (spec sub).onPanic x s0 sf ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap)
    (hpanFull : ∀ x s0 sf,
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ⊢ (spec full).onPanic x s0 sf)
    (hexit : ∀ x c s0 sf, (spec sub).onExit x c s0 sf = ⌜False⌝)
    (hoom : ∀ x s0 sf, (spec sub).onOom x s0 sf = ⌜False⌝) :
    subroutine_ok (initProg img W) e ((spec full).inImage img) :=
  lift_stack_inImage_ext hsub hle hhi hpreEq hpostEq hpanEq hpanFull hexit hoom

theorem init_dealloc_ok_at_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {stk : Nat} (hh : RunHooksExt img A (cliExternsWith ext))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliInitiateName +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
      ((rustDeallocExternSpecWithStack A (stk - cliInitiateFrame)).inImage img) := by
  have hbase := dealloc_ok_at_norm_ext_x hh.alloc (name := cliInitiateName)
    (k := num% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
    (by rw [cliInitiate_fnOff, (ls_stub% "__rustc::__rust_dealloc")])
  have hle : extHookStack ≤ stk - cliInitiateFrame := by
    have h1 := stk_sub_ge_base hstk
    have hext : extHookStack ≤ 65536 := by decide
    omega
  have hhi : stk - cliInitiateFrame ≤ 2 ^ 64 := by omega
  apply subroutine_ok_outcome_intro
  intro gx R s0 hpc hrun hpre hsp
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (rustDeallocExternSpecWithStack A (stk - cliInitiateFrame)).pre gx s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  dsimp only [rustDeallocExternSpecWithStack, withStack] at hpre
  rw [stackAt_sub_split_local s0.sp hle hhi] at hpre
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 (stk - cliInitiateFrame))
    ((stk - cliInitiateFrame) - extHookStack)
  have hpre0 : s0.mem ⊨ ((rustDeallocExternSpecWithStack A extHookStack).inImage img).pre gx s0 ∗
      (stkRem ∗ R) := by
    refine satisfies_inImage_pre hinv ?_
    dsimp only [rustDeallocExternSpecWithStack, withStack, stkRem]
    convert hpre using 1; ac_rfl
  refine (hbase.to_outcome gx (stkRem ∗ R) s0 hpc hrun hpre0 hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change sf.mem ⊨ (rustDeallocExternSpecWithStack A (stk - cliInitiateFrame)).post gx s0 sf ∗ R
    dsimp only [Spec.inImage, rustDeallocExternSpecWithStack, withStack] at hq ⊢
    rw [stackAt_sub_split_local s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem init_dealloc_ok_at {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {B : RunBudgets}
    {stk : Nat} (hh : RunHooks img A (cliExterns W))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliInitiateName +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
      ((rustDeallocExternSpecWithStack A (stk - cliInitiateFrame)).inImage img) :=
  init_dealloc_ok_at_ext (ext := cliHookExterns W) hh.toExt hstk hstk64

def stringCloneAtStkSpec (A : RustAlloc) (calleeStk : Nat) :
    Spec (BitVec 64 × BitVec 64 × VecGhost) where
  pre := fun (p, ret, g) s =>
    ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret⌝ ∗ vecGhostAt A g p ∗ memRegion ret 24 ∗
      A.pool ∗ stackAt s.sp calleeStk
  post := fun (p, ret, g) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ vecGhostAt A g p ∗ vecU8 A ret g.bytes ∗ A.pool ∗
      stackAt s0.sp calleeStk
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem init_stringClone_ok_at_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {stk : Nat} (hh : RunHooksExt img A (cliExternsWith ext))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliInitiateName +
        bv% (ls_rel% "libsignal_cli_handshake::initiate"
          "<alloc::string::String as core::clone::Clone>::clone"))
      ((stringCloneAtStkSpec A (stk - cliInitiateFrame)).inImage img) := by
  have heq :
      (initProgExt img ext).fnAddr cliInitiateName +
        bv% (ls_rel% "libsignal_cli_handshake::initiate"
          "<alloc::string::String as core::clone::Clone>::clone") =
      (tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr stringCloneHookName :=
    fnAddr_add_rel_init cliInitiateName stringCloneHookName
      (k := ls_rel% "libsignal_cli_handshake::initiate"
        "<alloc::string::String as core::clone::Clone>::clone")
      (by rw [cliInitiate_fnOff,
          LibsignalBinary.Proofs.Common.StringCloneFlat.stringCloneName_fnOff])
  have hbase :
      subroutine_ok (initProgExt img ext)
        ((initProgExt img ext).fnAddr cliInitiateName +
          bv% (ls_rel% "libsignal_cli_handshake::initiate"
            "<alloc::string::String as core::clone::Clone>::clone"))
        ((stringCloneAtStkSpec A (2 * extHookStack)).inImage img) := by
    rw [heq]
    exact LibsignalBinary.Proofs.Common.StringCloneFlatX.stringClone2x_inImage_of_allocContractsX hh.alloc
  have hle : 2 * extHookStack ≤ stk - cliInitiateFrame := by
    have h1 := stk_sub_ge_base hstk
    have hext : 2 * extHookStack ≤ 65536 := by decide
    omega
  have hhi : stk - cliInitiateFrame ≤ 2 ^ 64 := by omega
  exact lift_stack_inImage_ext hbase hle hhi
    (fun (p, ret, g) s => by
      dsimp only [stringCloneAtStkSpec]
      rw [stackAt_sub_split_local s.sp hle hhi]
      ac_rfl)
    (fun (p, ret, g) s0 sf => by
      dsimp only [stringCloneAtStkSpec]
      rw [stackAt_sub_split_local s0.sp hle hhi]
      ac_rfl)
    (fun _ _ _ => Entails.refl _)
    (fun _ _ _ => Entails.refl _)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl)

theorem init_stringClone_ok_at {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {B : RunBudgets}
    {stk : Nat} (hh : RunHooks img A (cliExterns W))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliInitiateName +
        bv% (ls_rel% "libsignal_cli_handshake::initiate"
          "<alloc::string::String as core::clone::Clone>::clone"))
      ((stringCloneAtStkSpec A (stk - cliInitiateFrame)).inImage img) :=
  init_stringClone_ok_at_ext (ext := cliHookExterns W) hh.toExt hstk hstk64

def pubKeySerializeAtStkSpec (A : RustAlloc) (calleeStk : Nat) : Spec PublicKeySerializeCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self⌝ ∗ (x.self ↦ₛ x.pk.bytes.toList) ∗ A.pool ∗ stackAt s.sp calleeStk
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x1 = 33#64 ∧ sf.trace = s0.trace⌝ ∗
      (x.self ↦ₛ x.pk.bytes.toList) ∗ boxU8Buf A (sf.readReg64 .x0) x.pk.serialize ∗
      A.pool ∗ stackAt s0.sp calleeStk
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem init_pubKeySerialize_ok_at_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {stk : Nat}
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliInitiateName +
        bv% (2 ^ 64 + ls_off% "<libsignal_core::curve::PublicKey>::serialize" -
          ls_off% "libsignal_cli_handshake::initiate"))
      ((pubKeySerializeAtStkSpec A (stk - cliInitiateFrame)).inImage img) := by
  have haddr :
      (initProgExt img ext).fnAddr cliInitiateName +
        bv% (2 ^ 64 + ls_off% "<libsignal_core::curve::PublicKey>::serialize" -
          ls_off% "libsignal_cli_handshake::initiate") =
        (initProgExt img ext).fnAddr publicKeySerializeName := by
    have h1 := cliInitiate_fnOff
    have h2 : libsignalSessionCode.fnOff publicKeySerializeName =
        num% (ls_off% "<libsignal_core::curve::PublicKey>::serialize") :=
      Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
        (ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::serialize")
    simp only [initProgExt, tripleRatchetProgAtExt, Program.fnAddr_rebase,
      cliInitiateName, publicKeySerializeName, h1, h2]
    bv_omega
  rw [haddr]
  have hbase := public_key_serialize_ok_ext_x hh.alloc
  have hle : publicKeySerializeStackX ≤ stk - cliInitiateFrame := by
    have h1 := stk_sub_ge_base hstk
    have hp : publicKeySerializeStackX ≤ 65536 := by decide
    omega
  have hhi : stk - cliInitiateFrame ≤ 2 ^ 64 := by omega
  have hspecEq : publicKeySerializeSpecX A = pubKeySerializeAtStkSpec A publicKeySerializeStackX :=
    rfl
  rw [hspecEq] at hbase
  exact lift_stack_inImage_ext hbase hle hhi
    (fun gx s => by
      dsimp only [pubKeySerializeAtStkSpec]
      rw [stackAt_sub_split_local s.sp hle hhi]
      ac_rfl)
    (fun gx s0 sf => by
      dsimp only [pubKeySerializeAtStkSpec]
      rw [stackAt_sub_split_local s0.sp hle hhi]
      ac_rfl)
    (fun _ _ _ => Entails.refl _)
    (fun _ _ _ => Entails.refl _)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl)

theorem init_pubKeySerialize_ok_at {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {B : RunBudgets} {stk : Nat} (hh : RunHooks img A (cliExterns W))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliInitiateName +
        bv% (2 ^ 64 + ls_off% "<libsignal_core::curve::PublicKey>::serialize" -
          ls_off% "libsignal_cli_handshake::initiate"))
      ((pubKeySerializeAtStkSpec A (stk - cliInitiateFrame)).inImage img) :=
  init_pubKeySerialize_ok_at_ext (ext := cliHookExterns W) hh.toExt hstk hstk64

def verifySigAtStkSpec (P : SignalPqxdh.Primitives) (calleeStk : Nat) :
    Spec VerifySignatureGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.pkPtr ∧
      s.readReg64 .x1 = g.msgPtr ∧
      s.readReg64 .x2 = BitVec.ofNat 64 g.m.length ∧
      s.readReg64 .x3 = g.sigPtr ∧
      s.readReg64 .x4 = 64#64 ∧
      g.pk.length = 32 ∧
      (g.m.length = 33 ∨ g.m.length = 1569) ∧
      g.sig.length = 64⌝ ∗
      (g.pkPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.pk) ∗
      (g.msgPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.m) ∗
      (g.sigPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.sig) ∗
      stackAt s.sp calleeStk
  post := fun g s0 sf =>
    ⌜sf.readReg64 .x0 = (if P.sigVerify g.pk g.m g.sig = true then 1#64 else 0#64) ∧
      sf.trace = s0.trace⌝ ∗
      (g.pkPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.pk) ∗
      (g.msgPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.m) ∗
      (g.sigPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.sig) ∗
      stackAt s0.sp calleeStk

theorem init_verifySig_ok_at_ext {img : Obj.Image} {P : PEParams}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives}
    {calStk stk : Nat} (hcal : calStk ≤ stk - cliInitiateFrame) (hstk64 : stk ≤ 2 ^ 63)
    (hVerify : subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliVerifySignatureName)
      ((verifySigAtStkSpec (modelPrims X P) calStk).inImage img)) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliInitiateName +
        bv% (2 ^ 64 + ls_off% "<libsignal_core::curve::PublicKey>::verify_signature" -
          ls_off% "libsignal_cli_handshake::initiate"))
      ((verifySigAtStkSpec (modelPrims X P) (stk - cliInitiateFrame)).inImage img) := by
  have haddr :
      (initProgExt img ext).fnAddr cliInitiateName +
        bv% (2 ^ 64 + ls_off% "<libsignal_core::curve::PublicKey>::verify_signature" -
          ls_off% "libsignal_cli_handshake::initiate") =
        (initProgExt img ext).fnAddr cliVerifySignatureName := by
    have h1 := cliInitiate_fnOff
    have h2 := cliVerifySignature_fnOff
    simp only [initProgExt, tripleRatchetProgAtExt, Program.fnAddr_rebase,
      cliInitiateName, cliVerifySignatureName, h1, h2]
    bv_omega
  rw [haddr]
  have hhi : stk - cliInitiateFrame ≤ 2 ^ 64 := by omega
  apply subroutine_ok_outcome_intro
  intro gx R s0 hpc hrun hpre hsp
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (verifySigAtStkSpec (modelPrims X P) (stk - cliInitiateFrame)).pre gx s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  dsimp only [verifySigAtStkSpec] at hpre
  rw [stackAt_sub_split_local s0.sp hcal hhi] at hpre
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 (stk - cliInitiateFrame))
    ((stk - cliInitiateFrame) - calStk)
  have hpre0 : s0.mem ⊨
      ((verifySigAtStkSpec (modelPrims X P) calStk).inImage img).pre gx s0 ∗ (stkRem ∗ R) := by
    refine satisfies_inImage_pre hinv ?_
    dsimp only [verifySigAtStkSpec, stkRem]
    convert hpre using 1; ac_rfl
  refine (hVerify.to_outcome gx (stkRem ∗ R) s0 hpc hrun hpre0 hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change sf.mem ⊨
      (verifySigAtStkSpec (modelPrims X P) (stk - cliInitiateFrame)).post gx s0 sf ∗ R
    dsimp only [Spec.inImage, verifySigAtStkSpec] at hq ⊢
    rw [stackAt_sub_split_local s0.sp hcal hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem init_verifySig_ok_at {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {X : UnreachedPqxdhPrimitives}
    {B : RunBudgets} {stk : Nat} (hLocal : InitLocalCallees img A W stk)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliInitiateName +
        bv% (2 ^ 64 + ls_off% "<libsignal_core::curve::PublicKey>::verify_signature" -
          ls_off% "libsignal_cli_handshake::initiate"))
      ((verifySigAtStkSpec (modelPrims X ⟨W.C, W.Q⟩) (stk - cliInitiateFrame)).inImage img) := by
  have hbase := hLocal.verifySignature X
  have hspecEq : verifySignatureSpec (modelPrims X ⟨W.C, W.Q⟩) img =
      (verifySigAtStkSpec (modelPrims X ⟨W.C, W.Q⟩)
        (Pqxdh.Shared.pqxdhHookStack + 1280)).inImage img := rfl
  rw [hspecEq] at hbase
  have hle : Pqxdh.Shared.pqxdhHookStack + 1280 ≤ stk - cliInitiateFrame := by
    have h1 := stk_sub_ge_base hstk
    have hp : Pqxdh.Shared.pqxdhHookStack + 1280 ≤ 516880 := by decide
    omega
  exact init_verifySig_ok_at_ext (P := ⟨W.C, W.Q⟩) (ext := cliHookExterns W) hle hstk64 hbase

theorem init_kemPubSerialize_ok_at {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {stk : Nat}
    (hLocal : InitLocalCallees img A W stk) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliInitiateName +
        bv% (ls_rel% "libsignal_cli_handshake::initiate"
          "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::serialize [local#1]"))
      (kemPubSerializeSpec A img (stk - cliInitiateFrame)) := by
  have haddr :
      (initProg img W).fnAddr cliInitiateName +
        bv% (ls_rel% "libsignal_cli_handshake::initiate"
          "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::serialize [local#1]") =
        (initProg img W).fnAddr cliKemPublicKeySerializeName := by
    have h1 := cliInitiate_fnOff
    have h2 := cliKemPublicKeySerialize_fnOff
    simp only [initProg, tripleRatchetProgAtExt, Program.fnAddr_rebase,
      cliInitiateName, cliKemPublicKeySerializeName, h1, h2]
    bv_omega
  rw [haddr]
  exact hLocal.kemPubSerialize

def memcpyScratchSpec (n calleeStk : Nat) : Spec (BitVec 64 × BitVec 64) where
  pre := fun (dst, src) s =>
    ⌜s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧ (s.readReg64 .x2).toNat = n⌝ ∗
      memRegion dst n ∗ memRegion src n ∗ stackAt s.sp calleeStk
  post := fun (dst, src) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion dst n ∗ memRegion src n ∗ stackAt s0.sp calleeStk

theorem memRegion_merge (a b : BitVec 64) (m n mn : Nat)
    (hb : a + BitVec.ofNat 64 m = b) (hmn : m + n = mn) (hle : mn ≤ 2 ^ 64) :
    memRegion a m ∗ memRegion b n = memRegion a mn := by
  subst hb; subst hmn
  exact (memRegion_split a m n hle).symm

theorem pointsTo16_zero_eq (a : BitVec 64) :
    (a ↦₁₆ 0#16) = ((a ↦₈ 0#8) ∗ ((a + 1#64) ↦₈ 0#8)) := by
  rw [pointsTo16_split8]; rfl

theorem byte_and_pad7_entails_word64 (p : BitVec 64) (b : BitVec 8) :
    (p ↦₈ b) ∗ memRegion (p + 1#64) 7 ⊢
      ∃∗ w : BitVec 64, ⌜BitVec.extractLsb' 0 8 w = b⌝ ∗ (p ↦₆₄ w) := by
  rw [ProofLib.memRegion_eq_exists_bytes (p + 1#64) 7 (by decide),
      sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  rw [show (p ↦₈ b) ∗ (⌜bs.length = 7⌝ ∗ ((p + 1#64) ↦ₛ bs)) =
        ⌜bs.length = 7⌝ ∗ ((p ↦₈ b) ∗ ((p + 1#64) ↦ₛ bs)) by ac_rfl]
  refine pure_sepConj_elim fun hlen => ?_
  have hcons : ((p ↦₈ b) ∗ ((p + 1#64) ↦ₛ bs)) = (p ↦ₛ (b :: bs)) :=
    (pointsToBytes_cons p b bs).symm
  obtain ⟨w, hw⟩ := exists_unpack64_of_length_8 (bs := b :: bs) (by simp [hlen])
  have hb : BitVec.extractLsb' 0 8 w = b := by
    have h0 := congrArg List.head? hw
    simp [unpack64] at h0
    exact h0.symm
  rw [hcons, hw, ← pointsTo64_eq_pointsToBytes]
  exact Entails.sepExists_right w (pure_sepConj_intro hb (Entails.refl _))

theorem initArgsAt_entails_memRegion (img : Obj.Image) (fsp : BitVec 64) (x : InitGhost)
    (s0 : State) :
    initArgsAt img fsp x s0 ⊢ memRegion (fsp + 0xd0#64) 0x58 := by
  unfold initArgsAt
  have m64 : ∀ p v, (p ↦₆₄ v) ⊢ memRegion p 8 := pointsTo64_entails_memRegion
  have m32 : ∀ p v, (p ↦₃₂ v) ⊢ memRegion p 4 := pointsTo32_entails_memRegion
  refine Entails.trans (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m32 _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (m64 _ _) (m64 _ _)))))))))))) ?_
  rw [← sepConj_assoc, memRegion_merge (fsp + 0xd0#64) (fsp + 0xd8#64) 8 8 16 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0xd0#64) (fsp + 0xe0#64) 16 8 24 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0xd0#64) (fsp + 0xe8#64) 24 8 32 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0xd0#64) (fsp + 0xf0#64) 32 8 40 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0xd0#64) (fsp + 0xf8#64) 40 8 48 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0xd0#64) (fsp + 0x100#64) 48 8 56 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0xd0#64) (fsp + 0x108#64) 56 8 64 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0xd0#64) (fsp + 0x110#64) 64 4 68 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0xd0#64) (fsp + 0x114#64) 68 4 72 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0xd0#64) (fsp + 0x118#64) 72 8 80 (by bv_omega) (by decide) (by decide)]
  rw [memRegion_merge (fsp + 0xd0#64) (fsp + 0x120#64) 80 8 88 (by bv_omega) (by decide) (by decide)]
  exact Entails.refl _

theorem stage2Locals_entails_memRegion (img : Obj.Image) (fsp : BitVec 64) (x : InitGhost)
    (s0 : State) :
    memRegion fsp 0xd0 ∗ initArgsAt img fsp x s0 ∗
      memRegion (fsp + 0x128#64) 0x490 ∗
      ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ⊢
      memRegion fsp initLocalsSize := by
  have h16 : ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ⊢
      memRegion (fsp + 0x5b8#64) 2 := by
    have hadd : (fsp + 0x5b8#64) + 1#64 = fsp + 0x5b9#64 := by bv_omega
    rw [← hadd, ← pointsTo16_zero_eq (fsp + 0x5b8#64)]
    exact pointsTo16_entails_memRegion _ _
  have h5ba :
      ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ (((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba)) ⊢
      memRegion (fsp + 0x5b8#64) (initLocalsSize - 0x5b8) := by
    rw [← sepConj_assoc]
    refine Entails.trans (sepConj_mono_left h16) ?_
    rw [memRegion_merge (fsp + 0x5b8#64) (fsp + 0x5ba#64) 2 (initLocalsSize - 0x5ba)
      (initLocalsSize - 0x5b8) (by bv_omega) (by decide) (by decide)]
    exact Entails.refl _
  refine Entails.trans
    (sepConj_mono_right
      (sepConj_mono (initArgsAt_entails_memRegion img fsp x s0)
        (sepConj_mono_right h5ba))) ?_
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0xd0#64) 0xd0 0x58 0x128
    (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0x128#64) 0x128 0x490 0x5b8
    (by bv_omega) (by decide) (by decide)]
  rw [memRegion_merge fsp (fsp + 0x5b8#64) 0x5b8 (initLocalsSize - 0x5b8) initLocalsSize
    (by bv_omega) (by decide) (by decide)]
  exact Entails.refl _

theorem init_memcpyScratch_ok_at_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {n stk : Nat}
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hn : n ≤ 2 ^ 64 := by decide) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliInitiateName +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
      ((memcpyScratchSpec n (stk - cliInitiateFrame)).inImage img) := by
  have hmc := hh.alloc.session_memcpy_region_ok_at cliInitiateName
    (ls_rel% "libsignal_cli_handshake::initiate" "memcpy")
    (hk := by rw [cliInitiate_fnOff]; simp only [arm64_norm])
  have hle : extHookStack ≤ stk - cliInitiateFrame := by
    have h1 := stk_sub_ge_base hstk
    have hext : extHookStack ≤ 65536 := by decide
    omega
  have hhi : stk - cliInitiateFrame ≤ 2 ^ 64 := by omega
  apply subroutine_ok_outcome_intro
  intro ⟨dst, src⟩ R s0 hpc hrun hpre hsp
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (memcpyScratchSpec n (stk - cliInitiateFrame)).pre (dst, src) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [memcpyScratchSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
  rw [ProofLib.memRegion_eq_exists_bytes src n hn] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨bs, hmem⟩
  rw [show memRegion dst n ∗ ((⌜bs.length = n⌝ ∗ (src ↦ₛ bs)) ∗
        stackAt s0.sp (stk - cliInitiateFrame) ∗ R) =
      ⌜bs.length = n⌝ ∗
        (memRegion dst n ∗ (src ↦ₛ bs) ∗ stackAt s0.sp (stk - cliInitiateFrame) ∗ R) by ac_rfl,
      satisfies_pure_sepConj] at hmem
  rcases hmem with ⟨hlen, hmem⟩
  subst hlen
  rw [stackAt_sub_split_local s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 (stk - cliInitiateFrame))
    ((stk - cliInitiateFrame) - extHookStack)
  have hpre0 : s0.mem ⊨
      ((withStack sessionMemcpyRegionSpec extHookStack).inImage img).pre
        (dst, src, bs) s0 ∗ (stkRem ∗ R) := by
    refine satisfies_inImage_pre hinv ?_
    simp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  refine (hmc.to_outcome (dst, src, bs) (stkRem ∗ R) s0 hpc hrun hpre0 hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change sf.mem ⊨ (memcpyScratchSpec bs.length (stk - cliInitiateFrame)).post (dst, src) s0 sf ∗ R
    simp only [Spec.inImage, withStack, sessionMemcpyRegionSpec,
      memcpyScratchSpec, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨⟨_hx0f, htr⟩, hq⟩
    refine ⟨htr, ?_⟩
    have h1 := pointsToBytes_entails_memRegion dst bs
    have h2 := pointsToBytes_entails_memRegion src bs
    rw [stackAt_sub_split_local s0.sp hle hhi]
    dsimp only [stkRem] at hq
    refine Satisfies.mono ?_ hq
    refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (Entails.refl _))) ?_
    sep_frame
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem init_memcpyScratch_ok_at {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {B : RunBudgets} {n stk : Nat} (hh : RunHooks img A (cliExterns W))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hn : n ≤ 2 ^ 64 := by decide) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliInitiateName +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
      ((memcpyScratchSpec n (stk - cliInitiateFrame)).inImage img) :=
  init_memcpyScratch_ok_at_ext (ext := cliHookExterns W) hh.toExt hstk hstk64 hn

theorem idTrustBoxAt_entails_memRegion (box self addrA keyA : BitVec 64) (st d : BitVec 8) :
    idTrustBoxAt box self addrA keyA st d ⊢ memRegion box 32 := by
  unfold idTrustBoxAt
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo8_entails_memRegion _ _)
            (sepConj_mono (pointsTo8_entails_memRegion _ _) (Entails.refl _)))))) ?_
  rw [← sepConj_assoc, memRegion_merge box (box + 8#64) 8 8 16 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge box (box + 0x10#64) 16 8 24 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge box (box + 0x18#64) 24 1 25 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge box (box + 0x19#64) 25 1 26 (by bv_omega) (by decide) (by decide)]
  rw [memRegion_merge box (box + 0x1a#64) 26 6 32 (by bv_omega) (by decide) (by decide)]
  exact Entails.refl _

theorem sessLoadBoxAt_entails_memRegion (box self addrA : BitVec 64) (st : BitVec 8) :
    sessLoadBoxAt box self addrA st ⊢ memRegion box 24 := by
  unfold sessLoadBoxAt
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo8_entails_memRegion _ _) (Entails.refl _)))) ?_
  rw [← sepConj_assoc, memRegion_merge box (box + 8#64) 8 8 16 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge box (box + 0x10#64) 16 1 17 (by bv_omega) (by decide) (by decide)]
  rw [memRegion_merge box (box + 0x11#64) 17 7 24 (by bv_omega) (by decide) (by decide)]
  exact Entails.refl _

theorem memRegion_two_pointsTo16 (a : BitVec 64) :
    memRegion a 2 ⊢ ∃∗ v : BitVec 16, a ↦₁₆ v := by
  rw [show (2 : Nat) = 1 + 1 from rfl, memRegion_split a 1 1 (by decide),
    ProofLib.memRegion_one, ProofLib.memRegion_one]
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro b0
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro b1
  refine Entails.sepExists_right (b1 ++ b0) ?_
  have h0 : BitVec.extractLsb' 0 8 (b1 ++ b0) = b0 := by bv_bits
  have h1 : BitVec.extractLsb' 8 8 (b1 ++ b0) = b1 := by bv_bits
  rw [pointsTo16_split8, h0, h1]
  exact Entails.refl _

theorem getLsbD0_of_extract8_one {w : BitVec 64} (h : BitVec.extractLsb' 0 8 w = 1#8) :
    w.getLsbD 0 = true := by
  have h0 : (BitVec.extractLsb' 0 8 w).getLsbD 0 = (1#8).getLsbD 0 := congrArg (·.getLsbD 0) h
  simpa using h0

theorem getLsbD0_of_extract8_zero {w : BitVec 64} (h : BitVec.extractLsb' 0 8 w = 0#8) :
    w.getLsbD 0 = false := by
  have h0 : (BitVec.extractLsb' 0 8 w).getLsbD 0 = (0#8).getLsbD 0 := congrArg (·.getLsbD 0) h
  simpa using h0

/-! ## Shared error epilogue (`0x0350 → ret`) -/

theorem sp_sub_96_sub_4096 (sp : BitVec 64) : (sp - 96#64) - 4096#64 = sp - 4192#64 := by bv_omega
theorem sp_sub_4192_sub_3216 (sp : BitVec 64) : (sp - 4192#64) - 3216#64 = sp - 7408#64 := by bv_omega
theorem sp_sub_96_add_96 (sp : BitVec 64) : (sp - 96#64) + 96#64 = sp := by bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit sp_sub_96_sub_4096 sp_sub_4192_sub_3216 sp_sub_96_add_96 BitVec.toNat_zero

theorem initSaved_norm (s0 : State) :
    initSaved s0 =
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .fp) ∗
      ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
      ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
      ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
      ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) := by
  unfold initSaved
  dsimp only
  rw [BitVec.add_zero,
      bv_sub_add_lit s0.sp 96 8,
      bv_sub_add_lit s0.sp 96 16,
      bv_sub_add_lit s0.sp 96 24,
      bv_sub_add_lit s0.sp 96 32,
      bv_sub_add_lit s0.sp 96 40,
      bv_sub_add_lit s0.sp 96 48,
      bv_sub_add_lit s0.sp 96 56,
      bv_sub_add_lit s0.sp 96 64,
      bv_sub_add_lit s0.sp 96 72,
      bv_sub_add_lit s0.sp 96 80,
      bv_sub_add_lit s0.sp 96 88]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 200000 in
theorem stage1_epilogue_err_ext_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {S : RunSem} {x : InitGhost} {stk : Nat} {s0 s : State}
    {H_err H_extra : SepProp} {Q Qp : State → SepProp → Prop}
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hctrl : InInitiateExt img ext s0 s 0x0350)
    (htr : s.trace = s0.trace)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hans : S.initiate x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hres :
      (x.ret ↦₆₄ s.readReg64 (.gpr 26#5)) ∗
        ((x.ret + 8#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
        ((x.ret + 16#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
        ((x.ret + 24#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
        ((x.ret + 32#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗
        ((x.ret + 40#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗ H_err ⊢
        initResAt A x.ret stage1Err) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s
      (storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗
        protocolAddressAt A x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        (s0.sp ↦₃₂ 0#32) ∗ logOff img ∗ A.pool ∗
        memRegion x.ret 48 ∗
        initSaved s0 ∗
        memRegion fsp initLocalsSize ∗
        stackAt fsp (stk - cliInitiateFrame) ∗
        H_err ∗ H_extra)
      Q Qp (initOom s0) := by
  intro fsp
  code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage1Bin img.base
    (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
    (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x0350 0x30
  have hpc := hctrl.pc
  have hrun := hctrl.run
  have hsp := hctrl.sp
  have hal0 := hctrl.spAligned
  have hx19 : s.readReg64 (.gpr 19#5) = x.ret := hctrl.x19.trans hx8
  have hfs := hctrl.files0
  have hvregs := hctrl.vregs
  dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpc ⊢
  try simp only [BitVec.ofNat_eq_ofNat] at hpc
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase
  examples_hide_fetches
  rw [memRegion_48_words x.ret, initSaved_norm s0]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_elim fun w5 => sepWPp_exists_elim fun w4 =>
    sepWPp_exists_elim fun w3 => sepWPp_exists_elim fun w2 =>
    sepWPp_exists_elim fun w1 => sepWPp_exists_elim fun w0 => ?_
  apply sepWPp_ret_of_sepWP
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  apply hpost
  refine ⟨?_, ?_, ?_⟩
  · simp only [wp_norm, arm64_norm]
  · unfold CalleeSavedPreserved
    simp [wp_norm, arm64_norm, hvregs]
  · have hstkMerge :
        initSaved s0 ∗ memRegion fsp initLocalsSize ∗ stackAt fsp (stk - cliInitiateFrame) ⊢
          stackAt s0.sp stk := by
      rw [stackAt_entry_split s0 (stk_ge_frame hstk) hstk64]
      refine Entails.trans
        (sepConj_mono_left (initSaved_entails_memRegion s0)) ?_
      sep_frame
    dsimp only [initSlotSpec, Spec.inImage]
    refine Entails.sepExists_right StoresGhost.opened ?_
    refine Entails.sepExists_right stage1Err ?_
    refine pure_sepConj_intro ⟨⟨?_, ?_, ?_⟩, ?_⟩ ?_
    · simp only [wp_norm, arm64_norm, htr]; exact List.prefix_refl _
    · simp only [wp_norm, arm64_norm, hfs]
    · simp only [wp_norm, arm64_norm, htr]
    · simp [slotOut, hans, stage1Err]
    simp only [← initSaved_norm s0]
    have hre :
        storesAt A x.stores StoresGhost.opened ∗
          protocolAddressAt A x.peer x.peerA ∗
          protocolAddressAt A x.me x.meA ∗
          cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
          (s0.sp ↦₃₂ 0#32) ∗ logOff img ∗ A.pool ∗
          ((x.ret ↦₆₄ s.readReg64 (.gpr 26#5)) ∗
            ((x.ret + 8#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
            ((x.ret + 16#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
            ((x.ret + 24#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
            ((x.ret + 32#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗
            ((x.ret + 40#64) ↦₆₄ s.readReg64 (.gpr 21#5))) ∗
          initSaved s0 ∗
          memRegion fsp initLocalsSize ∗
          stackAt fsp (stk - cliInitiateFrame) ∗ H_err ∗ H_extra =
        ((x.ret ↦₆₄ s.readReg64 (.gpr 26#5)) ∗
          ((x.ret + 8#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
          ((x.ret + 16#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
          ((x.ret + 24#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
          ((x.ret + 32#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗
          ((x.ret + 40#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗ H_err) ∗
        (initSaved s0 ∗ memRegion fsp initLocalsSize ∗ stackAt fsp (stk - cliInitiateFrame)) ∗
        H_extra ∗
        (storesAt A x.stores StoresGhost.opened ∗
          protocolAddressAt A x.peer x.peerA ∗
          protocolAddressAt A x.me x.meA ∗
          cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
          (s0.sp ↦₃₂ 0#32) ∗ logOff img ∗ A.pool) := by ac_rfl
    rw [hre]
    refine Entails.trans (sepConj_mono hres
      (sepConj_mono hstkMerge (sepConj_mono_left (entails_anyHeap H_extra)))) ?_
    sep_frame

theorem stage1_epilogue_err_ok {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {B : RunBudgets}
    {S : RunSem} {x : InitGhost} {stk : Nat} {s0 s : State}
    {H_err H_extra : SepProp} {Q Qp : State → SepProp → Prop}
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hctrl : InInitiate img W s0 s 0x0350)
    (htr : s.trace = s0.trace)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hans : S.initiate x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hres :
      (x.ret ↦₆₄ s.readReg64 (.gpr 26#5)) ∗
        ((x.ret + 8#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
        ((x.ret + 16#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
        ((x.ret + 24#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
        ((x.ret + 32#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗
        ((x.ret + 40#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗ H_err ⊢
        initResAt A x.ret stage1Err) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProg img W) (s0.readReg64 .lr) s
      (storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗
        protocolAddressAt A x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        (s0.sp ↦₃₂ 0#32) ∗ logOff img ∗ A.pool ∗
        memRegion x.ret 48 ∗
        initSaved s0 ∗
        memRegion fsp initLocalsSize ∗
        stackAt fsp (stk - cliInitiateFrame) ∗
        H_err ∗ H_extra)
      Q Qp (initOom s0) :=
  stage1_epilogue_err_ext_ok (ext := cliHookExterns W) hstk hstk64 (inInitiate_toExt hctrl)
    htr hx8 hans hpost hres

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
