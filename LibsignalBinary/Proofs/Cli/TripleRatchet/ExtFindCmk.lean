/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.Defs
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.FindChain
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.FindChainSym
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsX
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueX
import LibsignalBinary.Proofs.TripleRatchet.ChainKey.FindReceiverChainKey
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.RegChain
import ProofLib.SepLogic.WP.Apply

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-!
# Stacked `grow_one`, `find_receiver_chain_key`, and Segment S2 (`FindChain`)

Proves `GrowOneChainOkX`, `FindReceiverChainKeyOkExt144` (`17552` B), `FindReceiverChainKeyOkExtX`
(`18432` B), and `S2SpecExtX` on `tripleRatchetProgAtExt`.
-/

namespace CryptoVerification.Cli.LibsignalTripleRatchet.ExtFindCmk

open Arm64 ProofLib SepProp ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem growOneChain_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext) :
    Proofs.libsignal.Stage1X.GrowOneChainOkX img A ext :=
  Proofs.libsignal.Hooks2.grow_one_72_ok_ext_x hA

theorem growOneChain_ok_tr_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    Proofs.libsignal.Stage1X.GrowOneChainOkX img A ext :=
  Proofs.libsignal.Hooks2.grow_one_72_ok_ext_x
    (CryptoVerification.SignalSession.Cli.Store.SerGlueX.stage1XAllocContractsX_of_trAllocContractsX hA)

/-- Stacked budget of `RatchetState::find_receiver_chain_key` (`2048 + extHookStack = 18432` B,
also derivable at `144 + Stage1X.findIndexStackX = 17552` B). -/
abbrev findReceiverChainKeyStackExt144 : Nat := 144 + Proofs.libsignal.Stage1X.findIndexStackX
abbrev findReceiverChainKeyStackX : Nat := findReceiverChainKeyStack + extHookStack

def findReceiverChainKeySpecWithStack (A : RustAlloc) (img : Obj.Image) (stk : Nat) :
    Spec FindReceiverChainKeyGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.theirA ∧ s.readReg64 .x8 = x.ret⌝ ∗
        ratchetAt A x.self x.G x.st ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        memRegion x.ret 40 ∗
        logOff img ∗
        stackAt s.sp stk
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
        ratchetAt A x.self x.G x.st ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        findReceiverChainKeyResultAt x.ret (x.st.findReceiverChainKey x.their) ∗
        logOff img ∗
        stackAt s0.sp stk }
    img

def FindReceiverChainKeyOkExt144 (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr findReceiverChainKeyName)
    (findReceiverChainKeySpecWithStack A img findReceiverChainKeyStackExt144)

def FindReceiverChainKeyOkExtX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr findReceiverChainKeyName)
    (findReceiverChainKeySpecWithStack A img findReceiverChainKeyStackX)

private theorem entails_of_eq' {P P' Q : SepProp} (h : P = P') (hq : P' ⊢ Q) : P ⊢ Q :=
  h ▸ hq

private theorem mr_cut'' (sp : BitVec 64) (c c' n k N : Nat) (hN : n + k = N) (hc' : c - n = c')
    (hn : n ≤ c) (hc : c < 2 ^ 64) (h : N ≤ 2 ^ 64) :
    memRegion (sp - BitVec.ofNat 64 c) N =
      memRegion (sp - BitVec.ofNat 64 c) n ∗ memRegion (sp - BitVec.ofNat 64 c') k := by
  subst hN hc'
  have haddr : sp - BitVec.ofNat 64 c + BitVec.ofNat 64 n = sp - BitVec.ofNat 64 (c - n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    have h1 : c % 2 ^ 64 = c := Nat.mod_eq_of_lt hc
    have h2 : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hn hc)
    have h3 : (c - n) % 2 ^ 64 = c - n := Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le c n) hc)
    rw [h1, h2, h3]
    omega
  rw [← haddr]
  exact memRegion_split (sp - BitVec.ofNat 64 c) n k h

private theorem stackAt_frck144 (sp : BitVec 64) :
    stackAt sp findReceiverChainKeyStackExt144 =
      memRegion (sp - 17552#64) 64 ∗
      stackAt (sp - 80#64) Proofs.libsignal.Stage1X.findIndexStackX ∗
      memRegion (sp - 80#64) 32 ∗
      (∃∗ v29 : BitVec 64, (sp - 48#64) ↦₆₄ v29) ∗
      (∃∗ v30 : BitVec 64, (sp - 40#64) ↦₆₄ v30) ∗
      (∃∗ v21 : BitVec 64, (sp - 32#64) ↦₆₄ v21) ∗
      memRegion (sp - 24#64) 8 ∗
      (∃∗ v20 : BitVec 64, (sp - 16#64) ↦₆₄ v20) ∗
      (∃∗ v19 : BitVec 64, (sp - 8#64) ↦₆₄ v19) := by
  unfold stackAt findReceiverChainKeyStackExt144 Proofs.libsignal.Stage1X.findIndexStackX extHookStack
  simp only [Nat.reducePow, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  rw [mr_cut'' sp 17552 17488 64 17488 17552 rfl rfl (by decide) (by decide) (by decide),
      mr_cut'' sp 17488 80 17408 80 17488 rfl rfl (by decide) (by decide) (by decide),
      mr_cut'' sp 80 48 32 48 80 rfl rfl (by decide) (by decide) (by decide),
      mr_cut'' sp 48 40 8 40 48 rfl rfl (by decide) (by decide) (by decide),
      mr_cut'' sp 40 32 8 32 40 rfl rfl (by decide) (by decide) (by decide),
      mr_cut'' sp 32 24 8 24 32 rfl rfl (by decide) (by decide) (by decide),
      mr_cut'' sp 24 16 8 16 24 rfl rfl (by decide) (by decide) (by decide),
      mr_cut'' sp 16 8 8 8 16 rfl rfl (by decide) (by decide) (by decide)]
  rw [ProofLib.memRegion_eight (sp - 48#64), ProofLib.memRegion_eight (sp - 40#64),
      ProofLib.memRegion_eight (sp - 32#64), ProofLib.memRegion_eight (sp - 16#64),
      ProofLib.memRegion_eight (sp - 8#64)]
  have h17488 : sp - 80#64 - 17408#64 = sp - 17488#64 := by bv_omega
  rw [h17488]

private theorem stackAt_frck144_repack (sp : BitVec 64) (v29 v30 v21 v20 v19 : BitVec 64) :
    memRegion (sp - 17552#64) 64 ∗
    stackAt (sp - 80#64) Proofs.libsignal.Stage1X.findIndexStackX ∗
    memRegion (sp - 80#64) 32 ∗
    ((sp - 48#64) ↦₆₄ v29) ∗
    ((sp - 40#64) ↦₆₄ v30) ∗
    ((sp - 32#64) ↦₆₄ v21) ∗
    memRegion (sp - 24#64) 8 ∗
    ((sp - 16#64) ↦₆₄ v20) ∗
    ((sp - 8#64) ↦₆₄ v19) ⊢
      stackAt sp findReceiverChainKeyStackExt144 := by
  rw [stackAt_frck144 sp]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine sepConj_mono (Entails.sepExists_intro v29)
    (sepConj_mono (Entails.sepExists_intro v30)
      (sepConj_mono (Entails.sepExists_intro v21)
        (sepConj_mono_right (sepConj_mono (Entails.sepExists_intro v20)
          (Entails.sepExists_intro v19)))))

private theorem adrp_missingReceiverChainKey' {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {entry : BitVec 64}
    (hentry : entry = img.base + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_key")) :
    ((entry + bv% (272)) &&& bv% (2 ^ 64 - 4096)) +
      bv% (ls_str% "missing receiver chain key" - page% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 296)) =
      img.base + bv% (ls_str% "missing receiver chain key") := by
  have hbal := ProofLib.base_aligned_of_loads himg
  rw [hentry]
  revert hbal
  bv_bits

private theorem cap_add_one_beq_zero_false' {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
  omega

private theorem SepWPp_conseq_pre' {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P ⊢ P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  fun R hm hL => h R (Satisfies.mono (sepConj_mono_left hP) hm) hL

private theorem findIndexX_ok_at_frck {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hfind : Proofs.libsignal.Stage1X.FindIndexOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr findReceiverChainKeyName +
        bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" -
          ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_key"))
      ((Proofs.libsignal.Stage1X.findIndexSpecX img A).inImage img) := by
  have hprog : Proofs.libsignal.Stage1X.SP2Ext img.base ext = tripleRatchetProgAtExt img.base ext := rfl
  unfold Proofs.libsignal.Stage1X.FindIndexOkX at hfind
  rw [hprog] at hfind
  have haddr : (tripleRatchetProgAtExt img.base ext).fnAddr findReceiverChainKeyName +
      bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" -
        ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_key") =
      (tripleRatchetProgAtExt img.base ext).fnAddr Proofs.libsignal.Stage1X.findIndexName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
        (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_key"),
        (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index"),
        BitVec.add_assoc]
    rfl
  rwa [haddr]

private theorem pure_and_entails_pure_sep_of {P P' Q : Prop} {R : SepProp}
    (h : P → P' ∧ Q) :
    ⌜P⌝ ∗ R ⊢ ⌜P'⌝ ∗ (⌜Q⌝ ∗ R) := by
  apply Entails.pure_left
  intro hp
  rcases h hp with ⟨hp', hq⟩
  exact Entails.pure_right hp' (Entails.pure_right hq (Entails.refl R))

private theorem findIndexX_ok_at_state_prog {prog : Program} {A : RustAlloc} {img : Obj.Image}
    {addr : BitVec 64} {s : State}
    (hfind : subroutine_ok prog addr ((Proofs.libsignal.Stage1X.findIndexSpecX img A).inImage img))
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) :
    subroutine_ok prog addr
      { pre := fun (p, cs, theirA, their) s' =>
          ⌜s'.mem = s.mem ∧ s'.symtab = s.symtab ∧
            s'.readReg64 .x0 = p ∧ (s'.readReg64 .x1).toNat = cs.length ∧ s'.readReg64 .x2 = theirA ∧
            cs.length * 104 < 2 ^ 63⌝ ∗
          arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
          (CryptoVerification.LibsignalSession.logFilterAddr img ↦₆₄ 0#64) ∗ stackAt s'.sp Proofs.libsignal.Stage1X.findIndexStackX
        post := (Proofs.libsignal.Stage1X.findIndexSpecX img A).post } := by
  refine subroutine_ok_mono hfind (fun ⟨p, cs, theirA, their⟩ R s0 hm => ?_) (fun _ _ _ _ hq => hq)
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  dsimp only [Spec.inImage, Proofs.libsignal.Stage1X.findIndexSpecX]
  exact pure_and_entails_pure_sep_of fun ⟨hmem, hsym', hrest⟩ =>
    ⟨⟨frozenLoaded_of_mem_eq hmem hfrozen, hsym'.trans hsym⟩, hrest⟩

section FindReceiverChainKeyProof

attribute [local arm64_norm] mul_104_eq setWidth_32_16_of_64 setWidth_32_8_of_64
  setWidth_16_of_64 setWidth_8_of_64 setWidth_32_of_64 setWidth_16_of_32

@[local arm64_norm]
private theorem setWidth_8_of_32' (v : BitVec 8) :
    (BitVec.setWidth 32 v).setWidth 8 = v := by bv_bits

/-- `RatchetState::find_receiver_chain_key` at `17552` B (`144 + findIndexStackX`),
for callers with `17552`-byte stack (such as `DecryptPq`). -/
theorem findReceiverChainKey_ok_ext144_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hfind : Proofs.libsignal.Stage1X.FindIndexOkX img A ext) :
    FindReceiverChainKeyOkExt144 img A ext := by
  have hfn := FindReceiverChainKeyFacts.findReceiverChainKey_fnOff
  have hfind_at := findIndexX_ok_at_frck hfind
  have hadrp : ((((tripleRatchetProgAtExt img.base ext).fnAddr findReceiverChainKeyName) + 272#64) &&& bv% (2 ^ 64 - 4096)) +
      bv% (ls_str% "missing receiver chain key" - page% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 296)) =
      img.base + bv% (ls_str% "missing receiver chain key") := by
    apply adrp_missingReceiverChainKey' himg; rw [Program.fnAddr_rebase, hfn]
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp0
  simp only [findReceiverChainKeySpecWithStack, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfrozen0, hsym0⟩, ⟨hx0, hx1, hx8⟩, hmem⟩
  refine ⟨ratchetAt A x.self x.G x.st ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗ memRegion x.ret 40 ∗
    logOff img ∗ stackAt s0.sp findReceiverChainKeyStackExt144, R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  apply SepWPp_conseq_pre' (sepConj_mono_left (ratchetAt_expose_findIndex A x.self x.G x.st))
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hchains_len, hcs_lt⟩ => ?_
  set cs := x.G.chains.zip x.st.receiverChains
  have hcs_toNat : (BitVec.ofNat 64 cs.length).toNat = cs.length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  unfold logOff; rw [stackAt_frck144 s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v19 => SepWPp.exists_elim fun v20 =>
    SepWPp.exists_elim fun v21 => SepWPp.exists_elim fun v30 =>
    SepWPp.exists_elim fun v29 => ?_
  dsimp only [tripleRatchetProgAtExt] at hpc hfind_at hadrp ⊢
  code_fetches libsignalSessionCode libsignalSessionBin img.base (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_key")) 392
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr findReceiverChainKeyName = entry
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog reverting [Program.fetch, subroutine_ok]
  examples_hide_fetches
  apply SepWPp.of_sepWP_frozen
    (mid := entry + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" -
      ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_key"))
    hfrozen0 hsym0
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hfrozen1 hsym1
  have hfind1 := findIndexX_ok_at_state_prog hfind_at hfrozen1 hsym1
  apply SepWPp.of_sepWP_frozen (mid := entry + bv% (44)) hfrozen1 hsym1
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hfrozen2 hsym2
  have hmap_cs : cs.map (·.2) = x.st.receiverChains :=
    zip_map_snd x.G.chains x.st.receiverChains hchains_len
  have hidx_post : match x.st.findReceiverChainIndex x.their with
      | some i => sf.readReg64 (Reg.gpr 0#5) = 1#64 ∧ (sf.readReg64 (Reg.gpr 1#5)).toNat = i
      | none => sf.readReg64 (Reg.gpr 0#5) = 0#64 := by
    have h := hpost; rw [hmap_cs] at h; exact h
  cases hfind_res : x.st.findReceiverChainIndex x.their with
  | none =>
    rw [hfind_res] at hidx_post; dsimp only at hidx_post
    rw [memRegion40_unpack_none x.ret]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun t0 => ?_
    apply SepWPp.of_sepWP_frozen (mid := s0.readReg64 Reg.lr) hfrozen2 hsym2
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro _ _
    refine SepWPp.done (by wp_norm_goal) (by wp_norm_goal) ⟨fun hm => ?_, rfl, by findReceiverChainKey_cc_close⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    rw [findReceiverChainKey_of_none hfind_res]; dsimp only [findReceiverChainKeyResultAt, logOff]
    refine Entails.pure_right (by simp only [wp_norm, arm64_norm, *]) ?_
    have hrat := ratchetAt_reassemble_findIndex A x.self x.G x.st
    have hstk := stackAt_frck144_repack s0.sp
      (s0.readReg64 Reg.x29) (s0.readReg64 Reg.lr) (s0.readReg64 Reg.x21)
      (s0.readReg64 Reg.x20) (s0.readReg64 Reg.x19)
    refine Entails.trans ?_
      (sepConj_mono hrat (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk))))
    exact entails_of_eq' (by dsimp only [cs, Reg.x19, Reg.x20, Reg.x21, Reg.lr, Reg.x29]; ac_rfl)
      (Entails.refl _)
  | some i =>
    rw [hfind_res] at hidx_post; rcases hidx_post with ⟨hx0_1, hx1_1⟩
    have hi_rc : i < x.st.receiverChains.length := findReceiverChainIndex_lt hfind_res
    have hi : i < cs.length := by rwa [zip_length_eq hchains_len]
    have hx1_eq : sf.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; rw [hx1_1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hule : (BitVec.ofNat 64 cs.length).ule (BitVec.ofNat 64 i) = false :=
      len_ule_idx_false hi hcs_lt
    rw [arrayAt_split_at (chainAt A) 104 x.G.chainsPtr cs hi]
    set elemAddr := x.G.chainsPtr + BitVec.ofNat 64 (i * 104)
    cases hck : cs[i].2.chainKey with
    | none =>
      rw [chainAt_none_expose A cs[i] elemAddr hck, memRegion40_unpack_err x.ret]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun l0 => SepWPp.exists_elim fun p0 =>
        SepWPp.exists_elim fun t0 => ?_
      apply SepWPp.of_sepWP_frozen (mid := s0.readReg64 Reg.lr) hfrozen2 hsym2
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hfrozen3 _
      apply SepWPp_intro_rodata_missingReceiverChainKey_shared_lb himg hfrozen3
      refine SepWPp.done (by wp_norm_goal) (by wp_norm_goal) ⟨fun hm => ?_, rfl, by findReceiverChainKey_cc_close⟩
      refine Satisfies.mono (sepConj_mono_left ?_) hm
      rw [findReceiverChainKey_of_some_none hchains_len hfind_res hi hck]; dsimp only [logOff]
      refine Entails.pure_right (by simp only [wp_norm, arm64_norm, *]) ?_
      have herr := findReceiverChainKeyResultAt_err_repack x.ret (img.base + bv% (ls_str% "missing receiver chain key"))
      have hrat := ratchetAt_reassemble_findIndex A x.self x.G x.st
      have hstk := stackAt_frck144_repack s0.sp
        (s0.readReg64 Reg.x29) (s0.readReg64 Reg.lr) (s0.readReg64 Reg.x21)
        (s0.readReg64 Reg.x20) (s0.readReg64 Reg.x19)
      rw [arrayAt_split_at (chainAt A) 104 x.G.chainsPtr cs hi,
          chainAt_none_expose A cs[i] elemAddr hck] at hrat
      refine Entails.trans ?_
        (sepConj_mono hrat (sepConj_mono_right (sepConj_mono herr (sepConj_mono_right hstk))))
      exact entails_of_eq' (by dsimp only [cs, elemAddr, Reg.x19, Reg.x20, Reg.x21, Reg.lr, Reg.x29]; ac_rfl)
        (Entails.refl _)
    | some ck =>
      apply SepWPp_conseq_pre'
        (sepConj_mono_left (sepConj_mono_left (chainAt_some_expose A cs[i] ck elemAddr hck)))
      apply SepWPp_eq_pre_shared_lb (by simp only [sepConj_assoc]; rfl)
      refine SepWPp.pure_elim fun hcap_lt => ?_
      have hcap_ne := cap_add_one_beq_zero_false' hcap_lt
      have hlen_key : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
      obtain ⟨v0, v4, v6, v7, v15, v23, v31, hkey⟩ :=
        exists_findReceiverChainKeyKeyChunks_of_length_32 hlen_key
      rw [hkey cs[i].1.ck.ptr]; unfold findReceiverChainKeyKeyChunks
      rw [sp_scratch32_unpack s0.sp, memRegion40_unpack_some x.ret]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun r36 => SepWPp.exists_elim fun r35 =>
        SepWPp.exists_elim fun r27 => SepWPp.exists_elim fun r26 =>
        SepWPp.exists_elim fun r24 => SepWPp.exists_elim fun r23 =>
        SepWPp.exists_elim fun r19 => SepWPp.exists_elim fun r18 =>
        SepWPp.exists_elim fun r16 => SepWPp.exists_elim fun r8 =>
        SepWPp.exists_elim fun r4 => SepWPp.exists_elim fun r0 =>
        SepWPp.exists_elim fun s24 => SepWPp.exists_elim fun s16 =>
        SepWPp.exists_elim fun s3 => SepWPp.exists_elim fun s2 =>
        SepWPp.exists_elim fun s0_scr => ?_
      apply SepWPp.of_sepWP_frozen (mid := entry + bv% (156)) hfrozen2 hsym2
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hfrozen3 hsym3
      apply SepWPp_eq_pre_shared_lb (by simp only [sepConj_assoc, sp_11_repack_rest s0.sp v4 v6 v7]; rfl)
      apply SepWPp.of_sepWP_frozen (mid := s0.readReg64 Reg.lr) hfrozen3 hsym3
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro _ _
      refine SepWPp.done (by wp_norm_goal) (by wp_norm_goal) ⟨fun hm => ?_, rfl, by findReceiverChainKey_cc_close⟩
      refine Satisfies.mono (sepConj_mono_left ?_) hm
      rw [findReceiverChainKey_of_some_some hchains_len hfind_res hi hck]; dsimp only [logOff]
      refine Entails.pure_right (by simp only [wp_norm, arm64_norm, *]) ?_
      have hres := findReceiverChainKeyResultAt_some_repack x.ret ck v0 v4 v6 v7 v15 v23 v31 hkey
      have hscr := sp_scratch32_repack s0.sp
        (v7.extractLsb' 0 40 ++ v6 ++ v4) (v7.extractLsb' 40 16) (v7.extractLsb' 56 8) v23 v31
      have hstk := stackAt_frck144_repack s0.sp
        (s0.readReg64 Reg.x29) (s0.readReg64 Reg.lr) (s0.readReg64 Reg.x21)
        (s0.readReg64 Reg.x20) (s0.readReg64 Reg.x19)
      have hch := chainAt_some_reassemble A cs[i] ck elemAddr hck
      rw [hkey cs[i].1.ck.ptr] at hch; unfold findReceiverChainKeyKeyChunks at hch
      have hrat := ratchetAt_reassemble_findIndex A x.self x.G x.st
      rw [arrayAt_split_at (chainAt A) 104 x.G.chainsPtr cs hi] at hrat
      have hrat' := FindReceiverChainKeyFacts.ratchet_reassemble_chain hch hrat
      have hstk' := FindReceiverChainKeyFacts.stack_reassemble_scr hscr hstk
      rw [← hres]
      refine Entails.trans ?_
        (sepConj_mono hrat' (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk'))))
      exact entails_of_eq'
        (by dsimp only [cs, elemAddr, Reg.x19, Reg.x20, Reg.x21, Reg.lr, Reg.x29]; ac_rfl)
        (Entails.refl _)

end FindReceiverChainKeyProof

private theorem stackAt_frckX_split (sp : BitVec 64) :
    stackAt sp findReceiverChainKeyStackX =
      memRegion (sp - 18432#64) 880 ∗ stackAt sp findReceiverChainKeyStackExt144 := by
  unfold stackAt findReceiverChainKeyStackX findReceiverChainKeyStack
    findReceiverChainKeyStackExt144 Proofs.libsignal.Stage1X.findIndexStackX extHookStack
  exact mr_cut'' sp 18432 17552 880 17552 18432 rfl rfl (by decide) (by decide) (by decide)

/-- `RatchetState::find_receiver_chain_key` at `18432` B (`2048 + extHookStack`),
framed from `findReceiverChainKey_ok_ext144_x` (`17552` B). -/
theorem findReceiverChainKey_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hfind : Proofs.libsignal.Stage1X.FindIndexOkX img A ext) :
    FindReceiverChainKeyOkExtX img A ext := by
  have h144 := findReceiverChainKey_ok_ext144_x himg hfind
  refine Proofs.libsignal.Hooks2.subroutine_ok_inImage_map' h144 fun x R s0 hpre => ?_
  refine ⟨x, memRegion (s0.sp - 18432#64) 880 ∗ R, ?_, fun sf hpost => ?_⟩
  · simp only [stackAt_frckX_split s0.sp] at hpre
    convert hpre using 1; sep_ac_rfl
  · simp only [stackAt_frckX_split s0.sp]
    convert hpost using 1; sep_ac_rfl

/-! ## Segment S2 (`findChain_ok_ext_x`) -/

section FindChainS2

open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup

def S2SpecExtX (img : Obj.Image) (A : RustAlloc) (ctl : BitVec 64)
    (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  FindReceiverChainKeyOkExtX img A ext →
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.FindChainState A ctl img x trG tr st1 R s0 s →
    (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
    match tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
    | .ok (some ck) =>
        reaches_pc (tripleRatchetProgAtExt img.base ext)
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segConsumeMsgKeyPC img) s
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyState A ctl img x trG tr st1 ck 0 R s0)
    | .ok none =>
        reaches_pc (tripleRatchetProgAtExt img.base ext)
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segDhStepPC img) s
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStepState A ctl img x trG tr st1 R s0)
    | .error e =>
        reaches_pc (tripleRatchetProgAtExt img.base ext)
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.errTailPC img) s
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 e 0 R s0)

theorem findChain_call_findReceiverChainKey_reaches_x {img : Obj.Image} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hfrck : FindReceiverChainKeyOkExtX img A ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State)
    (hS2 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.FindChainState A ctl img x trG tr st1 R s0 s) :
    let prog := tripleRatchetProgAtExt img.base ext
    let sp := s0.sp - 1504#64
    reaches_pc prog (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img + 680#64) s
      (fun s_ret =>
        tryDecryptMidMeta img s0 s_ret ∧
        s_ret.readReg64 .x19 = x.ret ∧
        s_ret.readReg64 .x20 = sp + 320#64 ∧
        s_ret.readReg64 .x21 = x.ss ∧
        s_ret.readReg64 .x22 = x.msgA ∧
        s_ret.readReg64 .x23 = sp + 1280#64 ∧
        (s_ret.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s_ret.readReg64 .x25 = sp + 400#64 ∧
        s_ret.readReg64 .x27 = sp + 56#64 ∧
        s_ret.readReg64 .x28 = sp + 704#64 ∧
        (s_ret.mem ⊨
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG tr ∗
          memRegion x.ret 48 ∗
          memRegion sp 32 ∗
          ((sp + 32#64) ↦₆₄ x.locA) ∗
          ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
          memRegion (sp + 44#64) 4 ∗
          ((sp + 48#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 320#64) 80 ∗
          findReceiverChainKeyResultAt (sp + 400#64) (tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey) ∗
          memRegion (sp + 440#64) 968 ∗
          CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  rcases hS2 with ⟨hpc, hmeta, hx0, hx1, hx8, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hmem⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.tryDecryptEntry_eq_fnAddr (ext := ext) himg
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segFindChainPC] at hpc
  rw [hentry] at hpc
  have hwp_bl := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_bl_wp hpc (tryDecryptMidMeta.to_wpInv hmeta)
  have hmem_emp : s.mem ⊨ emp ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 56#64) trG tr ∗
       memRegion x.ret 48 ∗
       memRegion sp 32 ∗
       ((sp + 32#64) ↦₆₄ x.locA) ∗
       ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 44#64) 4 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 320#64) 1088 ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    rw [emp_sepConj]; exact hmem
  have hinv_s : img.FrozenLoaded s ∧ s.symtab = img.symtab := ⟨hmeta.2.2.2.2.2.2.1, hmeta.2.2.2.2.2.2.2.1⟩
  refine ChainLookup.reaches_pc_seq_callInv hinv_s (sepWP_to_reaches_pc hwp_bl hmem_emp) ?_
  intro s_call hpc_call _ ⟨P1, hm_call, ⟨hP1, hwpInv_call, hlr_call, hx0_c, hx1_c, hx8_c, hcs_c⟩⟩ hinv_call
  subst hP1
  rw [emp_sepConj] at hm_call
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap at hm_call
  rw [trAt_eq_ratchetAt_trRestAt, signalMessageAt_eq_srk_rest, memRegion_0x140_split_findReceiverChainKey,
      stackAt_tryDecryptSubStack_sub s0.sp findReceiverChainKeyStackX (by decide)] at hm_call
  have hsp_call : s_call.sp = sp := hwpInv_call.2.1
  have halign_call : s_call.spAligned = true := hwpInv_call.2.2.2.1
  have hlr_call' : s_call.readReg64 Reg.lr = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img + 680#64 := by
    rw [hentry]; exact hlr_call
  let fg : FindReceiverChainKeyGhost :=
    { self := sp + 56#64
      G := trG.ratchet
      st := tr.ratchet
      theirA := x.msgA + 56#64
      their := x.msg.senderRatchetKey
      ret := sp + 400#64 }
  let F_call : SepProp :=
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trRestAt A (sp + 56#64) trG tr ∗
    memRegion x.ret 48 ∗
    memRegion sp 32 ∗
    ((sp + 32#64) ↦₆₄ x.locA) ∗
    ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 44#64) 4 ∗
    ((sp + 48#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 320#64) 80 ∗
    memRegion (sp + 440#64) 968 ∗
    protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗
    signalMessageRestAt A x.msgG x.msgA x.msg ∗
    CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗
    memRegion (s0.sp - 262144#64) (tryDecryptSubStack - findReceiverChainKeyStackX) ∗
    tryDecryptSavedRegs s0.sp s0 ∗
    A.pool ∗ R
  have hpre_call :
      s_call.mem ⊨
        (⌜s_call.readReg64 .x0 = fg.self ∧ s_call.readReg64 .x1 = fg.theirA ∧
            s_call.readReg64 .x8 = fg.ret⌝ ∗
         ratchetAt A fg.self fg.G fg.st ∗
         (fg.theirA ↦ₛ fg.their.bytes.toList) ∗
         memRegion fg.ret 40 ∗
         logOff img ∗
         stackAt s_call.sp findReceiverChainKeyStackX) ∗ F_call := by
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_c.trans hx0, hx1_c.trans hx1, hx8_c.trans hx8⟩, ?_⟩
    rw [hsp_call]
    dsimp only [fg, F_call, sp] at hm_call ⊢
    convert hm_call using 1; sep_ac_rfl
  refine ChainLookup.reaches_pc_call_inImage hfrck fg F_call hpc_call hwpInv_call.1 hlr_call' hinv_call hpre_call
    (fun s_ret hpc_ret hrun_ret hsp_ret hcs_ret hinv_ret hpost_ret => ?_) halign_call
  refine reaches_pc_refl hpc_ret hrun_ret ?_
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_ret
  rcases hpost_ret with ⟨htr_ret, hm_ret⟩
  have hsp_ret' : s_ret.sp = s0.sp - 1504#64 := by reg_chain
  have halign_ret : s_ret.spAligned = true := by
    rw [State.spAligned, hsp_ret', ← hwpInv_call.2.1]
    exact halign_call
  have hmeta_ret : tryDecryptMidMeta img s0 s_ret :=
    ⟨hrun_ret, hsp_ret', hwpInv_call.2.2.1, halign_ret, by reg_chain, by reg_chain,
     hinv_ret.1, hinv_ret.2, by reg_chain⟩
  refine ⟨hmeta_ret, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, ?_⟩
  rw [hsp_call] at hm_ret
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap
  rw [trAt_eq_ratchetAt_trRestAt, signalMessageAt_eq_srk_rest,
      stackAt_tryDecryptSubStack_sub s0.sp findReceiverChainKeyStackX (by decide)]
  dsimp only [fg, F_call, sp] at hm_ret ⊢
  convert hm_ret using 1; sep_ac_rfl

theorem findChain_ok_ext_x {img : Obj.Image} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)} :
    S2SpecExtX img A ctl ext := by
  intro himg hfrck x trG tr st1 R s0 s hs2 _hcode
  have hcall := findChain_call_findReceiverChainKey_reaches_x himg hfrck x trG tr st1 R s0 s hs2
  cases hres : tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
  | ok optCk =>
    cases optCk with
    | some ck =>
      rw [hres] at hcall
      refine reaches_pc_seq hcall (fun s_ret hpc_ret _ ⟨hmeta_ret, hx19_ret, hx20_ret, hx21_ret, hx22_ret, hx23_ret, hx24_ret, hx25_ret, _, hx28_ret, hm_ret⟩ => ?_)
      exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_after_call_ok_some
        himg hpc_ret hmeta_ret hx19_ret hx20_ret hx21_ret hx22_ret hx23_ret hx24_ret hx25_ret hx28_ret hm_ret
    | none =>
      rw [hres] at hcall
      refine reaches_pc_seq hcall (fun s_ret hpc_ret _ ⟨hmeta_ret, hx19_ret, hx20_ret, hx21_ret, hx22_ret, hx23_ret, hx24_ret, hx25_ret, hx27_ret, hx28_ret, hm_ret⟩ => ?_)
      exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_after_call_ok_none
        himg hpc_ret hmeta_ret hx19_ret hx20_ret hx21_ret hx22_ret hx23_ret hx24_ret hx25_ret hx27_ret hx28_ret hm_ret
  | error e =>
    rw [hres] at hcall
    refine reaches_pc_seq hcall (fun s_ret hpc_ret _ ⟨hmeta_ret, hx19_ret, hx20_ret, _, _, _, _, hx25_ret, _, _, hm_ret⟩ => ?_)
    exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_after_call_error
      himg hpc_ret hmeta_ret hx19_ret hx20_ret hx25_ret hm_ret

end FindChainS2

end CryptoVerification.Cli.LibsignalTripleRatchet.ExtFindCmk
