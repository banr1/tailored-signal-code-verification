/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.DropsLocal1Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.WPX
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.VecX
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.X
import ProofLib.SepLogic.WPp

/-!
# `core::ptr::drop_glue::<SessionStructure> [local#1]`

Verifies `drop_glue::<SessionStructure> [local#1]` against `dropSessionStructureLocal1SpecX` under
`AllocContractsX`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalSession
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.DropsX
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.DropsLocal1Layout

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

local macro "drop_call_auto " sId:ident hspId:ident hfspId:ident hcall:ident : tactic =>
  `(tactic| (
    have _hal1 : State.spAligned $sId = true := by
      simp only [State.spAligned, $hspId:ident, $hfspId:ident]
    have _hal2 : (($sId).sp &&& 15#64 == 0#64) = true := by
      rw [$hspId:ident]; exact $hfspId:ident
    conv => arg 4; rw [← $hspId:ident]
    wpx_call $hcall
    clear _hal1 _hal2))

local macro "drop_dealloc " sId:ident hspId:ident hfspId:ident hdeallocId:ident ptr:term:max cap:term:max : tactic =>
  `(tactic| (
    refine sepWP_pull_pure fun ⟨_hpos, _hlt⟩ => ?_
    have _hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have _hbound : ($cap).toNat + 1 ≤ 2 ^ 63 := by omega
    have _hlay : LayoutOk ($cap).toNat 1 := ⟨_hpos, _hpow2, _hbound⟩
    wpx_steps
    have _hal1 : State.spAligned $sId = true := by
      simp only [State.spAligned, $hspId:ident, $hfspId:ident]
    have _hal2 : (($sId).sp &&& 15#64 == 0#64) = true := by
      rw [$hspId:ident]; exact $hfspId:ident
    conv => arg 4; rw [← $hspId:ident]
    wpx_call $hdeallocId ($ptr, ($cap).toNat, 1)
    clear _hal1 _hal2 _hlay _hbound _hpow2 _hpos _hlt))

private theorem drop_ss_local1_first3 {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropSessionStructureLocal1Name + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr dropSessionStructureLocal1Name + 12#64 →
      s.status = .Running →
      Saved32Preserved s0 s fsp →
      s.readReg64 .x0 = ss →
      ImgCallInv img s →
      SepWP (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr dropSessionStructureLocal1Name + 76#64)
        s
        ((ssFirst3HeadersAt ss G ∗
          vecPinDeallocX A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
          vecPinDeallocX A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
          vecPinDeallocX A G.root) ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24) ∗
            A.pool ∗ stackAt fsp extHookStack ∗ Frame) ∧
          Saved32Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  have hfn : libsignalSessionCode.fnOff dropSessionStructureLocal1Name = num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")
  dsimp only [tripleRatchetProgAtExt, dropSessionStructureLocal1Name] at *
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) 12 64
  examples_generalize_entry
  examples_hide_fetches
  intro G s Frame hpc hrun hpres hx0 _hinv0
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine seq_cleanX (img := img) (mid := entry + bv% (36)) (P_mid :=
    (ssFirst3HeadersAt ss G ∗
      vecPinDeallocX A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
      vecPinDeallocX A G.root) ∗
    A.pool ∗ stackAt fsp extHookStack ∗ Frame)
    (Q := fun sm => Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
    ?_ ?_
  · dsimp only [ssFirst3HeadersAt, vecPinDeallocX]
    by_cases hcap : (G.localIk.cap == 0#64) = true <;>
      simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wpx_steps
      wp_done
    · drop_dealloc s hsp hfsp_align hdealloc G.localIk.ptr G.localIk.cap
      refine SepWP.align_pre (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 _hinv_seq ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_cleanX (img := img) (mid := entry + bv% (56)) (P_mid :=
      (ssFirst3HeadersAt ss G ∗ vecPinDeallocX A G.root) ∗
      A.pool ∗ stackAt fsp extHookStack ∗ Frame)
      (Q := fun sm => Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
      ?_ ?_
    · dsimp only [ssFirst3HeadersAt, vecPinDeallocX]
      by_cases hcap : (G.remoteIk.cap == 0#64) = true <;>
        simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wpx_steps
        wp_done
      · drop_dealloc s1 hsp_1 hfsp_align hdealloc G.remoteIk.ptr G.remoteIk.cap
        refine SepWP.align_pre (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 _hinv_seq ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      have hstep3 : SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) (entry + bv% (76)) s2
          ((ssFirst3HeadersAt ss G ∗ vecPinDeallocX A G.root) ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssFirst3HeadersAt ss G ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame) ∧
            Saved32Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        dsimp only [ssFirst3HeadersAt, vecPinDeallocX]
        by_cases hcap : (G.root.cap == 0#64) = true <;>
          simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wpx_steps
          wp_done
        · drop_dealloc s2 hsp_2 hfsp_align hdealloc G.root.ptr G.root.cap
          refine SepWP.align_pre (by rw [hsp_2]; ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (ssFirst3HeadersAt_entails_memRegions ss G)), h.2⟩)

private theorem drop_ss_local1_sender {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropSessionStructureLocal1Name + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img))
    (hdrop_mk : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropSessionStructureLocal1Name + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>") - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")))
      ((Getters.dropVecMessageKeySpecX A).inImage img))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (senderG : Option SenderChainGhost) (senderSt : Option SenderChain)
      (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr dropSessionStructureLocal1Name + 76#64 →
      s.status = .Running →
      Saved32Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      ImgCallInv img s →
      SepWP (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr dropSessionStructureLocal1Name + 156#64)
        s
        (optSenderChainAt A (ss + 144#64) senderG senderSt ∗
          A.pool ∗ stackAt fsp Getters.dropVecMessageKeyStackX ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion (ss + 144#64) 104 ∗ A.pool ∗ stackAt fsp Getters.dropVecMessageKeyStackX ∗ Frame) ∧
          Saved32Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  have hfn : libsignalSessionCode.fnOff dropSessionStructureLocal1Name = num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")
  dsimp only [tripleRatchetProgAtExt, dropSessionStructureLocal1Name] at *
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) 76 80
  examples_generalize_entry
  examples_hide_fetches
  intro senderG senderSt s Frame hpc hrun hpres hx19 _hinv0
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  cases senderG with
  | none =>
    cases senderSt with
    | none =>
      have hnone : optSenderChainAt A (ss + 144#64) none none =
          (((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion (ss + 152#64) 96) := by
        unfold optSenderChainAt
        have ha : (ss + 144#64) + 8#64 = ss + 152#64 := by bv_omega
        rw [ha]
      rw [hnone]
      have hstep : SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) (entry + bv% (156)) s
          ((((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion (ss + 152#64) 96) ∗
            A.pool ∗ stackAt fsp Getters.dropVecMessageKeyStackX ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ (((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion (ss + 152#64) 96) ∗
              A.pool ∗ stackAt fsp Getters.dropVecMessageKeyStackX ∗ Frame) ∧
            Saved32Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        dsimp only [noneCap]
        wpx_steps
        wp_done
      refine SepWP.mono hstep (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
      have ha : ss + 152#64 = (ss + 144#64) + 8#64 := by bv_omega
      rw [ha]
      exact sepConj_mono_left (sender_none_entails_memRegion_104 (ss + 144#64))
    | some _ =>
      simp only [optSenderChainAt]
      exact SepWP.false_elim_left
  | some sg =>
    cases senderSt with
    | none =>
      simp only [optSenderChainAt]
      exact SepWP.false_elim_left
    | some sc =>
      refine SepWP.weaken_pre (sepConj_mono_left (optSenderChainAt_some_entails_ss_local1X A ss sg sc)) ?_
      wp_pull_exists
      rename_i ckCap ckPtr
      refine SepWP.pure_elim ?_
      intro hcmn
      have hcmn_beq : (sg.srk.cap + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hcmn
      conv => arg 4; rw [stackAt_dropVecMessageKey_split_alloc fsp]
      refine SepWP.weaken_pre (P' :=
        (ssSender1HeadersAt ss sg ckCap ckPtr ∗
          vecPinDeallocX A ⟨sg.srk.cap, sg.srk.ptr⟩ ∗
          vecPinDeallocX A ⟨sg.priv.cap, sg.priv.ptr⟩ ∗
          sgnPinDeallocX A ckCap ckPtr) ∗
        A.pool ∗ stackAt fsp extHookStack ∗
        (vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
          memRegion (fsp - 16432#64) 48 ∗ Frame))
        (Entails.of_eq (by dsimp only [ssSender1HeadersAt]; ac_rfl)) ?_
      refine seq_cleanX (img := img) (mid := entry + bv% (104)) (P_mid :=
        (ssSender1HeadersAt ss sg ckCap ckPtr ∗
          vecPinDeallocX A ⟨sg.priv.cap, sg.priv.ptr⟩ ∗
          sgnPinDeallocX A ckCap ckPtr) ∗
        A.pool ∗ stackAt fsp extHookStack ∗
        (vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
          memRegion (fsp - 16432#64) 48 ∗ Frame))
        (Q := fun sm => Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
        ?_ ?_
      · dsimp only [ssSender1HeadersAt, vecPinDeallocX, sgnPinDeallocX]
        by_cases hcap : (sg.srk.cap == 0#64) = true <;>
          simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wpx_steps
          refine SepWP.align_pre (by ac_rfl) ?_
          wp_done
        · drop_dealloc s hsp hfsp_align hdealloc sg.srk.ptr sg.srk.cap
          refine SepWP.align_pre (by rw [hsp]; ac_rfl) ?_
          wp_done
      · intro s1 hpc1 hrun1 _hinv_seq ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
        refine seq_cleanX (img := img) (mid := entry + bv% (124)) (P_mid :=
          (ssSender1HeadersAt ss sg ckCap ckPtr ∗ sgnPinDeallocX A ckCap ckPtr) ∗
          A.pool ∗ stackAt fsp extHookStack ∗
          (vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
            memRegion (fsp - 16432#64) 48 ∗ Frame))
          (Q := fun sm => Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
          ?_ ?_
        · dsimp only [ssSender1HeadersAt, vecPinDeallocX, sgnPinDeallocX]
          by_cases hcap : (sg.priv.cap == 0#64) = true <;>
            simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wpx_steps
            wp_done
          · drop_dealloc s1 hsp_1 hfsp_align hdealloc sg.priv.ptr sg.priv.cap
            refine SepWP.align_pre (by rw [hsp_1]; ac_rfl) ?_
            wp_done
        · intro s2 hpc2 hrun2 _hinv_seq ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
          refine seq_cleanX (img := img) (mid := entry + bv% (148)) (P_mid :=
            vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
            A.pool ∗ stackAt fsp Getters.dropVecMessageKeyStackX ∗
            ((memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) ∗ Frame))
            (Q := fun sm => Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
            ?_ ?_
          · have hstep3 : SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) (entry + bv% (148)) s2
                ((ssSender1HeadersAt ss sg ckCap ckPtr ∗ sgnPinDeallocX A ckCap ckPtr) ∗
                  A.pool ∗ stackAt fsp extHookStack ∗
                  (vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                    memRegion (fsp - 16432#64) 48 ∗ Frame))
                (fun sm Pm =>
                  (Pm ⊢ ssSender1HeadersAt ss sg ckCap ckPtr ∗
                    A.pool ∗ stackAt fsp extHookStack ∗
                    (vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                      memRegion (fsp - 16432#64) 48 ∗ Frame)) ∧
                  Saved32Preserved s0 sm fsp ∧
                  sm.readReg64 .x19 = ss) := by
              dsimp only [ssSender1HeadersAt, sgnPinDeallocX]
              by_cases hcap : ckCap.slt 1#64 = true <;>
                simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
              · wpx_steps
                wp_done
              · drop_dealloc s2 hsp_2 hfsp_align hdealloc ckPtr ckCap
                refine SepWP.align_pre (by rw [hsp_2]; ac_rfl) ?_
                wp_done
            refine SepWP.mono hstep3 (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
            refine Entails.trans (sepConj_mono_left (ssSender1HeadersAt_entails_memRegions ss sg ckCap ckPtr)) ?_
            rw [stackAt_dropVecMessageKey_split_alloc fsp]
            exact Entails.of_eq (by ac_rfl)
          · intro s3 hpc3 hrun3 _hinv_seq ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
            have hstep4 : SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) (entry + bv% (156)) s3
                (vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                  A.pool ∗ stackAt fsp Getters.dropVecMessageKeyStackX ∗
                  ((memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) ∗ Frame))
                (fun sm Pm =>
                  (Pm ⊢ (memRegion (ss + 192#64) 24 ∗ memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) ∗
                    A.pool ∗ stackAt fsp Getters.dropVecMessageKeyStackX ∗ Frame) ∧
                  Saved32Preserved s0 sm fsp ∧
                  sm.readReg64 .x19 = ss) := by
              wpx_steps
              drop_call_auto s3 hsp_3 hfsp_align hdrop_mk
              refine SepWP.align_pre (by rw [hsp_3]; ac_rfl) ?_
              wp_done
            refine SepWP.mono hstep4 (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
            exact sepConj_mono_left (ssSender1_memRegions_entails_104 ss)

private theorem drop_ss_local1_tail3 {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropSessionStructureLocal1Name + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (pCap pPtr kCap kPtr : BitVec 64) (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr dropSessionStructureLocal1Name + 164#64 →
      s.status = .Running →
      Saved32Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      ImgCallInv img s →
      SepWP (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr dropSessionStructureLocal1Name + 232#64)
        s
        ((ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
          sgnPinDeallocX A pCap pPtr ∗
          sgnPinDeallocX A kCap kPtr ∗
          vecPinDeallocX A ⟨G.alice.cap, G.alice.ptr⟩) ∗
          A.pool ∗ stackAt fsp extHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion (ss + 248#64) 48 ∗ memRegion (ss + 296#64) 32 ∗ memRegion (ss + 96#64) 24) ∗
            A.pool ∗ stackAt fsp extHookStack ∗ Frame) ∧
          Saved32Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  have hfn : libsignalSessionCode.fnOff dropSessionStructureLocal1Name = num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")
  dsimp only [tripleRatchetProgAtExt, dropSessionStructureLocal1Name] at *
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) 164 68
  examples_generalize_entry
  examples_hide_fetches
  intro pCap pPtr kCap kPtr G s Frame hpc hrun hpres hx19 _hinv0
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine seq_cleanX (img := img) (mid := entry + bv% (188)) (P_mid :=
    (ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
      sgnPinDeallocX A kCap kPtr ∗
      vecPinDeallocX A ⟨G.alice.cap, G.alice.ptr⟩) ∗
    A.pool ∗ stackAt fsp extHookStack ∗ Frame)
    (Q := fun sm => Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
    ?_ ?_
  · dsimp only [ssTail3HeadersAt, sgnPinDeallocX, vecPinDeallocX]
    by_cases hcap : pCap.slt 1#64 = true <;>
      simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wpx_steps
      wp_done
    · drop_dealloc s hsp hfsp_align hdealloc pPtr pCap
      refine SepWP.align_pre (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 _hinv_seq ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_cleanX (img := img) (mid := entry + bv% (212)) (P_mid :=
      (ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
        vecPinDeallocX A ⟨G.alice.cap, G.alice.ptr⟩) ∗
      A.pool ∗ stackAt fsp extHookStack ∗ Frame)
      (Q := fun sm => Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
      ?_ ?_
    · dsimp only [ssTail3HeadersAt, sgnPinDeallocX, vecPinDeallocX]
      by_cases hcap : kCap.slt 1#64 = true <;>
        simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wpx_steps
        wp_done
      · drop_dealloc s1 hsp_1 hfsp_align hdealloc kPtr kCap
        refine SepWP.align_pre (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 _hinv_seq ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      have hstep3 : SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) (entry + bv% (232)) s2
          ((ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
            vecPinDeallocX A ⟨G.alice.cap, G.alice.ptr⟩) ∗
            A.pool ∗ stackAt fsp extHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame) ∧
            Saved32Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        dsimp only [ssTail3HeadersAt, vecPinDeallocX]
        by_cases hcap : (G.alice.cap == 0#64) = true <;>
          simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wpx_steps
          wp_done
        · drop_dealloc s2 hsp_2 hfsp_align hdealloc G.alice.ptr G.alice.cap
          refine SepWP.align_pre (by rw [hsp_2]; ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (ssTail3HeadersAt_entails_memRegions ss pCap pPtr kCap kPtr G)), h.2⟩)

set_option maxHeartbeats 1200000 in
/-- `core::ptr::drop_glue::<SessionStructure> [local#1]` meets `dropSessionStructureLocal1SpecX A`. -/
theorem drop_session_structure_local1_ok_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (hmk : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropVecMessageKeyName)
      ((Getters.dropVecMessageKeySpecX A).inImage img))
    (hvc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropVecChainName)
      ((Getters.dropVecChainSpecX A).inImage img)) :
    OkAtX img ext dropSessionStructureLocal1Name (dropSessionStructureLocal1SpecX A) := by
  apply subroutine_ok_inImage_iff_right
  simp only [dropSessionStructureLocal1SpecX]
  have hfn := (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")
  have hdealloc_raw := hA.dealloc_ok_at dropSessionStructureLocal1Name
    (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]"))
    (hk := by rw [hfn]; simp only [arm64_norm])
  have hdrop_mk_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropSessionStructureLocal1Name + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>") - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")))
      ((Getters.dropVecMessageKeySpecX A).inImage img) := by
    rw [← fnAddr_dropVecMessageKey_eq_ss_local1_add img.base ext]
    exact hmk
  have hdrop_vc_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropSessionStructureLocal1Name + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")))
      ((Getters.dropVecChainSpecX A).inImage img) := by
    rw [← fnAddr_dropVecChain_eq_ss_local1_add img.base ext]
    exact hvc
  clear hmk hvc
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) 0 12
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) 156 8
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) 232 40
  clear hfn
  wp_init x s0
  have hdealloc := hdealloc_raw
  have hdrop_vc := hdrop_vc_raw
  have hfirst3 := drop_ss_local1_first3 (img := img) (ext := ext) hdealloc_raw
  have hsender := drop_ss_local1_sender (img := img) (ext := ext) hdealloc_raw hdrop_mk_raw
  have htail3 := drop_ss_local1_tail3 (img := img) (ext := ext) hdealloc_raw
  clear hdealloc_raw hdrop_mk_raw hdrop_vc_raw
  dsimp only [tripleRatchetProgAtExt, dropSessionStructureLocal1Name] at hfirst3 hsender htail3 hdrop_vc hdealloc
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨ss, G, st⟩ := x
  dsimp only at *
  rcases ‹s0.readReg64 _ = ss› with rfl
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  rw [stackAt_ss_local1_split s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i v0 v1 v2 v3
  refine drop4_strengthen_post (session_memRegions_entails_344 (s0.readReg64 (Reg.gpr 0#5))) ?_
  refine SepWP.weaken_pre
    (sepConj_mono_left (sessionStateAt_entails_deallocX A (s0.readReg64 (Reg.gpr 0#5)) G st)) ?_
  wp_pull_exists
  rename_i pCap pPtr kCap kPtr
  refine seq_cleanX (img := img) (mid := entry + bv% (12))
    (P_mid :=
      (ssFirst3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) G ∗
        vecPinDeallocX A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
        vecPinDeallocX A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
        vecPinDeallocX A G.root) ∗
      A.pool ∗ stackAt (s0.sp - 32#64) extHookStack ∗
      (optSenderChainAt A (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender st.senderChain ∗
        vecAt A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        (ssTail3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
          sgnPinDeallocX A pCap pPtr ∗
          sgnPinDeallocX A kCap kPtr ∗
          vecPinDeallocX A ⟨G.alice.cap, G.alice.ptr⟩) ∗
        (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDeallocX A G.pq) ∗
        memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
        memRegion (s0.sp - 16512#64) 96 ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v3)))
    (Q := fun sm =>
      Saved32Preserved s0 sm (s0.sp - 32#64) ∧
      sm.readReg64 .x0 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · rw [stackAt_dropVecChain_split_alloc (s0.sp - 32#64)]
    have hsp_sub : (s0.sp - 32#64) - 16480#64 = s0.sp - 16512#64 := by bv_omega
    rw [hsp_sub]
    wp_steps
    refine SepWP.align_pre (by dsimp only [ssFirst3HeadersAt, ssTail3HeadersAt, Reg.x19, Reg.lr, Reg.fp]; ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 _hinv_seq ⟨hpres1, hx0_1⟩
    refine seq_cleanX (img := img) (mid := entry + bv% (76))
      (P_mid :=
        optSenderChainAt A (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender st.senderChain ∗
        A.pool ∗ stackAt (s0.sp - 32#64) Getters.dropVecMessageKeyStackX ∗
        (vecAt A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        (ssTail3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
          sgnPinDeallocX A pCap pPtr ∗
          sgnPinDeallocX A kCap kPtr ∗
          vecPinDeallocX A ⟨G.alice.cap, G.alice.ptr⟩) ∗
        (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDeallocX A G.pq) ∗
        (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
        memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
        memRegion (s0.sp - 16512#64) 48 ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v3)))
      (Q := fun sm =>
        Saved32Preserved s0 sm (s0.sp - 32#64) ∧
        sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
      ?_ ?_
    · refine SepWP.mono
        (hfirst3 s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align G s1 _
          hpc1 hrun1 hpres1 hx0_1 ‹_›) ?_
      intro sm Pm _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      rw [stackAt_dropVecMessageKey_split_alloc (s0.sp - 32#64)]
      have hsp_sub1 : (s0.sp - 32#64) - 16432#64 = s0.sp - 16464#64 := by bv_omega
      rw [hsp_sub1,
          ProofLib.memRegion_split' (b := s0.sp - 16512#64) (n := 48) (k := 48)
            (b' := s0.sp - 16464#64) rfl (by bv_omega) (by decide)]
      exact Entails.of_eq (by ac_rfl)
    · intro s2 hpc2 hrun2 _hinv_seq ⟨hpres2, hx19_2⟩
      refine seq_cleanX (img := img) (mid := entry + bv% (156))
        (P_mid :=
          vecAt A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
            (G.chains.zip st.receiverChains) ∗
          A.pool ∗ stackAt (s0.sp - 32#64) Getters.dropVecChainStackX ∗
          ((ssTail3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
            sgnPinDeallocX A pCap pPtr ∗
            sgnPinDeallocX A kCap kPtr ∗
            vecPinDeallocX A ⟨G.alice.cap, G.alice.ptr⟩) ∗
          (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDeallocX A G.pq) ∗
          (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v3)))
        (Q := fun sm =>
          Saved32Preserved s0 sm (s0.sp - 32#64) ∧
          sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
        ?_ ?_
      · refine SepWP.mono
          (hsender s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align G.sender st.senderChain s2 _
            hpc2 hrun2 hpres2 hx19_2 ‹_›) ?_
        intro sm Pm _ _ h
        refine ⟨Entails.trans h.1 ?_, h.2⟩
        rw [stackAt_dropVecChain_split_mk (s0.sp - 32#64)]
        have hsp_sub2 : (s0.sp - 32#64) - 16480#64 = s0.sp - 16512#64 := by bv_omega
        rw [hsp_sub2]
        exact Entails.of_eq (by ac_rfl)
      · intro s3 hpc3 hrun3 _hinv_seq ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        refine seq_cleanX (img := img) (mid := entry + bv% (164))
          (P_mid :=
            (ssTail3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
              sgnPinDeallocX A pCap pPtr ∗
              sgnPinDeallocX A kCap kPtr ∗
              vecPinDeallocX A ⟨G.alice.cap, G.alice.ptr⟩) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) extHookStack ∗
            ((((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
              ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDeallocX A G.pq) ∗
            (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
            memRegion (s0.sp - 16512#64) 96 ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v3)))
          (Q := fun sm =>
            Saved32Preserved s0 sm (s0.sp - 32#64) ∧
            sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
          ?_ ?_
        · wpx_steps
          drop_call_auto s3 hsp_3 hfsp_align hdrop_vc
          refine SepWP.align_pre ?_ ?_
          · rw [hsp_3, stackAt_dropVecChain_split_alloc (s0.sp - 32#64)]
            have hsp_sub3 : (s0.sp - 32#64) - 16480#64 = s0.sp - 16512#64 := by bv_omega
            rw [hsp_sub3]
            dsimp only [ssTail3HeadersAt]
            ac_rfl
          · wp_done
        · intro s4 hpc4 hrun4 _hinv_seq ⟨hpres4, hx19_4⟩
          refine seq_cleanX (img := img) (mid := entry + bv% (232))
            (P_mid :=
              ((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
              ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDeallocX A G.pq ∗
              (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 96#64) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 248#64) 48 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 296#64) 32 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16) ∗
              A.pool ∗ stackAt (s0.sp - 32#64) Getters.dropVecChainStackX ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v3))
            (Q := fun sm =>
              Saved32Preserved s0 sm (s0.sp - 32#64) ∧
              sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
            ?_ ?_
          · refine SepWP.mono
              (htail3 s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align pCap pPtr kCap kPtr G s4 _
                hpc4 hrun4 hpres4 hx19_4 ‹_›) ?_
            intro sm Pm _ _ h
            refine ⟨Entails.trans h.1 ?_, h.2⟩
            rw [stackAt_dropVecChain_split_alloc (s0.sp - 32#64)]
            have hsp_sub4 : (s0.sp - 32#64) - 16480#64 = s0.sp - 16512#64 := by bv_omega
            rw [hsp_sub4]
            exact Entails.of_eq (by ac_rfl)
          · intro s5 hpc5 hrun5 _hinv_seq ⟨⟨hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩, hx19_5⟩
            have hsp_tail : s5.sp + 32#64 = s0.sp := by rw [hsp_5]; bv_omega
            dsimp only [vecPinDeallocX]
            by_cases hcap : (G.pq.cap == 0#64) = true <;>
              simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wpx_steps
              refine SepWP.weaken_pre (pq_header24_weaken (s0.readReg64 (Reg.gpr 0#5)) G.pq.cap G.pq.ptr _) ?_
              wp_done
            · refine sepWP_pull_pure fun ⟨_hpos, _hlt⟩ => ?_
              have _hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
              have _hbound : G.pq.cap.toNat + 1 ≤ 2 ^ 63 := by omega
              have _hlay : LayoutOk G.pq.cap.toNat 1 := ⟨_hpos, _hpow2, _hbound⟩
              wpx_steps
              have _hal_tail1 : ((s5.sp + 32#64) &&& 15#64 == 0#64) = true := by
                rw [hsp_tail]; assumption
              refine SepWP.weaken_pre
                (tail_dealloc_ss_local1_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) G.pq.cap G.pq.ptr
                  _ _ _ s0.sp _ _ _ _) ?_
              conv => arg 4; rw [show stackAt s0.sp extHookStack = stackAt (s5.sp + 32#64) extHookStack by rw [hsp_tail]]
              wpx_call hdealloc (G.pq.ptr, G.pq.cap.toNat, 1)
              simp only [hsp_tail] at *
              refine SepWP.weaken_pre (P' :=
                (memRegion (s0.readReg64 (Reg.gpr 0#5) + 120#64) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 96#64) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 248#64) 48 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 296#64) 32 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16) ∗
                A.pool ∗
                (stackAt (s0.sp - 32#64) Getters.dropVecChainStackX ∗ cells (s0.sp - 32#64) 4))
                (by rw [← tail_stack_128_from_bottom s0.sp]; exact Entails.of_eq (by ac_rfl)) ?_
              cells_unfold
              wp_pull_exists
              wp_done

theorem drop_session_structure_local1_ok_x {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    OkAtX img ext dropSessionStructureLocal1Name (dropSessionStructureLocal1SpecX A) :=
  drop_session_structure_local1_ok_ext hA
    (Getters.drop_vec_message_key_ok_x hA)
    (Getters.drop_vec_chain_ok_x hA)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
