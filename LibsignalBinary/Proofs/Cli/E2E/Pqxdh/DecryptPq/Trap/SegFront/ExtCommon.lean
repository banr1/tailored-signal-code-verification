/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.OnPanicTight
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Fetch
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegFront.Common
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.Common
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# Contract-Backed Front-Segment Helpers & Return Epilogue

Shared stack recombination and return epilogue (`+0x394 .. +0x3b0`) for
`try_decrypt_with_state::<signal_session_handshake::Coins>` on `tripleRatchetProgAtExt`.
-/

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (libsignalSessionCode libsignalSessionImage)
open CryptoVerification.RustHeap (AllocHooks RustAlloc rustDeallocSpec)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost vecResultAt decryptDraws
  protocolAddressAt sessionStateAt signalMessageAt uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel TryDecryptGhost
  entryOf_eq_tripleRatchetProgAtExt logOff rootStack tripleRatchetProgAtExt)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq (tryDecryptMidMeta tryDecryptSavedRegs
  tryDecryptSubStack)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA (sepWP_to_reaches_pc
  tryDecryptStack_recombine)

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.ExtCommon

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr_ext
    {img : Obj.Image} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img =
      (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName :=
  entryOf_eq_tripleRatchetProgAtExt ext himg
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName

/-! ## Shared Stack Recombination and Return Epilogue (`+0x394 .. +0x3b0`) -/

/-- Shared return epilogue (`+0x394 .. +0x3b0`, `retEpiloguePC` to `s0.readReg64 .x30`)
on `tripleRatchetProgAtExt b ext`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecrypt_epilogue_394_wp_ext
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0x394#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1504#64)
    (hs0_align : s0.spAligned = true)
    (_hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
        memRegion (s0.sp - 1504#64) 1408 ∗
        tryDecryptSavedRegs s0.sp s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        sf.trace = s0.trace ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ stackAt s0.sp rootStack)) := by
  unfold tryDecryptSavedRegs
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  dec_fetches_cli b ext hfn 0x394 32
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], ?_, ?_⟩
  · simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]
  · exact tryDecryptStack_recombine s0.sp s0

/-- From a `reaches_pc` reaching `retEpiloguePC img` (`+0x394`), execute the shared return
epilogue (`+0x394 .. +0x3b0`) and conclude `reaches_outcome` for `tryDecryptSpec` on `tripleRatchetProgAtExt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.reaches_epilogue_to_outcome_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (x : TryDecryptGhost) (G' : SessionGhost) (R : SepProp) (s0 s : State)
    (hnpan : (x.model C S uuidTryParse).1 ≠ .error .panic)
    (hG' : x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool G')
    (hreach : reaches_pc (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.retEpiloguePC img) s
      (fun s1 =>
        tryDecryptMidMeta img s0 s1 ∧
        (s1.mem ⊨
          sessionStateAt A x.ss G' (x.model C S uuidTryParse).2 ∗
          vecResultAt A x.ret (x.model C S uuidTryParse).1 ∗
          memRegion (s0.sp - 1504#64) 1408 ∗
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x
            (decryptDraws C x.st x.msg.senderRatchetKey x.rest) s0 ∗ R))) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img) x R s0 s := by
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr_ext
    (ext := ext) himg
  have hcomb : reaches_pc (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (fun sf =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).post x s0 sf ∗ R)) := by
    refine reaches_pc_seq hreach ?_
    intro s1 hpc1 _ ⟨⟨hrun1, hsp1, hs0_align, hsp_align1, _, htrace1, _, _, hvregs1⟩, hm1⟩
    dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.retEpiloguePC] at hpc1
    rw [hentry] at hpc1
    unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap at hm1
    have hm1_re : s1.mem ⊨
        (stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
          memRegion (s0.sp - 1504#64) 1408 ∗
          tryDecryptSavedRegs s0.sp s0) ∗
        (sessionStateAt A x.ss G' (x.model C S uuidTryParse).2 ∗
         vecResultAt A x.ret (x.model C S uuidTryParse).1 ∗
         protocolAddressAt A x.rem x.remA ∗
         protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗
         CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
         logOff img ∗ A.pool ∗ R) := by
      convert hm1 using 1; sep_ac_rfl
    refine reaches_pc_mono
      (sepWP_to_reaches_pc
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecrypt_epilogue_394_wp_ext
          s0 s1 hpc1 hrun1 hsp1 hs0_align hsp_align1 htrace1 hvregs1) hm1_re) ?_
    intro sf _ _ ⟨P_f, hm_sf, hsp_sf, htrace_sf, hcc_sf, hP_f⟩
    refine ⟨hsp_sf, hcc_sf, ?_⟩
    have hm2 := Satisfies.mono (sepConj_mono_left hP_f) hm_sf
    simp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage]
    have hm3 : sf.mem ⊨
        sessionStateAt A x.ss G' (x.model C S uuidTryParse).2 ∗
        (vecResultAt A x.ret (x.model C S uuidTryParse).1 ∗
         protocolAddressAt A x.rem x.remA ∗
         protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗
         CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
         logOff img ∗ stackAt s0.sp rootStack ∗ A.pool ∗ R) := by
      convert hm2 using 1; sep_ac_rfl
    have hent :
        sessionStateAt A x.ss G' (x.model C S uuidTryParse).2 ⊢
          ⌜(x.model C S uuidTryParse).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
            (∃∗ G'' : SessionGhost, ⌜x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool G''⌝ ∗
              sessionStateAt A x.ss G'' (x.model C S uuidTryParse).2) :=
      Entails.pure_right ⟨hnpan, htrace_sf⟩
        (Entails.trans (Entails.pure_right hG' (Entails.refl _))
          (Entails.sepExists_intro
            (P := fun G'' => ⌜x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool G''⌝ ∗
              sessionStateAt A x.ss G'' (x.model C S uuidTryParse).2) G'))
    have hm4 := Satisfies.mono (sepConj_mono_left hent) hm3
    convert hm4 using 1; sep_ac_rfl
  exact reaches_outcome_of_reaches_pc
    (reaches_pc_mono hcomb fun sf _ _ ⟨hsp_sf, hcc_sf, hpost_sf⟩ => ⟨hpost_sf, hsp_sf, hcc_sf⟩)

/-- Tight variant of `reaches_epilogue_to_outcome_ext`: since the return epilogue always halts
normally (`Or.inl`), the outcome holds immediately against `Decrypt.tryDecryptSpecTight` as well. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.reaches_epilogue_to_outcome_tight_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (x : TryDecryptGhost) (G' : SessionGhost) (R : SepProp) (s0 s : State)
    (hnpan : (x.model C S uuidTryParse).1 ≠ .error .panic)
    (hG' : x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool G')
    (hreach : reaches_pc (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.retEpiloguePC img) s
      (fun s1 =>
        tryDecryptMidMeta img s0 s1 ∧
        (s1.mem ⊨
          sessionStateAt A x.ss G' (x.model C S uuidTryParse).2 ∗
          vecResultAt A x.ret (x.model C S uuidTryParse).1 ∗
          memRegion (s0.sp - 1504#64) 1408 ∗
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x
            (decryptDraws C x.st x.msg.senderRatchetKey x.rest) s0 ∗ R))) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight C A ctl uuidTryParse S img) x R s0 s := by
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr_ext
    (ext := ext) himg
  have hcomb : reaches_pc (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (fun sf =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).post x s0 sf ∗ R)) := by
    refine reaches_pc_seq hreach ?_
    intro s1 hpc1 _ ⟨⟨hrun1, hsp1, hs0_align, hsp_align1, _, htrace1, _, _, hvregs1⟩, hm1⟩
    dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.retEpiloguePC] at hpc1
    rw [hentry] at hpc1
    unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap at hm1
    have hm1_re : s1.mem ⊨
        (stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
          memRegion (s0.sp - 1504#64) 1408 ∗
          tryDecryptSavedRegs s0.sp s0) ∗
        (sessionStateAt A x.ss G' (x.model C S uuidTryParse).2 ∗
         vecResultAt A x.ret (x.model C S uuidTryParse).1 ∗
         protocolAddressAt A x.rem x.remA ∗
         protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗
         CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
         logOff img ∗ A.pool ∗ R) := by
      convert hm1 using 1; sep_ac_rfl
    refine reaches_pc_mono
      (sepWP_to_reaches_pc
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecrypt_epilogue_394_wp_ext
          s0 s1 hpc1 hrun1 hsp1 hs0_align hsp_align1 htrace1 hvregs1) hm1_re) ?_
    intro sf _ _ ⟨P_f, hm_sf, hsp_sf, htrace_sf, hcc_sf, hP_f⟩
    refine ⟨hsp_sf, hcc_sf, ?_⟩
    have hm2 := Satisfies.mono (sepConj_mono_left hP_f) hm_sf
    simp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage]
    have hm3 : sf.mem ⊨
        sessionStateAt A x.ss G' (x.model C S uuidTryParse).2 ∗
        (vecResultAt A x.ret (x.model C S uuidTryParse).1 ∗
         protocolAddressAt A x.rem x.remA ∗
         protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗
         CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
         logOff img ∗ stackAt s0.sp rootStack ∗ A.pool ∗ R) := by
      convert hm2 using 1; sep_ac_rfl
    have hent :
        sessionStateAt A x.ss G' (x.model C S uuidTryParse).2 ⊢
          ⌜(x.model C S uuidTryParse).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
            (∃∗ G'' : SessionGhost, ⌜x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool G''⌝ ∗
              sessionStateAt A x.ss G'' (x.model C S uuidTryParse).2) :=
      Entails.pure_right ⟨hnpan, htrace_sf⟩
        (Entails.trans (Entails.pure_right hG' (Entails.refl _))
          (Entails.sepExists_intro
            (P := fun G'' => ⌜x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool G''⌝ ∗
              sessionStateAt A x.ss G'' (x.model C S uuidTryParse).2) G'))
    have hm4 := Satisfies.mono (sepConj_mono_left hent) hm3
    convert hm4 using 1; sep_ac_rfl
  exact reaches_outcome_of_reaches_pc
    (reaches_pc_mono hcomb fun sf _ _ ⟨hsp_sf, hcc_sf, hpost_sf⟩ => ⟨hpost_sf, hsp_sf, hcc_sf⟩)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.fnAddr_tryDecrypt_add_eq_ext
    {b : BitVec 64} {ext : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + k =
      libsignalSessionCode.fnOff name := by fnoff_eq) :
    (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + BitVec.ofNat 64 k =
      (tripleRatchetProgAtExt b ext).fnAddr name := by
  simp only [Program.fnAddr_rebase, BitVec.add_assoc, ← BitVec.ofNat_add, hk]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.fnAddr_tryDecrypt_rel64_ext
    {b : BitVec 64} {ext : String → Option (State → State)}
    {callee : String} {off' : Nat} {d : BitVec 64}
    (hfn' : libsignalSessionCode.fnOff callee = off')
    (hd : ((bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) : BitVec 64) + d = BitVec.ofNat 64 off') :
    (tripleRatchetProgAtExt b ext).fnAddr callee =
      (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + d := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"),
    hfn', BitVec.add_assoc, hd]

section BS9

ls_attribute [local simp, local arm64_norm ↓] (ls_stub% "__rustc::__rust_dealloc")

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.BS9.tryDecrypt_dealloc_ok_ext
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocHooks A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" -
          (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))))
      (rustDeallocSpec A) :=
  hook_ok_at (P := libsignalSessionCode) (hname := "__rustc::__rust_dealloc")
    (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
    (by fnoff_eq)
    (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm])
    (by simp [Rust.isPanicSymbol])
    hA.dealloc

end BS9

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.ExtCommon
