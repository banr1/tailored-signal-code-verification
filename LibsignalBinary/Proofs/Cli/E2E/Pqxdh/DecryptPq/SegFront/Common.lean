/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Fetch
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.Common
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Handshake `DecryptPq` Front-Segment Helpers & Return Epilogue

Fetch macro `dec_fetches_cli`, stack recombination helpers, and the shared return epilogue
(`+0x394 .. +0x3b0`) for `try_decrypt_with_state::<signal_session_handshake::Coins>` on
`tripleRatchetProgAt`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open CryptoVerification.LibsignalTripleRatchet.DecryptPq

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Fetch hypotheses for `try_decrypt_with_state::<HookRng>` (`0x6eff8`), from fn-relative offset
`k0`, `len` bytes. -/
macro "dec_fetches_cli " b:term:max H:term:max hfn:ident k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBinCli
      $b (Rust.withPanics $H) $hfn (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") $k0 $len)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName :=
  entryOf_eq_tripleRatchetProgAt himg CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName

/-! ## Shared Stack Recombination and Return Epilogue (`+0x394 .. +0x3b0`) -/

/-- Shared return epilogue (`+0x394 .. +0x3b0`, `retEpiloguePC` to `s0.readReg64 .x30`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecrypt_epilogue_394_wp {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (s0 s : State)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0x394#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1504#64)
    (hs0_align : s0.spAligned = true)
    (_hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (tripleRatchetProgAt b C ctl abs) (s0.readReg64 .x30) s
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
  dec_fetches_cli b (tripleRatchetExterns C ctl abs) hfn 0x394 32
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], ?_, ?_⟩
  · simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]
  · exact tryDecryptStack_recombine s0.sp s0

/-- From a `reaches_pc` reaching `retEpiloguePC img` (`+0x394`), execute the shared return
epilogue (`+0x394 .. +0x3b0`) and conclude `reaches_outcome` for `tryDecryptSpec`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.reaches_epilogue_to_outcome {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (x : TryDecryptGhost) (G' : SessionGhost) (R : SepProp) (s0 s : State)
    (hnpan : (x.model C S uuidTryParse).1 ≠ .error .panic)
    (hG' : x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool G')
    (hreach : reaches_pc (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.retEpiloguePC img) s
      (fun s1 =>
        tryDecryptMidMeta img s0 s1 ∧
        (s1.mem ⊨
          sessionStateAt A x.ss G' (x.model C S uuidTryParse).2 ∗
          vecResultAt A x.ret (x.model C S uuidTryParse).1 ∗
          memRegion (s0.sp - 1504#64) 1408 ∗
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x
            (decryptDraws C x.st x.msg.senderRatchetKey x.rest) s0 ∗ R))) :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img) x R s0 s := by
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr (C := C) (ctl := ctl) (abs := abs) himg
  have hcomb : reaches_pc (tripleRatchetProgAt img.base C ctl abs) (s0.readReg64 .x30) s
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
      convert hm1 using 1; ac_rfl
    refine reaches_pc_mono
      (sepWP_to_reaches_pc
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecrypt_epilogue_394_wp s0 s1 hpc1 hrun1 hsp1 hs0_align hsp_align1 htrace1 hvregs1) hm1_re) ?_
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
      convert hm2 using 1; ac_rfl
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
    convert hm4 using 1; ac_rfl
  exact reaches_outcome_of_reaches_pc
    (reaches_pc_mono hcomb fun _ _ _ ⟨hsp_sf, hcc_sf, hpost_sf⟩ => ⟨hpost_sf, hsp_sf, hcc_sf⟩)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.fnAddr_tryDecrypt_add_eq {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + k =
      libsignalSessionCode.fnOff name := by fnoff_eq) :
    (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + BitVec.ofNat 64 k =
      (tripleRatchetProgAt b C ctl abs).fnAddr name := by
  simp only [Program.fnAddr_rebase, BitVec.add_assoc, ← BitVec.ofNat_add, hk]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.fnAddr_tryDecrypt_rel64 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {callee : String} {off' : Nat} {d : BitVec 64}
    (hfn' : libsignalSessionCode.fnOff callee = off')
    (hd : ((bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) : BitVec 64) + d = BitVec.ofNat 64 off') :
    (tripleRatchetProgAt b C ctl abs).fnAddr callee =
      (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + d := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"), hfn',
    BitVec.add_assoc, hd]

namespace BS9

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.BS9.tryDecrypt_dealloc_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))))
      (rustDeallocSpec A) :=
  hook_ok_at_raw (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
    (k := num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))) rfl (by decide)
    (ls_hook% "__rustc::__rust_dealloc")
    (allocHooks_tripleRatchetExterns C ctl A abs hA).dealloc

end BS9

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA
