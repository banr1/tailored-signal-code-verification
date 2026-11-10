/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtDefs
public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.Common
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Fetch
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegFront.Common
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.Common
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.ErrTailSym
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23

@[expose] public section

set_option autoImplicit false

/-!
# Generalised (`tripleRatchetProgAtExt`) and Trap (`trTrapProgAt`) `ErrTail` Symbolic Steps for Handshake `DecryptPq`
-/

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ReceiverChain)
open CryptoVerification (libsignalSessionCode libsignalSessionImage)
open CryptoVerification.RustHeap (AllocHooks RustAlloc allocHookStack arrayAt rustDeallocSpec)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt)
open CryptoVerification.LibsignalTripleRatchet (trTrapExterns trTrapProgAt tripleRatchetProgAtExt)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropChainSpec dropChainStack)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA (SepWP.bind_framed SepWP.rw_pre
  arrayAt_cons arrayAt_nil bv_ofNat_succ_beq_zero bv_ofNat_succ_sub_one bv_ofNat_succ_succ_bne_one
  sp_sub_1504_add_0x38 sp_sub_1504_add_0xe8 sp_sub_1504_add_0xf0 tryDecryptWPInv words5At)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (AllocContractsMem4K)

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.ErrTailSym

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Step `+0x30c .. +0x330` (`10` instructions) of `ErrTail` on `tripleRatchetProgAtExt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_copy_spe_wp_ext
    {img : Obj.Image} {ext : String → Option (State → State)}
    {ret tag chainsPtr chainsLen : BitVec 64}
    {w0 w1 w2 w3 w4 r0 r1 r2 r3 r4 r5 t0 t1 t2 : BitVec 64}
    {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errTailPC img)
    (hmeta : tryDecryptWPInv s0 s)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx26 : s.readReg64 .x26 = tag) :
    let prog := tripleRatchetProgAtExt img.base ext
    let sp := s0.sp - 1504#64
    SepWP prog (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x334#64) s
      (((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ chainsLen) ∗
       ((sp + 0x140#64) ↦₆₄ t0) ∗
       ((sp + 0x148#64) ↦₆₄ t1) ∗
       ((sp + 0x150#64) ↦₆₄ t2) ∗
       words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
       (ret ↦₆₄ r0) ∗
       words5At (ret + 8#64) r1 r2 r3 r4 r5)
      (fun sf P =>
        P = (((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
             ((sp + 0x48#64) ↦₆₄ chainsLen) ∗
             ((sp + 0x140#64) ↦₆₄ w0) ∗
             ((sp + 0x148#64) ↦₆₄ w1) ∗
             ((sp + 0x150#64) ↦₆₄ w2) ∗
             words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
             (ret ↦₆₄ tag) ∗
             words5At (ret + 8#64) w0 w1 w2 w3 w4) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x20 = chainsPtr ∧
        sf.readReg64 .x21 = chainsLen) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry_eq_fnAddr_ext
    (ext := ext) himg
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  dec_fetches_cli img.base ext hfn 0x30c 40
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errTailPC] at hpc
  rw [hentry] at hpc ⊢
  clear hentry hfn
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  unfold words5At
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by sep_ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_copy_spe_wp_trap {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    {ret tag chainsPtr chainsLen : BitVec 64}
    {w0 w1 w2 w3 w4 r0 r1 r2 r3 r4 r5 t0 t1 t2 : BitVec 64}
    {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errTailPC img)
    (hmeta : tryDecryptWPInv s0 s)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx26 : s.readReg64 .x26 = tag) :
    let prog := trTrapProgAt img.base C abs
    let sp := s0.sp - 1504#64
    SepWP prog (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x334#64) s
      (((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ chainsLen) ∗
       ((sp + 0x140#64) ↦₆₄ t0) ∗
       ((sp + 0x148#64) ↦₆₄ t1) ∗
       ((sp + 0x150#64) ↦₆₄ t2) ∗
       words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
       (ret ↦₆₄ r0) ∗
       words5At (ret + 8#64) r1 r2 r3 r4 r5)
      (fun sf P =>
        P = (((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
             ((sp + 0x48#64) ↦₆₄ chainsLen) ∗
             ((sp + 0x140#64) ↦₆₄ w0) ∗
             ((sp + 0x148#64) ↦₆₄ w1) ∗
             ((sp + 0x150#64) ↦₆₄ w2) ∗
             words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
             (ret ↦₆₄ tag) ∗
             words5At (ret + 8#64) w0 w1 w2 w3 w4) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x20 = chainsPtr ∧
        sf.readReg64 .x21 = chainsLen) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_copy_spe_wp_ext
    (img := img) (ext := trTrapExterns C abs)
    (chainsPtr := chainsPtr) (chainsLen := chainsLen)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
    (t0 := t0) (t1 := t1) (t2 := t2)
    himg hpc hmeta hx19 hx20 hx26

/-- Single iteration `+0x33c .. +0x344` (`mov x0, x19; bl drop_glue<Chain>`) of the `ErrTail`
chain-drop loop on `tripleRatchetProgAtExt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_one_wp_ext
    {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {p chainsPtr rem : BitVec 64} (gc : ChainGhost × ReceiverChain) {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hdrop : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk_ext img.base A ext)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errDropChainLoopPC img)
    (hmeta : tryDecryptWPInv s0 s)
    (hx19 : s.readReg64 .x19 = p)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = rem) :
    let prog := tripleRatchetProgAtExt img.base ext
    let sp := s0.sp - 1504#64
    SepWP prog (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x344#64) s
      (chainAt A gc p ∗ A.pool ∗ stackAt sp dropChainStack)
      (fun sf P =>
        P = (memRegion p 104 ∗ A.pool ∗ stackAt sp dropChainStack) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x19 = p ∧
        sf.readReg64 .x20 = chainsPtr ∧
        sf.readReg64 .x21 = rem) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry_eq_fnAddr_ext
    (ext := ext) himg
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  dec_fetches_cli img.base ext hfn 0x33c 8
  have hdrop' :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
          BitVec.ofNat 64 (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" -
            ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")))
        (dropChainSpec A) := by
    rw [← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.fnAddr_tryDecrypt_rel64_ext
      (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]") (by decide)]
    exact hdrop
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errDropChainLoopPC] at hpc
  rw [hentry] at hpc ⊢
  clear hentry hfn hdrop himg
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  refine SepWP.rw_pre (by rw [← hsp]) ?_
  wp_steps
  wp_call hdrop' ⟨p, gc⟩
  wp_finish
  refine ⟨?_, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  rw [hsp]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_one_wp_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    {p chainsPtr rem : BitVec 64} (gc : ChainGhost × ReceiverChain) {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hdrop : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk_trap img.base C A abs)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errDropChainLoopPC img)
    (hmeta : tryDecryptWPInv s0 s)
    (hx19 : s.readReg64 .x19 = p)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = rem) :
    let prog := trTrapProgAt img.base C abs
    let sp := s0.sp - 1504#64
    SepWP prog (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x344#64) s
      (chainAt A gc p ∗ A.pool ∗ stackAt sp dropChainStack)
      (fun sf P =>
        P = (memRegion p 104 ∗ A.pool ∗ stackAt sp dropChainStack) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x19 = p ∧
        sf.readReg64 .x20 = chainsPtr ∧
        sf.readReg64 .x21 = rem) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_one_wp_ext
    (img := img) (A := A) (ext := trTrapExterns C abs)
    (p := p) (chainsPtr := chainsPtr) (rem := rem) (s0 := s0) (s := s)
    gc himg hdrop hpc hmeta hx19 hx20 hx21

/-- Loop latch `+0x344 .. +0x350` when `x21 = 1` on `tripleRatchetProgAtExt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_exit_wp_ext
    {img : Obj.Image} {ext : String → Option (State → State)}
    {chainsPtr : BitVec 64} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x344#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = 1#64) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x350#64) s
      emp
      (fun sf P =>
        P = emp ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x20 = chainsPtr) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry_eq_fnAddr_ext
    (ext := ext) himg
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  dec_fetches_cli img.base ext hfn 0x344 12
  rw [hentry] at hpc ⊢
  clear hentry hfn himg
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  wp_steps
  wp_finish
  exact ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm]⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_exit_wp_trap {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    {chainsPtr : BitVec 64} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x344#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = 1#64) :
    SepWP (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x350#64) s
      emp
      (fun sf P =>
        P = emp ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x20 = chainsPtr) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_exit_wp_ext
    (img := img) (ext := trTrapExterns C abs) (chainsPtr := chainsPtr) (s0 := s0) (s := s)
    himg hpc hmeta hx20 hx21

/-- Loop latch `+0x344 .. +0x33c` when `x21 = rem` with `rem ≠ 1` on `tripleRatchetProgAtExt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_cont_wp_ext
    {img : Obj.Image} {ext : String → Option (State → State)}
    {p chainsPtr rem : BitVec 64} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hne : (rem != 1#64) = true)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x344#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx19 : s.readReg64 .x19 = p)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = rem) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errDropChainLoopPC img) s
      emp
      (fun sf P =>
        P = emp ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x19 = p + 104#64 ∧
        sf.readReg64 .x20 = chainsPtr ∧
        sf.readReg64 .x21 = rem - 1#64) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry_eq_fnAddr_ext
    (ext := ext) himg
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  dec_fetches_cli img.base ext hfn 0x344 12
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errDropChainLoopPC]
  rw [hentry] at hpc ⊢
  clear hentry hfn himg
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  wp_steps
  generalize tripleRatchetProgAtExt img.base ext = prog at *
  try rw [hne, if_pos rfl]
  wp_finish
  refine ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], ?_⟩
  simp_all [arm64_norm]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_cont_wp_trap {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    {p chainsPtr rem : BitVec 64} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hne : (rem != 1#64) = true)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x344#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx19 : s.readReg64 .x19 = p)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = rem) :
    SepWP (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errDropChainLoopPC img) s
      emp
      (fun sf P =>
        P = emp ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x19 = p + 104#64 ∧
        sf.readReg64 .x20 = chainsPtr ∧
        sf.readReg64 .x21 = rem - 1#64) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_cont_wp_ext
    (img := img) (ext := trTrapExterns C abs)
    (p := p) (chainsPtr := chainsPtr) (rem := rem) (s0 := s0) (s := s)
    himg hne hpc hmeta hx19 hx20 hx21

/-- Loop `+0x33c .. +0x350` over `gc :: rest` in `ErrTail` on `tripleRatchetProgAtExt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_loop_wp_ext
    {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hdrop : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk_ext img.base A ext)
    {chainsPtr : BitVec 64} {s0 : State}
    (rest : List (ChainGhost × ReceiverChain)) :
    ∀ (gc : ChainGhost × ReceiverChain) (p : BitVec 64) (s : State),
      (rest.length + 1) * 104 < 2 ^ 63 →
      s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errDropChainLoopPC img →
      tryDecryptWPInv s0 s →
      s.readReg64 .x19 = p →
      s.readReg64 .x20 = chainsPtr →
      s.readReg64 .x21 = BitVec.ofNat 64 (rest.length + 1) →
      SepWP (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x350#64) s
        (arrayAt (chainAt A) 104 p (gc :: rest) ∗ A.pool ∗ stackAt (s0.sp - 1504#64) dropChainStack)
        (fun sf P =>
          P = (memRegion p ((rest.length + 1) * 104) ∗ A.pool ∗
            stackAt (s0.sp - 1504#64) dropChainStack) ∧
          tryDecryptWPInv s0 sf ∧
          sf.readReg64 .x20 = chainsPtr) := by
  have hone_step : ∀ (gc : ChainGhost × ReceiverChain) (p rem : BitVec 64) (s : State),
      s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errDropChainLoopPC img →
      tryDecryptWPInv s0 s →
      s.readReg64 .x19 = p →
      s.readReg64 .x20 = chainsPtr →
      s.readReg64 .x21 = rem →
      SepWP (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x344#64) s
        (chainAt A gc p ∗ A.pool ∗ stackAt (s0.sp - 1504#64) dropChainStack)
        (fun sf P =>
          P = (memRegion p 104 ∗ A.pool ∗ stackAt (s0.sp - 1504#64) dropChainStack) ∧
          tryDecryptWPInv s0 sf ∧
          sf.readReg64 .x19 = p ∧
          sf.readReg64 .x20 = chainsPtr ∧
          sf.readReg64 .x21 = rem) :=
    fun gc p rem s hpc hmeta hx19 hx20 hx21 =>
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_one_wp_ext
        (img := img) (A := A) (ext := ext)
        (p := p) (chainsPtr := chainsPtr) (rem := rem) (s0 := s0) (s := s)
        gc himg hdrop hpc hmeta hx19 hx20 hx21
  have hexit_step : ∀ (s : State),
      s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x344#64 →
      tryDecryptWPInv s0 s →
      s.readReg64 .x20 = chainsPtr →
      s.readReg64 .x21 = 1#64 →
      SepWP (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x350#64) s
        emp
        (fun sf P =>
          P = emp ∧
          tryDecryptWPInv s0 sf ∧
          sf.readReg64 .x20 = chainsPtr) :=
    fun s hpc hmeta hx20 hx21 =>
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_exit_wp_ext
        (img := img) (ext := ext) (chainsPtr := chainsPtr) (s0 := s0) (s := s) himg hpc hmeta hx20 hx21
  have hcont_step : ∀ (p rem : BitVec 64) (s : State),
      (rem != 1#64) = true →
      s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x344#64 →
      tryDecryptWPInv s0 s →
      s.readReg64 .x19 = p →
      s.readReg64 .x20 = chainsPtr →
      s.readReg64 .x21 = rem →
      SepWP (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errDropChainLoopPC img) s
        emp
        (fun sf P =>
          P = emp ∧
          tryDecryptWPInv s0 sf ∧
          sf.readReg64 .x19 = p + 104#64 ∧
          sf.readReg64 .x20 = chainsPtr ∧
          sf.readReg64 .x21 = rem - 1#64) :=
    fun p rem s hne hpc hmeta hx19 hx20 hx21 =>
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_cont_wp_ext
        (img := img) (ext := ext) (p := p) (chainsPtr := chainsPtr) (rem := rem) (s0 := s0) (s := s)
        himg hne hpc hmeta hx19 hx20 hx21
  clear himg hdrop
  generalize tripleRatchetProgAtExt img.base ext = prog at *
  generalize CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errDropChainLoopPC img = loop_pc at *
  generalize CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img = entry at *
  induction rest with
  | nil =>
    intro gc p s hlt hpc hmeta hx19 hx20 hx21
    rw [List.length_nil, Nat.zero_add] at hx21
    have hone := hone_step gc p 1#64 s hpc hmeta hx19 hx20 hx21
    refine SepWP.bind_framed (F := emp) hone ?_ ?_
    · rw [arrayAt_cons, arrayAt_nil, sepConj_emp, sepConj_emp]
    intro s1 P1 ⟨hP1, hmeta1, _, hx20_1, hx21_1⟩ hpc1
    subst hP1
    have hexit := hexit_step s1 hpc1 hmeta1 hx20_1 hx21_1
    refine SepWP.bind_framed
      (F := memRegion p 104 ∗ A.pool ∗ stackAt (s0.sp - 1504#64) dropChainStack) hexit ?_ ?_
    · rw [emp_sepConj, sepConj_emp]
    intro sf Pf ⟨hPf, hmeta_f, hx20_f⟩ hpcf
    subst hPf
    refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f, hx20_f⟩
    rw [emp_sepConj, List.length_nil, Nat.zero_add, Nat.one_mul]
  | cons gc' rest' ih =>
    intro gc p s hlt hpc hmeta hx19 hx20 hx21
    rw [List.length_cons] at hlt hx21
    have hone := hone_step gc p (BitVec.ofNat 64 (rest'.length + 1 + 1)) s hpc hmeta hx19 hx20 hx21
    refine SepWP.bind_framed (F := arrayAt (chainAt A) 104 (p + 104#64) (gc' :: rest')) hone ?_ ?_
    · rw [arrayAt_cons]; sep_ac_rfl
    intro s1 P1 ⟨hP1, hmeta1, hx19_1, hx20_1, hx21_1⟩ hpc1
    subst hP1
    have hstep := hcont_step p (BitVec.ofNat 64 (rest'.length + 1 + 1)) s1
      (bv_ofNat_succ_succ_bne_one hlt) hpc1 hmeta1 hx19_1 hx20_1 hx21_1
    refine SepWP.bind_framed
      (F := (memRegion p 104 ∗ A.pool ∗ stackAt (s0.sp - 1504#64) dropChainStack) ∗
            arrayAt (chainAt A) 104 (p + 104#64) (gc' :: rest')) hstep ?_ ?_
    · rw [emp_sepConj]
    intro s2 P2 ⟨hP2, hmeta2, hx19_2, hx20_2, hx21_2⟩ hpc2
    subst hP2
    have hx21_2' : s2.readReg64 .x21 = BitVec.ofNat 64 (rest'.length + 1) := by
      rw [hx21_2, bv_ofNat_succ_sub_one (rest'.length + 1)]
    have hlt' : (rest'.length + 1) * 104 < 2 ^ 63 :=
      Nat.lt_trans (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (by decide)) hlt
    have hih := ih gc' (p + 104#64) s2 hlt' hpc2 hmeta2 hx19_2 hx20_2 hx21_2'
    refine SepWP.bind_framed (F := memRegion p 104) hih ?_ ?_
    · sep_ac_rfl
    intro sf Pf ⟨hPf, hmeta_f, hx20_f⟩ hpcf
    subst hPf
    refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f, hx20_f⟩
    have hcomb :
        memRegion p ((rest'.length + 1 + 1) * 104) =
        memRegion p 104 ∗ memRegion (p + 104#64) ((rest'.length + 1) * 104) := by
      rw [show (rest'.length + 1 + 1) * 104 = 104 + (rest'.length + 1) * 104 by omega]
      exact memRegion_split p 104 ((rest'.length + 1) * 104) (by omega)
    rw [List.length_cons, hcomb]
    sep_ac_rfl

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_loop_wp_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hdrop : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk_trap img.base C A abs)
    {chainsPtr : BitVec 64} {s0 : State}
    (rest : List (ChainGhost × ReceiverChain)) :
    ∀ (gc : ChainGhost × ReceiverChain) (p : BitVec 64) (s : State),
      (rest.length + 1) * 104 < 2 ^ 63 →
      s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errDropChainLoopPC img →
      tryDecryptWPInv s0 s →
      s.readReg64 .x19 = p →
      s.readReg64 .x20 = chainsPtr →
      s.readReg64 .x21 = BitVec.ofNat 64 (rest.length + 1) →
      SepWP (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x350#64) s
        (arrayAt (chainAt A) 104 p (gc :: rest) ∗ A.pool ∗ stackAt (s0.sp - 1504#64) dropChainStack)
        (fun sf P =>
          P = (memRegion p ((rest.length + 1) * 104) ∗ A.pool ∗
            stackAt (s0.sp - 1504#64) dropChainStack) ∧
          tryDecryptWPInv s0 sf ∧
          sf.readReg64 .x20 = chainsPtr) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_loop_wp_ext
    (img := img) (A := A) (ext := trTrapExterns C abs) (chainsPtr := chainsPtr) (s0 := s0)
    himg hdrop rest

/-- Step `+0x334 .. +0x350` when `x21 = 0` on `tripleRatchetProgAtExt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_nil_wp_ext
    {img : Obj.Image} {ext : String → Option (State → State)}
    {chainsPtr : BitVec 64} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x334#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = 0#64) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x350#64) s
      emp
      (fun sf P =>
        P = emp ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x20 = chainsPtr) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry_eq_fnAddr_ext
    (ext := ext) himg
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  dec_fetches_cli img.base ext hfn 0x334 4
  rw [hentry] at hpc ⊢
  clear hentry hfn himg
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  wp_steps
  wp_finish
  exact ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm]⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_nil_wp_trap {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    {chainsPtr : BitVec 64} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x334#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = 0#64) :
    SepWP (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x350#64) s
      emp
      (fun sf P =>
        P = emp ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x20 = chainsPtr) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_nil_wp_ext
    (img := img) (ext := trTrapExterns C abs) (chainsPtr := chainsPtr) (s0 := s0) (s := s)
    himg hpc hmeta hx20 hx21

/-- Step `+0x334 .. +0x33c` when `x21 = rem` with `(rem == 0) = false` on `tripleRatchetProgAtExt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_init_wp_ext
    {img : Obj.Image} {ext : String → Option (State → State)}
    {chainsPtr rem : BitVec 64} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hne : (rem == 0#64) = false)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x334#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = rem) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errDropChainLoopPC img) s
      emp
      (fun s1 P1 =>
        P1 = emp ∧
        tryDecryptWPInv s0 s1 ∧
        s1.readReg64 .x19 = chainsPtr ∧
        s1.readReg64 .x20 = chainsPtr ∧
        s1.readReg64 .x21 = rem) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry_eq_fnAddr_ext
    (ext := ext) himg
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  dec_fetches_cli img.base ext hfn 0x334 8
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errDropChainLoopPC]
  rw [hentry] at hpc ⊢
  clear hentry hfn himg
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  wp_steps
  wp_finish
  exact ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_init_wp_trap {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    {chainsPtr rem : BitVec 64} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hne : (rem == 0#64) = false)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x334#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = rem) :
    SepWP (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errDropChainLoopPC img) s
      emp
      (fun s1 P1 =>
        P1 = emp ∧
        tryDecryptWPInv s0 s1 ∧
        s1.readReg64 .x19 = chainsPtr ∧
        s1.readReg64 .x20 = chainsPtr ∧
        s1.readReg64 .x21 = rem) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_init_wp_ext
    (img := img) (ext := trTrapExterns C abs) (chainsPtr := chainsPtr) (rem := rem) (s0 := s0) (s := s)
    himg hne hpc hmeta hx20 hx21

/-- Step `+0x334 .. +0x350` of `ErrTail` on `tripleRatchetProgAtExt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_chains_wp_ext
    {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {chainsPtr : BitVec 64} {cs : List (ChainGhost × ReceiverChain)} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hdrop : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk_ext img.base A ext)
    (hlt : cs.length * 104 < 2 ^ 63)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x334#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 cs.length) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x350#64) s
      (arrayAt (chainAt A) 104 chainsPtr cs ∗ A.pool ∗ stackAt (s0.sp - 1504#64) dropChainStack)
      (fun sf P =>
        P = (memRegion chainsPtr (cs.length * 104) ∗ A.pool ∗
          stackAt (s0.sp - 1504#64) dropChainStack) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x20 = chainsPtr) := by
  cases cs with
  | nil =>
    rw [List.length_nil] at hx21
    have hstep := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_nil_wp_ext
      (img := img) (ext := ext) himg hpc hmeta hx20 hx21
    refine SepWP.bind_framed (F := A.pool ∗ stackAt (s0.sp - 1504#64) dropChainStack) hstep ?_ ?_
    · rw [arrayAt_nil]
    intro sf Pf ⟨hPf, hmeta_f, hx20_f⟩ hpcf
    subst hPf
    refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f, hx20_f⟩
    rw [List.length_nil, Nat.zero_mul, memRegion_zero]
  | cons gc rest =>
    rw [List.length_cons] at hlt hx21 ⊢
    have hstep := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_init_wp_ext
      (img := img) (ext := ext) himg (bv_ofNat_succ_beq_zero hlt) hpc hmeta hx20 hx21
    refine SepWP.bind_framed
      (F := arrayAt (chainAt A) 104 chainsPtr (gc :: rest) ∗ A.pool ∗
            stackAt (s0.sp - 1504#64) dropChainStack) hstep ?_ ?_
    · rw [emp_sepConj]
    intro s1 P1 ⟨hP1, hmeta1, hx19_1, hx20_1, hx21_1⟩ hpc1
    subst hP1
    refine SepWP.rw_pre (emp_sepConj _) ?_
    exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_loop_wp_ext
      (img := img) (A := A) (ext := ext) (chainsPtr := chainsPtr) (s0 := s0)
      himg hdrop rest gc chainsPtr s1 hlt hpc1 hmeta1 hx19_1 hx20_1 hx21_1

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_chains_wp_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    {chainsPtr : BitVec 64} {cs : List (ChainGhost × ReceiverChain)} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hdrop : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk_trap img.base C A abs)
    (hlt : cs.length * 104 < 2 ^ 63)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x334#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 cs.length) :
    SepWP (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x350#64) s
      (arrayAt (chainAt A) 104 chainsPtr cs ∗ A.pool ∗ stackAt (s0.sp - 1504#64) dropChainStack)
      (fun sf P =>
        P = (memRegion chainsPtr (cs.length * 104) ∗ A.pool ∗
          stackAt (s0.sp - 1504#64) dropChainStack) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x20 = chainsPtr) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_drop_chains_wp_ext
    (img := img) (A := A) (ext := trTrapExterns C abs) (chainsPtr := chainsPtr) (cs := cs) (s0 := s0) (s := s)
    himg hdrop hlt hpc hmeta hx20 hx21

private theorem errTail_dealloc_chains_wp_gen
    {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {chainsCap chainsPtr : BitVec 64} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")))
      (rustDeallocSpec A))
    (hlt : chainsCap.toNat * 104 < 2 ^ 63)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x350#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x36c#64) s
      (((s0.sp - 1504#64 + 0x38#64) ↦₆₄ chainsCap) ∗
       (if chainsCap = 0#64 then emp
        else A.live chainsPtr (chainsCap.toNat * 104) 8 ∗
          memRegion chainsPtr (chainsCap.toNat * 104)) ∗
       A.pool ∗ stackAt (s0.sp - 1504#64) allocHookStack)
      (fun sf P =>
        P = (((s0.sp - 1504#64 + 0x38#64) ↦₆₄ chainsCap) ∗ A.pool ∗
          stackAt (s0.sp - 1504#64) allocHookStack) ∧
        tryDecryptWPInv s0 sf) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry_eq_fnAddr_ext
    (ext := ext) himg
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  dec_fetches_cli img.base ext hfn 0x350 28
  rw [hentry] at hpc ⊢
  clear hentry hfn himg
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  by_cases hcap : chainsCap = 0#64
  · subst hcap
    refine SepWP.rw_pre (by simp only [ite_true, emp_sepConj, ← hsp]; exact rfl) ?_
    wp_steps
    wp_finish
    refine ⟨?_, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩⟩
    rw [hsp]
  · refine SepWP.rw_pre (by simp only [hcap, ite_false, ← hsp]; exact rfl) ?_
    have hcap_beq : (chainsCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hmul : (chainsCap * 104#64).toNat = chainsCap.toNat * 104 := by
      rw [BitVec.toNat_mul, show (104#64 : BitVec 64).toNat = 104 from rfl,
          Nat.mod_eq_of_lt (by omega)]
    wp_steps
    wp_call hdealloc (chainsPtr, chainsCap.toNat * 104, 8)
    wp_finish
    refine ⟨?_, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩⟩
    rw [hsp, sp_sub_1504_add_0x38]
    sep_ac_rfl

/-- Step `+0x350 .. +0x36c` of `ErrTail` on `tripleRatchetProgAtExt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_dealloc_chains_wp_ext
    {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {chainsCap chainsPtr : BitVec 64} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hMem : AllocContractsMem4K img.base A ext)
    (hlt : chainsCap.toNat * 104 < 2 ^ 63)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x350#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x36c#64) s
      (((s0.sp - 1504#64 + 0x38#64) ↦₆₄ chainsCap) ∗
       (if chainsCap = 0#64 then emp
        else A.live chainsPtr (chainsCap.toNat * 104) 8 ∗
          memRegion chainsPtr (chainsCap.toNat * 104)) ∗
       A.pool ∗ stackAt (s0.sp - 1504#64) allocHookStack)
      (fun sf P =>
        P = (((s0.sp - 1504#64 + 0x38#64) ↦₆₄ chainsCap) ∗ A.pool ∗
          stackAt (s0.sp - 1504#64) allocHookStack) ∧
        tryDecryptWPInv s0 sf) :=
  errTail_dealloc_chains_wp_gen (chainsCap := chainsCap) himg
    (hMem.dealloc_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
      (num% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")))
    hlt hpc hmeta hx20

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_dealloc_chains_wp_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    {chainsCap chainsPtr : BitVec 64} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocHooks A abs)
    (hlt : chainsCap.toNat * 104 < 2 ^ 63)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x350#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr) :
    SepWP (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x36c#64) s
      (((s0.sp - 1504#64 + 0x38#64) ↦₆₄ chainsCap) ∗
       (if chainsCap = 0#64 then emp
        else A.live chainsPtr (chainsCap.toNat * 104) 8 ∗
          memRegion chainsPtr (chainsCap.toNat * 104)) ∗
       A.pool ∗ stackAt (s0.sp - 1504#64) allocHookStack)
      (fun sf P =>
        P = (((s0.sp - 1504#64 + 0x38#64) ↦₆₄ chainsCap) ∗ A.pool ∗
          stackAt (s0.sp - 1504#64) allocHookStack) ∧
        tryDecryptWPInv s0 sf) :=
  errTail_dealloc_chains_wp_gen (ext := trTrapExterns C abs) (chainsCap := chainsCap) himg
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.BS9.tryDecrypt_dealloc_ok_trap
      (b := img.base) (C := C) hA)
    hlt hpc hmeta hx20

private theorem errTail_dealloc_pq_wp_gen
    {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {pqCap pqPtr : BitVec 64} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")))
      (rustDeallocSpec A))
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x36c#64)
    (hmeta : tryDecryptWPInv s0 s) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.retEpiloguePC img) s
      (((s0.sp - 1504#64 + 0xe8#64) ↦₆₄ pqCap) ∗
       ((s0.sp - 1504#64 + 0xf0#64) ↦₆₄ pqPtr) ∗
       (if pqCap = 0#64 then emp
        else A.live pqPtr pqCap.toNat 1 ∗ memRegion pqPtr pqCap.toNat) ∗
       A.pool ∗ stackAt (s0.sp - 1504#64) allocHookStack)
      (fun sf P =>
        P = (((s0.sp - 1504#64 + 0xe8#64) ↦₆₄ pqCap) ∗
             ((s0.sp - 1504#64 + 0xf0#64) ↦₆₄ pqPtr) ∗
             A.pool ∗ stackAt (s0.sp - 1504#64) allocHookStack) ∧
        tryDecryptWPInv s0 sf) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry_eq_fnAddr_ext
    (ext := ext) himg
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  dec_fetches_cli img.base ext hfn 0x36c 24
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.retEpiloguePC]
  rw [hentry] at hpc ⊢
  clear hentry hfn himg
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  by_cases hcap : pqCap = 0#64
  · subst hcap
    refine SepWP.rw_pre (by simp only [ite_true, emp_sepConj, ← hsp]; exact rfl) ?_
    wp_steps
    wp_finish
    refine ⟨?_, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩⟩
    rw [hsp]
  · refine SepWP.rw_pre (by simp only [hcap, ite_false, ← hsp]; exact rfl) ?_
    have hcap_beq : (pqCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    wp_steps
    wp_call hdealloc (pqPtr, pqCap.toNat, 1)
    wp_steps
    wp_finish
    refine ⟨?_, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩⟩
    rw [hsp, sp_sub_1504_add_0xe8, sp_sub_1504_add_0xf0]
    sep_ac_rfl

/-- Step `+0x36c .. +0x394` of `ErrTail` on `tripleRatchetProgAtExt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_dealloc_pq_wp_ext
    {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {pqCap pqPtr : BitVec 64} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hMem : AllocContractsMem4K img.base A ext)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x36c#64)
    (hmeta : tryDecryptWPInv s0 s) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.retEpiloguePC img) s
      (((s0.sp - 1504#64 + 0xe8#64) ↦₆₄ pqCap) ∗
       ((s0.sp - 1504#64 + 0xf0#64) ↦₆₄ pqPtr) ∗
       (if pqCap = 0#64 then emp
        else A.live pqPtr pqCap.toNat 1 ∗ memRegion pqPtr pqCap.toNat) ∗
       A.pool ∗ stackAt (s0.sp - 1504#64) allocHookStack)
      (fun sf P =>
        P = (((s0.sp - 1504#64 + 0xe8#64) ↦₆₄ pqCap) ∗
             ((s0.sp - 1504#64 + 0xf0#64) ↦₆₄ pqPtr) ∗
             A.pool ∗ stackAt (s0.sp - 1504#64) allocHookStack) ∧
        tryDecryptWPInv s0 sf) :=
  errTail_dealloc_pq_wp_gen (pqCap := pqCap) (pqPtr := pqPtr) himg
    (hMem.dealloc_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
      (num% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")))
    hpc hmeta

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_dealloc_pq_wp_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    {pqCap pqPtr : BitVec 64} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocHooks A abs)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x36c#64)
    (hmeta : tryDecryptWPInv s0 s) :
    SepWP (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.retEpiloguePC img) s
      (((s0.sp - 1504#64 + 0xe8#64) ↦₆₄ pqCap) ∗
       ((s0.sp - 1504#64 + 0xf0#64) ↦₆₄ pqPtr) ∗
       (if pqCap = 0#64 then emp
        else A.live pqPtr pqCap.toNat 1 ∗ memRegion pqPtr pqCap.toNat) ∗
       A.pool ∗ stackAt (s0.sp - 1504#64) allocHookStack)
      (fun sf P =>
        P = (((s0.sp - 1504#64 + 0xe8#64) ↦₆₄ pqCap) ∗
             ((s0.sp - 1504#64 + 0xf0#64) ↦₆₄ pqPtr) ∗
             A.pool ∗ stackAt (s0.sp - 1504#64) allocHookStack) ∧
        tryDecryptWPInv s0 sf) :=
  errTail_dealloc_pq_wp_gen (ext := trTrapExterns C abs) (pqCap := pqCap) (pqPtr := pqPtr) himg
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.BS9.tryDecrypt_dealloc_ok_trap
      (b := img.base) (C := C) hA)
    hpc hmeta

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.ErrTailSym
