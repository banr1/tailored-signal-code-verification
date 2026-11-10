/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.ProtocolErrCommon
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.ProtocolErrPreKeyEncrypt
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply

/-!
# T5 Pre-Key Encrypt Error Tail (`+0xc38..+0xc64` → `+0x46c`)

Proves `kyber_run` and `tailPreKeyEncryptErr` (plus trap-mode variants), staging error words to
`sp + 0x9d0`, freeing any non-empty `KyberPayload` heap buffer, and branching to T1 `+0x46c`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?

/-- The T5 Kyber packet `+0xc38 → bl __rust_dealloc → +0x46c`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.kyber_run_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocHooks A abs)
    (w0 w1 w2 w3 w4 w5 kyPtr : BitVec 64) (kp : Option KyberPayload) (s : State)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0xc38#64) (hrun : s.status = .Running)
    (hal : s.spAligned = true) (hx29 : s.readReg64 .x29 = s.sp + 0xb80#64)
    (hregs : tailRegs w0 w1 w2 s.sp s) :
    SepWP (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x46c#64) s
      (memRegion (s.sp + 0x9d0#64) 24 ∗ words64At (s.sp + 0xb00#64) [w3, w4, w5] ∗
        optKyberAt A (s.sp + 0x8a0#64) kyPtr kp ∗ A.pool ∗ stackAt s.sp allocHookStack)
      (fun s' P => s'.sp = s.sp ∧ s'.trace = s.trace ∧ s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs s' = calleeSavedVRegs s ∧ tailRegs w0 w1 w2 s.sp s' ∧
        ∀ m F, (m ⊨ P ∗ F) →
          (m ⊨ (words64At (s.sp + 0x9d0#64) [w3, w4, w5] ∗ memRegion (s.sp + 0xb00#64) 24 ∗
            memRegion (s.sp + 0x8a0#64) 24 ∗ A.pool ∗ stackAt s.sp allocHookStack) ∗ F)) := by
  obtain ⟨hx26, hx28, hx27, hx21, hx23⟩ := hregs
  have hal' : (s.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hal
  dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry] at hpc ⊢
  rw [entryOf_eq_tripleRatchetProgAt_trap (C := C) (abs := abs) himg] at hpc ⊢
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = num% (ls_off% "libsignal_cli_ratchet::encrypt") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")
  have hdealloc := dealloc_ok_at_trap img.base C A abs hA CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli_ratchet::encrypt"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_dealloc")])
  code_fetches_range CryptoVerification.libsignalSessionCode protocolErrBinCli img.base
    (Rust.withPanics (trTrapExterns C abs)) hfn (num% (ls_off% "libsignal_cli_ratchet::encrypt")) 3128 44
  rw [memRegion_24_eq]
  simp only [sepExists_sepConj_left]
  refine SepWP.exists_elim fun u2 => SepWP.exists_elim fun u1 => SepWP.exists_elim fun u0 => ?_
  simp only [words64At, sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at *
  clear himg hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  cases kp with
  | none =>
    simp only [optKyberAt, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], ?_, ?_⟩
    · unfold tailRegs
      simp only [wp_norm, arm64_norm, *]
    · intro m F hm
      have hb := words64At_three_entails (s.sp + 2816#64) w3 w4 w5
      simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd] at hb
      have hk := kyberNone_entails (s.sp + 2208#64)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hk
      simp only [sepConj_assoc] at hm
      exact Satisfies.mono (kyberPost_two hb hk) hm
  | some k =>
    simp only [optKyberAt, boxU8At, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
    wp_focus_pure
    rintro ⟨hptr_ne, hlen_lt⟩
    have hptr_beq : (kyPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hptr_ne
    by_cases hbs : k.ciphertext = []
    · simp only [hbs, List.length_nil, ite_true, emp_sepConj]
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], ?_, ?_⟩
      · unfold tailRegs
        simp only [wp_norm, arm64_norm, *]
      · intro m F hm
        have hb := words64At_three_entails (s.sp + 2816#64) w3 w4 w5
        simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd] at hb
        have hk := kyberSome_entails (s.sp + 2208#64) kyPtr 0#64 k.preKeyId
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hk
        simp only [sepConj_assoc] at hm
        exact Satisfies.mono (kyberPost_four hb hk) hm
    · have hpos : 0 < k.ciphertext.length := List.length_pos_iff.mpr hbs
      have hlen_toNat : (BitVec.ofNat 64 k.ciphertext.length).toNat = k.ciphertext.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      have hlen_ne : BitVec.ofNat 64 k.ciphertext.length ≠ 0#64 := by
        intro h
        have ht := congrArg BitVec.toNat h
        rw [hlen_toNat] at ht
        change k.ciphertext.length = 0 at ht
        omega
      have hlen_beq0 : (BitVec.ofNat 64 k.ciphertext.length == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hlen_ne
      simp only [hbs, ite_false]
      refine SepWP.focus_weaken (pointsToBytes_entails_memRegion kyPtr k.ciphertext) (by sep_focus) ?_
      wp_steps
      wp_apply
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], ?_, ?_⟩
      · unfold tailRegs
        simp only [wp_norm, arm64_norm, *]
      · intro m F hm
        have hb := words64At_three_entails (s.sp + 2816#64) w3 w4 w5
        simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd] at hb
        have hk := kyberSome_entails (s.sp + 2208#64) kyPtr (BitVec.ofNat 64 k.ciphertext.length)
          k.preKeyId
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hk
        simp only [sepConj_assoc] at hm
        exact Satisfies.mono (kyberPost_four' hb hk) hm

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.kyber_run {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocHooks A abs)
    (w0 w1 w2 w3 w4 w5 kyPtr : BitVec 64) (kp : Option KyberPayload) (s : State)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0xc38#64) (hrun : s.status = .Running)
    (hal : s.spAligned = true) (hx29 : s.readReg64 .x29 = s.sp + 0xb80#64)
    (hregs : tailRegs w0 w1 w2 s.sp s) :
    SepWP (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x46c#64) s
      (memRegion (s.sp + 0x9d0#64) 24 ∗ words64At (s.sp + 0xb00#64) [w3, w4, w5] ∗
        optKyberAt A (s.sp + 0x8a0#64) kyPtr kp ∗ A.pool ∗ stackAt s.sp allocHookStack)
      (fun s' P => s'.sp = s.sp ∧ s'.trace = s.trace ∧ s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs s' = calleeSavedVRegs s ∧ tailRegs w0 w1 w2 s.sp s' ∧
        ∀ m F, (m ⊨ P ∗ F) →
          (m ⊨ (words64At (s.sp + 0x9d0#64) [w3, w4, w5] ∗ memRegion (s.sp + 0xb00#64) 24 ∗
            memRegion (s.sp + 0x8a0#64) 24 ∗ A.pool ∗ stackAt s.sp allocHookStack) ∗ F)) := by
  obtain ⟨hx26, hx28, hx27, hx21, hx23⟩ := hregs
  have hal' : (s.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hal
  dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry] at hpc ⊢
  rw [entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl) (abs := abs) himg] at hpc ⊢
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = num% (ls_off% "libsignal_cli_ratchet::encrypt") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")
  have hdealloc := dealloc_ok_at img.base C A ctl abs hA CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli_ratchet::encrypt"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_dealloc")])
  code_fetches_range CryptoVerification.libsignalSessionCode protocolErrBinCli img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (num% (ls_off% "libsignal_cli_ratchet::encrypt")) 3128 44
  rw [memRegion_24_eq]
  simp only [sepExists_sepConj_left]
  refine SepWP.exists_elim fun u2 => SepWP.exists_elim fun u1 => SepWP.exists_elim fun u0 => ?_
  simp only [words64At, sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
  dsimp only [tripleRatchetProgAt] at *
  clear himg hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  cases kp with
  | none =>
    simp only [optKyberAt, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], ?_, ?_⟩
    · unfold tailRegs
      simp only [wp_norm, arm64_norm, *]
    · intro m F hm
      have hb := words64At_three_entails (s.sp + 2816#64) w3 w4 w5
      simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd] at hb
      have hk := kyberNone_entails (s.sp + 2208#64)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hk
      simp only [sepConj_assoc] at hm
      exact Satisfies.mono (kyberPost_two hb hk) hm
  | some k =>
    simp only [optKyberAt, boxU8At, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
    wp_focus_pure
    rintro ⟨hptr_ne, hlen_lt⟩
    have hptr_beq : (kyPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hptr_ne
    by_cases hbs : k.ciphertext = []
    · simp only [hbs, List.length_nil, ite_true, emp_sepConj]
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], ?_, ?_⟩
      · unfold tailRegs
        simp only [wp_norm, arm64_norm, *]
      · intro m F hm
        have hb := words64At_three_entails (s.sp + 2816#64) w3 w4 w5
        simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd] at hb
        have hk := kyberSome_entails (s.sp + 2208#64) kyPtr 0#64 k.preKeyId
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hk
        simp only [sepConj_assoc] at hm
        exact Satisfies.mono (kyberPost_four hb hk) hm
    · have hpos : 0 < k.ciphertext.length := List.length_pos_iff.mpr hbs
      have hlen_toNat : (BitVec.ofNat 64 k.ciphertext.length).toNat = k.ciphertext.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      have hlen_ne : BitVec.ofNat 64 k.ciphertext.length ≠ 0#64 := by
        intro h
        have ht := congrArg BitVec.toNat h
        rw [hlen_toNat] at ht
        change k.ciphertext.length = 0 at ht
        omega
      have hlen_beq0 : (BitVec.ofNat 64 k.ciphertext.length == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hlen_ne
      simp only [hbs, ite_false]
      refine SepWP.focus_weaken (pointsToBytes_entails_memRegion kyPtr k.ciphertext) (by sep_focus) ?_
      wp_steps
      wp_apply
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], ?_, ?_⟩
      · unfold tailRegs
        simp only [wp_norm, arm64_norm, *]
      · intro m F hm
        have hb := words64At_three_entails (s.sp + 2816#64) w3 w4 w5
        simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd] at hb
        have hk := kyberSome_entails (s.sp + 2208#64) kyPtr (BitVec.ofNat 64 k.ciphertext.length)
          k.preKeyId
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hk
        simp only [sepConj_assoc] at hm
        exact Satisfies.mono (kyberPost_four' hb hk) hm

open CryptoVerification.LibsignalPublicApi.StoreKit

/-- **T5 Kyber**: `tailPreKeyEncryptErr_ok` with the T1 tail theorem (`tailDropRecord_ok`, specialized to this
call's frame) as the hypothesis `hT1`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.tailPreKeyEncryptErr_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocHooks A abs)
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State}
    {answers : StoreAnswers (List (BitVec 8)) Unit} {e : ApiError AddrVal Unit}
    {w0 w1 w2 w3 w4 w5 : BitVec 64} {H : SepProp} {scratch : BitVec 64 → SepProp}
    {g : RecordGhost} {rec : SessionRecord (List (BitVec 8))}
    {ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8)))}
    {kyPtr : BitVec 64} {kp : Option KyberPayload}
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0xc38#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A sp scratch g rec ot none
          (memRegion (sp + 0x46a#64) 0x436 ∗ optKyberAt A (sp + 0x8a0#64) kyPtr kp ∗
            memRegion (sp + 0x8b8#64) 0x248 ∗ words64At (sp + 0xb00#64) [w3, w4, w5] ∗
            memRegion (sp + 0xb18#64) 0x68) ∗ H)
      R s0 s)
    (hT1 : ∀ s', TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s' →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x46c#64) (tailRegs w0 w1 w2)
        (fun sp => dropRecordSlots A sp scratch g rec ot none (pollWith sp 0x9d0 [w3, w4, w5]) ∗ H)
        R s0 s' →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s' (fun _ => False)) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False) := by
  have hn : allocHookStack ≤ encSubStack := by decide
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.segExit_of_run_trap hm (fun hL => ?_) hT1
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encTail_run_withEncCommon_trap (C := C) (abs := abs)
    (Act := memRegion (s0.sp - 0xbe0#64 + 0x9d0#64) 24 ∗
      words64At (s0.sp - 0xbe0#64 + 0xb00#64) [w3, w4, w5] ∗
      optKyberAt A (s0.sp - 0xbe0#64 + 0x8a0#64) kyPtr kp ∗ A.pool ∗
      stackAt (s0.sp - 0xbe0#64) allocHookStack)
    (Act' := words64At (s0.sp - 0xbe0#64 + 0x9d0#64) [w3, w4, w5] ∗
      memRegion (s0.sp - 0xbe0#64 + 0xb00#64) 24 ∗ memRegion (s0.sp - 0xbe0#64 + 0x8a0#64) 24 ∗
      A.pool ∗ stackAt (s0.sp - 0xbe0#64) allocHookStack)
    (Fr := (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x436 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x8b8#64) 0x118 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x9e8#64) 0x118 ∗
        memRegion (s0.sp - 0xbe0#64 + 0xb18#64) 0x68) ∗
      dropRecordBase A (s0.sp - 0xbe0#64) scratch g rec ot ∗ cmSlotAt A (s0.sp - 0xbe0#64) none ∗
      H ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encCommonFr A ctl img x (x.draws S answers) s0 allocHookStack)
    hs ?_ ?_ ?_ hL
  · refine Entails.of_eq ?_
    rw [dropRecordSlots_eq, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encCommon_eq A ctl img x (x.draws S answers) s0 _ hn, kyberPoll_eq]
    ac_rfl
  · refine Entails.of_eq ?_
    rw [dropRecordSlots_eq, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encCommon_eq A ctl img x (x.draws S answers) s0 _ hn, kyberDropRecordPoll_eq]
    ac_rfl
  · intro hpc hmeta hregs
    obtain ⟨hrun, hssp, _, hspal, hx29, -⟩ := hmeta
    rw [← hssp] at hregs ⊢
    exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.kyber_run_trap himg hA w0 w1 w2 w3 w4 w5 kyPtr kp s hpc hrun hspal
      (by rw [hx29, hssp]; bv_omega) hregs

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.tailPreKeyEncryptErr {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocHooks A abs)
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State}
    {answers : StoreAnswers (List (BitVec 8)) Unit} {e : ApiError AddrVal Unit}
    {w0 w1 w2 w3 w4 w5 : BitVec 64} {H : SepProp} {scratch : BitVec 64 → SepProp}
    {g : RecordGhost} {rec : SessionRecord (List (BitVec 8))}
    {ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8)))}
    {kyPtr : BitVec 64} {kp : Option KyberPayload}
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0xc38#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A sp scratch g rec ot none
          (memRegion (sp + 0x46a#64) 0x436 ∗ optKyberAt A (sp + 0x8a0#64) kyPtr kp ∗
            memRegion (sp + 0x8b8#64) 0x248 ∗ words64At (sp + 0xb00#64) [w3, w4, w5] ∗
            memRegion (sp + 0xb18#64) 0x68) ∗ H)
      R s0 s)
    (hT1 : ∀ s', TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s' →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x46c#64) (tailRegs w0 w1 w2)
        (fun sp => dropRecordSlots A sp scratch g rec ot none (pollWith sp 0x9d0 [w3, w4, w5]) ∗ H)
        R s0 s' →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s' (fun _ => False)) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False) := by
  have hn : allocHookStack ≤ encSubStack := by decide
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.segExit_of_run hm (fun hL => ?_) hT1
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encTail_run_withEncCommon (C := C) (abs := abs)
    (Act := memRegion (s0.sp - 0xbe0#64 + 0x9d0#64) 24 ∗
      words64At (s0.sp - 0xbe0#64 + 0xb00#64) [w3, w4, w5] ∗
      optKyberAt A (s0.sp - 0xbe0#64 + 0x8a0#64) kyPtr kp ∗ A.pool ∗
      stackAt (s0.sp - 0xbe0#64) allocHookStack)
    (Act' := words64At (s0.sp - 0xbe0#64 + 0x9d0#64) [w3, w4, w5] ∗
      memRegion (s0.sp - 0xbe0#64 + 0xb00#64) 24 ∗ memRegion (s0.sp - 0xbe0#64 + 0x8a0#64) 24 ∗
      A.pool ∗ stackAt (s0.sp - 0xbe0#64) allocHookStack)
    (Fr := (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x436 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x8b8#64) 0x118 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x9e8#64) 0x118 ∗
        memRegion (s0.sp - 0xbe0#64 + 0xb18#64) 0x68) ∗
      dropRecordBase A (s0.sp - 0xbe0#64) scratch g rec ot ∗ cmSlotAt A (s0.sp - 0xbe0#64) none ∗
      H ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encCommonFr A ctl img x (x.draws S answers) s0 allocHookStack)
    hs ?_ ?_ ?_ hL
  · refine Entails.of_eq ?_
    rw [dropRecordSlots_eq, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encCommon_eq A ctl img x (x.draws S answers) s0 _ hn, kyberPoll_eq]
    ac_rfl
  · refine Entails.of_eq ?_
    rw [dropRecordSlots_eq, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encCommon_eq A ctl img x (x.draws S answers) s0 _ hn, kyberDropRecordPoll_eq]
    ac_rfl
  · intro hpc hmeta hregs
    obtain ⟨hrun, hssp, _, hspal, hx29, -⟩ := hmeta
    rw [← hssp] at hregs ⊢
    exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.kyber_run himg hA w0 w1 w2 w3 w4 w5 kyPtr kp s hpc hrun hspal
      (by rw [hx29, hssp]; bv_omega) hregs

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr
