/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegDispatchAux
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Defs
import all Init.Data.String.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefs
import LibsignalBinary.Proofs.Common.StringCloneFlat
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop

/-!
# CLI `SegDispatch` Instruction Decodes and Frame Helpers

Instruction decode tables and stack `memRegion` split/join lemmas for `SegDispatch` in
`signal_session_ratchet::decrypt_signal`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoVerification.RustHeap CryptoGames.LibsignalSession

open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoGames CryptoGames.LibsignalSessionApi

open CryptoVerification.LibsignalTripleRatchet.RawByteMove

open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit

open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove

open CryptoVerification.LibsignalPublicApi.MessageDecrypt

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Instruction decode lemmas -/

gen_decodes libsignalSessionCode_tree messageDecryptDispatchBinCli [(ls_off% "libsignal_cli_ratchet::decrypt_signal" + 140) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 148), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 216) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 420), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1192) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1268), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8972) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8996)]

set_option maxRecDepth 200000 in
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.satisfies_rodata_msgDecryptStr {img : Obj.Image} {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1208) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1212))) ↦ᵣ utf8 "message_decrypt_signal") ∗ P :=
  Satisfies.of_rodata_bytes' himg hF (off := num% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1208) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1212))) (bs := utf8 "message_decrypt_signal")
    (by rfl_kernel) hP

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.apiDecResultAt_sessionNotFound_of_words (A : RustAlloc) (a : AddrVal)
    (cap ptr b w4 : BitVec 64) (pad : List (BitVec 8))
    (hpad : pad.length = 7) (hw4 : a.device :: pad = unpack64 w4) (r : BitVec 64) :
    ((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ ptr) ∗
      ((r + 0x10#64) ↦₆₄ BitVec.ofNat 64 a.name.length) ∗
      ((r + 0x18#64) ↦₆₄ w4) ∗
      ((r + 0x20#64) ↦₆₄ (b + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1208) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1212)))) ∗ ((r + 0x28#64) ↦₆₄ 22#64) ∗
      (vecU8Buf A cap ptr a.name ∗ ((b + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1208) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1212))) ↦ᵣ utf8 "message_decrypt_signal"))) ⊢
      apiDecResultAt A r (.error (.sessionNotFound a "message_decrypt_signal")) := by
  dsimp only [apiDecResultAt, apiErrAt, addrCloneAt]
  have hvec := vecU8_intro A r cap ptr a.name
  have hw4_ent := pointsTo64_entails_byte_memRegion7 (r + 0x18#64) a.device pad w4 hpad hw4
  have h19 : r + 0x18#64 + 1#64 = r + 0x19#64 := by bv_arith
  rw [h19] at hw4_ent
  have hstr : (((r + 0x20#64) ↦₆₄ (b + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1208) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1212)))) ∗
      ((r + 0x28#64) ↦₆₄ 22#64) ∗ ((b + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1208) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1212))) ↦ᵣ utf8 "message_decrypt_signal")) ⊢
      strRefAt (r + 0x20#64) (utf8 "message_decrypt_signal") := by
    have hlen : BitVec.ofNat 64 (utf8 "message_decrypt_signal").length = 22#64 := by rfl_kernel
    have h28 : r + 0x20#64 + 8#64 = r + 0x28#64 := by bv_arith
    have h := strRefAt_intro (r + 0x20#64) (b + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1208) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1212))) (utf8 "message_decrypt_signal")
    rwa [hlen, h28] at h
  have hreord :
      ((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ ptr) ∗
        ((r + 0x10#64) ↦₆₄ BitVec.ofNat 64 a.name.length) ∗
        ((r + 0x18#64) ↦₆₄ w4) ∗
        ((r + 0x20#64) ↦₆₄ (b + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1208) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1212)))) ∗ ((r + 0x28#64) ↦₆₄ 22#64) ∗
        (vecU8Buf A cap ptr a.name ∗ ((b + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1208) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1212))) ↦ᵣ utf8 "message_decrypt_signal"))) =
      ((((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ ptr) ∗
          ((r + 0x10#64) ↦₆₄ BitVec.ofNat 64 a.name.length) ∗
          vecU8Buf A cap ptr a.name) ∗
        ((r + 0x18#64) ↦₆₄ w4)) ∗
        (((r + 0x20#64) ↦₆₄ (b + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1208) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1212)))) ∗ ((r + 0x28#64) ↦₆₄ 22#64) ∗
          ((b + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1208) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1212))) ↦ᵣ utf8 "message_decrypt_signal"))) := by ac_rfl
  rw [hreord]
  exact sepConj_mono (sepConj_mono hvec hw4_ent) hstr

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.stagedRes_sessionNotFound (A : RustAlloc) (src : BitVec 64) (a : AddrVal)
    (cap ptr b w4 : BitVec 64) (pad : List (BitVec 8))
    (hpad : pad.length = 7) (hw4 : a.device :: pad = unpack64 w4) :
    (((src ↦₁₂₈ q0OfWords ptr (BitVec.ofNat 64 a.name.length) w4) ∗
      ((src + 0x10#64) ↦₁₂₈ q1OfWords w4 (b + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1208) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1212))) 22#64) ∗
      ((src + 0x20#64) ↦₃₂ 0#32)) ∗
      (vecU8Buf A cap ptr a.name ∗ ((b + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1208) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1212))) ↦ᵣ utf8 "message_decrypt_signal"))) ⊢
      StagedRes A cap
        (BitVec.zeroExtend 64
          (BitVec.truncate 32 (BitVec.zeroExtend 64 (ptr.extractLsb' 0 32) >>> 8)))
        (BitVec.zeroExtend 64 (ptr.extractLsb' 0 32))
        src (.error (.sessionNotFound a "message_decrypt_signal")) := by
  have h22 : (22#64 : BitVec 64).extractLsb' 32 32 = 0#32 := rfl
  rw [← h22]
  exact stagedRes_of_words5 A src cap ptr (BitVec.ofNat 64 a.name.length) w4
    (b + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1208) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1212))) 22#64
    (vecU8Buf A cap ptr a.name ∗ ((b + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1208) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1212))) ↦ᵣ utf8 "message_decrypt_signal"))
    (.error (.sessionNotFound a "message_decrypt_signal"))
    (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.apiDecResultAt_sessionNotFound_of_words A a cap ptr b w4 pad hpad hw4)

/-! ## Stack and frame `memRegion` split/join helpers -/

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.stringClone_ok_at_dec {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + bv% ((2^64 + ls_off% "<alloc::string::String as core::clone::Clone>::clone" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64)) (stringCloneSpec A) := by
  have haddr :
      (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "<alloc::string::String as core::clone::Clone>::clone" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64) =
      (tripleRatchetProgAt b C ctl abs).fnAddr stringCloneHookName := by
    simp only [tripleRatchetProgAt, Program.fnAddr_rebase,
      CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName,
      (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal"),
      LibsignalBinary.Proofs.Common.StringCloneFlat.stringCloneName_fnOff, BitVec.add_assoc]
    bv_omega
  rw [haddr]
  exact LibsignalBinary.Proofs.Common.StringCloneFlat.stringClone_tripleRatchetProgAt_ok b C A ctl abs hA

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.msgDecrypt_memcpy_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + bv% ((2^64 + ls_off% "memcpy" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64)) framelessMemcpySpec := by
  exact framelessMemcpy_ok_at (b := b) (C := C) (ctl := ctl)
    (abs := abs) (name := CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName) (k := num% (ls_off% "memcpy" - ls_off% "libsignal_cli_ratchet::decrypt_signal"))

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.msgDecrypt_dealloc_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64)) (rustDeallocSpec A) := by
  exact dealloc_ok_at_norm (b := b) (C := C) (ctl := ctl)
    (name := CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName) (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli_ratchet::decrypt_signal")) hA

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.tapeAt_entails_tapeAfter_zero (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    CryptoVerification.SignalSession.Coins.coinsAt ctl cur rest ⊢ CryptoVerification.SignalSession.Coins.coinsAfter ctl cur rest 0 := by
  unfold CryptoVerification.SignalSession.Coins.coinsAt CryptoVerification.SignalSession.Coins.tapeAt2 CryptoVerification.SignalSession.Coins.coinsAfter CryptoVerification.SignalSession.Coins.tapeAfter2
  apply Entails.pure_left; intro _
  simp only [BitVec.add_zero, Nat.sub_zero]
  exact Entails.refl _

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.stringClone_onPanic_entails {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {img : Obj.Image} {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {s0 s sf : State} {F : SepProp}
    (h0s : s0.trace <+: s.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).onPanic x s0 sf := by
  dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecV, Spec.inImage]
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨halloc, hpref⟩ => ?_
  exact Entails.pure_right ⟨h0s.trans hpref, Or.inl (allocFailedIn_trans' h0s halloc)⟩
    (entails_anyHeap _)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.decSeg_of_sepWP_mid {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {mid : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hF : FrozenInv img s) (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWP (tripleRatchetProgAt img.base C ctl abs) mid s P
      (fun sm Pm => FrozenInv img sm → (sm.mem ⊨ Pm ∗ R) →
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope x R s0 sm Out)) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope x R s0 s Out := by
  intro hL
  obtain ⟨sm, hsteps, ⟨_, _, Pm, hmm, hnext⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ := hnext (hF.of_steps hsteps) hmm (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.decSeg_of_sepWP_done {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hF : FrozenInv img s) (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWP (tripleRatchetProgAt img.base C ctl abs) target s P
      (fun sf P_f => FrozenInv img sf → (sf.mem ⊨ P_f ∗ R) → Out sf)) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope x R s0 s Out := by
  intro hL
  obtain ⟨sf, hsteps, ⟨_, _, P_f, hmf, hOut⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  exact ⟨sf, hsteps, Or.inl (hOut (hF.of_steps hsteps) hmf)⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.decSeg_of_sepWPp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp (tripleRatchetProgAt img.base C ctl abs) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → Out sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).onPanic x s0 sf ∗ R))) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope x R s0 s Out := by
  intro hL
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hOut⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, _hoom⟩
  · exact ⟨sf, hsteps, Or.inl (hOut hmf)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, hqp hmf⟩))⟩
  · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.msgDecrypt_memcpy_ok_trap
    {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A (trTrapExterns C abs)) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "memcpy" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
      framelessMemcpySpec := by
  have hAC := AllocContracts.of_tripleRatchetProgAt_trap b C A (trTrapExterns C abs) hA
  rw [trTrapExterns_idem C abs] at hAC
  exact CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT.msgDecrypt_memcpy_ok_ext hAC

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.msgDecrypt_dealloc_ok_trap
    {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A (trTrapExterns C abs)) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
      (rustDeallocSpec A) := by
  have hAC := AllocContracts.of_tripleRatchetProgAt_trap b C A (trTrapExterns C abs) hA
  rw [trTrapExterns_idem C abs] at hAC
  exact CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT.msgDecrypt_dealloc_ok_ext hAC

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.decSeg_of_sepWP_mid_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {mid : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hF : FrozenInv img s) (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWP (trTrapProgAt img.base C abs) mid s P
      (fun sm Pm => FrozenInv img sm → (sm.mem ⊨ Pm ∗ R) →
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV_trap
          img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope x R s0 sm Out)) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV_trap
      img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope x R s0 s Out :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT.decSegVXExt_of_sepWP_mid (ctl := ctl) hF hm hwp

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.decSeg_of_sepWP_done_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hF : FrozenInv img s) (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWP (trTrapProgAt img.base C abs) target s P
      (fun sf P_f => FrozenInv img sf → (sf.mem ⊨ P_f ∗ R) → Out sf)) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV_trap
      img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope x R s0 s Out :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT.decSegVXExt_of_sepWP_done (ctl := ctl) hF hm hwp

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.decSeg_of_sepWPp_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp (trTrapProgAt img.base C abs) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → Out sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecV
          C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).onPanic x s0 sf ∗ R))) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV_trap
      img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope x R s0 s Out :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT.decSegVXExt_of_sepWPp (ctl := ctl) hm hwp

end CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch
