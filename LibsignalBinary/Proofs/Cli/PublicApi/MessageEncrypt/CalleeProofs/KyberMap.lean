/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Callees
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.CliEncHooks
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply

/-!
# CLI `Option::map` Kyber Payload Closure Proof

Verifies the `<Option<(KyberPreKeyId, Box<[u8]>)>>::map` closure used when constructing a
`PreKeySignalMessage` on the CLI image.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalPublicApi.MessageEncrypt

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[simp, arm64_norm]
abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMapName : String :=
  "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>"

gen_decodes libsignalSessionCode_tree kyberMapBinCli [(ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>" + 0) → (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>" + 148)]

private theorem stackAt_kyberMap (sp : BitVec 64) :
    stackAt sp (allocHookStack + 0x40) =
      stackAt (sp - 64#64) allocHookStack ∗ cells (sp - 64#64) 8 :=
  ProofLib.stackAt_split_cells sp allocHookStack 8 (by decide)

private theorem memRegion_24_none (p : BitVec 64) :
    memRegion p 24 =
      (∃∗ u0 : BitVec 64, (p ↦₆₄ u0) ∗ memRegion (p + 8#64) 16) := by
  rw [memRegion_split p 8 16 (by decide), ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left]

private theorem memRegion_24_some (p : BitVec 64) :
    memRegion p 24 =
      (∃∗ u2 : BitVec 32, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 16#64) ↦₃₂ u2) ∗ memRegion (p + 20#64) 4) := by
  rw [memRegion_split p 8 16 (by decide),
    memRegion_split (p + 8#64) 8 8 (by decide),
    memRegion_split (p + 8#64 + 8#64) 4 4 (by decide),
    memRegion_four, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem ofNat_ne_zero_of_pos {n : Nat} (hpos : 0 < n) (h64 : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64] at ht
  change n = 0 at ht
  omega

private theorem beq_ofNat_zero_eq_false {n : Nat} (hpos : 0 < n) (h64 : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact ofNat_ne_zero_of_pos hpos h64

private theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

private theorem fnAddr_tripleRatchetProgAt {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {off : Nat}
    (h : libsignalSessionCode.fnOff name = off) :
    (tripleRatchetProgAt b C ctl abs).fnAddr name = b + BitVec.ofNat 64 off := by
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, h]

private theorem optKyberAt_none_exists (A : RustAlloc) (out : BitVec 64) :
    (∃∗ bp : BitVec 64, optKyberAt A out bp none) =
      (out ↦₆₄ 0#64) ∗ memRegion (out + 8#64) 16 := by
  apply ProofLib.sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun _ => by simp only [optKyberAt]; exact Entails.refl _
  · exact Entails.sepExists_right 0#64 (by simp only [optKyberAt]; exact Entails.refl _)

private theorem fnAddr_trTrapProgAt {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {name : String} {off : Nat}
    (h : libsignalSessionCode.fnOff name = off) :
    (trTrapProgAt b C abs).fnAddr name = b + BitVec.ofNat 64 off := by
  simp only [trTrapProgAt, Program.fnAddr_rebase, h]

set_option maxHeartbeats 1600000 in
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMap_fn_ok_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMapName)
      (kyberMapSpec A) := by
  simp only [kyberMapSpec, stackAt_kyberMap]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMapName = (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>") := by
    fnoff_eq
  have hshim := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.cliNoAllocShim_ok_at_trap (b := b) (C := C) (abs := abs)
    (name := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMapName) (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>")))
  have halloc := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.cliAlloc_ok_at_norm_trap (b := b) (C := C) hA
    (name := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMapName) (k := num% (ls_off% "__rustc::__rust_alloc" - (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>")))
  have hmemcpy := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.cliFramelessMemcpy_ok_at_trap (b := b) (C := C) (abs := abs)
    (name := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMapName) (k := num% (ls_off% "memcpy" - (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>")))
  have hpanic : (trTrapProgAt b C abs).externAt?
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMapName + BitVec.ofNat 64 (num% (ls_off% "alloc::alloc::handle_alloc_error" - (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>")))) =
      some Rust.panicked :=
    panic_at_panicSymbol (hname := "alloc::alloc::handle_alloc_error") hfn
      (by fnoff_eq) (by fnoff_eq)
      (by fnoff_eq) (by simp [Rust.isPanicSymbol])
  dsimp only [sessionShimSpec] at hshim
  dsimp only [framelessMemcpySpec] at hmemcpy
  code_fetches CryptoVerification.libsignalSessionCode kyberMapBinCli b
    (Rust.withPanics (trTrapExterns C abs)) hfn (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>") 152
  wpp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, arg, ptr, kp⟩ := x
  dsimp only at *
  cases kp with
  | none =>
    simp only [kyberArgAt, optKyberAt_none_exists, memRegion_24_none, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun u0 => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done
  | some k =>
    simp only [kyberArgAt, optKyberAt, boxU8At, memRegion_24_some, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u0 => ?_
    refine SepWPp.pure_elim fun ⟨hptr_ne, hlen_lt32⟩ => ?_
    have hptr_beq : (ptr == 0#64) = false := beq_eq_false_iff_ne.mpr hptr_ne
    have hlen_lt63 : k.ciphertext.length < 2 ^ 63 := by omega
    by_cases hbs : k.ciphertext = []
    · simp only [hbs, List.length_nil, ite_true, sepConj_emp, emp_sepConj]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
    · have hpos : 0 < k.ciphertext.length := List.length_pos_iff.mpr hbs
      have hlen_ne0 : BitVec.ofNat 64 k.ciphertext.length ≠ 0#64 :=
        ofNat_ne_zero_of_pos hpos (by omega)
      have hlen_beq0 : (BitVec.ofNat 64 k.ciphertext.length == 0#64) = false :=
        beq_ofNat_zero_eq_false hpos (by omega)
      have hpow2 : ∃ m, 1 = 2 ^ m := ⟨0, rfl⟩
      have hbound : k.ciphertext.length + 1 ≤ 2 ^ 63 := by omega
      have hlay : LayoutOk k.ciphertext.length 1 := ⟨hpos, hpow2, hbound⟩
      simp only [hbs, ite_false]
      apply SepWPp.of_sepWP (mid := entry + 60#64)
      wp_steps
      wp_apply
      wp_steps
      wp_apply
      apply SepWP.done (by simp_all) (by simp_all)
      by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
      · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
        simp only [hoom, ite_true, sepConj_assoc]
        refine sepWPp_pure_mid fun htrace => ?_
        apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "alloc::alloc::handle_alloc_error" - (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>")) % 2^64))
        wp_steps
        apply SepWP.done (by simp_all) (by simp_all)
        refine SepWPp.panic (by simp_all) (by simp_all) fun hm => ?_
        simpa only [sepConj_assoc] using
          allowPanic_panicked (allocFailedIn_of_eq (by simp_all [Rust.panicked])) hm
      · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
        simp only [hoom, ite_false, sepConj_assoc]
        refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
        apply SepWPp.of_sepWP_ret
        wp_steps
        wp_apply
        wp_steps
        wp_done

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMap_fn_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMapName)
      (kyberMapSpec A) :=
  subroutine_ok_kit_of_trTrap (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMap_fn_ok_trap hA)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMap_ok_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {abs : String → Option (State → State)} (h3 : TripleRatchetHooks C A S (trTrapExterns C abs))
    (_himg : Obj.Loads libsignalSessionImage img) : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KyberMapOk_trap img C A abs := by
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KyberMapOk_trap
  have hA : AllocHooks A abs := (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.allocHooks_trTrap_iff C A abs).mp h3.alloc
  have h := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMap_fn_ok_trap (b := img.base) (C := C) hA
  rwa [fnAddr_trTrapProgAt (off := (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>")) (ls_lemma% fnOff "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>")] at h

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMap_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} (h3 : PublicApiHooks C A S encRecord abs)
    (_himg : Obj.Loads libsignalSessionImage img) : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KyberMapOk img C A ctl abs := by
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KyberMapOk
  have h := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMap_fn_ok (b := img.base) (C := C) (ctl := ctl) h3.alloc
  rwa [fnAddr_tripleRatchetProgAt (off := (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>")) (ls_lemma% fnOff "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>")] at h

private theorem fnAddr_trExtProgAt {b : BitVec 64}
    {ext : String → Option (State → State)} {name : String} {off : Nat}
    (h : libsignalSessionCode.fnOff name = off) :
    (tripleRatchetProgAtExt b ext).fnAddr name = b + BitVec.ofNat 64 off := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, h]

private theorem kyberMap_stackedMemcpy_ok_at_ext {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hMc : HookSat ext memcpyName CryptoVerification.SignalSession.CliExt.memcpySpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMapName +
        BitVec.ofNat 64 (num% (ls_off% "memcpy" - (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>"))))
      (withStack framelessMemcpySpec allocHookStack) := by
  have hraw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMapName +
        BitVec.ofNat 64 (num% (ls_off% "memcpy" - (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>"))))
      CryptoVerification.SignalSession.CliExt.memcpySpec :=
    hook_ok_at (hname := memcpyName) rfl (by fnoff_eq) (by fnoff_eq) (by fnoff_eq)
      (by simp [Rust.isPanicSymbol, memcpyName]) hMc
  refine subroutine_ok_mono hraw (fun (dst, src, bs) R s0 hpre => ?_)
    (fun (dst, src, bs) R s0 sf hpost => ?_)
  · dsimp only [withStack, framelessMemcpySpec] at hpre
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hm⟩
    dsimp only [CryptoVerification.SignalSession.CliExt.memcpySpec, libcMemcpySpec,
      CryptoVerification.SignalSession.CliExt.memHookStack, allocHookStack] at hm ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  · dsimp only [CryptoVerification.SignalSession.CliExt.memcpySpec,
      CryptoVerification.SignalSession.CliExt.memHookStack, withStack, framelessMemcpySpec,
      allocHookStack] at hpost ⊢
    simpa only [sepConj_assoc] using hpost

set_option maxHeartbeats 1600000 in
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMap_fn_ok_ext
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocHooks A ext)
    (hSh : HookSat ext shimName CryptoVerification.SignalSession.CliExt.shimSpec)
    (hMc : HookSat ext memcpyName CryptoVerification.SignalSession.CliExt.memcpySpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMapName)
      (kyberMapSpec A) := by
  simp only [kyberMapSpec, stackAt_kyberMap]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMapName = (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>") := by
    fnoff_eq
  have hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMapName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>"))))
      sessionShimSpec :=
    hook_ok_at (hname := shimName) rfl (by fnoff_eq) (by fnoff_eq) (by fnoff_eq)
      (by simp [Rust.isPanicSymbol, shimName]) hSh
  have halloc := alloc_ok_at_ext b A ext hA
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMapName
    (num% (ls_off% "__rustc::__rust_alloc" - (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>")))
    (by fnoff_eq)
  have hmemcpy := kyberMap_stackedMemcpy_ok_at_ext (b := b) hMc
  have hpanic : (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMapName + BitVec.ofNat 64 (num% (ls_off% "alloc::alloc::handle_alloc_error" - (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>")))) =
      some Rust.panicked :=
    panic_at_handle_alloc_error_ext b ext
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMapName
      (num% (ls_off% "alloc::alloc::handle_alloc_error" - (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>")))
      (by fnoff_eq)
  dsimp only [sessionShimSpec] at hshim
  dsimp only [withStack, framelessMemcpySpec] at hmemcpy
  code_fetches CryptoVerification.libsignalSessionCode kyberMapBinCli b
    (Rust.withPanics ext) hfn (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>") 152
  wpp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, arg, ptr, kp⟩ := x
  dsimp only at *
  cases kp with
  | none =>
    simp only [kyberArgAt, optKyberAt_none_exists, memRegion_24_none, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun u0 => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done
  | some k =>
    simp only [kyberArgAt, optKyberAt, boxU8At, memRegion_24_some, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u0 => ?_
    refine SepWPp.pure_elim fun ⟨hptr_ne, hlen_lt32⟩ => ?_
    have hptr_beq : (ptr == 0#64) = false := beq_eq_false_iff_ne.mpr hptr_ne
    have hlen_lt63 : k.ciphertext.length < 2 ^ 63 := by omega
    by_cases hbs : k.ciphertext = []
    · simp only [hbs, List.length_nil, ite_true, sepConj_emp, emp_sepConj]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
    · have hpos : 0 < k.ciphertext.length := List.length_pos_iff.mpr hbs
      have hlen_ne0 : BitVec.ofNat 64 k.ciphertext.length ≠ 0#64 :=
        ofNat_ne_zero_of_pos hpos (by omega)
      have hlen_beq0 : (BitVec.ofNat 64 k.ciphertext.length == 0#64) = false :=
        beq_ofNat_zero_eq_false hpos (by omega)
      have hpow2 : ∃ m, 1 = 2 ^ m := ⟨0, rfl⟩
      have hbound : k.ciphertext.length + 1 ≤ 2 ^ 63 := by omega
      have hlay : LayoutOk k.ciphertext.length 1 := ⟨hpos, hpow2, hbound⟩
      simp only [hbs, ite_false]
      apply SepWPp.of_sepWP (mid := entry + 60#64)
      wp_steps
      wp_apply
      wp_steps
      wp_apply
      apply SepWP.done (by simp_all) (by simp_all)
      by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
      · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
        simp only [hoom, ite_true, sepConj_assoc]
        refine sepWPp_pure_mid fun htrace => ?_
        apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "alloc::alloc::handle_alloc_error" - (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>")) % 2^64))
        wp_steps
        apply SepWP.done (by simp_all) (by simp_all)
        refine SepWPp.panic (by simp_all) (by simp_all) fun hm => ?_
        simpa only [sepConj_assoc] using
          allowPanic_panicked (allocFailedIn_of_eq (by simp_all [Rust.panicked])) hm
      · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
        simp only [hoom, ite_false, sepConj_assoc]
        refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
        apply SepWPp.of_sepWP_ret
        wp_steps
        wp_apply
        wp_steps
        wp_done

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMap_ok_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocHooks A ext)
    (hSh : HookSat ext shimName CryptoVerification.SignalSession.CliExt.shimSpec)
    (hMc : HookSat ext memcpyName CryptoVerification.SignalSession.CliExt.memcpySpec)
    (_himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (img.base + bv% (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>"))
      (kyberMapSpec A) := by
  have h := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMap_fn_ok_ext
    (b := img.base) hA hSh hMc
  rwa [fnAddr_trExtProgAt (off := (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>")) (ls_lemma% fnOff "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>")] at h

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap
