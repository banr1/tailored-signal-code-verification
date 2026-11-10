/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
import all Init.Data.String.Defs
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegMidBase
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ProtocolAddressDisplay
import ProofLib.SepLogic.Entry
public meta import Lean -- shake: keep

/-!
# Handshake `DecryptPq` Middle-Segment Base Helpers

Fetch macro, callee/hook wrappers, and shared separation-logic helpers for Segments S4–S6 of
`try_decrypt_with_state::<signal_session_handshake::Coins>` on `tripleRatchetProgAt`.
-/

@[expose] public section

private meta def portCliPickCli (env : Lean.Environment) (opts : Lean.Options) (ns : Lean.Name)
    (od : List Lean.OpenDecl) (n : Lean.Name) : Lean.Name :=
  if (Lean.ResolveName.resolveGlobalName env opts ns od n).any (fun r => r.2.isEmpty) then n
  else match n with
    | .str q s => .str q (((s.replace "Cli_decode_" "_decode_").replace "Cli_rebase_fetch_" "_rebase_fetch_").replace "Cli_fetch_" "_fetch_")
    | _ => n

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegC

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.DecryptPq

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc

attribute [local wp_norm] BitVec.add_assoc

macro "decrypt_fetches_cli " b:term:max H:term:max hfn:ident k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode
    libsignalTripleRatchetBinCli $b $H
    $hfn (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") $k0 $len)

namespace BS8

@[irreducible] noncomputable def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : BitVec 64 :=
  (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt b C ctl abs := by
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt
  rfl

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnOff_tryDecrypt :
    CryptoVerification.libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") :=
  (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.hk_formatInner :
    CryptoVerification.libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        num% (ls_off% "alloc::fmt::format::format_inner" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) =
      CryptoVerification.libsignalSessionCode.fnOff formatInnerName := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnOff_tryDecrypt, fnOff_formatInner]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.hk_dealloc :
    CryptoVerification.libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) =
      CryptoVerification.libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnOff_tryDecrypt, (ls_stub% "__rustc::__rust_dealloc")]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fetch_tryDecrypt_at {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {entry : BitVec 64}
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt b C ctl abs = entry)
    {k off_k : Nat} {inst : Instr}
    (hadd : (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") + k = off_k)
    (htext : Nat.ble off_k (num% (ls_field% textEnd - 1)) = true)
    (h : CryptoVerification.libsignalSessionCode_tree.fetchDecodeAt off_k = some inst) :
    (tripleRatchetProgAt b C ctl abs).fetch (entry + BitVec.ofNat 64 k) = some inst := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq]
  subst hadd
  have hlt : (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") + k < num% (ls_field% textEnd) :=
    Nat.lt_succ_of_le (Nat.le_of_ble_eq_true htext)
  exact CryptoVerification.libsignalSessionCode_fetch_fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnOff_tryDecrypt hlt h (lt_two_pow_64_of_lt_text hlt)

open Lean Elab Tactic in
elab "decrypt_fetches_at_cli " hentry:ident k0:num len:num : tactic => do
  let portEnv ← Lean.getEnv
  let portOpts ← Lean.getOptions
  let portNs ← Lean.getCurrNamespace
  let portOd ← Lean.getOpenDecls
  let off := (num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))
  let k0 := k0.getNat
  let len := len.getNat
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let off_k := off + k
    let hex := String.ofList (Nat.toDigits 16 off_k)
    let dec := mkIdent (portCliPickCli portEnv portOpts portNs portOd ((`libsignalTripleRatchetBinCli).appendAfter s!"_decode_0x{hex}"))
    let kq := Syntax.mkNumLit (toString k)
    let offkq := Syntax.mkNumLit (toString off_k)
    evalTactic (← `(tactic|
      have := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fetch_tryDecrypt_at $hentry (k := $kq) (off_k := $offkq) rfl rfl $dec))

end BS8

namespace BS8

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.spqrRecv_ok_at_entry {Q : List (BitVec 8) → Prop} {A : RustAlloc} {S : SpqrModel}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {img : Obj.Image} {entry : BitVec 64}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hrecv : SpqrRecvOkQ Q C A ctl S abs img)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt img.base C ctl abs = entry) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      (entry + bv% ((2^64 + ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64))
      ((spqrRecvSpec A S img).restrictPre (Q ·.1.bytes)) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq, ← fnAddr_callee_of_fnOff CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnOff_tryDecrypt
    fnOff_spqrRecv (k := (num% ((2^64 + ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64))) rfl]
  have h := hrecv
  unfold SpqrRecvOkQ at h
  rwa [tripleRatchetProg_eq_tripleRatchetProgAt hloads,
    entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl) (abs := abs) hloads] at h

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.spqrRecv_ok_at_entryQF {Q : List (BitVec 8) → Prop} {Pstk : Nat → Prop} {F : SepProp}
    {A : RustAlloc} {S : SpqrModel} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {img : Obj.Image} {entry : BitVec 64}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hrecv : SpqrRecvOkQF Q Pstk F C A ctl S abs img)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt img.base C ctl abs = entry) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      (entry + bv% ((2^64 + ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64))
      (spqrRecvSpecQF Q Pstk F A S img) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq, ← fnAddr_callee_of_fnOff CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnOff_tryDecrypt
    fnOff_spqrRecv (k := (num% ((2^64 + ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64))) rfl]
  have h := hrecv
  unfold SpqrRecvOkQF at h
  rwa [tripleRatchetProg_eq_tripleRatchetProgAt hloads,
    entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl) (abs := abs) hloads] at h

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.formatInner_ok_at_entry {A : RustAlloc} {S : SpqrModel} {b : BitVec 64} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)} {entry : BitVec 64}
    (hS : TripleRatchetHooks C A S abs)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt b C ctl abs = entry) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      (entry + bv% ((2^64 + ls_off% "alloc::fmt::format::format_inner" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) % 2^64))
      (formatInnerSpec A) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq]
  exact formatInner_ok_at_tripleRatchet hS (name := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
    (k := num% (ls_off% "alloc::fmt::format::format_inner" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))) CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.hk_formatInner

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.dealloc_ok_at_entry {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {entry : BitVec 64}
    (halloc : AllocHooks A abs)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt b C ctl abs = entry) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) % 2^64)) (rustDeallocSpec A) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq]
  exact dealloc_ok_at_norm halloc (b := b) (C := C) (ctl := ctl)
    (name := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName) (k := num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))) CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.hk_dealloc

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.addrDisplay_ok_at_entry {A : RustAlloc} {S : SpqrModel} {b : BitVec 64} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)} {entry : BitVec 64}
    (hS : TripleRatchetHooks C A S abs)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt b C ctl abs = entry) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      (entry + bv% ((2^64 + ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64)) (addrDisplaySpec A) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq, ← fnAddr_callee_of_fnOff CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnOff_tryDecrypt
    fnOff_addrDisplay (k := (num% ((2^64 + ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64))) rfl]
  exact addrDisplay_ok b C A ctl abs hS.fmtWrite

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.entry_eq_base {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {entry : BitVec 64}
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt b C ctl abs = entry) :
    entry = b + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq, Program.fnAddr_rebase, CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnOff_tryDecrypt]

end BS8

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.onPanic_drop_frame {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {F R : SepProp} {s0 s' : State}
    (h : s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ (F ∗ R)) :
    s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R := by
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  rcases h with ⟨hcond, hmem⟩
  rw [← sepConj_assoc] at hmem
  exact ⟨hcond, Satisfies.mono (sepConj_mono_left (ProofLib.entails_anyHeap _)) hmem⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.onPanic_of_spqrRecv {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {st msg : VecArg} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (htrace : sm.trace = s0.trace)
    (hst : st.bytes = x.st.pqRatchetState)
    (hmsg : msg.bytes = x.msg.pqRatchet)
    (h : sf.mem ⊨ ((spqrRecvSpec A S img).onPanic (st, msg, ret) sm sf ∗ F) ∗ R) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  dsimp only [spqrRecvSpec, CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage] at h ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h
  rcases h with ⟨⟨hpan, hpref⟩, hmem⟩
  rw [← sepConj_assoc] at hmem
  rw [hst, hmsg, allocFailedIn, htrace, ← allocFailedIn] at hpan
  rw [htrace] at hpref
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨?_, hpref⟩, ?_⟩
  · rcases hpan with ha | hp
    · exact Or.inr (Or.inr ha)
    · exact Or.inr (Or.inl hp)
  · exact Satisfies.mono (sepConj_mono_left (ProofLib.entails_anyHeap _)) hmem

set_option maxRecDepth 2000000 in
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.rodata_0x45416_eq :
    (libsignalSessionImage.data.drop
      (num% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2452) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2456)) - num% (ls_xref% 0x2440 0x2444))).take 7 =
        utf8 "decrypt" := by
  rfl_kernel

set_option maxRecDepth 2000000 in
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.rodata_decrypt_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2452) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2456))) ↦ᵣ utf8 "decrypt") ∗ P := by
  have hdlen : num% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2452) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2456)) - num% (ls_xref% 0x2440 0x2444) + 7 ≤
      libsignalSessionImage.data.length := by
    have h1 := congrArg List.length CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.rodata_0x45416_eq
    rw [List.length_take, List.length_drop, BS8.utf8_decrypt_len] at h1
    omega
  have h := ProofLib.Satisfies.of_rodata_loads himg
    (secOff := num% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2452) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2456))) (secLen := 7)
    (dataOff := num% (ls_xref% 0x2440 0x2444))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    hdlen (by rfl_kernel) hro hP
  rwa [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.rodata_0x45416_eq] at h

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.onPanic_of_formatInner {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (htrace : sm.trace = s0.trace)
    (h : sf.mem ⊨ ((formatInnerSpec A).onPanic ret sm sf ∗ F) ∗ R) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  dsimp only [formatInnerSpec, CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage] at h ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h
  rcases h with ⟨⟨hpan, hpref⟩, hmem⟩
  rw [← sepConj_assoc] at hmem
  rw [allocFailedIn, htrace, ← allocFailedIn] at hpan
  rw [htrace] at hpref
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨Or.inr (Or.inr hpan), hpref⟩, ?_⟩
  exact Satisfies.mono (sepConj_mono_left (ProofLib.entails_anyHeap _)) hmem

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.adrp_decryptStr {b entry : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64) (he : entry = b + bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) :
    (((entry + 2452#64) &&& 18446744073709547520#64) +
      bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2452) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2456)) - page% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2452))) +
      bv% ((ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2452) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2456)) % 4096) =
      b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2452) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2456)) := by
  rw [he, BitVec.add_assoc b, ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc b,
      BitVec.add_assoc b]
  rfl

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegC
