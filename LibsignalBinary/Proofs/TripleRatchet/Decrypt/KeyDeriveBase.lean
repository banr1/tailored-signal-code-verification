/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
import all Init.Data.String.Defs
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Calls
import ProofLib.SepLogic.WPp

/-!
# Shared Instruction Fetch, Callee, and `SepWPp` Helpers for `KeyDerive`

Shared instruction-fetch macros, extern/in-image callee resolution (`format_inner`, `__rust_dealloc`,
`<ProtocolAddress as Display>::fmt`, `spqr::recv`), and fixed-image / relocatable `SepWPp` stepping
combinators for segments `S4`–`S6` (`ConsumeMsgKey`, `PqRecv`, `DeriveKeys`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc
attribute [local wp_norm] BitVec.add_assoc

open Lean Elab Tactic in
elab "code_fetches_from " codeId:ident decPrefix:ident b:term:max H:term:max hfn:term:max
    off:term:max k0:num len:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat off "fetches"
  let k0 := k0.getNat
  let len := len.getNat
  let codeBase := codeId.getId.eraseMacroScopes
  let decBase := decPrefix.getId.eraseMacroScopes
  let fetchEntry := mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := mkIdent (decBase.appendAfter s!"_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

abbrev H2 (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : String → Option (State → State) :=
  Rust.withPanics (tripleRatchetExterns C ctl abs)

macro "decrypt_fetches " b:term:max H:term:max hfn:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_from CryptoVerification.libsignalSessionCode libsignalTripleRatchetBin $b $H
    $hfn (num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) $k0 $len)

namespace KeyDeriveCallees

@[irreducible] noncomputable def fnAddr_tryDecrypt_ext (b : BitVec 64)
    (ext : String → Option (State → State)) : BitVec 64 :=
  (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName

theorem fnAddr_tryDecrypt_ext_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName = fnAddr_tryDecrypt_ext b ext := by
  unfold fnAddr_tryDecrypt_ext
  rfl

@[irreducible] noncomputable def fnAddr_tryDecrypt (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : BitVec 64 :=
  (tripleRatchetProgAt b C ctl abs).fnAddr tryDecryptName

theorem fnAddr_tryDecrypt_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr tryDecryptName = fnAddr_tryDecrypt b C ctl abs := by
  unfold fnAddr_tryDecrypt
  rfl

theorem fnOff_tryDecrypt :
    CryptoVerification.libsignalSessionCode.fnOff tryDecryptName = num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") :=
  (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")

theorem fnOff_spqrRecv :
    CryptoVerification.libsignalSessionCode.fnOff spqrRecvName = num% (ls_off% "spqr::recv") :=
  (ls_lemma% fnOff "spqr::recv")

theorem fnOff_formatInner :
    CryptoVerification.libsignalSessionCode.fnOff formatInnerName = num% (ls_off% "alloc::fmt::format::format_inner") :=
  (ls_stub% "alloc::fmt::format::format_inner")

theorem fnOff_addrDisplay :
    CryptoVerification.libsignalSessionCode.fnOff addrDisplayName = num% (ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt") :=
  (ls_lemma% fnOff "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt")

theorem hk_spqrRecv :
    CryptoVerification.libsignalSessionCode.fnOff tryDecryptName + num% (ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") =
      CryptoVerification.libsignalSessionCode.fnOff spqrRecvName := by
  rw [fnOff_tryDecrypt, fnOff_spqrRecv]

theorem hk_formatInner :
    CryptoVerification.libsignalSessionCode.fnOff tryDecryptName + num% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") =
      CryptoVerification.libsignalSessionCode.fnOff formatInnerName := by
  rw [fnOff_tryDecrypt, fnOff_formatInner]

theorem hk_dealloc :
    CryptoVerification.libsignalSessionCode.fnOff tryDecryptName + num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") =
      CryptoVerification.libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by
  rw [fnOff_tryDecrypt, (ls_stub% "__rustc::__rust_dealloc")]

theorem hk_addrDisplay :
    CryptoVerification.libsignalSessionCode.fnOff tryDecryptName + num% (ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") =
      CryptoVerification.libsignalSessionCode.fnOff addrDisplayName := by
  rw [fnOff_tryDecrypt, fnOff_addrDisplay]

theorem lt_two_pow_64_of_lt_text {n : Nat} (h : n < num% (ls_field% textEnd)) : n < 2 ^ 64 :=
  Nat.lt_trans h (by decide)

theorem fetch_tryDecrypt_at_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {entry : BitVec 64}
    (hentry : fnAddr_tryDecrypt_ext b ext = entry)
    {k off_k : Nat} {inst : Instr}
    (hadd : 214564 + k = off_k)
    (htext : Nat.ble off_k (num% (ls_field% textEnd - 1)) = true)
    (h : CryptoVerification.libsignalSessionCode_tree.fetchDecodeAt off_k = some inst) :
    (tripleRatchetProgAtExt b ext).fetch (entry + BitVec.ofNat 64 k) = some inst := by
  rw [← hentry, ← fnAddr_tryDecrypt_ext_eq]
  subst hadd
  have hlt : 214564 + k < num% (ls_field% textEnd) := Nat.lt_succ_of_le (Nat.le_of_ble_eq_true htext)
  exact CryptoVerification.libsignalSessionCode_fetch_fnAddr
    fnOff_tryDecrypt hlt h (lt_two_pow_64_of_lt_text hlt)

theorem fetch_tryDecrypt_at {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {entry : BitVec 64}
    (hentry : fnAddr_tryDecrypt b C ctl abs = entry)
    {k off_k : Nat} {inst : Instr}
    (hadd : 214564 + k = off_k)
    (htext : Nat.ble off_k (num% (ls_field% textEnd - 1)) = true)
    (h : CryptoVerification.libsignalSessionCode_tree.fetchDecodeAt off_k = some inst) :
    (tripleRatchetProgAt b C ctl abs).fetch (entry + BitVec.ofNat 64 k) = some inst := by
  rw [← hentry, ← fnAddr_tryDecrypt_eq]
  subst hadd
  have hlt : 214564 + k < num% (ls_field% textEnd) := Nat.lt_succ_of_le (Nat.le_of_ble_eq_true htext)
  exact CryptoVerification.libsignalSessionCode_fetch_fnAddr
    fnOff_tryDecrypt hlt h (lt_two_pow_64_of_lt_text hlt)

open Lean Elab Tactic in
elab "decrypt_fetches_at_ext " hentry:ident k0:num len:num : tactic => do
  let off := num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  let k0 := k0.getNat
  let len := len.getNat
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let off_k := off + k
    let dec := mkIdent ((`libsignalTripleRatchetBin).appendAfter s!"_decode_0x{String.ofList (Nat.toDigits 16 off_k)}")
    let kq := Syntax.mkNumLit (toString k)
    let offkq := Syntax.mkNumLit (toString off_k)
    evalTactic (← `(tactic|
      have := KeyDeriveCallees.fetch_tryDecrypt_at_ext $hentry (k := $kq) (off_k := $offkq) rfl rfl $dec))

open Lean Elab Tactic in
elab "decrypt_fetches_at " hentry:ident k0:num len:num : tactic => do
  let off := num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  let k0 := k0.getNat
  let len := len.getNat
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let off_k := off + k
    let dec := mkIdent ((`libsignalTripleRatchetBin).appendAfter s!"_decode_0x{String.ofList (Nat.toDigits 16 off_k)}")
    let kq := Syntax.mkNumLit (toString k)
    let offkq := Syntax.mkNumLit (toString off_k)
    evalTactic (← `(tactic|
      have := KeyDeriveCallees.fetch_tryDecrypt_at $hentry (k := $kq) (off_k := $offkq) rfl rfl $dec))

end KeyDeriveCallees

theorem pointsTo64_split32 (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) = (a ↦₃₂ v.truncate 32) ∗ ((a + 4#64) ↦₃₂ v.extractLsb' 32 32) :=
  ProofLib.pointsTo64_split32' a v

theorem pointsTo32_merge64 (a : BitVec 64) (lo hi : BitVec 32) :
    ((a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi)) = (a ↦₆₄ (hi ++ lo)) := by
  rw [pointsTo64_split32]
  have h1 : (hi ++ lo).truncate 32 = lo := by bv_kernel
  have h2 : (hi ++ lo).extractLsb' 32 32 = hi := by bv_kernel
  rw [h1, h2]

theorem pts64_to_mr (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) ⊢ memRegion a 8 := by
  rw [memRegion_eight]
  exact Entails.sepExists_intro v

macro "fold_mr8 " addr:term : tactic =>
  `(tactic| refine SepWP.focus_weaken (pts64_to_mr $addr _) (by sep_focus) ?_)

@[local simp, local wp_norm, local arm64_norm]
theorem extractLsb0_8_append56 (hi : BitVec 56) (d : BitVec 8) :
    (hi ++ d).extractLsb' 0 8 = d := by bv_kernel

theorem pointsTo8_memRegion7_to_64 (a : BitVec 64) (d : BitVec 8) :
    ((a ↦₈ d) ∗ memRegion (a + 1#64) 7) ⊢ ∃∗ hi : BitVec 56, a ↦₆₄ (hi ++ d) := by
  rw [memRegion_eq_exists_bytes (a + 1#64) 7 (by decide), sepExists_sepConj_right]
  refine Entails.sepExists_elim fun bs => ?_
  rw [sepConj_pure_left_comm]
  refine Entails.pure_left fun hbs => ?_
  rcases bs with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩ <;> simp at hbs
  rw [← pointsToBytes_cons]
  refine Entails.trans (Entails.of_eq ?_) (Entails.sepExists_intro (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1))
  rw [pointsTo64_eq_pointsToBytes]
  congr 1
  simp only [unpack64, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_kernel

theorem pointsTo64_to_8_memRegion7 (a : BitVec 64) (hi : BitVec 56) (d : BitVec 8) :
    (a ↦₆₄ (hi ++ d)) ⊢ (a ↦₈ d) ∗ memRegion (a + 1#64) 7 := by
  simpa only [extractLsb0_8_append56] using ProofLib.cell_entails_lowByte_pad a (hi ++ d)

theorem mr_cut_add (a : BitVec 64) (c n k : Nat) (h : n + k ≤ 2 ^ 64) :
    memRegion (a + BitVec.ofNat 64 c) (n + k) =
      memRegion (a + BitVec.ofNat 64 c) n ∗ memRegion (a + BitVec.ofNat 64 (c + n)) k := by
  refine memRegion_split' rfl ?_ h
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem stackAt_sub (sp : BitVec 64) (N K : Nat) (hK : K ≤ N := by decide)
    (hN : N < 2 ^ 64 := by decide) :
    stackAt sp N = memRegion (sp - BitVec.ofNat 64 N) (N - K) ∗ stackAt sp K := by
  simp only [stackAt]
  refine memRegion_split' (by omega) ?_ (by omega)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have h1 : N % 2 ^ 64 = N := Nat.mod_eq_of_lt hN
  have h2 : (N - K) % 2 ^ 64 = N - K := Nat.mod_eq_of_lt (by omega)
  have h3 : K % 2 ^ 64 = K := Nat.mod_eq_of_lt (by omega)
  omega

def optKeyRest (A : RustAlloc) (w0 w1 w2 : BitVec 64) (x : Salt) : SepProp :=
  match x with
  | none =>
    ∃∗ isNiche : Bool,
      if isNiche then ⌜w0 = noneCap⌝
      else
        ⌜w0.toNat < 2 ^ 63 ∧ w1 ≠ 0#64 ∧ w2 = 0#64⌝ ∗
        (if w0 = 0#64 then emp else A.live w1 w0.toNat 1 ∗ memRegion w1 w0.toNat)
  | some k =>
    ⌜k.toList.length ≤ w0.toNat ∧ w0.toNat < 2 ^ 63 ∧ w1 ≠ 0#64 ∧
      w2 = BitVec.ofNat 64 k.toList.length⌝ ∗
    (if w0 = 0#64 then emp
     else A.live w1 w0.toNat 1 ∗ (w1 ↦ₛ k.toList) ∗
       memRegion (w1 + BitVec.ofNat 64 k.toList.length) (w0.toNat - k.toList.length))

theorem optKeyAt_split (A : RustAlloc) (a : BitVec 64) (x : Salt) :
    spqrRecvKeyAt A a x ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        optKeyRest A w0 w1 w2 x ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) := by
  cases x with
  | none =>
    simp only [spqrRecvKeyAt, optKeyRest]
    refine Entails.sepExists_elim fun isNiche => ?_
    cases isNiche
    · simp only [Bool.false_eq_true, ↓reduceIte, vecU8, vecU8At, vecHeader,
        List.length_nil, Nat.sub_zero, BitVec.ofNat_eq_ofNat, pointsToBytes_nil,
        emp_sepConj, BitVec.add_zero, sepConj_assoc, sepConj_pure_left_comm]
      refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
      refine Entails.pure_left fun ⟨_, hs, hp⟩ => ?_
      refine Entails.trans ?_ (Entails.sepExists_intro cap)
      refine Entails.trans ?_ (Entails.sepExists_intro ptr)
      refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
      rw [sepExists_sepConj_left]
      refine Entails.trans ?_ (Entails.sepExists_intro false)
      simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      refine Entails.pure_right ⟨hs, hp, trivial⟩ ?_
      rw [← sepConj_assoc, ← sepConj_assoc, sepConj_comm]
      simp only [sepConj_assoc]
      exact Entails.refl _
    · simp only [↓reduceIte]
      rw [memRegion_split (a + 8#64) 8 8 (by decide),
        BitVec.add_assoc, show (8#64 : BitVec 64) + 8#64 = 16#64 by rfl,
        memRegion_eight (a + 8#64), memRegion_eight (a + 16#64)]
      rw [sepExists_sepConj_left, sepExists_sepConj_right]
      refine Entails.sepExists_elim fun w1 => ?_
      rw [sepExists_sepConj_right, sepExists_sepConj_right]
      refine Entails.sepExists_elim fun w2 => ?_
      refine Entails.trans ?_ (Entails.sepExists_intro noneCap)
      refine Entails.trans ?_ (Entails.sepExists_intro w1)
      refine Entails.trans ?_ (Entails.sepExists_intro w2)
      rw [sepExists_sepConj_left]
      refine Entails.trans ?_ (Entails.sepExists_intro true)
      simp only [↓reduceIte]
      refine Entails.pure_right trivial ?_
      exact Entails.refl _
  | some k =>
    simp only [spqrRecvKeyAt, optKeyRest, vecU8, vecU8At, vecHeader]
    refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Entails.pure_left fun h => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro cap)
    refine Entails.trans ?_ (Entails.sepExists_intro ptr)
    refine Entails.trans ?_ (Entails.sepExists_intro (BitVec.ofNat 64 k.toList.length))
    refine Entails.pure_right ⟨h.1, h.2.1, h.2.2, rfl⟩ ?_
    rw [← sepConj_assoc, ← sepConj_assoc, sepConj_comm]
    simp only [sepConj_assoc]
    exact Entails.refl _

theorem optKeyAt_fold (A : RustAlloc) (a w0 w1 w2 : BitVec 64) (x : Salt) :
    optKeyRest A w0 w1 w2 x ∗
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢
    spqrRecvKeyAt A a x := by
  cases x with
  | none =>
    simp only [spqrRecvKeyAt, optKeyRest, sepExists_sepConj_left]
    refine Entails.sepExists_elim fun isNiche => ?_
    cases isNiche
    · simp only [Bool.false_eq_true, ↓reduceIte, vecU8, vecU8At, vecHeader,
        List.length_nil, Nat.sub_zero, BitVec.ofNat_eq_ofNat, pointsToBytes_nil,
        emp_sepConj, BitVec.add_zero, sepConj_assoc]
      refine Entails.pure_left fun ⟨hs, hp, hw2⟩ => ?_
      subst hw2
      refine Entails.trans ?_ (Entails.sepExists_intro false)
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine Entails.trans ?_ (Entails.sepExists_intro w0)
      refine Entails.trans ?_ (Entails.sepExists_intro w1)
      simp only [sepConj_pure_left_comm]
      refine Entails.pure_right ⟨Nat.zero_le _, hs, hp⟩ ?_
      rw [sepConj_comm]
      simp only [sepConj_assoc]
      exact Entails.refl _
    · simp only [↓reduceIte]
      refine Entails.pure_left fun hw0 => ?_
      subst hw0
      refine Entails.trans ?_ (Entails.sepExists_intro true)
      simp only [↓reduceIte]
      rw [memRegion_split (a + 8#64) 8 8 (by decide),
        BitVec.add_assoc, show (8#64 : BitVec 64) + 8#64 = 16#64 by rfl,
        memRegion_eight (a + 8#64), memRegion_eight (a + 16#64)]
      rw [sepExists_sepConj_left, sepExists_sepConj_right]
      refine Entails.trans ?_ (Entails.sepExists_intro w1)
      rw [sepExists_sepConj_right, sepExists_sepConj_right]
      refine Entails.trans ?_ (Entails.sepExists_intro w2)
      exact Entails.refl _
  | some k =>
    simp only [spqrRecvKeyAt, optKeyRest, vecU8, vecU8At, vecHeader, sepConj_assoc]
    refine Entails.pure_left fun ⟨h1, h2, h3, hw2⟩ => ?_
    subst hw2
    refine Entails.trans ?_ (Entails.sepExists_intro w0)
    refine Entails.trans ?_ (Entails.sepExists_intro w1)
    simp only [sepConj_pure_left_comm]
    refine Entails.pure_right ⟨h1, h2, h3⟩ ?_
    rw [sepConj_comm]
    simp only [sepConj_assoc]
    exact Entails.refl _

theorem mkgAt_fold (A : RustAlloc) (r seedCap seedPtr : BitVec 64) (pad1 pad2 : BitVec 32)
    (mkg : MessageKeyGenerator)
    (hseed : mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0) :
    (r ↦₃₂ 1#32) ∗ ((r + 4#64) ↦₃₂ pad1) ∗
    ((r + 8#64) ↦₆₄ seedCap) ∗ ((r + 16#64) ↦₆₄ seedPtr) ∗
    ((r + 24#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
    (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
      (seedPtr ↦ₛ mkg.seed) ∗
      memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
    ((r + 32#64) ↦₆₄ (pad2 ++ mkg.counter)) ⊢
    mkgAt A r mkg := by
  unfold mkgAt vecU8 vecU8At vecHeader
  rw [← pointsTo32_merge64 (r + 32#64) mkg.counter pad2,
    BitVec.add_assoc, show (32#64 : BitVec 64) + 4#64 = 36#64 by rfl]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.trans ?_ (Entails.sepExists_intro seedCap)
  refine Entails.trans ?_ (Entails.sepExists_intro seedPtr)
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  refine Entails.pure_right hseed ?_
  refine sepConj_mono (Entails.refl _) (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
        (sepConj_mono (Entails.refl _) (pointsTo32_entails_memRegion _ _)))))))

theorem reaches_pc_of_sepWP {prog : Program} {target_pc : BitVec 64} {s : State}
    {P R : SepProp} {Q : State → Prop}
    (hmem : s.mem ⊨ P ∗ R)
    (hwp : SepWP prog target_pc s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → Q sf)) :
    reaches_pc prog target_pc s Q := by
  intro hL
  rcases hwp.elim hmem hL with ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq⟩ | ⟨_, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, hq hmf⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem reaches_pc_of_sepWP_frozen {prog : Program} {img : Obj.Image}
    {mid target : BitVec 64} {s : State} {P P_mid R : SepProp}
    {RegMid Q : State → Prop}
    (hmem : s.mem ⊨ P ∗ R)
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h1 : SepWP prog mid s P (fun sm Pm => (sm.mem ⊨ Pm ∗ R) → RegMid sm ∧ (sm.mem ⊨ P_mid ∗ R)))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      img.FrozenLoaded sm → sm.symtab = img.symtab →
      RegMid sm → SepWP prog target sm P_mid (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → Q sf)) :
    reaches_pc prog target s Q := by
  intro hL
  rcases h1.elim hmem hL with ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, himp⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨hReg, hmm'⟩ := himp hmm
    rcases (h2 sm hpc hrun (hsteps.frozenLoaded hfrozen) (hsteps.symtab_eq.trans hsym) hReg).elim
        hmm' (hsteps.codeLoaded hL) with ⟨sf, hsteps', ⟨hpcf, hrunf, P_f, hmf, hq⟩ | ⟨_, hoom⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpcf, hrunf, hq hmf⟩⟩
    · exact (not_satisfies_false_sepConj hoom).elim
  · exact (not_satisfies_false_sepConj hoom).elim

def tryDecryptMidMetaCore (s0 s : State) : Prop :=
  s.status = .Running ∧
  s.sp = s0.sp - 1504#64 ∧
  s0.spAligned = true ∧
  s.spAligned = true ∧
  s.readReg64 .x29 = s0.sp - 96#64 ∧
  s.trace = s0.trace ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem tryDecryptMidMeta_of_core {img : Obj.Image} {s0 s : State}
    (hf : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : tryDecryptMidMetaCore s0 s) : tryDecryptMidMeta img s0 s := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  exact ⟨h1, h2, h3, h4, h5, h6, hf, hsym, h7⟩

theorem reaches_pc_midMeta {prog : Program} {img : Obj.Image} {target : BitVec 64}
    {s0 s : State} {Rest : State → Prop}
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : reaches_pc prog target s (fun sf => sf.pc = target ∧ tryDecryptMidMetaCore s0 sf ∧ Rest sf)) :
    reaches_pc prog target s (fun sf => sf.pc = target ∧ tryDecryptMidMeta img s0 sf ∧ Rest sf) := by
  intro hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, hpc', hcore, hrest⟩ | hoom⟩ := h hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, hpc',
      tryDecryptMidMeta_of_core (hsteps.frozenLoaded hfrozen) (hsteps.symtab_eq.trans hsym) hcore,
      hrest⟩⟩
  · exact ⟨sf, hsteps, Or.inr hoom⟩

theorem steps_of_sepWP {prog : Program} {img : Obj.Image}
    {mid : BitVec 64} {s : State} {P P_mid R : SepProp}
    {RegMid Out : State → Prop}
    (hmem : s.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s.mem)
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h1 : SepWP prog mid s P (fun sm Pm => (sm.mem ⊨ Pm ∗ R) → RegMid sm ∧ (sm.mem ⊨ P_mid ∗ R)))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      img.FrozenLoaded sm → sm.symtab = img.symtab →
      prog.CodeLoaded sm.mem → RegMid sm → (sm.mem ⊨ P_mid ∗ R) →
      ∃ s', Steps prog sm s' ∧ Out s') :
    ∃ s', Steps prog s s' ∧ Out s' := by
  rcases h1.elim hmem hL with ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, himp⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨hReg, hmm'⟩ := himp hmm
    obtain ⟨s', hsteps', hout⟩ :=
      h2 sm hpc hrun (hsteps.frozenLoaded hfrozen) (hsteps.symtab_eq.trans hsym)
        (hsteps.codeLoaded hL) hReg hmm'
    exact ⟨s', hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem steps_done_of_sepWP_frozen {prog : Program} {img : Obj.Image}
    {target : BitVec 64} {s : State} {P R : SepProp}
    {QCore NormalOut PanicOut : State → Prop}
    (hmem : s.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s.mem)
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (himp : ∀ sf, img.FrozenLoaded sf → sf.symtab = img.symtab → QCore sf → NormalOut sf)
    (hwp : SepWP prog target s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → QCore sf)) :
    ∃ s', Steps prog s s' ∧ (NormalOut s' ∨ PanicOut s') := by
  rcases hwp.elim hmem hL with ⟨sf, hsteps, ⟨_, _, P_f, hmf, hq⟩ | ⟨_, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl (himp sf (hsteps.frozenLoaded hfrozen) (hsteps.symtab_eq.trans hsym) (hq hmf))⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem steps_done_of_sepWP_midMeta {prog : Program} {img : Obj.Image}
    {target : BitVec 64} {s0 s : State} {P R : SepProp}
    {Rest PanicOut : State → Prop}
    (hmem : s.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s.mem)
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hwp : SepWP prog target s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
      sf.pc = target ∧ tryDecryptMidMetaCore s0 sf ∧ Rest sf)) :
    ∃ s', Steps prog s s' ∧
      ((s'.pc = target ∧ tryDecryptMidMeta img s0 s' ∧ Rest s') ∨ PanicOut s') := by
  refine steps_done_of_sepWP_frozen hmem hL hfrozen hsym ?_ hwp
  intro sf hff hsymf ⟨hpc', hcore, hrest⟩
  exact ⟨hpc', tryDecryptMidMeta_of_core hff hsymf hcore, hrest⟩

theorem steps_call {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc : BitVec 64} {spec : Spec α} (x : α)
    {sm : State} {F R : SepProp} {NormalOut PanicOut : State → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : sm.pc = entry) (hrun : sm.status = .Running) (hsp : sm.spAligned = true)
    (hlr : sm.readReg64 .lr = ret_pc)
    (hfrozen : img.FrozenLoaded sm) (hsym : sm.symtab = img.symtab)
    (hL : prog.CodeLoaded sm.mem)
    (hpre : sm.mem ⊨ spec.pre x sm ∗ (F ∗ R))
    (hpanic : ∀ sf, sf.status = .Panicked → (sf.mem ⊨ (spec.onPanic x sm sf ∗ F) ∗ R) → PanicOut sf)
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sm.sp → sf.spAligned = true → CalleeSavedPreserved sm sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab → prog.CodeLoaded sf.mem →
      (sf.mem ⊨ (spec.post x sm sf ∗ F) ∗ R) →
      ∃ s', Steps prog sf s' ∧ (NormalOut s' ∨ PanicOut s'))
    (hexit : ∀ sf code R', (sf.mem ⊨ spec.onExit x code sm sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h)
    (hoom : ∀ sf R', (sf.mem ⊨ spec.onOom x sm sf ∗ R') → False := by
      intro _ _ h; exact not_satisfies_false_sepConj h) :
    ∃ s', Steps prog sm s' ∧ (NormalOut s' ∨ PanicOut s') := by
  obtain ⟨sf, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) sm hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcf, _, hrunf⟩, ⟨hspf, hcsf⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcf
    have hsp_alf : sf.spAligned = true := by
      unfold State.spAligned at hsp ⊢; rw [hspf]; exact hsp
    obtain ⟨s', hsteps', hout'⟩ :=
      hnext sf hpcf hrunf hspf hsp_alf hcsf
        (hsteps.frozenLoaded hfrozen) (hsteps.symtab_eq.trans hsym) (hsteps.codeLoaded hL) hpost
    exact ⟨s', hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sf, hsteps, Or.inr (hpanic sf hpan hpost)⟩
  · exact (hexit sf code (F ∗ R) hpost).elim
  · exact (hoom sf (F ∗ R) hpost).elim

theorem spqrRecv_ok_at_tripleRatchet {Q : List (BitVec 8) → Prop} {A : RustAlloc} {S : SpqrModel} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)} {img : Obj.Image}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hrecv : SpqrRecvOkQ Q C A ctl S abs img) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff spqrRecvName := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      ((spqrRecvSpec A S img).restrictPre (Q ·.1.bytes)) := by
  have h : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) ((tripleRatchetProgAt img.base C ctl abs).fnAddr spqrRecvName)
      ((spqrRecvSpec A S img).restrictPre (Q ·.1.bytes)) := by
    have h := hrecv
    unfold SpqrRecvOkQ at h
    rwa [tripleRatchetProg_eq_tripleRatchetProgAt hloads, entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl) (abs := abs) hloads] at h
  rwa [← Program.fnAddr_rel rfl rfl hk]

theorem formatInner_ok_at_tripleRatchet {A : RustAlloc} {S : SpqrModel} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hS : TripleRatchetHooks C A S abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff formatInnerName := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (formatInnerSpec A) := by
  have habs := tripleRatchetExterns_abs C ctl abs
  have h3 : Rust.withPanics (tripleRatchetExterns C ctl abs) formatInnerName =
      abs formatInnerName := Option.some.inj (congrArg (·[2]?) habs)
  exact hook_ok_at_raw (hname := formatInnerName) rfl hk
    (by fnoff_eq)
    (by fnoff_eq)
    (by simpa [HookSat, h3] using hS.formatInner)

theorem addrDisplay_ok_at_tripleRatchet {A : RustAlloc} {S : SpqrModel} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hS : TripleRatchetHooks C A S abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff addrDisplayName := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (addrDisplaySpec A) :=
  addr_display_ok_at b C A ctl abs hS.fmtWrite name k hk

namespace KeyDeriveCallees

/-- `spqr::recv` is in-image code and `Stage2Contracts` does not carry it: the
`Q`-restricted recv contract `hrecv` on `tripleRatchetProgAtExt img.base ext` is taken explicitly. -/
theorem spqrRecv_ok_at_entry_ext {Q : List (BitVec 8) → Prop} {A : RustAlloc} {S : SpqrModel}
    {img : Obj.Image} {ext : String → Option (State → State)} {entry : BitVec 64}
    (hrecv : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName)
      ((spqrRecvSpec A S img).restrictPre (Q ·.1.bytes)))
    (hentry : fnAddr_tryDecrypt_ext img.base ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% (ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
      ((spqrRecvSpec A S img).restrictPre (Q ·.1.bytes)) := by
  rw [← hentry, ← fnAddr_tryDecrypt_ext_eq]
  exact sub_ok_at_of_fnAddr hrecv tryDecryptName (num% (ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) hk_spqrRecv

theorem spqrRecv_ok_at_entry_extQF {Q : List (BitVec 8) → Prop} {Pstk : Nat → Prop} {F : SepProp}
    {A : RustAlloc} {S : SpqrModel} {img : Obj.Image}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (hrecv : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName)
      (spqrRecvSpecQF Q Pstk F A S img))
    (hentry : fnAddr_tryDecrypt_ext img.base ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (entry + bv% (ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
      (spqrRecvSpecQF Q Pstk F A S img) := by
  rw [← hentry, ← fnAddr_tryDecrypt_ext_eq]
  exact sub_ok_at_of_fnAddr hrecv tryDecryptName
    (num% (ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
    hk_spqrRecv

theorem spqrRecv_ok_at_entry {Q : List (BitVec 8) → Prop} {A : RustAlloc} {S : SpqrModel}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {img : Obj.Image} {entry : BitVec 64}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hrecv : SpqrRecvOkQ Q C A ctl S abs img)
    (hentry : fnAddr_tryDecrypt img.base C ctl abs = entry) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (entry + bv% (ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
      ((spqrRecvSpec A S img).restrictPre (Q ·.1.bytes)) := by
  rw [← hentry, ← fnAddr_tryDecrypt_eq]
  exact spqrRecv_ok_at_tripleRatchet hloads hrecv (name := tryDecryptName) (k := num% (ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) hk_spqrRecv

theorem formatInner_ok_at_entry_ext {A : RustAlloc} {S : SpqrModel} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (hC : Stage2Contracts b C A ctl uuidTryParse S ext)
    (hentry : fnAddr_tryDecrypt_ext b ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) (formatInnerSpec A) := by
  rw [← hentry, ← fnAddr_tryDecrypt_ext_eq]
  exact hC.format_inner_ok_at tryDecryptName (num% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) hk_formatInner

theorem formatInner_ok_at_entry {A : RustAlloc} {S : SpqrModel} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {entry : BitVec 64}
    (hS : TripleRatchetHooks C A S abs)
    (hentry : fnAddr_tryDecrypt b C ctl abs = entry) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) (entry + bv% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) (formatInnerSpec A) := by
  rw [← hentry, ← fnAddr_tryDecrypt_eq]
  exact formatInner_ok_at_tripleRatchet hS (name := tryDecryptName) (k := num% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) hk_formatInner

theorem dealloc_ok_at_entry_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (halloc : AllocContracts b A ext)
    (hentry : fnAddr_tryDecrypt_ext b ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) (rustDeallocSpec A) := by
  rw [← hentry, ← fnAddr_tryDecrypt_ext_eq]
  exact halloc.dealloc_ok_at tryDecryptName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) hk_dealloc

theorem dealloc_ok_at_entry {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {entry : BitVec 64}
    (halloc : AllocHooks A abs)
    (hentry : fnAddr_tryDecrypt b C ctl abs = entry) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) (entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) (rustDeallocSpec A) := by
  rw [← hentry, ← fnAddr_tryDecrypt_eq]
  exact dealloc_ok_at_norm halloc (b := b) (C := C) (ctl := ctl)
    (name := tryDecryptName) (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) hk_dealloc

theorem addrDisplay_ok_at_entry_ext {A : RustAlloc} {S : SpqrModel} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (hC : Stage2Contracts b C A ctl uuidTryParse S ext)
    (hentry : fnAddr_tryDecrypt_ext b ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% (ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) (addrDisplaySpec A) := by
  rw [← hentry, ← fnAddr_tryDecrypt_ext_eq]
  exact addr_display_ok_at_ext b C A ctl S ext hC tryDecryptName (num% (ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) hk_addrDisplay

theorem addrDisplay_ok_at_entry {A : RustAlloc} {S : SpqrModel} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {entry : BitVec 64}
    (hS : TripleRatchetHooks C A S abs)
    (hentry : fnAddr_tryDecrypt b C ctl abs = entry) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) (entry + bv% (ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) (addrDisplaySpec A) := by
  rw [← hentry, ← fnAddr_tryDecrypt_eq]
  exact addrDisplay_ok_at_tripleRatchet hS (name := tryDecryptName) (k := num% (ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) hk_addrDisplay

theorem entry_eq_base_ext {b : BitVec 64} {ext : String → Option (State → State)} {entry : BitVec 64}
    (hentry : fnAddr_tryDecrypt_ext b ext = entry) :
    entry = b + bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") := by
  rw [← hentry, ← fnAddr_tryDecrypt_ext_eq, Program.fnAddr_rebase, fnOff_tryDecrypt]

theorem entry_eq_base {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {entry : BitVec 64}
    (hentry : fnAddr_tryDecrypt b C ctl abs = entry) :
    entry = b + bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") := by
  rw [← hentry, ← fnAddr_tryDecrypt_eq, Program.fnAddr_rebase, fnOff_tryDecrypt]

theorem spqrRecvEmptyAny_ok_at_entry_ext_x {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (hC : Stage2ContractsX img C A encFn decFn ext)
    (hentry : fnAddr_tryDecrypt_ext img.base ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% (ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
      ((spqrRecvEmptyAnySpec A).inImage img) := by
  rw [← hentry, ← fnAddr_tryDecrypt_ext_eq]
  exact hC.spqr_recv_ok_at tryDecryptName (num% (ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) hk_spqrRecv

theorem formatInner_ok_at_entry_ext_x {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (hC : Stage2ContractsX img C A encFn decFn ext)
    (hentry : fnAddr_tryDecrypt_ext img.base ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
      ((formatInnerSpec A).inImage img) := by
  rw [← hentry, ← fnAddr_tryDecrypt_ext_eq]
  exact hC.format_inner_ok_at tryDecryptName (num% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) hk_formatInner

theorem dealloc_ok_at_entry_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (halloc : AllocContractsX img A ext)
    (hentry : fnAddr_tryDecrypt_ext img.base ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) := by
  rw [← hentry, ← fnAddr_tryDecrypt_ext_eq]
  exact halloc.dealloc_ok_at tryDecryptName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) hk_dealloc

theorem addrDisplay_ok_at_entry_ext_x {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (hC : Stage2ContractsX img C A encFn decFn ext)
    (hentry : fnAddr_tryDecrypt_ext img.base ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% (ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
      ((addrDisplaySpec A).inImage img) := by
  rw [← hentry, ← fnAddr_tryDecrypt_ext_eq]
  exact addr_display_ok_at_ext_x img C A ext hC tryDecryptName (num% (ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) hk_addrDisplay

end KeyDeriveCallees

theorem mr_cut (sp : BitVec 64) (c n k m : Nat) (c' : BitVec 64)
    (hm : m = n + k := by rfl)
    (hc : BitVec.ofNat 64 (c + n) = c' := by rfl)
    (h : n + k ≤ 2 ^ 64 := by decide) :
    memRegion (sp + BitVec.ofNat 64 c) m =
      memRegion (sp + BitVec.ofNat 64 c) n ∗ memRegion (sp + c') k := by
  subst hm hc
  exact mr_cut_add sp c n k h

def trRestAt (A : RustAlloc) (sp : BitVec 64) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) : SepProp :=
  ⌜∀ sc, tr.ratchet.senderChain = some sc →
    Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes⌝ ∗
    ratchetAt A (sp + 56#64) trG.ratchet tr.ratchet ∗
    ((sp + 256#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
    ((sp + 288#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)

theorem trAt_split_pq (A : RustAlloc) (sp : BitVec 64) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) :
    trAt A (sp + 56#64) trG tr =
      vecU8At A (sp + 232#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
      trRestAt A sp trG tr := by
  unfold trAt trRestAt
  rw [BitVec.add_assoc, show (56#64 : BitVec 64) + 0xb0#64 = 232#64 by rfl,
    BitVec.add_assoc, show (56#64 : BitVec 64) + 0xc8#64 = 256#64 by rfl,
    BitVec.add_assoc, show (56#64 : BitVec 64) + 0xe8#64 = 288#64 by rfl]
  ac_rfl

def signalMessageRestAt (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) : SepProp :=
  ⌜macLength + 1 ≤ m.serialized.length ∧ m.serialized.length < 2 ^ 40 ∧
    m.ciphertext.length < 2 ^ 40 ∧ m.pqRatchet.length < 2 ^ 40 ∧
    (∀ ad, m.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
    boxU8At A (a + 0x18#64) g.ctPtr m.ciphertext ∗
    boxU8At A (a + 0x28#64) g.serPtr m.serialized ∗
    ((a + 0x38#64) ↦ₛ m.senderRatchetKey.bytes.toList) ∗
    optBoxU8At A (a + 0x58#64) g.addrPtr m.addresses ∗
    ((a + 0x68#64) ↦₃₂ m.counter) ∗ ((a + 0x6c#64) ↦₃₂ m.previousCounter) ∗
    ((a + 0x70#64) ↦₈ m.messageVersion) ∗ memRegion (a + 0x71#64) 7

theorem signalMessageAt_split_pq (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) :
    signalMessageAt A g a m =
      vecU8At A a g.pqCap g.pqPtr m.pqRatchet ∗
      signalMessageRestAt A g a m := by
  unfold signalMessageAt signalMessageRestAt
  ac_rfl

theorem msg_pqRatchet_lt_of_commonHeap {A : RustAlloc} {ctl : BitVec 64} {img : Obj.Image}
    {x : TryDecryptGhost} {draws : Nat} {s0 : State} {m : Memory} {P Q : SepProp}
    (h : m ⊨ P ∗ tryDecryptCommonHeap A ctl img x draws s0 ∗ Q) :
    x.msg.pqRatchet.length < 2 ^ 40 := by
  rw [sepConj_left_comm] at h
  unfold tryDecryptCommonHeap signalMessageAt at h
  simp only [sepConj_assoc] at h
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, satisfies_pure_sepConj] at h
  exact h.1.2.2.2.1

theorem onPanic_drop_frame {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {F R : SepProp} {s0 s' : State}
    (h : s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ (F ∗ R)) :
    s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R := by
  dsimp only [tryDecryptSpec, Spec.inImage] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  rcases h with ⟨hcond, hmem⟩
  rw [← sepConj_assoc] at hmem
  exact ⟨hcond, Satisfies.mono (sepConj_mono_left (ProofLib.entails_anyHeap _)) hmem⟩

theorem spqrRecvStack_le_sub_of_rootStack {sp0 : BitVec 64} (h : rootStack ≤ sp0.toNat) :
    spqrRecvStack ≤ (sp0 - 1504#64).toNat := by
  unfold rootStack spqrRecvStack at *
  bv_omega

theorem onPanic_of_spqrRecv {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {st msg : VecArg} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (htrace : sm.trace = s0.trace)
    (hst : st.bytes = x.st.pqRatchetState)
    (hmsg : msg.bytes = x.msg.pqRatchet)
    (h : sf.mem ⊨ ((spqrRecvSpec A S img).onPanic (st, msg, ret) sm sf ∗ F) ∗ R) :
    sf.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  dsimp only [spqrRecvSpec, tryDecryptSpec, Spec.inImage] at h ⊢
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
theorem rodata_0x45416_eq :
    (libsignalSessionImage.data.drop (num% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2452) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2456)) - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))).take 7 = utf8 "decrypt" := by
  rfl_kernel

theorem KeyDeriveCallees.utf8_decrypt_len : (utf8 "decrypt").length = 7 := by
  decide +kernel

set_option maxRecDepth 2000000 in
theorem rodata_decrypt_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2452) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2456))) ↦ᵣ utf8 "decrypt") ∗ P := by
  have hdlen : num% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2452) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2456)) - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)) + 7 ≤ libsignalSessionImage.data.length := by
    have h1 := congrArg List.length rodata_0x45416_eq
    rw [List.length_take, List.length_drop, KeyDeriveCallees.utf8_decrypt_len] at h1
    omega
  have h := ProofLib.Satisfies.of_rodata_loads himg
    (secOff := num% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2452) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2456))) (secLen := 7) (dataOff := num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    hdlen (by rfl_kernel) hro hP
  rwa [rodata_0x45416_eq] at h

theorem onPanic_of_formatInner {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (htrace : sm.trace = s0.trace)
    (h : sf.mem ⊨ ((formatInnerSpec A).onPanic ret sm sf ∗ F) ∗ R) :
    sf.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  dsimp only [formatInnerSpec, tryDecryptSpec, Spec.inImage] at h ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h
  rcases h with ⟨⟨hpan, hpref⟩, hmem⟩
  rw [← sepConj_assoc] at hmem
  rw [allocFailedIn, htrace, ← allocFailedIn] at hpan
  rw [htrace] at hpref
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨Or.inr (Or.inr hpan), hpref⟩, ?_⟩
  exact Satisfies.mono (sepConj_mono_left (ProofLib.entails_anyHeap _)) hmem

theorem onPanic_of_spqrRecv_fn {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {st msg : VecArg} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (htrace : sm.trace = s0.trace)
    (hst : st.bytes = x.st.pqRatchetState)
    (hmsg : msg.bytes = x.msg.pqRatchet)
    (h : sf.mem ⊨ ((spqrRecvSpec A S img).onPanic (st, msg, ret) sm sf ∗ F) ∗ R) :
    sf.mem ⊨ (tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  dsimp only [spqrRecvSpec, tryDecryptFnSpec, Spec.inImage] at h ⊢
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

theorem onPanic_of_formatInner_fn {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (htrace : sm.trace = s0.trace)
    (h : sf.mem ⊨ (((formatInnerSpec A).inImage img).onPanic ret sm sf ∗ F) ∗ R) :
    sf.mem ⊨ (tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  dsimp only [formatInnerSpec, tryDecryptFnSpec, Spec.inImage] at h ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h
  rcases h with ⟨⟨hpan, hpref⟩, hmem⟩
  rw [← sepConj_assoc] at hmem
  rw [allocFailedIn, htrace, ← allocFailedIn] at hpan
  rw [htrace] at hpref
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨Or.inr (Or.inr hpan), hpref⟩, ?_⟩
  exact Satisfies.mono (sepConj_mono_left (ProofLib.entails_anyHeap _)) hmem

theorem pointsToBytes_to_mr (a : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦ₛ bs) ⊢ memRegion a bs.length :=
  ProofLib.pointsToBytes_entails_memRegion a bs

theorem buf_to_mr (ptr : BitVec 64) (bs : List (BitVec 8)) (cap : Nat)
    (h1 : bs.length ≤ cap) (h2 : cap < 2 ^ 63) :
    (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap - bs.length) ⊢
    memRegion ptr cap := by
  refine Entails.trans (sepConj_mono_left (pointsToBytes_to_mr ptr bs)) ?_
  rw [← memRegion_split ptr bs.length (cap - bs.length) (by omega), Nat.add_sub_of_le h1]
  exact Entails.refl _

theorem sp56_weaken (sp seedPtr seedCap : BitVec 64) :
    memRegion sp 16 ∗
    ((sp + 16#64) ↦₆₄ seedPtr) ∗
    memRegion (sp + 24#64) 16 ∗
    ((sp + 40#64) ↦₆₄ seedCap) ∗
    memRegion (sp + 48#64) 8 ⊢
    memRegion sp 56 := by
  rw [memRegion_split sp 16 40 (by decide),
    mr_cut_add sp 16 8 32 (by decide),
    mr_cut_add sp 24 16 16 (by decide),
    mr_cut_add sp 40 8 8 (by decide)]
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono (pts64_to_mr _ _)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (pts64_to_mr _ _) (Entails.refl _))))

theorem sepWP_8_mr7_to_64 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {lo : BitVec 8} {F : SepProp} {post : State → SepProp → Prop}
    (h : ∀ hi : BitVec 56, SepWP prog target s ((a ↦₆₄ (hi ++ lo)) ∗ F) post) :
    SepWP prog target s ((a ↦₈ lo) ∗ memRegion (a + 1#64) 7 ∗ F) post := by
  refine SepWP.focus_weaken (pointsTo8_memRegion7_to_64 a lo) (by sep_focus) ?_
  rw [sepExists_sepConj_left]
  wp_pull_exists
  exact h _

theorem pts8_mr7_to_mr8 (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) ∗ memRegion (a + 1#64) 7 ⊢ memRegion a 8 := by
  rw [memRegion_split a 1 7 (by decide)]
  exact sepConj_mono (pts8_to_mr a b) (Entails.refl _)
  where
    pts8_to_mr (p : BitVec 64) (v : BitVec 8) : (p ↦₈ v) ⊢ memRegion p 1 := by
      rw [memRegion_one]
      exact Entails.sepExists_intro v

theorem extractLsb56_append_setWidth8 (w : BitVec 64) :
    w.extractLsb' 8 56 ++ w.setWidth 8 = w := by
  bv_kernel

theorem pointsTo64_to_8_mr7 (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) ⊢ (a ↦₈ w.setWidth 8) ∗ memRegion (a + 1#64) 7 := by
  have h := pointsTo64_to_8_memRegion7 a (w.extractLsb' 8 56) (w.setWidth 8)
  rwa [extractLsb56_append_setWidth8] at h

theorem adrp_decryptStr {b entry : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64) (he : entry = b + bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) :
    (((entry + bv% (2452)) &&& bv% (2 ^ 64 - 4096)) + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2452) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2456)) - page% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 500))) + bv% ((ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2452) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2456)) % 4096) =
      b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2452) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2456)) := by
  subst he; revert hb; bv_kernel

theorem sp_fp_eq {sp0 sp : BitVec 64} (h : sp0 - 1504#64 = sp) :
    sp0 - 96#64 = sp + 1408#64 := by
  subst h; bv_kernel

theorem cap_add_one_ne_zero {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  apply beq_false_of_ne
  intro heq
  have h1 : (cap + 1#64).toNat = 0 := by rw [heq]; rfl
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
  omega

theorem byte_ne_zero_cbz32 {d : BitVec 8} (h : d ≠ 0#8) :
    (BitVec.setWidth 32 d == 0#32) = false := by
  revert h; bv_kernel

theorem byte_ne_zero_cbz64_32 {d : BitVec 8} (h : d ≠ 0#8) :
    (BitVec.setWidth 32 (BitVec.setWidth 64 d) == 0#32) = false := by
  revert h; bv_kernel

theorem concat56_8_cbz64_zero (hi : BitVec 56) :
    (BitVec.zeroExtend 64 (BitVec.truncate 8 (hi ++ 0#8)) == 0#64) = true := by
  bv_kernel

theorem concat56_8_cbz64_ne_zero (hi : BitVec 56) {d : BitVec 8} (h : d ≠ 0#8) :
    (BitVec.zeroExtend 64 (BitVec.truncate 8 (hi ++ d)) == 0#64) = false := by
  revert h; bv_kernel

theorem concat56_8_cbz32_ne_zero (hi : BitVec 56) {d : BitVec 8} (h : d ≠ 0#8) :
    (BitVec.setWidth 32 (BitVec.zeroExtend 64 (BitVec.truncate 8 (hi ++ d))) == 0#32) = false := by
  revert h; bv_kernel

theorem speBodyAt_invalidState_fold (A : RustAlloc) (sp fmtCap fmtPtr p : BitVec 64)
    (fmtBs : List (BitVec 8))
    (hfb : fmtBs.length ≤ fmtCap.toNat ∧ fmtCap.toNat < 2 ^ 63 ∧ fmtPtr ≠ 0) :
    ((sp + 360#64) ↦₆₄ fmtCap) ∗
    ((sp + 368#64) ↦₆₄ fmtPtr) ∗
    ((sp + 376#64) ↦₆₄ BitVec.ofNat 64 fmtBs.length) ∗
    (if fmtCap = 0 then emp else A.live fmtPtr fmtCap.toNat 1 ∗
      (fmtPtr ↦ₛ fmtBs) ∗
      memRegion (fmtPtr + BitVec.ofNat 64 fmtBs.length) (fmtCap.toNat - fmtBs.length)) ∗
    ((sp + 384#64) ↦₆₄ p) ∗
    ((sp + 392#64) ↦₆₄ 7#64) ∗
    (p ↦ᵣ utf8 "decrypt") ⊢
    speBodyAt A (utf8 "decrypt") (sp + 360#64) .invalidState := by
  dsimp only [speBodyAt, strRefAt, vecU8, vecU8At, vecHeader]
  have hlen : BitVec.ofNat 64 (utf8 "decrypt").length = 7#64 := by decide +kernel
  rw [hlen]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left]
  refine Entails.trans ?_ (Entails.sepExists_intro fmtBs)
  refine Entails.trans ?_ (Entails.sepExists_intro fmtCap)
  refine Entails.trans ?_ (Entails.sepExists_intro fmtPtr)
  simp only [sepExists_sepConj_right]
  refine Entails.trans ?_ (Entails.sepExists_intro p)
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  exact Entails.pure_right hfb (Entails.refl _)

theorem speBodyAt_pqRatchet_fold (A : RustAlloc) (sp fmtCap fmtPtr w392 : BitVec 64)
    (fmtBs : List (BitVec 8)) (mt : MessageType)
    (hfb : fmtBs.length ≤ fmtCap.toNat ∧ fmtCap.toNat < 2 ^ 63 ∧ fmtPtr ≠ 0) :
    ((sp + 360#64) ↦₆₄ fmtCap) ∗
    ((sp + 368#64) ↦₆₄ fmtPtr) ∗
    ((sp + 376#64) ↦₆₄ BitVec.ofNat 64 fmtBs.length) ∗
    (if fmtCap = 0 then emp else A.live fmtPtr fmtCap.toNat 1 ∗
      (fmtPtr ↦ₛ fmtBs) ∗
      memRegion (fmtPtr + BitVec.ofNat 64 fmtBs.length) (fmtCap.toNat - fmtBs.length)) ∗
    ((sp + 384#64) ↦₈ msgTypeByte mt) ∗
    memRegion ((sp + 384#64) + 1#64) 7 ∗
    ((sp + 392#64) ↦₆₄ w392) ⊢
    speBodyAt A (utf8 "decrypt") (sp + 360#64) (.invalidMessage mt .pqRatchet) := by
  refine Entails.trans (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
    (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
        (pts64_to_mr (sp + 392#64) w392))))))) ?_
  dsimp only [speBodyAt, invalidMessageStrAt, vecU8, vecU8At, vecHeader]
  rw [show (sp + 384#64) + 1#64 = sp + 385#64 by rw [BitVec.add_assoc]; rfl,
    show (sp + 360#64) + 24#64 = sp + 384#64 by rw [BitVec.add_assoc]; rfl,
    show (sp + 360#64) + 25#64 = sp + 385#64 by rw [BitVec.add_assoc]; rfl,
    mr_cut sp 385 7 8 15 392#64]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left]
  refine Entails.trans ?_ (Entails.sepExists_intro fmtBs)
  refine Entails.trans ?_ (Entails.sepExists_intro fmtCap)
  refine Entails.trans ?_ (Entails.sepExists_intro fmtPtr)
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  exact Entails.pure_right hfb (Entails.refl _)

/-! ## Relocatable `[LibsignalPlacement]` Helpers for KeyDerive Segments -/

theorem reaches_pc_of_sepWP_placed [LibsignalPlacement] {prog : Program}
    {mid target : BitVec 64} {s : State} {P P_mid R : SepProp}
    {RegMid Q : State → Prop}
    (hmem : s.mem ⊨ P ∗ R)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (sm.mem ⊨ Pm ∗ R) → RegMid sm ∧ (sm.mem ⊨ P_mid ∗ R)))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      RegMid sm → SepWP prog target sm P_mid (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → Q sf)) :
    reaches_pc prog target s Q := by
  intro hL
  rcases h1.elim hmem hL with ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, himp⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨hReg, hmm'⟩ := himp hmm
    rcases (h2 sm hpc hrun (hcl.of_keepsFrozen hsteps.keepsFrozen) hReg).elim
        hmm' (hsteps.codeLoaded hL) with ⟨sf, hsteps', ⟨hpcf, hrunf, P_f, hmf, hq⟩ | ⟨_, hoom⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpcf, hrunf, hq hmf⟩⟩
    · exact (not_satisfies_false_sepConj hoom).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem tryDecryptMidMetaPlaced_of_core [LibsignalPlacement] {s0 s : State}
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : tryDecryptMidMetaCore s0 s) : tryDecryptMidMetaPlaced s0 s := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  exact ⟨h1, h2, h3, h4, h5, h6, hcl, h7⟩

theorem reaches_pc_midMeta_placed [LibsignalPlacement] {prog : Program} {target : BitVec 64}
    {s0 s : State} {Rest : State → Prop}
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : reaches_pc prog target s (fun sf => sf.pc = target ∧ tryDecryptMidMetaCore s0 sf ∧ Rest sf)) :
    reaches_pc prog target s (fun sf => sf.pc = target ∧ tryDecryptMidMetaPlaced s0 sf ∧ Rest sf) := by
  intro hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, hpc', hcore, hrest⟩ | hoom⟩ := h hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, hpc',
      tryDecryptMidMetaPlaced_of_core (hcl.of_keepsFrozen hsteps.keepsFrozen) hcore,
      hrest⟩⟩
  · exact ⟨sf, hsteps, Or.inr hoom⟩

theorem steps_of_sepWP_placed [LibsignalPlacement] {prog : Program}
    {mid : BitVec 64} {s : State} {P P_mid R : SepProp}
    {RegMid Out : State → Prop}
    (hmem : s.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s.mem)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (sm.mem ⊨ Pm ∗ R) → RegMid sm ∧ (sm.mem ⊨ P_mid ∗ R)))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      prog.CodeLoaded sm.mem → RegMid sm → (sm.mem ⊨ P_mid ∗ R) →
      ∃ s', Steps prog sm s' ∧ Out s') :
    ∃ s', Steps prog s s' ∧ Out s' := by
  rcases h1.elim hmem hL with ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, himp⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨hReg, hmm'⟩ := himp hmm
    obtain ⟨s', hsteps', hout⟩ :=
      h2 sm hpc hrun (hcl.of_keepsFrozen hsteps.keepsFrozen)
        (hsteps.codeLoaded hL) hReg hmm'
    exact ⟨s', hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem steps_done_of_sepWP_placed [LibsignalPlacement] {prog : Program}
    {target : BitVec 64} {s : State} {P R : SepProp}
    {QCore NormalOut PanicOut : State → Prop}
    (hmem : s.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s.mem)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (himp : ∀ sf, LibsignalCodeRoLoaded lsmpl sf.mem → QCore sf → NormalOut sf)
    (hwp : SepWP prog target s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → QCore sf)) :
    ∃ s', Steps prog s s' ∧ (NormalOut s' ∨ PanicOut s') := by
  rcases hwp.elim hmem hL with ⟨sf, hsteps, ⟨_, _, P_f, hmf, hq⟩ | ⟨_, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl (himp sf (hcl.of_keepsFrozen hsteps.keepsFrozen) (hq hmf))⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem steps_done_of_sepWP_midMeta_placed [LibsignalPlacement] {prog : Program}
    {target : BitVec 64} {s0 s : State} {P R : SepProp}
    {Rest PanicOut : State → Prop}
    (hmem : s.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s.mem)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hwp : SepWP prog target s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
      sf.pc = target ∧ tryDecryptMidMetaCore s0 sf ∧ Rest sf)) :
    ∃ s', Steps prog s s' ∧
      ((s'.pc = target ∧ tryDecryptMidMetaPlaced s0 s' ∧ Rest s') ∨ PanicOut s') := by
  refine steps_done_of_sepWP_placed hmem hL hcl ?_ hwp
  intro sf hclf ⟨hpc', hcore, hrest⟩
  exact ⟨hpc', tryDecryptMidMetaPlaced_of_core hclf hcore, hrest⟩

theorem steps_call_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc : BitVec 64} {spec : Spec α} (x : α)
    {sm : State} {F R : SepProp} {NormalOut PanicOut : State → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : sm.pc = entry) (hrun : sm.status = .Running) (hsp : sm.spAligned = true)
    (hlr : sm.readReg64 .lr = ret_pc)
    (hcl : LibsignalCodeRoLoaded lsmpl sm.mem)
    (hL : prog.CodeLoaded sm.mem)
    (hpre : sm.mem ⊨ spec.pre x sm ∗ (F ∗ R))
    (hpanic : ∀ sf, sf.status = .Panicked → (sf.mem ⊨ (spec.onPanic x sm sf ∗ F) ∗ R) → PanicOut sf)
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sm.sp → sf.spAligned = true → CalleeSavedPreserved sm sf →
      LibsignalCodeRoLoaded lsmpl sf.mem → prog.CodeLoaded sf.mem →
      (sf.mem ⊨ (spec.post x sm sf ∗ F) ∗ R) →
      ∃ s', Steps prog sf s' ∧ (NormalOut s' ∨ PanicOut s'))
    (hexit : ∀ sf code R', (sf.mem ⊨ spec.onExit x code sm sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h)
    (hoom : ∀ sf R', (sf.mem ⊨ spec.onOom x sm sf ∗ R') → False := by
      intro _ _ h; exact not_satisfies_false_sepConj h) :
    ∃ s', Steps prog sm s' ∧ (NormalOut s' ∨ PanicOut s') := by
  obtain ⟨sf, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) sm hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcf, _, hrunf⟩, ⟨hspf, hcsf⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcf
    have hsp_alf : sf.spAligned = true := by
      unfold State.spAligned at hsp ⊢; rw [hspf]; exact hsp
    obtain ⟨s', hsteps', hout'⟩ :=
      hnext sf hpcf hrunf hspf hsp_alf hcsf
        (hcl.of_keepsFrozen hsteps.keepsFrozen) (hsteps.codeLoaded hL) hpost
    exact ⟨s', hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sf, hsteps, Or.inr (hpanic sf hpan hpost)⟩
  · exact (hexit sf code (F ∗ R) hpost).elim
  · exact (hoom sf (F ∗ R) hpost).elim

theorem reaches_pc_of_sepWP_placed_cro [LibsignalPlacement] {prog : Program}
    {mid target : BitVec 64} {s : State} {P P_mid R : SepProp}
    {RegMid Q : State → Prop}
    (hmem : s.mem ⊨ P ∗ R)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (sm.mem ⊨ Pm ∗ R) → RegMid sm ∧ (sm.mem ⊨ P_mid ∗ R)))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      RegMid sm → SepWP prog target sm (⌜LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗ P_mid)
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → Q sf)) :
    reaches_pc prog target s Q := by
  intro hL
  rcases h1.elim hmem hL with ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, himp⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨hReg, hmm'⟩ := himp hmm
    have hclm := hcl.of_keepsFrozen hsteps.keepsFrozen
    have hmm'' : sm.mem ⊨ (⌜LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗ P_mid) ∗ R := by
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hclm, hmm'⟩
    rcases (h2 sm hpc hrun hclm hReg).elim hmm'' (hsteps.codeLoaded hL) with
      ⟨sf, hsteps', ⟨hpcf, hrunf, P_f, hmf, hq⟩ | ⟨_, hoom⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpcf, hrunf, hq hmf⟩⟩
    · exact (not_satisfies_false_sepConj hoom).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem steps_call_placed_cro [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc : BitVec 64} {spec : Spec α} (x : α)
    {sm : State} {F R : SepProp} {NormalOut PanicOut : State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hpc : sm.pc = entry) (hrun : sm.status = .Running) (hsp : sm.spAligned = true)
    (hlr : sm.readReg64 .lr = ret_pc)
    (hcl : LibsignalCodeRoLoaded lsmpl sm.mem)
    (hL : prog.CodeLoaded sm.mem)
    (hpre : sm.mem ⊨ spec.pre x sm ∗ (F ∗ R))
    (hpanic : ∀ sf, sf.status = .Panicked → (sf.mem ⊨ (spec.onPanic x sm sf ∗ F) ∗ R) → PanicOut sf)
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sm.sp → sf.spAligned = true → CalleeSavedPreserved sm sf →
      LibsignalCodeRoLoaded lsmpl sf.mem → prog.CodeLoaded sf.mem →
      (sf.mem ⊨ (spec.post x sm sf ∗ F) ∗ R) →
      ∃ s', Steps prog sf s' ∧ (NormalOut s' ∨ PanicOut s'))
    (hexit : ∀ sf code R', (sf.mem ⊨ spec.onExit x code sm sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h)
    (hoom : ∀ sf R', (sf.mem ⊨ spec.onOom x sm sf ∗ R') → False := by
      intro _ _ h; exact not_satisfies_false_sepConj h) :
    ∃ s', Steps prog sm s' ∧ (NormalOut s' ∨ PanicOut s') := by
  have hpre' : sm.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre x sm ∗ (F ∗ R) := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, hpre⟩
  exact steps_call_placed x hcall hpc hrun hsp hlr hcl hL hpre' hpanic hnext hexit hoom

theorem steps_call_placed_cl [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc : BitVec 64} {spec : Spec α} (x : α)
    {sm : State} {F R : SepProp} {NormalOut PanicOut : State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : sm.pc = entry) (hrun : sm.status = .Running) (hsp : sm.spAligned = true)
    (hlr : sm.readReg64 .lr = ret_pc)
    (hcl : LibsignalCodeRoLoaded lsmpl sm.mem)
    (hL : prog.CodeLoaded sm.mem)
    (hpre : sm.mem ⊨ spec.pre x sm ∗ (F ∗ R))
    (hpanic : ∀ sf, sf.status = .Panicked → (sf.mem ⊨ (spec.onPanic x sm sf ∗ F) ∗ R) → PanicOut sf)
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sm.sp → sf.spAligned = true → CalleeSavedPreserved sm sf →
      LibsignalCodeRoLoaded lsmpl sf.mem → prog.CodeLoaded sf.mem →
      (sf.mem ⊨ (spec.post x sm sf ∗ F) ∗ R) →
      ∃ s', Steps prog sf s' ∧ (NormalOut s' ∨ PanicOut s'))
    (hexit : ∀ sf code R', (sf.mem ⊨ spec.onExit x code sm sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h)
    (hoom : ∀ sf R', (sf.mem ⊨ spec.onOom x sm sf ∗ R') → False := by
      intro _ _ h; exact not_satisfies_false_sepConj h) :
    ∃ s', Steps prog sm s' ∧ (NormalOut s' ∨ PanicOut s') := by
  have hpre' : sm.mem ⊨ (withLsCodeLoaded lsmpl spec).pre x sm ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl.1, hpre⟩
  exact steps_call_placed x hcall hpc hrun hsp hlr hcl hL hpre' hpanic hnext hexit hoom

theorem onPanic_of_spqrRecv_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {x : TryDecryptGhost} {st msg : VecArg} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (htrace : sm.trace = s0.trace)
    (hst : st.bytes = x.st.pqRatchetState)
    (hmsg : msg.bytes = x.msg.pqRatchet)
    (h : sf.mem ⊨ ((spqrRecvSpec A S tryDecryptPlacedImg).onPanic (st, msg, ret) sm sf ∗ F) ∗ R) :
    sf.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 sf ∗ R :=
  onPanic_of_spqrRecv (img := tryDecryptPlacedImg) htrace hst hmsg h

theorem onPanic_of_formatInner_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {x : TryDecryptGhost} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (htrace : sm.trace = s0.trace)
    (h : sf.mem ⊨ ((formatInnerSpec A).onPanic ret sm sf ∗ F) ∗ R) :
    sf.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 sf ∗ R :=
  onPanic_of_formatInner (img := tryDecryptPlacedImg) htrace h

theorem onPanic_of_spqrRecv_fn_placed [LibsignalPlacement] {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {x : TryDecryptGhost} {st msg : VecArg} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (htrace : sm.trace = s0.trace)
    (hst : st.bytes = x.st.pqRatchetState)
    (hmsg : msg.bytes = x.msg.pqRatchet)
    (h : sf.mem ⊨ ((spqrRecvSpec A S tryDecryptPlacedImg).onPanic (st, msg, ret) sm sf ∗ F) ∗ R) :
    sf.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl uuidTryParse S).onPanic x s0 sf ∗ R :=
  onPanic_of_spqrRecv_fn (img := tryDecryptPlacedImg) htrace hst hmsg h

theorem onPanic_of_formatInner_fn_placed [LibsignalPlacement] {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {x : TryDecryptGhost} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (htrace : sm.trace = s0.trace)
    (h : sf.mem ⊨ ((formatInnerSpec A).onPanic ret sm sf ∗ F) ∗ R) :
    sf.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl uuidTryParse S).onPanic x s0 sf ∗ R :=
  onPanic_of_formatInner_fn (img := tryDecryptPlacedImg) (ret := ret) htrace h

private theorem exec_bind_panic_eq {σ α β : Type} (m : Mut σ α) (f₁ f₂ : α → Mut σ β) (s : σ)
    (h : ∀ a s', ((Mut.exec (f₁ a) s').1 = .error .panic) = ((Mut.exec (f₂ a) s').1 = .error .panic)) :
    ((Mut.exec (m >>= f₁) s).1 = .error .panic) = ((Mut.exec (m >>= f₂) s).1 = .error .panic) := by
  dsimp only [Bind.bind, ExceptT.bind, StateT.bind, Mut.exec, ExceptT.run, StateT.run, ExceptT.mk, ExceptT.bindCont]
  cases m s with
  | mk res s' =>
    cases res with
    | error e => rfl
    | ok a => exact h a s'

theorem decryptFn_error_panic_eq {PQ PQC : Type} (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) (s : TripleRatchet PQ) :
    ((Mut.exec (TripleRatchet.decryptFn C decFn spqr expected ciphertext msgType coins) s).1 = .error .panic) =
      ((Mut.exec (TripleRatchet.decrypt C spqr expected ciphertext msgType coins) s).1 = .error .panic) := by
  unfold TripleRatchet.decryptFn TripleRatchet.decrypt
  refine exec_bind_panic_eq _ _ _ s fun chainKey s1 => ?_
  refine exec_bind_panic_eq _ _ _ s1 fun messageKeyGen s2 => ?_
  refine exec_bind_panic_eq _ _ _ s2 fun t s3 => ?_
  dsimp only
  cases spqr.recvPanics t.pqrState ciphertext.pqRatchet with
  | true => rfl
  | false =>
    cases spqr.recv t.pqrState ciphertext.pqRatchet with
    | error sd => cases sd <;> rfl
    | ok r =>
      rcases r with ⟨newPqrState, pqrKey⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      dsimp only [Bind.bind, ExceptT.bind, StateT.bind, Mut.exec, ExceptT.run, StateT.run,
        pure, ExceptT.pure, StateT.pure, ExceptT.mk, ExceptT.bindCont]
      cases SignalMessage.verifyMacWithAddresses C.F ciphertext expected
          t.remoteIdentityKey t.localIdentityKey
          (MessageKeyGenerator.generateKeys C.F messageKeyGen pqrKey).macKey with
      | false => rfl
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases decFn ciphertext.ciphertext
            (keyToBytes32 (MessageKeyGenerator.generateKeys C.F messageKeyGen pqrKey).cipherKey)
            (CBC.blockToBytesLE (MessageKeyGenerator.generateKeys C.F messageKeyGen pqrKey).iv) <;>
          cases aesCbcDecrypt C.D
            (MessageKeyGenerator.generateKeys C.F messageKeyGen pqrKey).cipherKey
            (MessageKeyGenerator.generateKeys C.F messageKeyGen pqrKey).iv
            ciphertext.ciphertext <;>
          exact propext ⟨nofun, nofun⟩

private theorem exec_liftE_tail_panic_eq {PQ : Type} [Inhabited PQ]
    (r : Except SignalProtocolError (List (BitVec 8))) (session : TripleRatchet PQ)
    (s : SessionState PQ) :
    ((Mut.exec (do
      let ptext ← liftE r
      modify fun st => (session.applyToSessionState st).clearUnacknowledgedPreKeyMessage
      return ptext) s).1 = .error .panic) = (r = .error .panic) := by
  cases r with
  | error e => rfl
  | ok ptext => rfl

theorem tryDecryptWithStateFn_error_panic_eq {PQ PQC : Type} [Inhabited PQ] (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) (s : SessionState PQ) :
    ((Mut.exec (SessionState.tryDecryptWithStateFn C decFn spqr expected ciphertext msgType coins) s).1 = .error .panic) =
      ((Mut.exec (SessionState.tryDecryptWithState C spqr expected ciphertext msgType coins) s).1 = .error .panic) := by
  unfold SessionState.tryDecryptWithStateFn SessionState.tryDecryptWithState
  refine exec_bind_panic_eq _ _ _ s fun session s1 => ?_
  dsimp only
  rw [exec_liftE_tail_panic_eq, exec_liftE_tail_panic_eq]
  exact decryptFn_error_panic_eq C decFn spqr expected ciphertext msgType coins session

theorem modelFn_error_panic_eq (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (S : SpqrModel) (parse : UuidParser) (x : TryDecryptGhost) :
    ((x.modelFn C decFn S parse).1 = .error .panic) =
      ((x.model C S parse).1 = .error .panic) :=
  tryDecryptWithStateFn_error_panic_eq C decFn S.spqr
    (serializeAddresses (serviceIdParse parse) x.rem x.loc) x.msg x.msgType (coinsOf x.rest) x.st

theorem tryDecryptFnSpec_onPanic_eq (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (img : Obj.Image) :
    (tryDecryptFnSpec C decFn A ctl parse S img).onPanic =
      (tryDecryptSpec C A ctl parse S img).onPanic := by
  funext x s0 sf
  unfold tryDecryptFnSpec tryDecryptSpec Spec.inImage
  dsimp only
  rw [modelFn_error_panic_eq]

theorem tryDecryptFnSpecPlaced_onPanic_eq [LibsignalPlacement] (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) :
    (tryDecryptFnSpecPlaced C decFn A ctl parse S).onPanic =
      (tryDecryptSpecPlaced C A ctl parse S).onPanic :=
  tryDecryptFnSpec_onPanic_eq C decFn A ctl parse S tryDecryptPlacedImg

end CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive
