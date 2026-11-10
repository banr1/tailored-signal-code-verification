/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Mac.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Mac.MacCodeSym
public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Constant-Time MAC and Address Comparison Helpers

Proves the 8-byte MAC and 36-byte address constant-time comparison loops (via
`subtle::black_box::<u8>`) and stack/memory decompositions for
`<SignalMessage>::verify_mac_with_addresses`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Mac.VerifyMacWithAddresses

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession (logFilterAddr blackBoxHook)
open CryptoVerification.LibsignalTripleRatchet
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses") → (ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses" + 884)]

local elab "s2_ext_fetches " b:term:max ext:term:max
    hfn:term:max off:term:max len:term:max : tactic => open Lean Meta Elab Tactic in do
  let offLit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat off "s2_ext_fetches "))
  let k0Lit := Syntax.mkNumLit "0"
  let lenLit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat len "s2_ext_fetches "))
  let hfnId : Ident ← if hfn.raw.isIdent then pure ⟨hfn.raw⟩ else do
    let g ← getMainGoal
    let c? ← g.withContext do
      tryCatchRuntimeEx (do
        let e := (← instantiateMVars (← Term.elabTermAndSynthesize hfn none)).consumeMData
        return if e.isConst then some e.constName! else none) (fun _ => pure none)
    match c? with
    | some c => pure (mkCIdentFrom hfn c)
    | none =>
      let id := mkIdent `_hfn_layout
      evalTactic (← `(tactic| have $id := $hfn))
      pure id
  evalTactic (← `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode libsignalSessionBin $b (Rust.withPanics $ext) $hfnId:ident $offLit:num $k0Lit:num $lenLit:num))

/-- `subtle::black_box::<u8>` (`0x47fa8`) is `blackBoxHook`: returns immediately with `x0` set to
`(s0.readReg64 .x0).setWidth 8` zero-extended to 64 bits. -/
def session2BlackBoxSpec (b : BitVec 8) : Spec Unit where
  pre := fun _ s => ⌜(s.readReg64 .x0).setWidth 8 = b⌝
  post := fun _ s0 sf => ⌜sf.readReg64 .x0 = b.zeroExtend 64 ∧ sf.trace = s0.trace⌝

theorem session2BlackBox_of_blackBox {prog : Program} {addr : BitVec 64}
    (h : subroutine_ok prog addr blackBoxSpec) (v : BitVec 8) :
    subroutine_ok prog addr (session2BlackBoxSpec v) := by
  apply subroutine_ok.of_codeLoaded
  intro _ R s0 hpc hrun hpre hsp _
  rcases (satisfies_pure_sepConj _ _ _).mp hpre with ⟨hv, hR⟩
  have hpre' : s0.mem ⊨ blackBoxSpec.pre (s0.readReg64 .x0) s0 ∗ R :=
    (satisfies_pure_sepConj _ _ _).mpr ⟨rfl, hR⟩
  refine h.mono_outcome (s0.readReg64 .x0) R s0 hpc hrun hpre' hsp (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    rcases (satisfies_pure_sepConj _ _ _).mp hpost with ⟨⟨hx0, htr⟩, hR'⟩
    exact (satisfies_pure_sepConj _ _ _).mpr ⟨⟨by rw [hx0, hv], htr⟩, hR'⟩
  · right; left; exact ⟨hpan, hpost⟩
  · right; right; left; exact ⟨code, hex, hpost⟩
  · right; right; right; exact ⟨hoom, hpost⟩

theorem blackBox_ok_at2_ext {b : BitVec 64} {ext : String → Option (State → State)}
    (hbb_raw : subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr blackBoxName) blackBoxSpec)
    {name : String} {k : Nat} (v : BitVec 8)
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "subtle::black_box::<u8>" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (session2BlackBoxSpec v) :=
  session2BlackBox_of_blackBox (sub_ok_at_of_fnAddr hbb_raw name k hk) v

theorem verifyMacWithAddresses_fnOff :
    libsignalSessionCode.fnOff verifyMacWithAddressesName = num% (ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_lemma% fnOff "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses")

theorem adrp_logFilter_544_ext {img : Obj.Image} (ext : String → Option (State → State))
    (hb : img.base &&& 0xfff#64 = 0#64) :
    Unit →
    (((((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 544#64) &&&
      bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac" + 64))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096)) ↦₆₄ 0#64 = logOff img := fun _ => by
  have he : (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName =
      img.base + bv% (ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses") := by
    rw [tripleRatchetProgAtExt, Program.fnAddr_rebase, verifyMacWithAddresses_fnOff]
  have haddr : ((((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 544#64) &&&
      bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac" + 64))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) = logFilterAddr img := by
    rw [he]
    dsimp only [logFilterAddr]
    revert hb; bv_bits
  rw [haddr]

theorem adrp_logFilter_704_ext {img : Obj.Image} (ext : String → Option (State → State))
    (hb : img.base &&& 0xfff#64 = 0#64) :
    Unit →
    (((((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 704#64) &&&
      bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac" + 64))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096)) ↦₆₄ 0#64 = logOff img := fun _ => by
  have he : (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName =
      img.base + bv% (ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses") := by
    rw [tripleRatchetProgAtExt, Program.fnAddr_rebase, verifyMacWithAddresses_fnOff]
  have haddr : ((((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 704#64) &&&
      bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac" + 64))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) = logFilterAddr img := by
    rw [he]
    dsimp only [logFilterAddr]
    revert hb; bv_bits
  rw [haddr]

theorem adrp_logFilter_704'_ext {img : Obj.Image} (ext : String → Option (State → State))
    (hb : img.base &&& 0xfff#64 = 0#64) :
    Unit →
    ((((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 704#64) &&&
      bv% (2 ^ 64 - 4096)) + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256 - page% (ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac" + 64))) ↦₆₄ 0#64 = logOff img := fun _ => by
  have he : (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName =
      img.base + bv% (ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses") := by
    rw [tripleRatchetProgAtExt, Program.fnAddr_rebase, verifyMacWithAddresses_fnOff]
  have haddr : (((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 704#64) &&&
      bv% (2 ^ 64 - 4096)) + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256 - page% (ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac" + 64)) = logFilterAddr img := by
    rw [he]
    dsimp only [logFilterAddr]
    revert hb; bv_bits
  rw [haddr]

/-! ## Arithmetic and representation helpers -/

theorem len_sub_8_eq {n : Nat} (h9 : 9 ≤ n) (hlt : n < 2 ^ 40) :
    BitVec.ofNat 64 n + bv% (2 ^ 64 - 8) = BitVec.ofNat 64 (n - 8) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2 : (BitVec.ofNat 64 (n - 8)).toNat = n - 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : BitVec.ofNat 64 n + bv% (2 ^ 64 - 8) = BitVec.ofNat 64 n - 8#64 := by
    bv_omega
  rw [hsub, BitVec.toNat_sub_of_le]
  · rw [h1, h2]; rfl
  · rw [BitVec.le_def, h1]; change 8 ≤ n; omega

theorem len_sub_8_bv {n : Nat} (h9 : 9 ≤ n) (hlt : n < 2 ^ 40) :
    BitVec.ofNat 64 n - 8#64 = BitVec.ofNat 64 (n - 8) := by
  have hsub : BitVec.ofNat 64 n - 8#64 = BitVec.ofNat 64 n + bv% (2 ^ 64 - 8) := by
    bv_omega
  rw [hsub, len_sub_8_eq h9 hlt]

theorem len_ult_8_false {n : Nat} (h9 : 9 ≤ n) (hlt : n < 2 ^ 40) :
    (BitVec.ofNat 64 n).ult 8#64 = false := by
  have h1 : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp [BitVec.ult, h1]
  omega

theorem len_sub_8_ult {n : Nat} (h9 : 9 ≤ n) (hlt : n < 2 ^ 40) :
    (BitVec.ofNat 64 n - 8#64).ult (BitVec.ofNat 64 n) = true ∧
    (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 n - 8#64) = false ∧
    (BitVec.ofNat 64 n - 8#64).ule (BitVec.ofNat 64 n) = true ∧
    ((BitVec.ofNat 64 n - 8#64) == BitVec.ofNat 64 n) = false := by
  rw [len_sub_8_bv h9 hlt]
  have h1 : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2 : (BitVec.ofNat 64 (n - 8)).toNat = n - 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne : BitVec.ofNat 64 (n - 8) ≠ BitVec.ofNat 64 n := by
    intro heq
    have := congrArg BitVec.toNat heq
    omega
  refine ⟨?_, ?_, ?_, beq_false_of_ne hne⟩ <;>
    (simp [BitVec.ult, BitVec.ule, h1, h2]; try omega)

theorem serializeAddresses_some_length {parse : UuidParser} {s r : AddrGhost}
    {exp : List (BitVec 8)} (h : serializeAddresses (serviceIdParse parse) s r = some exp) :
    exp.length = 36 := by
  dsimp only [serializeAddresses] at h
  cases hs : serviceIdParse parse s.name.bytes with
  | none => simp [hs] at h
  | some sval =>
    cases hr : serviceIdParse parse r.name.bytes with
    | none => simp [hs, hr] at h
    | some rval =>
      simp only [hs, hr, Option.bind_eq_bind, Option.bind, pure, Option.some.injEq] at h
      subst h
      simp [addrBytes, sval.2.toList_length, rval.2.toList_length]

theorem optSerializeAddressesAt_some_eq (A : RustAlloc) (ret : BitVec 64)
    {exp : List (BitVec 8)} (hlen : exp.length = 36) :
    optSerializeAddressesAt A ret (some exp) =
      ∃∗ p : BitVec 64,
        ⌜p ≠ 0⌝ ∗
        (ret ↦₆₄ 36#64) ∗ ((ret + 8#64) ↦₆₄ p) ∗ ((ret + 16#64) ↦₆₄ 36#64) ∗
        A.live p 36 1 ∗ (p ↦ₛ exp) := by
  dsimp only [optSerializeAddressesAt, vecU8At, vecHeader]
  refine congrArg sepExists (funext fun p => ?_)
  have h36 : (36#64 : BitVec 64).toNat = 36 := rfl
  have hne : (36#64 : BitVec 64) ≠ 0 := by decide
  simp only [hlen, h36, hne, ite_false, Nat.sub_self, memRegion_zero, sepConj_emp]
  have hpure : (36 ≤ 36 ∧ 36 < 2 ^ 63 ∧ p ≠ 0) ↔ (p ≠ 0) :=
    ⟨fun ⟨_, _, hp⟩ => hp, fun hp => ⟨by decide, by decide, hp⟩⟩
  simp only [hpure]
  ac_rfl

/-- Byte comparison result in `cset w0, eq` (`SUBS wzr, w8, w9` + `CSINC w0, wzr, wzr, NE`). -/
@[local simp, local arm64_norm]
theorem cset_eq_byte (b1 b2 : BitVec 8) :
    (BitVec.zeroExtend 64
      (if (b1.zeroExtend 32 + (~~~b2.zeroExtend 32 + 1#32) != 0#32) = true then 0#32
       else 0#32 + 1#32)).setWidth 8 =
    if b1 == b2 then 1#8 else 0#8 := by
  by_cases h : b1 = b2 <;> simp [h] <;> bv_bits

@[local simp, local arm64_norm]
theorem cset_eq_byte_alt (b1 b2 : BitVec 8) :
    (BitVec.zeroExtend 64
      (if (b1.zeroExtend 32 + 4294967295#32 * b2.zeroExtend 32 != 0#32) = true then 0#32
       else 1#32)).setWidth 8 =
    if b1 == b2 then 1#8 else 0#8 := by
  by_cases h : b1 = b2 <;> simp [h] <;> bv_bits

theorem sub_one_ofNat_succ {n : Nat} (hlt : n + 1 < 2 ^ 64) :
    BitVec.ofNat 64 (n + 1) + bv% (2 ^ 64 - 1) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (BitVec.ofNat 64 (n + 1)).toNat = n + 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have h2 : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h0 : (1#64 : BitVec 64).toNat = 1 := rfl
  have hsub : BitVec.ofNat 64 (n + 1) + bv% (2 ^ 64 - 1) = BitVec.ofNat 64 (n + 1) - 1#64 := by
    bv_omega
  rw [hsub, BitVec.toNat_sub_of_le]
  · rw [h1, h2, h0]; omega
  · rw [BitVec.le_def, h1, h0]; omega

theorem ofNat_succ_ne_zero {n : Nat} (hlt : n + 1 < 2 ^ 64) :
    (BitVec.ofNat 64 (n + 1) != 0#64) = true := by
  rw [bne_iff_ne]
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n + 1 = 0 at ht
  omega

theorem ofNat_cons_sub_one {α : Type} (x : α) (xs : List α)
    (hlt : (x :: xs).length < 2 ^ 64) :
    BitVec.ofNat 64 (x :: xs).length - 1#64 = BitVec.ofNat 64 xs.length := by
  simp only [List.length_cons] at hlt ⊢
  have hsub : BitVec.ofNat 64 (xs.length + 1) - 1#64 =
      BitVec.ofNat 64 (xs.length + 1) + bv% (2 ^ 64 - 1) := by bv_omega
  rw [hsub]
  exact sub_one_ofNat_succ hlt

theorem ofNat_cons_cons_bne_one {α : Type} (x y : α) (xs : List α)
    (hlt : (x :: y :: xs).length < 2 ^ 64) :
    (BitVec.ofNat 64 (x :: y :: xs).length != 1#64) = true := by
  rw [bne_iff_ne]
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  simp only [List.length_cons] at ht
  change xs.length + 1 + 1 = 1 at ht
  omega

@[local simp, local arm64_norm]
theorem bne_zext32_ite (b1 b2 : BitVec 8) :
    (if (BitVec.zeroExtend 32 b1 != BitVec.zeroExtend 32 b2) = true then 0#8 else 1#8) =
      (if (b1 == b2) = true then 1#8 else 0#8) := by
  by_cases h : b1 = b2
  · simp [h]
  · simp [h]; bv_bits

/-! ## 8-byte MAC constant-time comparison -/

@[local simp, local arm64_norm]
theorem okTagVec_add_two_ne_zero : (okTagVec + 2#64 != 0#64) = false := by decide

@[local simp, local arm64_norm]
theorem okTagVec_add_two_eq_zero : (okTagVec + 2#64 == 0#64) = true := by decide

@[local simp, local arm64_norm]
theorem noneCap_add_one_eq_zero : (noneCap + 1#64 == 0#64) = true := by decide

@[local simp, local arm64_norm]
theorem pack64_byte0 (m0 m1 m2 m3 m4 m5 m6 m7 : BitVec 8) :
    BitVec.setWidth 8 (pack64 m0 m1 m2 m3 m4 m5 m6 m7) = m0 := by
  unfold pack64; bv_bits

@[local simp, local arm64_norm]
theorem pack64_byte1 (m0 m1 m2 m3 m4 m5 m6 m7 : BitVec 8) :
    BitVec.setWidth 8
      (BitVec.zeroExtend 64 (BitVec.setWidth 32 (pack64 m0 m1 m2 m3 m4 m5 m6 m7)) >>> 8) = m1 := by
  unfold pack64; bv_bits

@[local simp, local arm64_norm]
theorem pack64_byte2 (m0 m1 m2 m3 m4 m5 m6 m7 : BitVec 8) :
    BitVec.setWidth 8
      (BitVec.zeroExtend 64 (BitVec.setWidth 32 (pack64 m0 m1 m2 m3 m4 m5 m6 m7)) >>> 16) = m2 := by
  unfold pack64; bv_bits

@[local simp, local arm64_norm]
theorem pack64_byte3 (m0 m1 m2 m3 m4 m5 m6 m7 : BitVec 8) :
    BitVec.setWidth 32 (pack64 m0 m1 m2 m3 m4 m5 m6 m7) >>> 24 = BitVec.zeroExtend 32 m3 := by
  unfold pack64; bv_bits

@[local simp, local arm64_norm]
theorem pack64_byte4 (m0 m1 m2 m3 m4 m5 m6 m7 : BitVec 8) :
    BitVec.setWidth 8 (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 32) = m4 := by
  unfold pack64; bv_bits

@[local simp, local arm64_norm]
theorem pack64_byte5 (m0 m1 m2 m3 m4 m5 m6 m7 : BitVec 8) :
    BitVec.setWidth 8 (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 40) = m5 := by
  unfold pack64; bv_bits

@[local simp, local arm64_norm]
theorem pack64_byte6 (m0 m1 m2 m3 m4 m5 m6 m7 : BitVec 8) :
    BitVec.setWidth 8 (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 48) = m6 := by
  unfold pack64; bv_bits

@[local simp, local arm64_norm]
theorem pack64_byte7 (m0 m1 m2 m3 m4 m5 m6 m7 : BitVec 8) :
    BitVec.setWidth 32 (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 56) = BitVec.zeroExtend 32 m7 := by
  unfold pack64; bv_bits

@[local simp, local arm64_norm]
theorem ite_one_zero_and_64 (b1 b2 : Bool) :
    ((if b1 = true then 1#64 else 0#64) &&& (if b2 = true then 1#64 else 0#64)) =
      if (b1 && b2) = true then 1#64 else 0#64 := by
  cases b1 <;> cases b2 <;> rfl

@[local simp, local arm64_norm]
theorem ite_one_zero_and_32 (b1 b2 : Bool) :
    ((if b1 = true then 1#32 else 0#32) &&& (if b2 = true then 1#32 else 0#32)) =
      if (b1 && b2) = true then 1#32 else 0#32 := by
  cases b1 <;> cases b2 <;> rfl

@[local simp, local arm64_norm]
theorem setWidth32_ite_one_zero_64 (b : Bool) :
    BitVec.setWidth 32 (if b = true then 1#64 else 0#64) =
      if b = true then 1#32 else 0#32 := by
  cases b <;> rfl

@[local simp, local arm64_norm]
theorem zeroExtend64_ite_one_zero_32 (b : Bool) :
    BitVec.zeroExtend 64 (if b = true then 1#32 else 0#32) =
      if b = true then 1#64 else 0#64 := by
  cases b <;> rfl

@[local simp, local arm64_norm]
theorem ite_one_zero_and_one_64 (b : Bool) :
    ((if b = true then 1#64 else 0#64) &&& 4294967297#64) =
      if b = true then 1#64 else 0#64 := by
  cases b <;> rfl

@[local simp, local arm64_norm]
theorem setWidth8_ite_one_zero_64 (b : Bool) :
    BitVec.setWidth 8 (if b = true then 1#64 else 0#64) =
      if b = true then 1#8 else 0#8 := by
  cases b <;> rfl

@[local simp, local arm64_norm]
theorem mac8_eq_bool (m0 m1 m2 m3 m4 m5 m6 m7 t0 t1 t2 t3 t4 t5 t6 t7 : BitVec 8) :
    ((((t0 == m0 && t1 == m1) && (t2 == m2 && t3 == m3)) &&
      ((t4 == m4 && t5 == m5) && t6 == m6)) && t7 == m7) =
    (([m0, m1, m2, m3, m4, m5, m6, m7] : List (BitVec 8)) ==
      [t0, t1, t2, t3, t4, t5, t6, t7]) := by
  change ((((t0 == m0 && t1 == m1) && (t2 == m2 && t3 == m3)) &&
      ((t4 == m4 && t5 == m5) && t6 == m6)) && t7 == m7) =
    (m0 == t0 && (m1 == t1 && (m2 == t2 && (m3 == t3 && (m4 == t4 && (m5 == t5 && (m6 == t6 && (m7 == t7 && true))))))))
  rw [Bool.and_true]
  simp only [Bool.and_assoc]
  congr 1; · exact BEq.comm
  congr 1; · exact BEq.comm
  congr 1; · exact BEq.comm
  congr 1; · exact BEq.comm
  congr 1; · exact BEq.comm
  congr 1; · exact BEq.comm
  congr 1; · exact BEq.comm
  exact BEq.comm

/-! ## Stack and memory layout decompositions -/

theorem stackAt_split_ge (sp : BitVec 64) (n m : Nat) (h : m ≤ n := by decide)
    (hbound : n < 2 ^ 64 := by decide) :
    stackAt sp n = stackAt sp m ∗ memRegion (sp - BitVec.ofNat 64 n) (n - m) := by
  simp only [stackAt]
  have h1 : n = (n - m) + m := by omega
  conv => lhs; rw [h1]
  rw [memRegion_split (sp - BitVec.ofNat 64 ((n - m) + m)) (n - m) m (by omega)]
  have ha1 : BitVec.ofNat 64 ((n - m) + m) = BitVec.ofNat 64 n := by congr 1; omega
  have ha2 : sp - BitVec.ofNat 64 n + BitVec.ofNat 64 (n - m) = sp - BitVec.ofNat 64 m := by
    have : BitVec.ofNat 64 n = BitVec.ofNat 64 (n - m) + BitVec.ofNat 64 m := by
      rw [← BitVec.ofNat_add]; congr 1
    rw [this]; bv_arith
  rw [ha1, ha2]
  ac_rfl

def verifyMacFrameRest (sp : BitVec 64) : SepProp :=
  memRegion (sp - 240#64) 32 ∗ memRegion (sp - 184#64) 88

theorem stackAt_verifyMacWithAddresses_gen (cmStack : Nat)
    (hbound : cmStack + 288 ≤ 2 ^ 64 := by decide) (sp : BitVec 64) :
    stackAt sp (cmStack + 288) =
      stackAt (sp - 288#64) cmStack ∗
      verifyMacFrameRest sp ∗
      memRegion (sp - 208#64) 24 ∗
      (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64, ∃∗ s3 : BitVec 64,
       ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64,
        ((sp - 288#64) ↦₆₄ s0) ∗ ((sp - 280#64) ↦₆₄ s1) ∗
        ((sp - 272#64) ↦₆₄ s2) ∗ ((sp - 264#64) ↦₆₄ s3) ∗
        ((sp - 256#64) ↦₆₄ s4) ∗ ((sp - 248#64) ↦₆₄ s5)) ∗
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗
        ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
        ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗
        ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
        ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗
        ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) := by
  unfold verifyMacFrameRest
  have htop : stackAt sp (cmStack + 288) =
      stackAt (sp - 288#64) cmStack ∗ memRegion (sp - 288#64) 288 := by
    simp only [stackAt]
    rw [memRegion_split _ cmStack 288 hbound]
    have e1 : sp - BitVec.ofNat 64 (cmStack + 288) =
        sp - 288#64 - BitVec.ofNat 64 cmStack := by
      rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
    have e2 : sp - 288#64 - BitVec.ofNat 64 cmStack + BitVec.ofNat 64 cmStack =
        sp - 288#64 := by
      rw [BitVec.sub_add_cancel]
    rw [e1, e2]
  rw [htop]
  have hm288 : memRegion (sp - 288#64) 288 =
      memRegion (sp - 288#64) (8 * 6) ∗
      memRegion (sp - 240#64) 32 ∗
      memRegion (sp - 208#64) 24 ∗
      memRegion (sp - 184#64) 88 ∗
      memRegion (sp - 96#64) (8 * 12) := by
    rw [show (288 : Nat) = 48 + (32 + (24 + (88 + 96))) by decide,
      memRegion_split (sp - 288#64) 48 (32 + (24 + (88 + 96))) (by decide),
      memRegion_split (sp - 288#64 + 48#64) 32 (24 + (88 + 96)) (by decide),
      memRegion_split (sp - 288#64 + 48#64 + 32#64) 24 (88 + 96) (by decide),
      memRegion_split (sp - 288#64 + 48#64 + 32#64 + 24#64) 88 96 (by decide)]
    have a1 : sp - 288#64 + 48#64 = sp - 240#64 := by bv_arith
    have a2 : sp - 240#64 + 32#64 = sp - 208#64 := by bv_arith
    have a3 : sp - 208#64 + 24#64 = sp - 184#64 := by bv_arith
    have a4 : sp - 184#64 + 88#64 = sp - 96#64 := by bv_arith
    rw [a1, a2, a3, a4]
  rw [hm288, memRegion_cells (sp - 288#64) 6 (by decide),
    memRegion_cells (sp - 96#64) 12 (by decide)]
  have hc6 : cells (sp - 288#64) 6 =
      ∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64, ∃∗ s3 : BitVec 64,
      ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64,
        ((sp - 288#64) ↦₆₄ s0) ∗ ((sp - 280#64) ↦₆₄ s1) ∗
        ((sp - 272#64) ↦₆₄ s2) ∗ ((sp - 264#64) ↦₆₄ s3) ∗
        ((sp - 256#64) ↦₆₄ s4) ∗ ((sp - 248#64) ↦₆₄ s5) := by
    cells_unfold
  have hc12 : cells (sp - 96#64) 12 =
      ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
      ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
      ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗
        ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
        ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗
        ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
        ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗
        ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11) := by
    cells_unfold
  rw [hc6, hc12]
  ac_rfl

theorem stackAt_verifyMacWithAddresses (sp : BitVec 64) :
    stackAt sp verifyMacWithAddressesStack =
      stackAt (sp - 288#64) computeMacStack ∗
      verifyMacFrameRest sp ∗
      memRegion (sp - 208#64) 24 ∗
      (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64, ∃∗ s3 : BitVec 64,
       ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64,
        ((sp - 288#64) ↦₆₄ s0) ∗ ((sp - 280#64) ↦₆₄ s1) ∗
        ((sp - 272#64) ↦₆₄ s2) ∗ ((sp - 264#64) ↦₆₄ s3) ∗
        ((sp - 256#64) ↦₆₄ s4) ∗ ((sp - 248#64) ↦₆₄ s5)) ∗
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗
        ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
        ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗
        ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
        ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗
        ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) :=
  stackAt_verifyMacWithAddresses_gen computeMacStack (by decide) sp

theorem stackAt_verifyMacWithAddressesX (sp : BitVec 64) :
    stackAt sp verifyMacWithAddressesStackX =
      stackAt (sp - 288#64) computeMacStackX ∗
      verifyMacFrameRest sp ∗
      memRegion (sp - 208#64) 24 ∗
      (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64, ∃∗ s3 : BitVec 64,
       ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64,
        ((sp - 288#64) ↦₆₄ s0) ∗ ((sp - 280#64) ↦₆₄ s1) ∗
        ((sp - 272#64) ↦₆₄ s2) ∗ ((sp - 264#64) ↦₆₄ s3) ∗
        ((sp - 256#64) ↦₆₄ s4) ∗ ((sp - 248#64) ↦₆₄ s5)) ∗
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗
        ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
        ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗
        ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
        ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗
        ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) :=
  stackAt_verifyMacWithAddresses_gen computeMacStackX (by decide) sp

theorem memRegion_24_split_16_8 (r : BitVec 64) :
    memRegion r 24 = memRegion r 16 ∗ (∃∗ v2 : BitVec 64, (r + 16#64) ↦₆₄ v2) := by
  rw [show (24 : Nat) = 16 + 8 by decide, memRegion_split r 16 8 (by decide), memRegion_eight (r + 16#64)]

theorem memRegion_9_split (r : BitVec 64) :
    memRegion r 9 = (∃∗ v0 : BitVec 64, ∃∗ b8 : BitVec 8, (r ↦₆₄ v0) ∗ ((r + 8#64) ↦₈ b8)) := by
  rw [show (9 : Nat) = 8 + 1 by decide, memRegion_split r 8 1 (by decide),
    memRegion_eight r, memRegion_one (r + 8#64), sepExists_sepConj_left]
  refine congrArg sepExists (funext fun v0 => ?_)
  rw [sepExists_sepConj_right]

def signalMessageRest (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64) (m : SignalMessage) :
    SepProp :=
  vecU8At A a g.pqCap g.pqPtr m.pqRatchet ∗
  boxU8At A (a + 0x18#64) g.ctPtr m.ciphertext ∗
  ((a + 0x38#64) ↦ₛ m.senderRatchetKey.bytes.toList) ∗
  ((a + 0x68#64) ↦₃₂ m.counter) ∗ ((a + 0x6c#64) ↦₃₂ m.previousCounter) ∗
  ((a + 0x70#64) ↦₈ m.messageVersion) ∗ memRegion (a + 0x71#64) 7

theorem signalMessageAt_expose (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) :
    signalMessageAt A g a m =
      ⌜macLength + 1 ≤ m.serialized.length ∧ m.serialized.length < 2 ^ 40 ∧
        m.ciphertext.length < 2 ^ 40 ∧ m.pqRatchet.length < 2 ^ 40 ∧
        (∀ ad, m.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
      boxU8At A (a + 40#64) g.serPtr m.serialized ∗
      optBoxU8At A (a + 88#64) g.addrPtr m.addresses ∗
      signalMessageRest A g a m := by
  unfold signalMessageAt signalMessageRest
  have h40 : a + 0x28#64 = a + 40#64 := rfl
  have h88 : a + 0x58#64 = a + 88#64 := rfl
  rw [h40, h88]
  ac_rfl

theorem boxU8At_expose_nonempty (A : RustAlloc) (a ptr : BitVec 64) (bs : List (BitVec 8))
    (hne : bs ≠ []) :
    boxU8At A a ptr bs =
      ⌜ptr ≠ 0 ∧ bs.length < 2 ^ 63⌝ ∗
      (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗ A.live ptr bs.length 1 := by
  unfold boxU8At
  simp only [hne, ↓reduceIte]
  ac_rfl

theorem pointsToBytes_serialized_split (p : BitVec 64) (bs : List (BitVec 8))
    (h : 8 ≤ bs.length) :
    (p ↦ₛ bs) =
      (p ↦ₛ bs.take (bs.length - 8)) ∗
      ((p + BitVec.ofNat 64 (bs.length - 8)) ↦ₛ bs.drop (bs.length - 8)) := by
  conv => lhs; rw [← List.take_append_drop (bs.length - 8) bs]
  rw [pointsToBytes_append, List.length_take_of_le (by omega)]

theorem list_length_8_eq {α : Type _} (l : List α) (h : l.length = 8) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7, l = [b0, b1, b2, b3, b4, b5, b6, b7] := by
  match l, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ => exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩

theorem sha256With_length (F : ShaCompress) (m : List (BitVec 8)) :
    (HMAC.sha256With F m).length = 32 := by
  unfold HMAC.sha256With
  generalize ((HMAC.chunks64 (HMAC.sha256Pad m)).foldl F HMAC.sha256IV) = st
  rcases st with ⟨l, hl⟩
  match l, hl with
  | [w0, w1, w2, w3, w4, w5, w6, w7], _ => rfl

theorem computeMac_length (F : ShaCompress) (s r : IdentityKey) (k : BitVec 256)
    (msg : List (BitVec 8)) :
    (computeMac F s r k msg).length = 8 := by
  simp only [computeMac, HMAC.hmacSha256Trunc8, HMAC.hmacWith, List.length_take, sha256With_length]
  decide

theorem pointsToBytes_8_bytes (p : BitVec 64) (t0 t1 t2 t3 t4 t5 t6 t7 : BitVec 8) :
    (p ↦ₛ [t0, t1, t2, t3, t4, t5, t6, t7]) =
      (p ↦₈ t0) ∗ ((p + 1#64) ↦₈ t1) ∗ ((p + 2#64) ↦₈ t2) ∗ ((p + 3#64) ↦₈ t3) ∗
      ((p + 4#64) ↦₈ t4) ∗ ((p + 5#64) ↦₈ t5) ∗ ((p + 6#64) ↦₈ t6) ∗ ((p + 7#64) ↦₈ t7) := by
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  have h2 : p + 1#64 + 1#64 = p + 2#64 := by bv_arith
  have h3 : p + 2#64 + 1#64 = p + 3#64 := by bv_arith
  have h4 : p + 3#64 + 1#64 = p + 4#64 := by bv_arith
  have h5 : p + 4#64 + 1#64 = p + 5#64 := by bv_arith
  have h6 : p + 5#64 + 1#64 = p + 6#64 := by bv_arith
  have h7 : p + 6#64 + 1#64 = p + 7#64 := by bv_arith
  rw [h2, h3, h4, h5, h6, h7]

theorem pointsToBytes_pack64 (p : BitVec 64) (m0 m1 m2 m3 m4 m5 m6 m7 : BitVec 8) :
    (p ↦ₛ [m0, m1, m2, m3, m4, m5, m6, m7]) =
      (p ↦₆₄ pack64 m0 m1 m2 m3 m4 m5 m6 m7) := by
  simpa using pointsToBytes_take8_eq_pointsTo64 p [m0, m1, m2, m3, m4, m5, m6, m7] 0 (by simp)

theorem memRegion_16_split_8_8 (r : BitVec 64) :
    memRegion r 16 =
      (∃∗ v0 : BitVec 64, r ↦₆₄ v0) ∗ (∃∗ v1 : BitVec 64, (r + 8#64) ↦₆₄ v1) := by
  rw [show (16 : Nat) = 8 + 8 by decide, memRegion_split r 8 8 (by decide)]
  have h8 : r + BitVec.ofNat 64 8 = r + 8#64 := by bv_arith
  rw [h8, memRegion_eight r, memRegion_eight (r + 8#64)]

theorem memRegion_16_of_two_words (r v0 v1 : BitVec 64) :
    ((r ↦₆₄ v0) ∗ ((r + 8#64) ↦₆₄ v1)) ⊢ memRegion r 16 := by
  rw [memRegion_16_split_8_8 r]
  exact sepConj_mono (Entails.sepExists_intro v0) (Entails.sepExists_intro v1)

theorem memRegion_24_of_16_8 (sp v : BitVec 64) :
    (memRegion (sp - 208#64) 16 ∗ ((sp - 192#64) ↦₆₄ v)) ⊢ memRegion (sp - 208#64) 24 := by
  have h192 : sp - 208#64 + 16#64 = sp - 192#64 := by bv_arith
  rw [memRegion_24_split_16_8 (sp - 208#64), h192]
  exact sepConj_mono_right (Entails.sepExists_intro v)

theorem optBoxU8At_some_expose (A : RustAlloc) (p ptr : BitVec 64) (ad : List (BitVec 8)) :
    optBoxU8At A (p + 88#64) ptr (some ad) =
      ⌜ptr ≠ 0#64 ∧ ad.length < 2 ^ 63⌝ ∗
      ((p + 88#64) ↦₆₄ ptr) ∗ ((p + 96#64) ↦₆₄ BitVec.ofNat 64 ad.length) ∗
      (if ad = [] then emp else A.live ptr ad.length 1 ∗ (ptr ↦ₛ ad)) := by
  have h96 : p + 88#64 + 8#64 = p + 96#64 := by bv_arith
  simp only [optBoxU8At, boxU8At, h96]
  ac_rfl

/-! ## `verifyMacWithAddressesSpecX` helpers -/

theorem seq_inImage_h {prog : Program} (mid : BitVec 64) {target_pc : BitVec 64}
    {img : Obj.Image} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog mid s P (fun sm Pm =>
      img.FrozenLoaded sm → sm.symtab = img.symtab → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post := by
  unfold SepWP reaches_pc
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, hoom⟩⟩
  · rcases (hnext (hF.of_keepsFrozen hsteps.keepsFrozen) (hsteps.symtab_eq.trans hsym)).elim hmm (hsteps.codeLoaded hL) with
      ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hpost⟩ | ⟨_, hoom⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpcf, hrunf, Pf, hmf, hpost⟩⟩
    · exact (not_satisfies_false_sepConj hoom).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem seq_inImage_x30 {prog : Program} {target_pc : BitVec 64}
    {img : Obj.Image} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog (s.readReg64 .x30) s P (fun sm Pm =>
      img.FrozenLoaded sm → sm.symtab = img.symtab → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post :=
  seq_inImage_h (s.readReg64 .x30) hF hsym h

theorem of_sepWP_inImage_h {prog : Program} {img : Obj.Image} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog mid s P
      (fun sm Pm => img.FrozenLoaded sm → sm.symtab = img.symtab →
        SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext (hF.of_keepsFrozen hsteps.keepsFrozen) (hsteps.symtab_eq.trans hsym) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

local macro "wp_steps_inImage " mid:term : tactic =>
  `(tactic| (
    refine seq_inImage_h $mid ‹_› ‹_› ?_
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hF_step hsym_step))

def session2BlackBoxSpecX (sp_cur : BitVec 64) (n : Nat) (b : BitVec 8) : Spec Unit where
  pre := fun _ s =>
    ⌜(s.readReg64 .x0).setWidth 8 = b ∧ s.sp = sp_cur⌝ ∗ stackAt sp_cur n
  post := fun _ s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 8 = b ∧ sf.trace = s0.trace⌝ ∗ stackAt sp_cur n

theorem blackBox_ok_at2_ext_x {img : Obj.Image} {ext : String → Option (State → State)}
    (sp_cur : BitVec 64) (n : Nat)
    (hbb_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr blackBoxName)
      ((withStack blackBoxU8Spec extHookStack).inImage img))
    {name : String} {k : Nat} (v : BitVec 8)
    (hn : extHookStack ≤ n := by decide) (hbound : n < 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "subtle::black_box::<u8>" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((session2BlackBoxSpecX sp_cur n v).inImage img) := by
  have h := sub_ok_at_of_fnAddr hbb_raw name k hk
  have hsplit := stackAt_split_ge sp_cur n extHookStack hn hbound
  apply subroutine_ok.of_codeLoaded
  intro _ R s0 hpc hrun hpre hsp _
  simp only [Spec.inImage, session2BlackBoxSpecX, hsplit, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hv, hsp_eq⟩, hmem⟩
  have hpre' : s0.mem ⊨ ((withStack blackBoxU8Spec extHookStack).inImage img).pre (s0.readReg64 .x0) s0 ∗
      (memRegion (sp_cur - BitVec.ofNat 64 n) (n - extHookStack) ∗ R) := by
    simp only [Spec.inImage, withStack, blackBoxU8Spec, hsp_eq, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, trivial, hmem⟩
  refine h.mono_outcome (s0.readReg64 .x0)
    (memRegion (sp_cur - BitVec.ofNat 64 n) (n - extHookStack) ∗ R) s0 hpc hrun hpre' hsp (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    simp only [Spec.inImage, withStack, blackBoxU8Spec, session2BlackBoxSpecX, hsp_eq, hsplit,
      sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hx0, htr⟩, hmem'⟩
    exact ⟨⟨by rw [hx0, hv], htr⟩, hmem'⟩
  · dsimp only [Spec.inImage, withStack, blackBoxU8Spec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · dsimp only [Spec.inImage, withStack, blackBoxU8Spec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · dsimp only [Spec.inImage, withStack, blackBoxU8Spec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1

theorem blackBox_ok_at2_ext_inImage {img : Obj.Image} {ext : String → Option (State → State)}
    (sp_cur : BitVec 64) (n : Nat)
    (hbb_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr blackBoxName) blackBoxSpec)
    {name : String} {k : Nat} (v : BitVec 8)
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "subtle::black_box::<u8>" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((session2BlackBoxSpecX sp_cur n v).inImage img) := by
  apply subroutine_ok_inImage_of_subroutine_ok img
  have h := blackBox_ok_at2_ext hbb_raw (name := name) (k := k) v hk
  apply subroutine_ok.of_codeLoaded
  intro _ R s0 hpc hrun hpre hsp _
  simp only [session2BlackBoxSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hv, _⟩, hmem⟩
  have hpre' : s0.mem ⊨ (session2BlackBoxSpec v).pre () s0 ∗ (stackAt sp_cur n ∗ R) := by
    simp only [session2BlackBoxSpec, satisfies_pure_sepConj]
    exact ⟨hv, hmem⟩
  refine h.mono_outcome () (stackAt sp_cur n ∗ R) s0 hpc hrun hpre' hsp (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    simp only [session2BlackBoxSpec, session2BlackBoxSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hx0, htr⟩, hmem'⟩
    exact ⟨⟨by rw [hx0]; bv_bits, htr⟩, hmem'⟩
  · dsimp only [session2BlackBoxSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · dsimp only [session2BlackBoxSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · dsimp only [session2BlackBoxSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1

theorem and_w22_step_u8 (b1 b2 : BitVec 8) (acc : Bool) (x0 w22 : BitVec 64)
    (hx0 : x0.setWidth 8 = if (b1 == b2) = true then 1#8 else 0#8)
    (hw22 : w22.setWidth 8 = if acc then 1#8 else 0#8) :
    (BitVec.zeroExtend 64
      (BitVec.truncate 32
        (x0 &&& BitVec.zeroExtend 64 (BitVec.truncate 32 w22)))).setWidth 8 =
      if (acc && (b1 == b2)) then 1#8 else 0#8 := by
  have htrunc :
      (BitVec.zeroExtend 64
        (BitVec.truncate 32
          (x0 &&& BitVec.zeroExtend 64 (BitVec.truncate 32 w22)))).setWidth 8 =
      x0.setWidth 8 &&& w22.setWidth 8 := by
    ext i hi
    dsimp only [BitVec.zeroExtend, BitVec.truncate]
    simp [show i < 64 by omega]
  rw [htrunc, hx0, hw22]
  cases acc <;> cases (b1 == b2) <;> rfl

@[local simp, local arm64_norm]
theorem setWidth8_zext64_32 (x : BitVec 32) :
    BitVec.setWidth 8 (BitVec.zeroExtend 64 x) = BitVec.setWidth 8 x := by
  bv_bits

@[local simp, local arm64_norm]
theorem setWidth8_setWidth32 (x : BitVec 64) :
    BitVec.setWidth 8 (BitVec.setWidth 32 x) = BitVec.setWidth 8 x := by
  bv_bits

@[local simp, local arm64_norm]
theorem setWidth8_and64 (x y : BitVec 64) :
    BitVec.setWidth 8 (x &&& y) = BitVec.setWidth 8 x &&& BitVec.setWidth 8 y :=
  BitVec.setWidth_and

@[local simp, local arm64_norm]
theorem setWidth8_and32 (x y : BitVec 32) :
    BitVec.setWidth 8 (x &&& y) = BitVec.setWidth 8 x &&& BitVec.setWidth 8 y :=
  BitVec.setWidth_and

@[local simp, local arm64_norm]
theorem ite_one_zero_and_8 (b1 b2 : Bool) :
    ((if b1 = true then 1#8 else 0#8) &&& (if b2 = true then 1#8 else 0#8)) =
      if (b1 && b2) = true then 1#8 else 0#8 := by
  cases b1 <;> cases b2 <;> rfl

@[local simp, local arm64_norm]
theorem setWidth32_and_4294967297 (x : BitVec 64) :
    BitVec.setWidth 32 (x &&& 4294967297#64) =
      BitVec.zeroExtend 32 (BitVec.setWidth 8 x &&& 1#8) := by
  bv_bits

@[local simp, local arm64_norm]
theorem setWidth32_and_1095216660735 (x : BitVec 32) :
    BitVec.setWidth 32 (BitVec.zeroExtend 64 x &&& 1095216660735#64) =
      BitVec.zeroExtend 32 (BitVec.setWidth 8 x) := by
  bv_bits

@[local simp, local arm64_norm]
theorem ite_one_zero_and_one_8 (b : Bool) :
    ((if b = true then 1#8 else 0#8) &&& 1#8) =
      if b = true then 1#8 else 0#8 := by
  cases b <;> rfl

@[local simp, local arm64_norm]
theorem zeroExtend32_ite_one_zero_8 (b : Bool) :
    BitVec.zeroExtend 32 (if b = true then 1#8 else 0#8) =
      if b = true then 1#32 else 0#32 := by
  cases b <;> rfl

set_option maxHeartbeats 1600000 in
theorem ctEqLoop_sepWPp_gen (cmStack : Nat) (img : Obj.Image) (ext : String → Option (State → State))
    (sp_cur : BitVec 64)
    (hbb : ∀ v : BitVec 8, subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + bv% (ls_off% "subtle::black_box::<u8>" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
      ((session2BlackBoxSpecX sp_cur cmStack v).inImage img))
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop} :
    ∀ (bs1 bs2 : List (BitVec 8)) (p1 p2 : BitVec 64) (acc : Bool) (Frame : SepProp) (s : State),
      bs1 ≠ [] →
      bs1.length = bs2.length →
      bs1.length < 2 ^ 64 →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 412#64 →
      s.status = .Running →
      s.spAligned = true →
      s.sp = sp_cur →
      s.readReg64 .x25 = p1 →
      s.readReg64 .x23 = p2 →
      s.readReg64 .x24 = BitVec.ofNat 64 bs1.length →
      (s.readReg64 .x22).setWidth 8 = (if acc then 1#8 else 0#8) →
      (∀ sf,
        img.FrozenLoaded sf →
        sf.symtab = img.symtab →
        sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 444#64 →
        sf.status = .Running →
        sf.spAligned = true →
        sf.trace = s.trace →
        sf.sp = sp_cur →
        sf.readReg64 .x19 = s.readReg64 .x19 →
        sf.readReg64 .x20 = s.readReg64 .x20 →
        sf.readReg64 .x21 = s.readReg64 .x21 →
        sf.readReg64 .x26 = s.readReg64 .x26 →
        sf.readReg64 .x27 = s.readReg64 .x27 →
        sf.readReg64 .x28 = s.readReg64 .x28 →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        (sf.readReg64 .x22).setWidth 8 = (if (acc && (bs1 == bs2)) then 1#8 else 0#8) →
        SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
          ((p1 ↦ₛ bs1) ∗ (p2 ↦ₛ bs2) ∗ stackAt sp_cur cmStack ∗ Frame) Q Qp) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s
        ((p1 ↦ₛ bs1) ∗ (p2 ↦ₛ bs2) ∗ stackAt sp_cur cmStack ∗ Frame) Q Qp := by
  have hfn := verifyMacWithAddresses_fnOff
  have hf_412 := libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 412) hfn (by decide) (ls_decode% libsignalSessionBin (ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses" + 412))
  have hf_416 := libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 416) hfn (by decide) (ls_decode% libsignalSessionBin (ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses" + 416))
  have hf_420 := libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 420) hfn (by decide) (ls_decode% libsignalSessionBin (ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses" + 420))
  have hf_424 := libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 424) hfn (by decide) (ls_decode% libsignalSessionBin (ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses" + 424))
  have hf_428 := libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 428) hfn (by decide) (ls_decode% libsignalSessionBin (ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses" + 428))
  have hf_432 := libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 432) hfn (by decide) (ls_decode% libsignalSessionBin (ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses" + 432))
  have hf_436 := libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 436) hfn (by decide) (ls_decode% libsignalSessionBin (ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses" + 436))
  have hf_440 := libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 440) hfn (by decide) (ls_decode% libsignalSessionBin (ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses" + 440))
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName = entry
  intro bs1
  induction bs1 with
  | nil => intro _ _ _ _ _ _ hne; exact absurd rfl hne
  | cons b1 bs1' ih =>
    intro bs2 p1 p2 acc Frame s _ hlen hlt hF_s hsym_s hpc hrun hsp hsp_eq hx25 hx23 hx24 hx22 hcont
    have hsp_orig := hsp
    simp only [wp_norm, arm64_norm, hsp_eq] at hsp
    cases bs2 with
    | nil => simp at hlen
    | cons b2 bs2' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [pointsToBytes_cons, sepConj_assoc]
      have hbb_step := hbb (if b1 == b2 then 1#8 else 0#8)
      refine of_sepWP_inImage_h hF_s hsym_s (mid := entry + bv% (432)) ?_
      wp_steps_inImage (entry + bv% (ls_off% "subtle::black_box::<u8>" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
      wp_call hbb_step ()
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hF_1 hsym_1
      cases bs1' with
      | nil =>
        cases bs2' with
        | nil =>
          have hne_1 : (BitVec.ofNat 64 [b1].length != 1#64) = false := rfl
          refine of_sepWP_inImage_h hF_1 hsym_1 (mid := entry + bv% (444)) ?_
          wp_steps
          apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          intro hF_2 hsym_2
          have hbeq : (([b1] : List (BitVec 8)) == [b2]) = (b1 == b2) := by
            simp
          refine SepWPp.weaken_pre ?_
            (hcont _ hF_2 hsym_2 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [State.spAligned, arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by rw [hbeq, Bool.and_comm acc]; simp only [arm64_norm, *]))
          simp only [pointsToBytes_cons, sepConj_assoc]
          exact Entails.of_eq (by ac_rfl)
        | cons _ _ => simp at hlen
      | cons b1' bs1'' =>
        have hlen' : (b1' :: bs1'').length = bs2'.length := hlen
        have hlt' : (b1' :: bs1'').length < 2 ^ 64 := by simp only [List.length_cons] at hlt ⊢; omega
        have hsub := ofNat_cons_sub_one b1 (b1' :: bs1'') hlt
        have hne_z := ofNat_cons_cons_bne_one b1 b1' bs1'' hlt
        refine of_sepWP_inImage_h hF_1 hsym_1 (mid := entry + bv% (412)) ?_
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hF_2 hsym_2
        refine SepWPp.weaken_pre ?_
          (ih bs2' (p1 + 1#64) (p2 + 1#64) (acc && (b1 == b2)) (p1 ↦₈ b1 ∗ p2 ↦₈ b2 ∗ Frame) _
            (by simp) hlen' hlt' hF_2 hsym_2
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [State.spAligned, arm64_norm, *])
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by rw [Bool.and_comm acc]; simp only [arm64_norm, *])
            fun sf' hF_f hsym_f hpc_f hrun_f hsp_f htr_f hsp_eq' hx19_f hx20_f hx21_f hx26_f hx27_f hx28_f hx29_f hvregs_f hx22_f => ?_)
        · exact Entails.of_eq (by ac_rfl)
        · have hbeq_cons : ((b1 :: b1' :: bs1'') == (b2 :: bs2')) = ((b1 == b2) && ((b1' :: bs1'') == bs2')) := rfl
          have hbool_assoc : ((acc && (b1 == b2)) && ((b1' :: bs1'') == bs2')) =
              (acc && ((b1 :: b1' :: bs1'') == (b2 :: bs2'))) := by
            rw [hbeq_cons, Bool.and_assoc]
          rw [hbool_assoc] at hx22_f
          refine SepWPp.weaken_pre ?_
            (hcont sf' hF_f hsym_f hpc_f hrun_f hsp_f
              (by simp only [arm64_norm, *]) hsp_eq'
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hx22_f)
          simp only [pointsToBytes_cons, sepConj_assoc]
          exact Entails.of_eq (by ac_rfl)


theorem ctEqLoop_sepWPp_ext_x (img : Obj.Image) (ext : String → Option (State → State))
    (sp_cur : BitVec 64)
    (hbb_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr blackBoxName)
      ((withStack blackBoxU8Spec extHookStack).inImage img))
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop} :
    ∀ (bs1 bs2 : List (BitVec 8)) (p1 p2 : BitVec 64) (acc : Bool) (Frame : SepProp) (s : State),
      bs1 ≠ [] →
      bs1.length = bs2.length →
      bs1.length < 2 ^ 64 →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 412#64 →
      s.status = .Running →
      s.spAligned = true →
      s.sp = sp_cur →
      s.readReg64 .x25 = p1 →
      s.readReg64 .x23 = p2 →
      s.readReg64 .x24 = BitVec.ofNat 64 bs1.length →
      (s.readReg64 .x22).setWidth 8 = (if acc then 1#8 else 0#8) →
      (∀ sf,
        img.FrozenLoaded sf →
        sf.symtab = img.symtab →
        sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 444#64 →
        sf.status = .Running →
        sf.spAligned = true →
        sf.trace = s.trace →
        sf.sp = sp_cur →
        sf.readReg64 .x19 = s.readReg64 .x19 →
        sf.readReg64 .x20 = s.readReg64 .x20 →
        sf.readReg64 .x21 = s.readReg64 .x21 →
        sf.readReg64 .x26 = s.readReg64 .x26 →
        sf.readReg64 .x27 = s.readReg64 .x27 →
        sf.readReg64 .x28 = s.readReg64 .x28 →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        (sf.readReg64 .x22).setWidth 8 = (if (acc && (bs1 == bs2)) then 1#8 else 0#8) →
        SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
          ((p1 ↦ₛ bs1) ∗ (p2 ↦ₛ bs2) ∗ stackAt sp_cur computeMacStackX ∗ Frame) Q Qp) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s
        ((p1 ↦ₛ bs1) ∗ (p2 ↦ₛ bs2) ∗ stackAt sp_cur computeMacStackX ∗ Frame) Q Qp :=
  ctEqLoop_sepWPp_gen computeMacStackX img ext sp_cur
    (fun v => blackBox_ok_at2_ext_x sp_cur computeMacStackX hbb_raw
      (name := verifyMacWithAddressesName)
      (k := num% (ls_off% "subtle::black_box::<u8>" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
      v (by decide) (by decide) (by fnoff_eq))

set_option maxHeartbeats 1600000 in
theorem macCompare8_sepWPp_gen (cmStack : Nat) (img : Obj.Image) (ext : String → Option (State → State))
    (sp_cur : BitVec 64)
    (hbb : ∀ v : BitVec 8, subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + bv% (ls_off% "subtle::black_box::<u8>" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
      ((session2BlackBoxSpecX sp_cur cmStack v).inImage img))
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    (m0 m1 m2 m3 m4 m5 m6 m7 t0 t1 t2 t3 t4 t5 t6 t7 : BitVec 8)
    (serPtr msgA recvA sendA retA w_sp8 w_sp16 w_sp24 : BitVec 64)
    (len : Nat) (Frame : SepProp) (s : State)
    (hF_s : img.FrozenLoaded s)
    (hsym_s : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 100#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hsp_cur : s.sp = sp_cur)
    (hx19 : s.readReg64 .x19 = retA)
    (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = recvA)
    (hx22 : s.readReg64 .x22 = sendA)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (len - 8))
    (hx24 : s.readReg64 .x24 = serPtr)
    (hcont : ∀ sf : State,
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      sf.pc = (if (([m0, m1, m2, m3, m4, m5, m6, m7] : List (BitVec 8)) ==
                   [t0, t1, t2, t3, t4, t5, t6, t7]) then
                 (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 344#64
               else
                 (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 504#64) →
      sf.status = .Running →
      sf.spAligned = true →
      sf.trace = s.trace →
      sf.sp = sp_cur →
      sf.readReg64 .x20 = msgA →
      sf.readReg64 .x21 = recvA →
      sf.readReg64 .x22 = sendA →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        (((s.sp + 80#64) ↦₆₄ okTagVec) ∗ ((s.sp + 88#64) ↦₆₄ pack64 m0 m1 m2 m3 m4 m5 m6 m7) ∗
         ((s.sp + 8#64) ↦₆₄ (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 48)) ∗
         ((s.sp + 16#64) ↦₆₄ (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 56)) ∗
         ((s.sp + 24#64) ↦₆₄ retA) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8)) ↦₈ t0) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 1#64) ↦₈ t1) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 2#64) ↦₈ t2) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 3#64) ↦₈ t3) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 4#64) ↦₈ t4) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 5#64) ↦₈ t5) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 6#64) ↦₈ t6) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 7#64) ↦₈ t7) ∗
         stackAt sp_cur cmStack ∗ Frame) Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (((s.sp + 80#64) ↦₆₄ okTagVec) ∗ ((s.sp + 88#64) ↦₆₄ pack64 m0 m1 m2 m3 m4 m5 m6 m7) ∗
       ((s.sp + 8#64) ↦₆₄ w_sp8) ∗ ((s.sp + 16#64) ↦₆₄ w_sp16) ∗ ((s.sp + 24#64) ↦₆₄ w_sp24) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8)) ↦₈ t0) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 1#64) ↦₈ t1) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 2#64) ↦₈ t2) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 3#64) ↦₈ t3) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 4#64) ↦₈ t4) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 5#64) ↦₈ t5) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 6#64) ↦₈ t6) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 7#64) ↦₈ t7) ∗
       stackAt sp_cur cmStack ∗ Frame) Q Qp := by
  have hsp_orig := hsp
  simp only [wp_norm, arm64_norm, hsp_cur] at hsp
  have hfn := verifyMacWithAddresses_fnOff
  s2_ext_fetches img.base ext hfn (num% (ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses")) 344
  have hbb0 := hbb (if t0 == m0 then 1#8 else 0#8)
  have hbb1 := hbb (if t1 == m1 then 1#8 else 0#8)
  have hbb2 := hbb (if t2 == m2 then 1#8 else 0#8)
  have hbb3 := hbb (if t3 == m3 then 1#8 else 0#8)
  have hbb4 := hbb (if t4 == m4 then 1#8 else 0#8)
  have hbb5 := hbb (if t5 == m5 then 1#8 else 0#8)
  have hbb6 := hbb (if t6 == m6 then 1#8 else 0#8)
  have hbb7 := hbb (if t7 == m7 then 1#8 else 0#8)
  have hbb8 := hbb
    (if (([m0, m1, m2, m3, m4, m5, m6, m7] : List (BitVec 8)) ==
         [t0, t1, t2, t3, t4, t5, t6, t7]) then 1#8 else 0#8)
  clear hbb
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName = entry
  examples_hide_fetches
  refine of_sepWP_inImage_h hF_s hsym_s (mid := entry + bv% (336)) ?_
  wp_steps_inImage (entry + bv% (ls_off% "subtle::black_box::<u8>" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
  refine seq_inImage_x30 ‹_› ‹_› ?_
  wp_call hbb0 ()
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF0 hsym0
  wp_steps_inImage (entry + bv% (ls_off% "subtle::black_box::<u8>" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
  refine seq_inImage_x30 ‹_› ‹_› ?_
  wp_call hbb1 ()
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF1 hsym1
  wp_steps_inImage (entry + bv% (ls_off% "subtle::black_box::<u8>" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
  refine seq_inImage_x30 ‹_› ‹_› ?_
  wp_call hbb2 ()
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF2 hsym2
  wp_steps_inImage (entry + bv% (ls_off% "subtle::black_box::<u8>" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
  refine seq_inImage_x30 ‹_› ‹_› ?_
  wp_call hbb3 ()
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF3 hsym3
  wp_steps_inImage (entry + bv% (ls_off% "subtle::black_box::<u8>" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
  refine seq_inImage_x30 ‹_› ‹_› ?_
  wp_call hbb4 ()
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF4 hsym4
  wp_steps_inImage (entry + bv% (ls_off% "subtle::black_box::<u8>" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
  refine seq_inImage_x30 ‹_› ‹_› ?_
  wp_call hbb5 ()
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF5 hsym5
  wp_steps_inImage (entry + bv% (ls_off% "subtle::black_box::<u8>" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
  refine seq_inImage_x30 ‹_› ‹_› ?_
  wp_call hbb6 ()
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF6 hsym6
  wp_steps_inImage (entry + bv% (ls_off% "subtle::black_box::<u8>" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
  refine seq_inImage_x30 ‹_› ‹_› ?_
  wp_call hbb7 ()
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF7 hsym7
  wp_steps_inImage (entry + bv% (ls_off% "subtle::black_box::<u8>" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
  wp_call hbb8 ()
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF8 hsym8
  cases hmac : (([m0, m1, m2, m3, m4, m5, m6, m7] : List (BitVec 8)) ==
                [t0, t1, t2, t3, t4, t5, t6, t7])
  · simp only [hmac, Bool.false_eq_true, ↓reduceIte] at *
    refine of_sepWP_inImage_h hF8 hsym8 (mid := entry + bv% (504)) ?_
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hF9 hsym9
    refine SepWPp.weaken_pre ?_
      (hcont _ hF9 hsym9 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [State.spAligned, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]))
    rw [hsp_cur]
    exact Entails.of_eq (by ac_rfl)
  · simp only [hmac, ↓reduceIte] at *
    refine of_sepWP_inImage_h hF8 hsym8 (mid := entry + bv% (344)) ?_
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hF9 hsym9
    refine SepWPp.weaken_pre ?_
      (hcont _ hF9 hsym9 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [State.spAligned, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]))
    rw [hsp_cur]
    exact Entails.of_eq (by ac_rfl)


theorem macCompare8_sepWPp_ext_x (img : Obj.Image) (ext : String → Option (State → State))
    (sp_cur : BitVec 64)
    (hbb_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr blackBoxName)
      ((withStack blackBoxU8Spec extHookStack).inImage img))
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    (m0 m1 m2 m3 m4 m5 m6 m7 t0 t1 t2 t3 t4 t5 t6 t7 : BitVec 8)
    (serPtr msgA recvA sendA retA w_sp8 w_sp16 w_sp24 : BitVec 64)
    (len : Nat) (Frame : SepProp) (s : State)
    (hF_s : img.FrozenLoaded s)
    (hsym_s : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 100#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hsp_cur : s.sp = sp_cur)
    (hx19 : s.readReg64 .x19 = retA)
    (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = recvA)
    (hx22 : s.readReg64 .x22 = sendA)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (len - 8))
    (hx24 : s.readReg64 .x24 = serPtr)
    (hcont : ∀ sf : State,
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      sf.pc = (if (([m0, m1, m2, m3, m4, m5, m6, m7] : List (BitVec 8)) ==
                   [t0, t1, t2, t3, t4, t5, t6, t7]) then
                 (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 344#64
               else
                 (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 504#64) →
      sf.status = .Running →
      sf.spAligned = true →
      sf.trace = s.trace →
      sf.sp = sp_cur →
      sf.readReg64 .x20 = msgA →
      sf.readReg64 .x21 = recvA →
      sf.readReg64 .x22 = sendA →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        (((s.sp + 80#64) ↦₆₄ okTagVec) ∗ ((s.sp + 88#64) ↦₆₄ pack64 m0 m1 m2 m3 m4 m5 m6 m7) ∗
         ((s.sp + 8#64) ↦₆₄ (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 48)) ∗
         ((s.sp + 16#64) ↦₆₄ (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 56)) ∗
         ((s.sp + 24#64) ↦₆₄ retA) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8)) ↦₈ t0) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 1#64) ↦₈ t1) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 2#64) ↦₈ t2) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 3#64) ↦₈ t3) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 4#64) ↦₈ t4) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 5#64) ↦₈ t5) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 6#64) ↦₈ t6) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 7#64) ↦₈ t7) ∗
         stackAt sp_cur computeMacStackX ∗ Frame) Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (((s.sp + 80#64) ↦₆₄ okTagVec) ∗ ((s.sp + 88#64) ↦₆₄ pack64 m0 m1 m2 m3 m4 m5 m6 m7) ∗
       ((s.sp + 8#64) ↦₆₄ w_sp8) ∗ ((s.sp + 16#64) ↦₆₄ w_sp16) ∗ ((s.sp + 24#64) ↦₆₄ w_sp24) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8)) ↦₈ t0) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 1#64) ↦₈ t1) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 2#64) ↦₈ t2) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 3#64) ↦₈ t3) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 4#64) ↦₈ t4) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 5#64) ↦₈ t5) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 6#64) ↦₈ t6) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 7#64) ↦₈ t7) ∗
       stackAt sp_cur computeMacStackX ∗ Frame) Q Qp :=
  macCompare8_sepWPp_gen computeMacStackX img ext sp_cur
    (fun v => blackBox_ok_at2_ext_x sp_cur computeMacStackX hbb_raw
      (name := verifyMacWithAddressesName)
      (k := num% (ls_off% "subtle::black_box::<u8>" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
      v (by decide) (by decide) (by fnoff_eq))
    m0 m1 m2 m3 m4 m5 m6 m7 t0 t1 t2 t3 t4 t5 t6 t7
    serPtr msgA recvA sendA retA w_sp8 w_sp16 w_sp24 len Frame s
    hF_s hsym_s hpc hrun hsp hsp_cur hx19 hx20 hx21 hx22 hx23 hx24 hcont

theorem macCompare8_full_sepWPp_gen (cmStack : Nat) (img : Obj.Image) (ext : String → Option (State → State))
    (hbb : ∀ (sp_cur : BitVec 64) (v : BitVec 8), subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + bv% (ls_off% "subtle::black_box::<u8>" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
      ((session2BlackBoxSpecX sp_cur cmStack v).inImage img))
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    (ourMac bs : List (BitVec 8))
    (sp0 serPtr msgA recvA sendA retA w_sp8 w_sp16 w_sp24 : BitVec 64)
    (Frame : SepProp) (s : State)
    (hour : ourMac.length = 8) (h8 : 8 ≤ bs.length)
    (hF_s : img.FrozenLoaded s)
    (hsym_s : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 100#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hsp_eq : s.sp = sp0 - 288#64)
    (hx19 : s.readReg64 .x19 = retA)
    (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = recvA)
    (hx22 : s.readReg64 .x22 = sendA)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (bs.length - 8))
    (hx24 : s.readReg64 .x24 = serPtr)
    (hcont : ∀ (sf : State) (v8 v16 : BitVec 64),
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      sf.pc = (if (ourMac == bs.drop (bs.length - 8)) then
                 (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 344#64
               else
                 (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 504#64) →
      sf.status = .Running →
      sf.spAligned = true →
      sf.trace = s.trace →
      sf.sp = sp0 - 288#64 →
      sf.readReg64 .x20 = msgA →
      sf.readReg64 .x21 = recvA →
      sf.readReg64 .x22 = sendA →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        (memRegion (sp0 - 208#64) 16 ∗
         (serPtr ↦ₛ bs) ∗
         ((sp0 - 280#64) ↦₆₄ v8) ∗
         ((sp0 - 272#64) ↦₆₄ v16) ∗
         ((sp0 - 264#64) ↦₆₄ retA) ∗
         stackAt (sp0 - 288#64) cmStack ∗ Frame) Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (((sp0 - 208#64) ↦₆₄ okTagVec) ∗ ((sp0 - 208#64 + 8#64) ↦ₛ ourMac) ∗
       (serPtr ↦ₛ bs.take (bs.length - 8)) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8)) ↦ₛ bs.drop (bs.length - 8)) ∗
       ((sp0 - 280#64) ↦₆₄ w_sp8) ∗ ((sp0 - 272#64) ↦₆₄ w_sp16) ∗ ((sp0 - 264#64) ↦₆₄ w_sp24) ∗
       stackAt (sp0 - 288#64) cmStack ∗ Frame) Q Qp := by
  obtain ⟨m0, m1, m2, m3, m4, m5, m6, m7, hour_eq⟩ := list_length_8_eq ourMac hour
  have htheir_len : (bs.drop (bs.length - 8)).length = 8 := by rw [List.length_drop]; omega
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, htheir_eq⟩ := list_length_8_eq _ htheir_len
  have ha80 : sp0 - 208#64 = s.sp + 80#64 := by rw [hsp_eq]; bv_arith
  have ha88 : sp0 - 208#64 + 8#64 = s.sp + 88#64 := by rw [hsp_eq]; bv_arith
  have ha8 : sp0 - 280#64 = s.sp + 8#64 := by rw [hsp_eq]; bv_arith
  have ha16 : sp0 - 272#64 = s.sp + 16#64 := by rw [hsp_eq]; bv_arith
  have ha24 : sp0 - 264#64 = s.sp + 24#64 := by rw [hsp_eq]; bv_arith
  rw [hour_eq, htheir_eq, pointsToBytes_pack64, pointsToBytes_8_bytes, ha88, ha80, ha8, ha16, ha24]
  apply SepWPp.weaken_pre (P' :=
    ((s.sp + 80#64) ↦₆₄ okTagVec) ∗ ((s.sp + 88#64) ↦₆₄ pack64 m0 m1 m2 m3 m4 m5 m6 m7) ∗
    ((s.sp + 8#64) ↦₆₄ w_sp8) ∗ ((s.sp + 16#64) ↦₆₄ w_sp16) ∗ ((s.sp + 24#64) ↦₆₄ w_sp24) ∗
    ((serPtr + BitVec.ofNat 64 (bs.length - 8)) ↦₈ t0) ∗
    ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 1#64) ↦₈ t1) ∗
    ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 2#64) ↦₈ t2) ∗
    ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 3#64) ↦₈ t3) ∗
    ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 4#64) ↦₈ t4) ∗
    ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 5#64) ↦₈ t5) ∗
    ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 6#64) ↦₈ t6) ∗
    ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 7#64) ↦₈ t7) ∗
    stackAt (sp0 - 288#64) cmStack ∗
    ((serPtr ↦ₛ bs.take (bs.length - 8)) ∗ Frame)) (Entails.of_eq (by ac_rfl))
  refine macCompare8_sepWPp_gen cmStack img ext (sp0 - 288#64) (hbb (sp0 - 288#64)) m0 m1 m2 m3 m4 m5 m6 m7 t0 t1 t2 t3 t4 t5 t6 t7
    serPtr msgA recvA sendA retA w_sp8 w_sp16 w_sp24 bs.length
    ((serPtr ↦ₛ bs.take (bs.length - 8)) ∗ Frame) s hF_s hsym_s hpc hrun hsp hsp_eq hx19 hx20 hx21 hx22 hx23 hx24
    fun sf hF_f hsym_f hpc_f hrun_f hsp_f htr_f hsp_eq_f hx20_f hx21_f hx22_f hx29_f hvregs_f => ?_
  rw [← ha88, ← ha80, ← ha8, ← ha16, ← ha24]
  have htheir_back :
      ((serPtr + BitVec.ofNat 64 (bs.length - 8)) ↦₈ t0) ∗
      ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 1#64) ↦₈ t1) ∗
      ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 2#64) ↦₈ t2) ∗
      ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 3#64) ↦₈ t3) ∗
      ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 4#64) ↦₈ t4) ∗
      ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 5#64) ↦₈ t5) ∗
      ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 6#64) ↦₈ t6) ∗
      ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 7#64) ↦₈ t7) =
      ((serPtr + BitVec.ofNat 64 (bs.length - 8)) ↦ₛ bs.drop (bs.length - 8)) := by
    rw [htheir_eq, pointsToBytes_8_bytes]
  apply SepWPp.weaken_pre (P' :=
    (((sp0 - 208#64) ↦₆₄ okTagVec) ∗ ((sp0 - 208#64 + 8#64) ↦₆₄ pack64 m0 m1 m2 m3 m4 m5 m6 m7)) ∗
    (((serPtr ↦ₛ bs.take (bs.length - 8)) ∗
      (((serPtr + BitVec.ofNat 64 (bs.length - 8)) ↦₈ t0) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 1#64) ↦₈ t1) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 2#64) ↦₈ t2) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 3#64) ↦₈ t3) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 4#64) ↦₈ t4) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 5#64) ↦₈ t5) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 6#64) ↦₈ t6) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 7#64) ↦₈ t7))) ∗
     ((sp0 - 280#64) ↦₆₄ (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 48)) ∗
     ((sp0 - 272#64) ↦₆₄ (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 56)) ∗
     ((sp0 - 264#64) ↦₆₄ retA) ∗
     stackAt (sp0 - 288#64) cmStack ∗ Frame)) (Entails.of_eq (by ac_rfl))
  rw [htheir_back, ← pointsToBytes_serialized_split serPtr bs h8]
  apply SepWPp.weaken_pre
    (sepConj_mono_left (memRegion_16_of_two_words (sp0 - 208#64) okTagVec
      (pack64 m0 m1 m2 m3 m4 m5 m6 m7)))
  rw [← hour_eq, ← htheir_eq] at hpc_f
  exact hcont sf (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 48)
    (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 56)
    hF_f hsym_f hpc_f hrun_f hsp_f htr_f hsp_eq_f hx20_f hx21_f hx22_f hx29_f hvregs_f

theorem macCompare8_full_sepWPp_ext_x (img : Obj.Image) (ext : String → Option (State → State))
    (hbb_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr blackBoxName)
      ((withStack blackBoxU8Spec extHookStack).inImage img))
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    (ourMac bs : List (BitVec 8))
    (sp0 serPtr msgA recvA sendA retA w_sp8 w_sp16 w_sp24 : BitVec 64)
    (Frame : SepProp) (s : State)
    (hour : ourMac.length = 8) (h8 : 8 ≤ bs.length)
    (hF_s : img.FrozenLoaded s)
    (hsym_s : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 100#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hsp_eq : s.sp = sp0 - 288#64)
    (hx19 : s.readReg64 .x19 = retA)
    (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = recvA)
    (hx22 : s.readReg64 .x22 = sendA)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (bs.length - 8))
    (hx24 : s.readReg64 .x24 = serPtr)
    (hcont : ∀ (sf : State) (v8 v16 : BitVec 64),
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      sf.pc = (if (ourMac == bs.drop (bs.length - 8)) then
                 (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 344#64
               else
                 (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 504#64) →
      sf.status = .Running →
      sf.spAligned = true →
      sf.trace = s.trace →
      sf.sp = sp0 - 288#64 →
      sf.readReg64 .x20 = msgA →
      sf.readReg64 .x21 = recvA →
      sf.readReg64 .x22 = sendA →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        (memRegion (sp0 - 208#64) 16 ∗
         (serPtr ↦ₛ bs) ∗
         ((sp0 - 280#64) ↦₆₄ v8) ∗
         ((sp0 - 272#64) ↦₆₄ v16) ∗
         ((sp0 - 264#64) ↦₆₄ retA) ∗
         stackAt (sp0 - 288#64) computeMacStackX ∗ Frame) Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (((sp0 - 208#64) ↦₆₄ okTagVec) ∗ ((sp0 - 208#64 + 8#64) ↦ₛ ourMac) ∗
       (serPtr ↦ₛ bs.take (bs.length - 8)) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8)) ↦ₛ bs.drop (bs.length - 8)) ∗
       ((sp0 - 280#64) ↦₆₄ w_sp8) ∗ ((sp0 - 272#64) ↦₆₄ w_sp16) ∗ ((sp0 - 264#64) ↦₆₄ w_sp24) ∗
       stackAt (sp0 - 288#64) computeMacStackX ∗ Frame) Q Qp :=
  macCompare8_full_sepWPp_gen computeMacStackX img ext
    (fun sp_cur v => blackBox_ok_at2_ext_x sp_cur computeMacStackX hbb_raw
      (name := verifyMacWithAddressesName)
      (k := num% (ls_off% "subtle::black_box::<u8>" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
      v (by decide) (by decide) (by fnoff_eq))
    ourMac bs sp0 serPtr msgA recvA sendA retA w_sp8 w_sp16 w_sp24 Frame s
    hour h8 hF_s hsym_s hpc hrun hsp hsp_eq hx19 hx20 hx21 hx22 hx23 hx24 hcont

/-! ## Stacked `CliExt.blackBoxSpec` corollaries -/

theorem blackBoxU8_of_cliBlackBox {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr CryptoVerification.SignalSession.CliExt.blackBoxSpec) :
    subroutine_ok P addr (withStack blackBoxU8Spec extHookStack) := by
  apply subroutine_ok.of_codeLoaded
  intro v R s0 hpc hrun hpre hal _
  refine h.mono_outcome v R s0 hpc hrun hpre hal (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [CryptoVerification.SignalSession.CliExt.blackBoxSpec,
      CryptoVerification.SignalSession.CliExt.withStack, withStack, blackBoxU8Spec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hw0, htr⟩, hR⟩
    refine ⟨⟨?_, htr⟩, hR⟩
    have h8 : ((sf.readReg64 .x0).setWidth 32).setWidth 8 =
        ((v.setWidth 8).zeroExtend 32).setWidth 8 := congrArg (BitVec.setWidth 8) hw0
    simpa using h8
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem blackBoxU8_inImage_ok_ext32 (img : Obj.Image) {ext : String → Option (State → State)}
    (h_bb : HookSat ext blackBoxName CryptoVerification.SignalSession.CliExt.blackBoxSpec) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr blackBoxName)
      ((withStack blackBoxU8Spec extHookStack).inImage img) := by
  refine subroutine_ok_inImage_of_subroutine_ok img (blackBoxU8_of_cliBlackBox ?_)
  have h := hook_ok_at (P := libsignalSessionCode) (b := img.base) (k := 0)
    (ls_stub% "subtle::black_box::<u8>") (Nat.add_zero _) (by decide)
    (ls_hook% "subtle::black_box::<u8>")
    (by simp [Rust.isPanicSymbol]) h_bb
  simpa only [BitVec.add_zero] using h

theorem blackBox_ok_at2_ext32 {img : Obj.Image} {ext : String → Option (State → State)}
    (sp_cur : BitVec 64) (n : Nat)
    (h_bb : HookSat ext blackBoxName CryptoVerification.SignalSession.CliExt.blackBoxSpec)
    {name : String} {k : Nat} (v : BitVec 8)
    (hn : extHookStack ≤ n := by decide) (hbound : n < 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "subtle::black_box::<u8>" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((session2BlackBoxSpecX sp_cur n v).inImage img) :=
  blackBox_ok_at2_ext_x sp_cur n (blackBoxU8_inImage_ok_ext32 img h_bb) v hn hbound hk

theorem ctEqLoop_sepWPp_ext32 (img : Obj.Image) (ext : String → Option (State → State))
    (sp_cur : BitVec 64)
    (h_bb : HookSat ext blackBoxName CryptoVerification.SignalSession.CliExt.blackBoxSpec)
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop} :
    ∀ (bs1 bs2 : List (BitVec 8)) (p1 p2 : BitVec 64) (acc : Bool) (Frame : SepProp) (s : State),
      bs1 ≠ [] →
      bs1.length = bs2.length →
      bs1.length < 2 ^ 64 →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 412#64 →
      s.status = .Running →
      s.spAligned = true →
      s.sp = sp_cur →
      s.readReg64 .x25 = p1 →
      s.readReg64 .x23 = p2 →
      s.readReg64 .x24 = BitVec.ofNat 64 bs1.length →
      (s.readReg64 .x22).setWidth 8 = (if acc then 1#8 else 0#8) →
      (∀ sf,
        img.FrozenLoaded sf →
        sf.symtab = img.symtab →
        sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 444#64 →
        sf.status = .Running →
        sf.spAligned = true →
        sf.trace = s.trace →
        sf.sp = sp_cur →
        sf.readReg64 .x19 = s.readReg64 .x19 →
        sf.readReg64 .x20 = s.readReg64 .x20 →
        sf.readReg64 .x21 = s.readReg64 .x21 →
        sf.readReg64 .x26 = s.readReg64 .x26 →
        sf.readReg64 .x27 = s.readReg64 .x27 →
        sf.readReg64 .x28 = s.readReg64 .x28 →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        (sf.readReg64 .x22).setWidth 8 = (if (acc && (bs1 == bs2)) then 1#8 else 0#8) →
        SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
          ((p1 ↦ₛ bs1) ∗ (p2 ↦ₛ bs2) ∗ stackAt sp_cur computeMacStackX ∗ Frame) Q Qp) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s
        ((p1 ↦ₛ bs1) ∗ (p2 ↦ₛ bs2) ∗ stackAt sp_cur computeMacStackX ∗ Frame) Q Qp :=
  ctEqLoop_sepWPp_ext_x img ext sp_cur (blackBoxU8_inImage_ok_ext32 img h_bb)

theorem macCompare8_sepWPp_ext32 (img : Obj.Image) (ext : String → Option (State → State))
    (sp_cur : BitVec 64)
    (h_bb : HookSat ext blackBoxName CryptoVerification.SignalSession.CliExt.blackBoxSpec)
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    (m0 m1 m2 m3 m4 m5 m6 m7 t0 t1 t2 t3 t4 t5 t6 t7 : BitVec 8)
    (serPtr msgA recvA sendA retA w_sp8 w_sp16 w_sp24 : BitVec 64)
    (len : Nat) (Frame : SepProp) (s : State)
    (hF_s : img.FrozenLoaded s)
    (hsym_s : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 100#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hsp_cur : s.sp = sp_cur)
    (hx19 : s.readReg64 .x19 = retA)
    (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = recvA)
    (hx22 : s.readReg64 .x22 = sendA)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (len - 8))
    (hx24 : s.readReg64 .x24 = serPtr)
    (hcont : ∀ sf : State,
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      sf.pc = (if (([m0, m1, m2, m3, m4, m5, m6, m7] : List (BitVec 8)) ==
                   [t0, t1, t2, t3, t4, t5, t6, t7]) then
                 (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 344#64
               else
                 (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 504#64) →
      sf.status = .Running →
      sf.spAligned = true →
      sf.trace = s.trace →
      sf.sp = sp_cur →
      sf.readReg64 .x20 = msgA →
      sf.readReg64 .x21 = recvA →
      sf.readReg64 .x22 = sendA →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        (((s.sp + 80#64) ↦₆₄ okTagVec) ∗ ((s.sp + 88#64) ↦₆₄ pack64 m0 m1 m2 m3 m4 m5 m6 m7) ∗
         ((s.sp + 8#64) ↦₆₄ (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 48)) ∗
         ((s.sp + 16#64) ↦₆₄ (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 56)) ∗
         ((s.sp + 24#64) ↦₆₄ retA) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8)) ↦₈ t0) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 1#64) ↦₈ t1) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 2#64) ↦₈ t2) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 3#64) ↦₈ t3) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 4#64) ↦₈ t4) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 5#64) ↦₈ t5) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 6#64) ↦₈ t6) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 7#64) ↦₈ t7) ∗
         stackAt sp_cur computeMacStackX ∗ Frame) Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (((s.sp + 80#64) ↦₆₄ okTagVec) ∗ ((s.sp + 88#64) ↦₆₄ pack64 m0 m1 m2 m3 m4 m5 m6 m7) ∗
       ((s.sp + 8#64) ↦₆₄ w_sp8) ∗ ((s.sp + 16#64) ↦₆₄ w_sp16) ∗ ((s.sp + 24#64) ↦₆₄ w_sp24) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8)) ↦₈ t0) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 1#64) ↦₈ t1) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 2#64) ↦₈ t2) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 3#64) ↦₈ t3) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 4#64) ↦₈ t4) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 5#64) ↦₈ t5) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 6#64) ↦₈ t6) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 7#64) ↦₈ t7) ∗
       stackAt sp_cur computeMacStackX ∗ Frame) Q Qp :=
  macCompare8_sepWPp_ext_x img ext sp_cur (blackBoxU8_inImage_ok_ext32 img h_bb)
    m0 m1 m2 m3 m4 m5 m6 m7 t0 t1 t2 t3 t4 t5 t6 t7
    serPtr msgA recvA sendA retA w_sp8 w_sp16 w_sp24 len Frame s
    hF_s hsym_s hpc hrun hsp hsp_cur hx19 hx20 hx21 hx22 hx23 hx24 hcont

theorem macCompare8_full_sepWPp_ext32 (img : Obj.Image) (ext : String → Option (State → State))
    (h_bb : HookSat ext blackBoxName CryptoVerification.SignalSession.CliExt.blackBoxSpec)
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    (ourMac bs : List (BitVec 8))
    (sp0 serPtr msgA recvA sendA retA w_sp8 w_sp16 w_sp24 : BitVec 64)
    (Frame : SepProp) (s : State)
    (hour : ourMac.length = 8) (h8 : 8 ≤ bs.length)
    (hF_s : img.FrozenLoaded s)
    (hsym_s : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 100#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hsp_eq : s.sp = sp0 - 288#64)
    (hx19 : s.readReg64 .x19 = retA)
    (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = recvA)
    (hx22 : s.readReg64 .x22 = sendA)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (bs.length - 8))
    (hx24 : s.readReg64 .x24 = serPtr)
    (hcont : ∀ (sf : State) (v8 v16 : BitVec 64),
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      sf.pc = (if (ourMac == bs.drop (bs.length - 8)) then
                 (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 344#64
               else
                 (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName + 504#64) →
      sf.status = .Running →
      sf.spAligned = true →
      sf.trace = s.trace →
      sf.sp = sp0 - 288#64 →
      sf.readReg64 .x20 = msgA →
      sf.readReg64 .x21 = recvA →
      sf.readReg64 .x22 = sendA →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        (memRegion (sp0 - 208#64) 16 ∗
         (serPtr ↦ₛ bs) ∗
         ((sp0 - 280#64) ↦₆₄ v8) ∗
         ((sp0 - 272#64) ↦₆₄ v16) ∗
         ((sp0 - 264#64) ↦₆₄ retA) ∗
         stackAt (sp0 - 288#64) computeMacStackX ∗ Frame) Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (((sp0 - 208#64) ↦₆₄ okTagVec) ∗ ((sp0 - 208#64 + 8#64) ↦ₛ ourMac) ∗
       (serPtr ↦ₛ bs.take (bs.length - 8)) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8)) ↦ₛ bs.drop (bs.length - 8)) ∗
       ((sp0 - 280#64) ↦₆₄ w_sp8) ∗ ((sp0 - 272#64) ↦₆₄ w_sp16) ∗ ((sp0 - 264#64) ↦₆₄ w_sp24) ∗
       stackAt (sp0 - 288#64) computeMacStackX ∗ Frame) Q Qp :=
  macCompare8_full_sepWPp_ext_x img ext (blackBoxU8_inImage_ok_ext32 img h_bb)
    ourMac bs sp0 serPtr msgA recvA sendA retA w_sp8 w_sp16 w_sp24 Frame s
    hour h8 hF_s hsym_s hpc hrun hsp hsp_eq hx19 hx20 hx21 hx22 hx23 hx24 hcont

/-! ## Relocatable `[LibsignalPlacement]` MAC comparison lemmas -/

theorem blackBox_placed_ok {prog : Program} {addr : BitVec 64}
    (sp_cur : BitVec 64) (n : Nat)
    (hbb_raw : subroutine_ok prog addr blackBoxSpec) (v : BitVec 8) :
    subroutine_ok prog addr (session2BlackBoxSpecX sp_cur n v) := by
  have h := session2BlackBox_of_blackBox hbb_raw v
  apply subroutine_ok.of_codeLoaded
  intro _ R s0 hpc hrun hpre hsp _
  simp only [session2BlackBoxSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hv, _⟩, hmem⟩
  have hpre' : s0.mem ⊨ (session2BlackBoxSpec v).pre () s0 ∗ (stackAt sp_cur n ∗ R) := by
    simp only [session2BlackBoxSpec, satisfies_pure_sepConj]
    exact ⟨hv, hmem⟩
  refine h.mono_outcome () (stackAt sp_cur n ∗ R) s0 hpc hrun hpre' hsp (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    simp only [session2BlackBoxSpec, session2BlackBoxSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hx0, htr⟩, hmem'⟩
    exact ⟨⟨by rw [hx0]; bv_bits, htr⟩, hmem'⟩
  · dsimp only [session2BlackBoxSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · dsimp only [session2BlackBoxSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · dsimp only [session2BlackBoxSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1

theorem blackBox_placed_ok_x {prog : Program} {addr : BitVec 64}
    (sp_cur : BitVec 64) (n : Nat)
    (hbb_raw : subroutine_ok prog addr (withStack blackBoxU8Spec extHookStack))
    (v : BitVec 8) (hn : extHookStack ≤ n := by decide) (hbound : n < 2 ^ 64 := by decide) :
    subroutine_ok prog addr (session2BlackBoxSpecX sp_cur n v) := by
  have hsplit := stackAt_split_ge sp_cur n extHookStack hn hbound
  apply subroutine_ok.of_codeLoaded
  intro _ R s0 hpc hrun hpre hsp _
  simp only [session2BlackBoxSpecX, hsplit, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hv, hsp_eq⟩, hmem⟩
  have hpre' : s0.mem ⊨ (withStack blackBoxU8Spec extHookStack).pre (s0.readReg64 .x0) s0 ∗
      (memRegion (sp_cur - BitVec.ofNat 64 n) (n - extHookStack) ∗ R) := by
    simp only [withStack, blackBoxU8Spec, hsp_eq, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨trivial, hmem⟩
  refine hbb_raw.mono_outcome (s0.readReg64 .x0)
    (memRegion (sp_cur - BitVec.ofNat 64 n) (n - extHookStack) ∗ R) s0 hpc hrun hpre' hsp (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    simp only [withStack, blackBoxU8Spec, session2BlackBoxSpecX, hsp_eq, hsplit,
      sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hx0, htr⟩, hmem'⟩
    exact ⟨⟨by rw [hx0, hv], htr⟩, hmem'⟩
  · dsimp only [withStack, blackBoxU8Spec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · dsimp only [withStack, blackBoxU8Spec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · dsimp only [withStack, blackBoxU8Spec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1

set_option maxHeartbeats 1600000 in
theorem ctEqLoop_sepWPp_placed_gen [LibsignalPlacement] (cmStack : Nat)
    (H : String → Option (State → State))
    (sp_cur : BitVec 64)
    (hbb : ∀ v : BitVec 8, subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsρ lsBlackBoxU8Sym) (session2BlackBoxSpecX sp_cur cmStack v))
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop} :
    ∀ (bs1 bs2 : List (BitVec 8)) (p1 p2 : BitVec 64) (acc : Bool) (Frame : SepProp) (s : State),
      bs1 ≠ [] →
      bs1.length = bs2.length →
      bs1.length < 2 ^ 64 →
      s.pc = (blkPl_62).base + 412#64 →
      s.status = .Running →
      s.spAligned = true →
      s.sp = sp_cur →
      s.readReg64 .x25 = p1 →
      s.readReg64 .x23 = p2 →
      s.readReg64 .x24 = BitVec.ofNat 64 bs1.length →
      (s.readReg64 .x22).setWidth 8 = (if acc then 1#8 else 0#8) →
      (∀ sf,
        sf.pc = (blkPl_62).base + 444#64 →
        sf.status = .Running →
        sf.spAligned = true →
        sf.trace = s.trace →
        sf.sp = sp_cur →
        sf.readReg64 .x19 = s.readReg64 .x19 →
        sf.readReg64 .x20 = s.readReg64 .x20 →
        sf.readReg64 .x21 = s.readReg64 .x21 →
        sf.readReg64 .x26 = s.readReg64 .x26 →
        sf.readReg64 .x27 = s.readReg64 .x27 →
        sf.readReg64 .x28 = s.readReg64 .x28 →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        (sf.readReg64 .x22).setWidth 8 = (if (acc && (bs1 == bs2)) then 1#8 else 0#8) →
        SepWPp ((blkPC_62).rebase (blkPl_62).base H) ret sf
          ((p1 ↦ₛ bs1) ∗ (p2 ↦ₛ bs2) ∗ stackAt sp_cur cmStack ∗ Frame) Q Qp) →
      SepWPp ((blkPC_62).rebase (blkPl_62).base H) ret s
        ((p1 ↦ₛ bs1) ∗ (p2 ↦ₛ bs2) ∗ stackAt sp_cur cmStack ∗ Frame) Q Qp := by
  intro bs1
  induction bs1 with
  | nil => intro _ _ _ _ _ _ hne; exact absurd rfl hne
  | cons b1 bs1' ih =>
    intro bs2 p1 p2 acc Frame s _ hlen hlt hpc hrun hsp hsp_eq hx25 hx23 hx24 hx22 hcont
    have hsp_orig := hsp
    simp only [wp_norm, arm64_norm, hsp_eq] at hsp
    cases bs2 with
    | nil => simp at hlen
    | cons b2 bs2' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [pointsToBytes_cons, sepConj_assoc]
      have hbb_step := hbb (if b1 == b2 then 1#8 else 0#8)
      apply SepWPp.of_sepWP (mid := lsρ lsBlackBoxU8Sym)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      apply SepWPp.of_sepWP (mid := (blkPl_62).base + 432#64)
      wp_call hbb_step ()
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      cases bs1' with
      | nil =>
        cases bs2' with
        | nil =>
          have hne_1 : (BitVec.ofNat 64 [b1].length != 1#64) = false := rfl
          apply SepWPp.of_sepWP (mid := (blkPl_62).base + 444#64)
          wp_steps
          apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          have hbeq : (([b1] : List (BitVec 8)) == [b2]) = (b1 == b2) := by
            simp
          refine SepWPp.weaken_pre ?_
            (hcont _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [State.spAligned, arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by rw [hbeq, Bool.and_comm acc]; simp only [arm64_norm, *]))
          simp only [pointsToBytes_cons, sepConj_assoc]
          exact Entails.of_eq (by ac_rfl)
        | cons _ _ => simp at hlen
      | cons b1' bs1'' =>
        have hlen' : (b1' :: bs1'').length = bs2'.length := hlen
        have hlt' : (b1' :: bs1'').length < 2 ^ 64 := by simp only [List.length_cons] at hlt ⊢; omega
        have hsub := ofNat_cons_sub_one b1 (b1' :: bs1'') hlt
        have hne_z := ofNat_cons_cons_bne_one b1 b1' bs1'' hlt
        apply SepWPp.of_sepWP (mid := (blkPl_62).base + 412#64)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine SepWPp.weaken_pre ?_
          (ih bs2' (p1 + 1#64) (p2 + 1#64) (acc && (b1 == b2)) (p1 ↦₈ b1 ∗ p2 ↦₈ b2 ∗ Frame) _
            (by simp) hlen' hlt'
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [State.spAligned, arm64_norm, *])
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by rw [Bool.and_comm acc]; simp only [arm64_norm, *])
            fun sf' hpc_f hrun_f hsp_f htr_f hsp_eq' hx19_f hx20_f hx21_f hx26_f hx27_f hx28_f hx29_f hvregs_f hx22_f => ?_)
        · exact Entails.of_eq (by ac_rfl)
        · have hbeq_cons : ((b1 :: b1' :: bs1'') == (b2 :: bs2')) = ((b1 == b2) && ((b1' :: bs1'') == bs2')) := rfl
          have hbool_assoc : ((acc && (b1 == b2)) && ((b1' :: bs1'') == bs2')) =
              (acc && ((b1 :: b1' :: bs1'') == (b2 :: bs2'))) := by
            rw [hbeq_cons, Bool.and_assoc]
          rw [hbool_assoc] at hx22_f
          refine SepWPp.weaken_pre ?_
            (hcont sf' hpc_f hrun_f hsp_f
              (by simp only [arm64_norm, *]) hsp_eq'
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hx22_f)
          simp only [pointsToBytes_cons, sepConj_assoc]
          exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1600000 in
theorem macCompare8_sepWPp_placed_gen [LibsignalPlacement] (cmStack : Nat)
    (H : String → Option (State → State))
    (sp_cur : BitVec 64)
    (hbb : ∀ v : BitVec 8, subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsρ lsBlackBoxU8Sym) (session2BlackBoxSpecX sp_cur cmStack v))
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    (m0 m1 m2 m3 m4 m5 m6 m7 t0 t1 t2 t3 t4 t5 t6 t7 : BitVec 8)
    (serPtr msgA recvA sendA retA w_sp8 w_sp16 w_sp24 : BitVec 64)
    (len : Nat) (Frame : SepProp) (s : State)
    (hpc : s.pc = (blkPl_62).base + 100#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hsp_cur : s.sp = sp_cur)
    (hx19 : s.readReg64 .x19 = retA)
    (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = recvA)
    (hx22 : s.readReg64 .x22 = sendA)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (len - 8))
    (hx24 : s.readReg64 .x24 = serPtr)
    (hcont : ∀ sf : State,
      sf.pc = (if (([m0, m1, m2, m3, m4, m5, m6, m7] : List (BitVec 8)) ==
                   [t0, t1, t2, t3, t4, t5, t6, t7]) then
                 (blkPl_62).base + 344#64
               else
                 (blkPl_62).base + 504#64) →
      sf.status = .Running →
      sf.spAligned = true →
      sf.trace = s.trace →
      sf.sp = sp_cur →
      sf.readReg64 .x20 = msgA →
      sf.readReg64 .x21 = recvA →
      sf.readReg64 .x22 = sendA →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp ((blkPC_62).rebase (blkPl_62).base H) ret sf
        (((s.sp + 80#64) ↦₆₄ okTagVec) ∗ ((s.sp + 88#64) ↦₆₄ pack64 m0 m1 m2 m3 m4 m5 m6 m7) ∗
         ((s.sp + 8#64) ↦₆₄ (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 48)) ∗
         ((s.sp + 16#64) ↦₆₄ (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 56)) ∗
         ((s.sp + 24#64) ↦₆₄ retA) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8)) ↦₈ t0) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 1#64) ↦₈ t1) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 2#64) ↦₈ t2) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 3#64) ↦₈ t3) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 4#64) ↦₈ t4) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 5#64) ↦₈ t5) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 6#64) ↦₈ t6) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 7#64) ↦₈ t7) ∗
         stackAt sp_cur cmStack ∗ Frame) Q Qp) :
    SepWPp ((blkPC_62).rebase (blkPl_62).base H) ret s
      (((s.sp + 80#64) ↦₆₄ okTagVec) ∗ ((s.sp + 88#64) ↦₆₄ pack64 m0 m1 m2 m3 m4 m5 m6 m7) ∗
       ((s.sp + 8#64) ↦₆₄ w_sp8) ∗ ((s.sp + 16#64) ↦₆₄ w_sp16) ∗ ((s.sp + 24#64) ↦₆₄ w_sp24) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8)) ↦₈ t0) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 1#64) ↦₈ t1) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 2#64) ↦₈ t2) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 3#64) ↦₈ t3) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 4#64) ↦₈ t4) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 5#64) ↦₈ t5) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 6#64) ↦₈ t6) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 7#64) ↦₈ t7) ∗
       stackAt sp_cur cmStack ∗ Frame) Q Qp := by
  have hsp_orig := hsp
  simp only [wp_norm, arm64_norm, hsp_cur] at hsp
  have hbb0 := hbb (if t0 == m0 then 1#8 else 0#8)
  have hbb1 := hbb (if t1 == m1 then 1#8 else 0#8)
  have hbb2 := hbb (if t2 == m2 then 1#8 else 0#8)
  have hbb3 := hbb (if t3 == m3 then 1#8 else 0#8)
  have hbb4 := hbb (if t4 == m4 then 1#8 else 0#8)
  have hbb5 := hbb (if t5 == m5 then 1#8 else 0#8)
  have hbb6 := hbb (if t6 == m6 then 1#8 else 0#8)
  have hbb7 := hbb (if t7 == m7 then 1#8 else 0#8)
  have hbb8 := hbb
    (if (([m0, m1, m2, m3, m4, m5, m6, m7] : List (BitVec 8)) ==
         [t0, t1, t2, t3, t4, t5, t6, t7]) then 1#8 else 0#8)
  clear hbb
  apply SepWPp.of_sepWP (mid := lsρ lsBlackBoxU8Sym)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.of_sepWP (mid := (blkPl_62).base + 168#64)
  wp_call hbb0 ()
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.of_sepWP (mid := lsρ lsBlackBoxU8Sym)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.of_sepWP (mid := (blkPl_62).base + 188#64)
  wp_call hbb1 ()
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.of_sepWP (mid := lsρ lsBlackBoxU8Sym)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.of_sepWP (mid := (blkPl_62).base + 208#64)
  wp_call hbb2 ()
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.of_sepWP (mid := lsρ lsBlackBoxU8Sym)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.of_sepWP (mid := (blkPl_62).base + 228#64)
  wp_call hbb3 ()
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.of_sepWP (mid := lsρ lsBlackBoxU8Sym)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.of_sepWP (mid := (blkPl_62).base + 252#64)
  wp_call hbb4 ()
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.of_sepWP (mid := lsρ lsBlackBoxU8Sym)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.of_sepWP (mid := (blkPl_62).base + 272#64)
  wp_call hbb5 ()
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.of_sepWP (mid := lsρ lsBlackBoxU8Sym)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.of_sepWP (mid := (blkPl_62).base + 296#64)
  wp_call hbb6 ()
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.of_sepWP (mid := lsρ lsBlackBoxU8Sym)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.of_sepWP (mid := (blkPl_62).base + 324#64)
  wp_call hbb7 ()
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.of_sepWP (mid := lsρ lsBlackBoxU8Sym)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.of_sepWP (mid := (blkPl_62).base + 336#64)
  wp_call hbb8 ()
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  cases hmac : (([m0, m1, m2, m3, m4, m5, m6, m7] : List (BitVec 8)) ==
                [t0, t1, t2, t3, t4, t5, t6, t7])
  · simp only [hmac, Bool.false_eq_true, ↓reduceIte] at *
    apply SepWPp.of_sepWP (mid := (blkPl_62).base + 504#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPp.weaken_pre ?_
      (hcont _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [State.spAligned, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]))
    rw [hsp_cur]
    exact Entails.of_eq (by ac_rfl)
  · simp only [hmac, ↓reduceIte] at *
    apply SepWPp.of_sepWP (mid := (blkPl_62).base + 344#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPp.weaken_pre ?_
      (hcont _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [State.spAligned, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]))
    rw [hsp_cur]
    exact Entails.of_eq (by ac_rfl)

theorem macCompare8_full_sepWPp_placed_gen [LibsignalPlacement] (cmStack : Nat)
    (H : String → Option (State → State))
    (hbb : ∀ (sp_cur : BitVec 64) (v : BitVec 8), subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsρ lsBlackBoxU8Sym) (session2BlackBoxSpecX sp_cur cmStack v))
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    (ourMac bs : List (BitVec 8))
    (sp0 serPtr msgA recvA sendA retA w_sp8 w_sp16 w_sp24 : BitVec 64)
    (Frame : SepProp) (s : State)
    (hour : ourMac.length = 8) (h8 : 8 ≤ bs.length)
    (hpc : s.pc = (blkPl_62).base + 100#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hsp_eq : s.sp = sp0 - 288#64)
    (hx19 : s.readReg64 .x19 = retA)
    (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = recvA)
    (hx22 : s.readReg64 .x22 = sendA)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (bs.length - 8))
    (hx24 : s.readReg64 .x24 = serPtr)
    (hcont : ∀ (sf : State) (v8 v16 : BitVec 64),
      sf.pc = (if (ourMac == bs.drop (bs.length - 8)) then
                 (blkPl_62).base + 344#64
               else
                 (blkPl_62).base + 504#64) →
      sf.status = .Running →
      sf.spAligned = true →
      sf.trace = s.trace →
      sf.sp = sp0 - 288#64 →
      sf.readReg64 .x20 = msgA →
      sf.readReg64 .x21 = recvA →
      sf.readReg64 .x22 = sendA →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp ((blkPC_62).rebase (blkPl_62).base H) ret sf
        (memRegion (sp0 - 208#64) 16 ∗
         (serPtr ↦ₛ bs) ∗
         ((sp0 - 280#64) ↦₆₄ v8) ∗
         ((sp0 - 272#64) ↦₆₄ v16) ∗
         ((sp0 - 264#64) ↦₆₄ retA) ∗
         stackAt (sp0 - 288#64) cmStack ∗ Frame) Q Qp) :
    SepWPp ((blkPC_62).rebase (blkPl_62).base H) ret s
      (((sp0 - 208#64) ↦₆₄ okTagVec) ∗ ((sp0 - 208#64 + 8#64) ↦ₛ ourMac) ∗
       (serPtr ↦ₛ bs.take (bs.length - 8)) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8)) ↦ₛ bs.drop (bs.length - 8)) ∗
       ((sp0 - 280#64) ↦₆₄ w_sp8) ∗ ((sp0 - 272#64) ↦₆₄ w_sp16) ∗ ((sp0 - 264#64) ↦₆₄ w_sp24) ∗
       stackAt (sp0 - 288#64) cmStack ∗ Frame) Q Qp := by
  obtain ⟨m0, m1, m2, m3, m4, m5, m6, m7, hour_eq⟩ := list_length_8_eq ourMac hour
  have htheir_len : (bs.drop (bs.length - 8)).length = 8 := by rw [List.length_drop]; omega
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, htheir_eq⟩ := list_length_8_eq _ htheir_len
  have ha80 : sp0 - 208#64 = s.sp + 80#64 := by rw [hsp_eq]; bv_arith
  have ha88 : sp0 - 208#64 + 8#64 = s.sp + 88#64 := by rw [hsp_eq]; bv_arith
  have ha8 : sp0 - 280#64 = s.sp + 8#64 := by rw [hsp_eq]; bv_arith
  have ha16 : sp0 - 272#64 = s.sp + 16#64 := by rw [hsp_eq]; bv_arith
  have ha24 : sp0 - 264#64 = s.sp + 24#64 := by rw [hsp_eq]; bv_arith
  rw [hour_eq, htheir_eq, pointsToBytes_pack64, pointsToBytes_8_bytes, ha88, ha80, ha8, ha16, ha24]
  apply SepWPp.weaken_pre (P' :=
    ((s.sp + 80#64) ↦₆₄ okTagVec) ∗ ((s.sp + 88#64) ↦₆₄ pack64 m0 m1 m2 m3 m4 m5 m6 m7) ∗
    ((s.sp + 8#64) ↦₆₄ w_sp8) ∗ ((s.sp + 16#64) ↦₆₄ w_sp16) ∗ ((s.sp + 24#64) ↦₆₄ w_sp24) ∗
    ((serPtr + BitVec.ofNat 64 (bs.length - 8)) ↦₈ t0) ∗
    ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 1#64) ↦₈ t1) ∗
    ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 2#64) ↦₈ t2) ∗
    ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 3#64) ↦₈ t3) ∗
    ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 4#64) ↦₈ t4) ∗
    ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 5#64) ↦₈ t5) ∗
    ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 6#64) ↦₈ t6) ∗
    ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 7#64) ↦₈ t7) ∗
    stackAt (sp0 - 288#64) cmStack ∗
    ((serPtr ↦ₛ bs.take (bs.length - 8)) ∗ Frame)) (Entails.of_eq (by ac_rfl))
  refine macCompare8_sepWPp_placed_gen cmStack H (sp0 - 288#64) (hbb (sp0 - 288#64)) m0 m1 m2 m3 m4 m5 m6 m7 t0 t1 t2 t3 t4 t5 t6 t7
    serPtr msgA recvA sendA retA w_sp8 w_sp16 w_sp24 bs.length
    ((serPtr ↦ₛ bs.take (bs.length - 8)) ∗ Frame) s hpc hrun hsp hsp_eq hx19 hx20 hx21 hx22 hx23 hx24
    fun sf hpc_f hrun_f hsp_f htr_f hsp_eq_f hx20_f hx21_f hx22_f hx29_f hvregs_f => ?_
  rw [← ha88, ← ha80, ← ha8, ← ha16, ← ha24]
  have htheir_back :
      ((serPtr + BitVec.ofNat 64 (bs.length - 8)) ↦₈ t0) ∗
      ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 1#64) ↦₈ t1) ∗
      ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 2#64) ↦₈ t2) ∗
      ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 3#64) ↦₈ t3) ∗
      ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 4#64) ↦₈ t4) ∗
      ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 5#64) ↦₈ t5) ∗
      ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 6#64) ↦₈ t6) ∗
      ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 7#64) ↦₈ t7) =
      ((serPtr + BitVec.ofNat 64 (bs.length - 8)) ↦ₛ bs.drop (bs.length - 8)) := by
    rw [htheir_eq, pointsToBytes_8_bytes]
  apply SepWPp.weaken_pre (P' :=
    (((sp0 - 208#64) ↦₆₄ okTagVec) ∗ ((sp0 - 208#64 + 8#64) ↦₆₄ pack64 m0 m1 m2 m3 m4 m5 m6 m7)) ∗
    (((serPtr ↦ₛ bs.take (bs.length - 8)) ∗
      (((serPtr + BitVec.ofNat 64 (bs.length - 8)) ↦₈ t0) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 1#64) ↦₈ t1) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 2#64) ↦₈ t2) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 3#64) ↦₈ t3) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 4#64) ↦₈ t4) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 5#64) ↦₈ t5) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 6#64) ↦₈ t6) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 7#64) ↦₈ t7))) ∗
     ((sp0 - 280#64) ↦₆₄ (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 48)) ∗
     ((sp0 - 272#64) ↦₆₄ (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 56)) ∗
     ((sp0 - 264#64) ↦₆₄ retA) ∗
     stackAt (sp0 - 288#64) cmStack ∗ Frame)) (Entails.of_eq (by ac_rfl))
  rw [htheir_back, ← pointsToBytes_serialized_split serPtr bs h8]
  apply SepWPp.weaken_pre
    (sepConj_mono_left (memRegion_16_of_two_words (sp0 - 208#64) okTagVec
      (pack64 m0 m1 m2 m3 m4 m5 m6 m7)))
  rw [← hour_eq, ← htheir_eq] at hpc_f
  exact hcont sf (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 48)
    (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 56)
    hpc_f hrun_f hsp_f htr_f hsp_eq_f hx20_f hx21_f hx22_f hx29_f hvregs_f

end CryptoVerification.LibsignalTripleRatchet.Mac.VerifyMacWithAddresses
