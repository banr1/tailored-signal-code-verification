/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.Common
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailDropRecordSteps
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFetch
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteErr
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# MessageEncrypt T1 from-error (`+0x49c..+0x564`, `tailFromSessionStateErr_ok`) proof
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

variable {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
  {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {abs : String → Option (State → State)}

abbrev logAddrAtEntry (entry : BitVec 64) : BitVec 64 :=
  ((entry + bv% (1188) &&& bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "session_message_encrypt" + 1188))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096)

theorem tripleRatchetProgAt_fnAddr_encryptWithStores (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName = b + bv% (ls_off% "session_message_encrypt") := by
  unfold tripleRatchetProgAt
  rw [Program.fnAddr_rebase, libsignalSessionCode_fnOff_sym_3caf4]

theorem logAddrAtEntry_eq_logFilterAddr {img : Obj.Image}
    (hloads : Obj.Loads libsignalSessionImage img) :
    logAddrAtEntry ((tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName) =
      logFilterAddr img := by
  have hbal := ProofLib.base_aligned_of_loads hloads
  unfold logAddrAtEntry
  rw [tripleRatchetProgAt_fnAddr_encryptWithStores, BitVec.add_assoc img.base, adrp_page_of_aligned hbal, logFilterAddr]
  have hmask : ((248792#64 + 1188#64 : BitVec 64) &&& bv% (2 ^ 64 - 4096)) = 249856#64 := rfl
  rw [hmask]
  bv_omega

/-! ## `SepWP` Stepping Lemma (`+0x49c..+0x54c`) -/

set_option maxHeartbeats 800000 in
theorem fromSessionStateErr_sepWP {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {sp logA : BitVec 64}
    {w0 w1 w2 w3 w4 w5 : BitVec 64}
    {u850 u858 u860 u9d0 u9d8 u9e0 uab0 uab8 uac0 uac8 uad0 uad8 : BitVec 64}
    (hlog : logAddrAtEntry ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName) = logA)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x49c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp)
    (hx21 : s.readReg64 .x21 = sp + 0x580#64)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hx29 : s.readReg64 .x29 = sp + 0xb80#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x54c#64) s
      (((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗
        ((sp + 0x598#64) ↦₆₄ w2) ∗ ((sp + 0x5a0#64) ↦₆₄ w3) ∗
        ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5) ∗
        ((sp + 0x850#64) ↦₆₄ u850) ∗ ((sp + 0x858#64) ↦₆₄ u858) ∗
        ((sp + 0x860#64) ↦₆₄ u860) ∗
        ((sp + 0x9d0#64) ↦₆₄ u9d0) ∗ ((sp + 0x9d8#64) ↦₆₄ u9d8) ∗
        ((sp + 0x9e0#64) ↦₆₄ u9e0) ∗
        ((sp + 0xab0#64) ↦₆₄ uab0) ∗ ((sp + 0xab8#64) ↦₆₄ uab8) ∗
        ((sp + 0xac0#64) ↦₆₄ uac0) ∗ ((sp + 0xac8#64) ↦₆₄ uac8) ∗
        ((sp + 0xad0#64) ↦₆₄ uad0) ∗ ((sp + 0xad8#64) ↦₆₄ uad8) ∗
        (logA ↦₆₄ 0#64))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = w1 ∧
        sf.readReg64 .x23 = w2 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = w0 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗
          ((sp + 0x598#64) ↦₆₄ w2) ∗ ((sp + 0x5a0#64) ↦₆₄ w3) ∗
          ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5) ∗
          ((sp + 0x850#64) ↦₆₄ w3) ∗ ((sp + 0x858#64) ↦₆₄ w4) ∗
          ((sp + 0x860#64) ↦₆₄ w5) ∗
          ((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ w4) ∗
          ((sp + 0x9e0#64) ↦₆₄ w5) ∗
          ((sp + 0xab0#64) ↦₆₄ w0) ∗ ((sp + 0xab8#64) ↦₆₄ w1) ∗
          ((sp + 0xac0#64) ↦₆₄ w2) ∗ ((sp + 0xac8#64) ↦₆₄ w3) ∗
          ((sp + 0xad0#64) ↦₆₄ w4) ∗ ((sp + 0xad8#64) ↦₆₄ w5) ∗
          (logA ↦₆₄ 0#64))) := by
  subst hsp
  subst hlog
  unfold logAddrAtEntry
  have hfn := libsignalSessionCode_fnOff_sym_3caf4
  messageEncryptTail_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 1180 32
  messageEncryptTail_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 1324 32
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  exact ⟨rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by ac_rfl⟩

/-! ## Frame Splitting and Weakening Lemmas -/

theorem satisfies_memRegion_1 {m : Memory} {a : BitVec 64} {R : SepProp}
    (h : m ⊨ memRegion a 1 ∗ R) :
    ∃ b : BitVec 8, m ⊨ (a ↦₈ b) ∗ R := by
  rw [ProofLib.memRegion_one, sepExists_sepConj_left, satisfies_sepExists] at h
  exact h

theorem satisfies_memRegion_24 {m : Memory} {a : BitVec 64} {R : SepProp}
    (h : m ⊨ memRegion a 24 ∗ R) :
    ∃ u0 u1 u2 : BitVec 64,
      m ⊨ ((a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2)) ∗ R := by
  rw [memRegion_24_eq_exists_vecHeader, sepExists_sepConj_left, satisfies_sepExists] at h
  rcases h with ⟨u0, h⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at h
  rcases h with ⟨u1, h⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at h
  rcases h with ⟨u2, h⟩
  exact ⟨u0, u1, u2, h⟩

def pollFromRest (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0x46a#64) 0x11e ∗
    memRegion (sp + 0x5b8#64) 0x298 ∗
    memRegion (sp + 0x868#64) 0x168 ∗
    memRegion (sp + 0x9e8#64) 0xc8 ∗
    memRegion (sp + 0xae0#64) 0xa0

theorem pollWith_588_split (sp w0 w1 w2 w3 w4 w5 : BitVec 64) :
    pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] =
      (((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗
        ((sp + 0x598#64) ↦₆₄ w2) ∗ ((sp + 0x5a0#64) ↦₆₄ w3) ∗
        ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5)) ∗
      memRegion (sp + 0x850#64) 24 ∗
      memRegion (sp + 0x9d0#64) 24 ∗
      memRegion (sp + 0xab0#64) 24 ∗
      memRegion (sp + 0xac8#64) 24 ∗
      pollFromRest sp := by
  unfold pollWith pollFromRest
  dsimp only [List.length_cons, List.length_nil]
  have h_off : sp + BitVec.ofNat 64 0x588 = sp + 0x588#64 := rfl
  have h_end : sp + BitVec.ofNat 64 (0x588 + 8 * 6) = sp + 0x5b8#64 := by bv_omega
  have h_words :
      words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] =
        ((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗
          ((sp + 0x598#64) ↦₆₄ w2) ∗ ((sp + 0x5a0#64) ↦₆₄ w3) ∗
          ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5) := by
    dsimp only [words64At]
    have h1 : sp + 0x588#64 + 8#64 = sp + 0x590#64 := by bv_omega
    have h2 : sp + 0x590#64 + 8#64 = sp + 0x598#64 := by bv_omega
    have h3 : sp + 0x598#64 + 8#64 = sp + 0x5a0#64 := by bv_omega
    have h4 : sp + 0x5a0#64 + 8#64 = sp + 0x5a8#64 := by bv_omega
    have h5 : sp + 0x5a8#64 + 8#64 = sp + 0x5b0#64 := by bv_omega
    rw [h1, h2, h3, h4, h5, sepConj_emp]
  have h_split :
      memRegion (sp + 0x5b8#64) (0xb80 - (0x588 + 8 * 6)) =
        memRegion (sp + 0x5b8#64) 0x298 ∗
          (memRegion (sp + 0x850#64) 24 ∗
            (memRegion (sp + 0x868#64) 0x168 ∗
              (memRegion (sp + 0x9d0#64) 24 ∗
                (memRegion (sp + 0x9e8#64) 0xc8 ∗
                  (memRegion (sp + 0xab0#64) 24 ∗
                    (memRegion (sp + 0xac8#64) 24 ∗
                      memRegion (sp + 0xae0#64) 0xa0)))))) := by
    rw [memRegion_split' (b := sp + 0x5b8#64) (b' := sp + 0x850#64) (N := 0x5c8) (n := 0x298) (k := 0x330)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x850#64) (b' := sp + 0x868#64) (N := 0x330) (n := 24) (k := 0x318)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x868#64) (b' := sp + 0x9d0#64) (N := 0x318) (n := 0x168) (k := 0x1b0)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x9d0#64) (b' := sp + 0x9e8#64) (N := 0x1b0) (n := 24) (k := 0x198)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x9e8#64) (b' := sp + 0xab0#64) (N := 0x198) (n := 0xc8) (k := 0xd0)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0xab0#64) (b' := sp + 0xac8#64) (N := 0xd0) (n := 24) (k := 0xb8)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0xac8#64) (b' := sp + 0xae0#64) (N := 0xb8) (n := 24) (k := 0xa0)
          (by decide) (by bv_omega) (by decide)]
  rw [h_off, h_end, h_words, h_split]
  ac_rfl

theorem pollWith_588_mem_elim {m : Memory} {sp logA : BitVec 64}
    {w0 w1 w2 w3 w4 w5 : BitVec 64} {R : SepProp}
    (h : m ⊨ pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ (logA ↦₆₄ 0#64) ∗ R) :
    ∃ u850 u858 u860 u9d0 u9d8 u9e0 uab0 uab8 uac0 uac8 uad0 uad8 : BitVec 64,
      m ⊨ (((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗
        ((sp + 0x598#64) ↦₆₄ w2) ∗ ((sp + 0x5a0#64) ↦₆₄ w3) ∗
        ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5) ∗
        ((sp + 0x850#64) ↦₆₄ u850) ∗ ((sp + 0x858#64) ↦₆₄ u858) ∗
        ((sp + 0x860#64) ↦₆₄ u860) ∗
        ((sp + 0x9d0#64) ↦₆₄ u9d0) ∗ ((sp + 0x9d8#64) ↦₆₄ u9d8) ∗
        ((sp + 0x9e0#64) ↦₆₄ u9e0) ∗
        ((sp + 0xab0#64) ↦₆₄ uab0) ∗ ((sp + 0xab8#64) ↦₆₄ uab8) ∗
        ((sp + 0xac0#64) ↦₆₄ uac0) ∗ ((sp + 0xac8#64) ↦₆₄ uac8) ∗
        ((sp + 0xad0#64) ↦₆₄ uad0) ∗ ((sp + 0xad8#64) ↦₆₄ uad8) ∗
        (logA ↦₆₄ 0#64)) ∗ (pollFromRest sp ∗ R) := by
  rw [pollWith_588_split sp w0 w1 w2 w3 w4 w5] at h
  let W6 := ((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗
    ((sp + 0x598#64) ↦₆₄ w2) ∗ ((sp + 0x5a0#64) ↦₆₄ w3) ∗
    ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5)
  have h1 : m ⊨ memRegion (sp + 0x850#64) 24 ∗
      (memRegion (sp + 0x9d0#64) 24 ∗ memRegion (sp + 0xab0#64) 24 ∗
        memRegion (sp + 0xac8#64) 24 ∗ W6 ∗ (logA ↦₆₄ 0#64) ∗ pollFromRest sp ∗ R) := by
    have heq :
        ((W6 ∗ memRegion (sp + 0x850#64) 24 ∗ memRegion (sp + 0x9d0#64) 24 ∗
          memRegion (sp + 0xab0#64) 24 ∗ memRegion (sp + 0xac8#64) 24 ∗ pollFromRest sp) ∗
         (logA ↦₆₄ 0#64) ∗ R) =
        (memRegion (sp + 0x850#64) 24 ∗
         (memRegion (sp + 0x9d0#64) 24 ∗ memRegion (sp + 0xab0#64) 24 ∗
          memRegion (sp + 0xac8#64) 24 ∗ W6 ∗ (logA ↦₆₄ 0#64) ∗ pollFromRest sp ∗ R)) := by ac_rfl
    rwa [← heq]
  obtain ⟨u850, u858, u860, h1'⟩ := satisfies_memRegion_24 h1
  have h858_eq : sp + 0x850#64 + 8#64 = sp + 0x858#64 := by bv_omega
  have h860_eq : sp + 0x850#64 + 16#64 = sp + 0x860#64 := by bv_omega
  rw [h858_eq, h860_eq] at h1'
  let U850 := ((sp + 0x850#64) ↦₆₄ u850) ∗ ((sp + 0x858#64) ↦₆₄ u858) ∗ ((sp + 0x860#64) ↦₆₄ u860)
  have h2 : m ⊨ memRegion (sp + 0x9d0#64) 24 ∗
      (memRegion (sp + 0xab0#64) 24 ∗ memRegion (sp + 0xac8#64) 24 ∗
        U850 ∗ W6 ∗ (logA ↦₆₄ 0#64) ∗ pollFromRest sp ∗ R) := by
    have heq :
        (U850 ∗ (memRegion (sp + 0x9d0#64) 24 ∗ memRegion (sp + 0xab0#64) 24 ∗
          memRegion (sp + 0xac8#64) 24 ∗ W6 ∗ (logA ↦₆₄ 0#64) ∗ pollFromRest sp ∗ R)) =
        (memRegion (sp + 0x9d0#64) 24 ∗
         (memRegion (sp + 0xab0#64) 24 ∗ memRegion (sp + 0xac8#64) 24 ∗
          U850 ∗ W6 ∗ (logA ↦₆₄ 0#64) ∗ pollFromRest sp ∗ R)) := by ac_rfl
    rwa [← heq]
  obtain ⟨u9d0, u9d8, u9e0, h2'⟩ := satisfies_memRegion_24 h2
  have h9d8_eq : sp + 0x9d0#64 + 8#64 = sp + 0x9d8#64 := by bv_omega
  have h9e0_eq : sp + 0x9d0#64 + 16#64 = sp + 0x9e0#64 := by bv_omega
  rw [h9d8_eq, h9e0_eq] at h2'
  let U9d0 := ((sp + 0x9d0#64) ↦₆₄ u9d0) ∗ ((sp + 0x9d8#64) ↦₆₄ u9d8) ∗ ((sp + 0x9e0#64) ↦₆₄ u9e0)
  have h3 : m ⊨ memRegion (sp + 0xab0#64) 24 ∗
      (memRegion (sp + 0xac8#64) 24 ∗ U9d0 ∗ U850 ∗ W6 ∗ (logA ↦₆₄ 0#64) ∗ pollFromRest sp ∗ R) := by
    have heq :
        (U9d0 ∗ (memRegion (sp + 0xab0#64) 24 ∗ memRegion (sp + 0xac8#64) 24 ∗
          U850 ∗ W6 ∗ (logA ↦₆₄ 0#64) ∗ pollFromRest sp ∗ R)) =
        (memRegion (sp + 0xab0#64) 24 ∗
         (memRegion (sp + 0xac8#64) 24 ∗ U9d0 ∗ U850 ∗ W6 ∗ (logA ↦₆₄ 0#64) ∗ pollFromRest sp ∗ R)) := by ac_rfl
    rwa [← heq]
  obtain ⟨uab0, uab8, uac0, h3'⟩ := satisfies_memRegion_24 h3
  have hab8_eq : sp + 0xab0#64 + 8#64 = sp + 0xab8#64 := by bv_omega
  have hac0_eq : sp + 0xab0#64 + 16#64 = sp + 0xac0#64 := by bv_omega
  rw [hab8_eq, hac0_eq] at h3'
  let Uab0 := ((sp + 0xab0#64) ↦₆₄ uab0) ∗ ((sp + 0xab8#64) ↦₆₄ uab8) ∗ ((sp + 0xac0#64) ↦₆₄ uac0)
  have h4 : m ⊨ memRegion (sp + 0xac8#64) 24 ∗
      (Uab0 ∗ U9d0 ∗ U850 ∗ W6 ∗ (logA ↦₆₄ 0#64) ∗ pollFromRest sp ∗ R) := by
    have heq :
        (Uab0 ∗ (memRegion (sp + 0xac8#64) 24 ∗
          U9d0 ∗ U850 ∗ W6 ∗ (logA ↦₆₄ 0#64) ∗ pollFromRest sp ∗ R)) =
        (memRegion (sp + 0xac8#64) 24 ∗
         (Uab0 ∗ U9d0 ∗ U850 ∗ W6 ∗ (logA ↦₆₄ 0#64) ∗ pollFromRest sp ∗ R)) := by ac_rfl
    rwa [← heq]
  obtain ⟨uac8, uad0, uad8, h4'⟩ := satisfies_memRegion_24 h4
  have had0_eq : sp + 0xac8#64 + 8#64 = sp + 0xad0#64 := by bv_omega
  have had8_eq : sp + 0xac8#64 + 16#64 = sp + 0xad8#64 := by bv_omega
  rw [had0_eq, had8_eq] at h4'
  refine ⟨u850, u858, u860, u9d0, u9d8, u9e0, uab0, uab8, uac0, uac8, uad0, uad8, ?_⟩
  have heq :
      ((((sp + 0xac8#64) ↦₆₄ uac8) ∗ ((sp + 0xad0#64) ↦₆₄ uad0) ∗ ((sp + 0xad8#64) ↦₆₄ uad8)) ∗
       (Uab0 ∗ U9d0 ∗ U850 ∗ W6 ∗ (logA ↦₆₄ 0#64) ∗ pollFromRest sp ∗ R)) =
      ((((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗
        ((sp + 0x598#64) ↦₆₄ w2) ∗ ((sp + 0x5a0#64) ↦₆₄ w3) ∗
        ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5) ∗
        ((sp + 0x850#64) ↦₆₄ u850) ∗ ((sp + 0x858#64) ↦₆₄ u858) ∗
        ((sp + 0x860#64) ↦₆₄ u860) ∗
        ((sp + 0x9d0#64) ↦₆₄ u9d0) ∗ ((sp + 0x9d8#64) ↦₆₄ u9d8) ∗
        ((sp + 0x9e0#64) ↦₆₄ u9e0) ∗
        ((sp + 0xab0#64) ↦₆₄ uab0) ∗ ((sp + 0xab8#64) ↦₆₄ uab8) ∗
        ((sp + 0xac0#64) ↦₆₄ uac0) ∗ ((sp + 0xac8#64) ↦₆₄ uac8) ∗
        ((sp + 0xad0#64) ↦₆₄ uad0) ∗ ((sp + 0xad8#64) ↦₆₄ uad8) ∗
        (logA ↦₆₄ 0#64)) ∗ (pollFromRest sp ∗ R)) := by
    dsimp only [W6, U850, U9d0, Uab0]
    ac_rfl
  rwa [← heq]

theorem words3_weaken_memRegion24 (a b c : BitVec 64) (w0 w1 w2 : BitVec 64)
    (hb : a + 8#64 = b) (hc : a + 16#64 = c) :
    (a ↦₆₄ w0) ∗ (b ↦₆₄ w1) ∗ (c ↦₆₄ w2) ⊢ memRegion a 24 := by
  subst hb hc
  exact vecHeader_entails_memRegion a w0 w1 w2

theorem pollFrom_post_weaken (sp w0 w1 w2 w3 w4 w5 : BitVec 64) :
    (((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗ ((sp + 0x598#64) ↦₆₄ w2)) ∗
      (((sp + 0x5a0#64) ↦₆₄ w3) ∗ ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5)) ∗
      (((sp + 0x850#64) ↦₆₄ w3) ∗ ((sp + 0x858#64) ↦₆₄ w4) ∗ ((sp + 0x860#64) ↦₆₄ w5)) ∗
      (((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ w4) ∗ ((sp + 0x9e0#64) ↦₆₄ w5)) ∗
      (((sp + 0xab0#64) ↦₆₄ w0) ∗ ((sp + 0xab8#64) ↦₆₄ w1) ∗ ((sp + 0xac0#64) ↦₆₄ w2)) ∗
      (((sp + 0xac8#64) ↦₆₄ w3) ∗ ((sp + 0xad0#64) ↦₆₄ w4) ∗ ((sp + 0xad8#64) ↦₆₄ w5)) ∗
      pollFromRest sp ⊢
    pollWith sp 0x9d0 [w3, w4, w5] := by
  have hw1 := words3_weaken_memRegion24 (sp + 0x588#64) (sp + 0x590#64) (sp + 0x598#64)
    w0 w1 w2 (by bv_omega) (by bv_omega)
  have hw2 := words3_weaken_memRegion24 (sp + 0x5a0#64) (sp + 0x5a8#64) (sp + 0x5b0#64)
    w3 w4 w5 (by bv_omega) (by bv_omega)
  have hw3 := words3_weaken_memRegion24 (sp + 0x850#64) (sp + 0x858#64) (sp + 0x860#64)
    w3 w4 w5 (by bv_omega) (by bv_omega)
  have hw4 := words3_weaken_memRegion24 (sp + 0xab0#64) (sp + 0xab8#64) (sp + 0xac0#64)
    w0 w1 w2 (by bv_omega) (by bv_omega)
  have hw5 := words3_weaken_memRegion24 (sp + 0xac8#64) (sp + 0xad0#64) (sp + 0xad8#64)
    w3 w4 w5 (by bv_omega) (by bv_omega)
  refine Entails.trans
    (sepConj_mono hw1 (sepConj_mono hw2 (sepConj_mono hw3
      (sepConj_mono_right (sepConj_mono hw4 (sepConj_mono_left hw5)))))) ?_
  unfold pollWith pollFromRest
  dsimp only [List.length_cons, List.length_nil]
  have h_off : sp + BitVec.ofNat 64 0x9d0 = sp + 0x9d0#64 := rfl
  have h_end : sp + BitVec.ofNat 64 (0x9d0 + 8 * 3) = sp + 0x9e8#64 := by bv_omega
  have h_words :
      words64At (sp + 0x9d0#64) [w3, w4, w5] =
        ((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ w4) ∗ ((sp + 0x9e0#64) ↦₆₄ w5) := by
    dsimp only [words64At]
    have h1 : sp + 0x9d0#64 + 8#64 = sp + 0x9d8#64 := by bv_omega
    have h2 : sp + 0x9d8#64 + 8#64 = sp + 0x9e0#64 := by bv_omega
    rw [h1, h2, sepConj_emp]
  have h_pre :
      memRegion (sp + 0x46a#64) (0x9d0 - 0x46a) =
        memRegion (sp + 0x46a#64) 0x11e ∗
          (memRegion (sp + 0x588#64) 24 ∗
            (memRegion (sp + 0x5a0#64) 24 ∗
              (memRegion (sp + 0x5b8#64) 0x298 ∗
                (memRegion (sp + 0x850#64) 24 ∗
                  memRegion (sp + 0x868#64) 0x168)))) := by
    rw [memRegion_split' (b := sp + 0x46a#64) (b' := sp + 0x588#64) (N := 0x566) (n := 0x11e) (k := 0x448)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x588#64) (b' := sp + 0x5a0#64) (N := 0x448) (n := 24) (k := 0x430)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x5a0#64) (b' := sp + 0x5b8#64) (N := 0x430) (n := 24) (k := 0x418)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x5b8#64) (b' := sp + 0x850#64) (N := 0x418) (n := 0x298) (k := 0x180)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x850#64) (b' := sp + 0x868#64) (N := 0x180) (n := 24) (k := 0x168)
          (by decide) (by bv_omega) (by decide)]
  have h_post :
      memRegion (sp + 0x9e8#64) (0xb80 - (0x9d0 + 8 * 3)) =
        memRegion (sp + 0x9e8#64) 0xc8 ∗
          (memRegion (sp + 0xab0#64) 24 ∗
            (memRegion (sp + 0xac8#64) 24 ∗
              memRegion (sp + 0xae0#64) 0xa0)) := by
    rw [memRegion_split' (b := sp + 0x9e8#64) (b' := sp + 0xab0#64) (N := 0x198) (n := 0xc8) (k := 0xd0)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0xab0#64) (b' := sp + 0xac8#64) (N := 0xd0) (n := 24) (k := 0xb8)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0xac8#64) (b' := sp + 0xae0#64) (N := 0xb8) (n := 24) (k := 0xa0)
          (by decide) (by bv_omega) (by decide)]
  rw [h_off, h_end, h_words, h_pre, h_post]
  have heq :
      (memRegion (sp + 0x588#64) 24 ∗ memRegion (sp + 0x5a0#64) 24 ∗
        memRegion (sp + 0x850#64) 24 ∗
        (((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ w4) ∗ ((sp + 0x9e0#64) ↦₆₄ w5)) ∗
        memRegion (sp + 0xab0#64) 24 ∗ memRegion (sp + 0xac8#64) 24 ∗
        (memRegion (sp + 0x46a#64) 0x11e ∗ memRegion (sp + 0x5b8#64) 0x298 ∗
          memRegion (sp + 0x868#64) 0x168 ∗ memRegion (sp + 0x9e8#64) 0xc8 ∗
          memRegion (sp + 0xae0#64) 0xa0)) =
      ((memRegion (sp + 0x46a#64) 0x11e ∗
        (memRegion (sp + 0x588#64) 24 ∗
          (memRegion (sp + 0x5a0#64) 24 ∗
            (memRegion (sp + 0x5b8#64) 0x298 ∗
              (memRegion (sp + 0x850#64) 24 ∗ memRegion (sp + 0x868#64) 0x168))))) ∗
       (((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ w4) ∗ ((sp + 0x9e0#64) ↦₆₄ w5)) ∗
       (memRegion (sp + 0x9e8#64) 0xc8 ∗
         (memRegion (sp + 0xab0#64) 24 ∗
           (memRegion (sp + 0xac8#64) 24 ∗ memRegion (sp + 0xae0#64) 0xa0)))) := by ac_rfl
  rw [heq]
  exact Entails.refl _

theorem pollFrom_post_mem_weaken {m : Memory} {sp logA : BitVec 64}
    {w0 w1 w2 w3 w4 w5 : BitVec 64} {R : SepProp}
    (h : m ⊨ (((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗
        ((sp + 0x598#64) ↦₆₄ w2) ∗ ((sp + 0x5a0#64) ↦₆₄ w3) ∗
        ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5) ∗
        ((sp + 0x850#64) ↦₆₄ w3) ∗ ((sp + 0x858#64) ↦₆₄ w4) ∗
        ((sp + 0x860#64) ↦₆₄ w5) ∗
        ((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ w4) ∗
        ((sp + 0x9e0#64) ↦₆₄ w5) ∗
        ((sp + 0xab0#64) ↦₆₄ w0) ∗ ((sp + 0xab8#64) ↦₆₄ w1) ∗
        ((sp + 0xac0#64) ↦₆₄ w2) ∗ ((sp + 0xac8#64) ↦₆₄ w3) ∗
        ((sp + 0xad0#64) ↦₆₄ w4) ∗ ((sp + 0xad8#64) ↦₆₄ w5) ∗
        (logA ↦₆₄ 0#64)) ∗ (pollFromRest sp ∗ R)) :
    m ⊨ pollWith sp 0x9d0 [w3, w4, w5] ∗ (logA ↦₆₄ 0#64) ∗ R := by
  have h1 : m ⊨
      ((((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗ ((sp + 0x598#64) ↦₆₄ w2)) ∗
        (((sp + 0x5a0#64) ↦₆₄ w3) ∗ ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5)) ∗
        (((sp + 0x850#64) ↦₆₄ w3) ∗ ((sp + 0x858#64) ↦₆₄ w4) ∗ ((sp + 0x860#64) ↦₆₄ w5)) ∗
        (((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ w4) ∗ ((sp + 0x9e0#64) ↦₆₄ w5)) ∗
        (((sp + 0xab0#64) ↦₆₄ w0) ∗ ((sp + 0xab8#64) ↦₆₄ w1) ∗ ((sp + 0xac0#64) ↦₆₄ w2)) ∗
        (((sp + 0xac8#64) ↦₆₄ w3) ∗ ((sp + 0xad0#64) ↦₆₄ w4) ∗ ((sp + 0xad8#64) ↦₆₄ w5)) ∗
        pollFromRest sp) ∗ ((logA ↦₆₄ 0#64) ∗ R) := by
    have heq :
        ((((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗
          ((sp + 0x598#64) ↦₆₄ w2) ∗ ((sp + 0x5a0#64) ↦₆₄ w3) ∗
          ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5) ∗
          ((sp + 0x850#64) ↦₆₄ w3) ∗ ((sp + 0x858#64) ↦₆₄ w4) ∗
          ((sp + 0x860#64) ↦₆₄ w5) ∗
          ((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ w4) ∗
          ((sp + 0x9e0#64) ↦₆₄ w5) ∗
          ((sp + 0xab0#64) ↦₆₄ w0) ∗ ((sp + 0xab8#64) ↦₆₄ w1) ∗
          ((sp + 0xac0#64) ↦₆₄ w2) ∗ ((sp + 0xac8#64) ↦₆₄ w3) ∗
          ((sp + 0xad0#64) ↦₆₄ w4) ∗ ((sp + 0xad8#64) ↦₆₄ w5) ∗
          (logA ↦₆₄ 0#64)) ∗ (pollFromRest sp ∗ R)) =
        (((((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗ ((sp + 0x598#64) ↦₆₄ w2)) ∗
          (((sp + 0x5a0#64) ↦₆₄ w3) ∗ ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5)) ∗
          (((sp + 0x850#64) ↦₆₄ w3) ∗ ((sp + 0x858#64) ↦₆₄ w4) ∗ ((sp + 0x860#64) ↦₆₄ w5)) ∗
          (((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ w4) ∗ ((sp + 0x9e0#64) ↦₆₄ w5)) ∗
          (((sp + 0xab0#64) ↦₆₄ w0) ∗ ((sp + 0xab8#64) ↦₆₄ w1) ∗ ((sp + 0xac0#64) ↦₆₄ w2)) ∗
          (((sp + 0xac8#64) ↦₆₄ w3) ∗ ((sp + 0xad0#64) ↦₆₄ w4) ∗ ((sp + 0xad8#64) ↦₆₄ w5)) ∗
          pollFromRest sp) ∗ ((logA ↦₆₄ 0#64) ∗ R)) := by ac_rfl
    rwa [← heq]
  exact Satisfies.mono (sepConj_mono_left (pollFrom_post_weaken sp w0 w1 w2 w3 w4 w5)) h1

def encCommonRest (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (draws : Nat) (s0 : State) : SepProp :=
  (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ nowAt s0.sp x.now ∗
    tapeAfter ctl x.cur x.rest draws ∗
    stackAt (s0.sp - 0xbe0#64) encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool

theorem encCommon_eq_logOff_rest (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (draws : Nat) (s0 : State) :
    encCommon A ctl img x draws s0 =
      (logFilterAddr img ↦₆₄ 0#64) ∗ encCommonRest A ctl x draws s0 := by
  unfold encCommon logOff encCommonRest
  ac_rfl

/-! ## `tailFromSessionStateErr_ok` (`+0x49c..+0x564`) -/

open CryptoVerification.LibsignalPublicApi.StoreKit

theorem tailFromSessionStateErr_ok {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (encEntry img + 0x49c#64)
      (fun sp s => s.readReg64 .x21 = sp + 0x580#64 ∧ s.readReg64 .x25 = sp + 0x580#64 ∧
        s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64)
      (fun sp => curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ H)
      R0 s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) := by
  let R := encStoreExtra kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    ⟨hx21, hx25, hx26, hx28⟩, hstack_le, hmem⟩
  rw [entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads] at hpc
  let sp := s0.sp - 0xbe0#64
  change s.mem ⊨
    (curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
      memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommon A ctl img x (x.draws S answers) s0 ∗ R at hmem
  have h1ea : memRegion (sp + 0x280#64) 0x1ea =
      memRegion (sp + 0x280#64) 0x1e9 ∗ memRegion (sp + 0x469#64) 1 := by
    rw [memRegion_split' (b := sp + 0x280#64) (b' := sp + 0x469#64) (N := 0x1ea) (n := 0x1e9) (k := 1)
          (by decide) (by bv_omega) (by decide)]
  rw [h1ea, encCommon_eq_logOff_rest A ctl img x (x.draws S answers) s0] at hmem
  let F_inv := curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
    memRegion (sp + 0x280#64) 0x1e9 ∗ H ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommonRest A ctl x (x.draws S answers) s0 ∗ R
  have hmem_469 : s.mem ⊨
      memRegion (sp + 0x469#64) 1 ∗
      (pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗ F_inv) := by
    have heq :
        ((curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
          (memRegion (sp + 0x280#64) 0x1e9 ∗ memRegion (sp + 0x469#64) 1) ∗
          pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         ((logFilterAddr img ↦₆₄ 0#64) ∗ encCommonRest A ctl x (x.draws S answers) s0) ∗ R) =
        (memRegion (sp + 0x469#64) 1 ∗
         (pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
           (logFilterAddr img ↦₆₄ 0#64) ∗ F_inv)) := by
      dsimp only [F_inv]; ac_rfl
    rwa [← heq]
  obtain ⟨b469, hmem_b469⟩ := satisfies_memRegion_1 hmem_469
  have hmem_poll : s.mem ⊨
      pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
      (logFilterAddr img ↦₆₄ 0#64) ∗ (((sp + 0x469#64) ↦₈ b469) ∗ F_inv) := by
    have heq :
        (((sp + 0x469#64) ↦₈ b469) ∗
         (pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
           (logFilterAddr img ↦₆₄ 0#64) ∗ F_inv)) =
        (pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
         (logFilterAddr img ↦₆₄ 0#64) ∗ (((sp + 0x469#64) ↦₈ b469) ∗ F_inv)) := by ac_rfl
    rwa [← heq]
  obtain ⟨u850, u858, u860, u9d0, u9d8, u9e0, uab0, uab8, uac0, uac8, uad0, uad8, hmem_wp⟩ :=
    pollWith_588_mem_elim hmem_poll
  have hx29' : s.readReg64 .x29 = sp + 0xb80#64 := by
    rw [hx29]; dsimp only [sp]; bv_omega
  have hlog := logAddrAtEntry_eq_logFilterAddr (C := C) (ctl := ctl) (abs := abs)
    env.loads
  have hwp := fromSessionStateErr_sepWP (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5)
    (u850 := u850) (u858 := u858) (u860 := u860) (u9d0 := u9d0) (u9d8 := u9d8) (u9e0 := u9e0)
    (uab0 := uab0) (uab8 := uab8) (uac0 := uac0) (uac8 := uac8) (uad0 := uad0) (uad8 := uad8)
    hlog hpc hrun hsp_al hsp hx21 hx25 hx26 hx28 hx29'
  refine segExit_of_sepWP hmem_wp hwp ?_
  intro s1 P_f hsteps1 hpc1 hrun1 hmf1
    ⟨hsp1, hsp1_al, htr1, hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
  subst hPf
  have hpc1' : s1.pc = encEntry img + 0x54c#64 := by
    rw [entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads, hpc1]
  have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
    ⟨hm.1, htr1.trans hm.2⟩
  refine tailDropRecordCur_ok env x R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H curScratch (Or.inl rfl) g rec b469 hm1 hst ?_
  refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
    hsteps1.frozenLoaded hfl, hsym1.trans hsym, hvregs1.trans hvregs⟩,
    ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1, hx21_1, hx23_1⟩,
    hstack_le, ?_⟩
  have hmf2 := pollFrom_post_mem_weaken hmf1
  change s1.mem ⊨
    (curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
      memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
      pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommon A ctl img x (x.draws S answers) s0 ∗ R
  rw [encCommon_eq_logOff_rest A ctl img x (x.draws S answers) s0]
  have heq :
      (pollWith sp 0x9d0 [w3, w4, w5] ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
        (((sp + 0x469#64) ↦₈ b469) ∗ F_inv)) =
      ((curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
        pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       ((logFilterAddr img ↦₆₄ 0#64) ∗ encCommonRest A ctl x (x.draws S answers) s0) ∗ R) := by
    dsimp only [F_inv]; ac_rfl
  rwa [← heq]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr
