/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Stage2ContractsExt
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4K
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# Contract-Backed Segment S3 Callee Helpers (`coinsFill` & `StaticSecret::drop`)

Provides `signal_session_coins_fill` and `<StaticSecret as Drop>::drop` `subroutine_ok` helpers
on `tripleRatchetProgAtExt` for handshake `try_decrypt_with_state::<Coins>` (`S3`).
-/

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (extHookStack sessionMemcpyRegionSpec
  sessionMemsetRegionSpec sub_ok_at_of_fnAddr tripleRatchetProgAtExt withStack zeroizeSecretSpec)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq (tryDecryptSubStack)
open CryptoVerification.SignalSession.Coins (coinsAfter coinsFillAtSpec coinsFillAt_of_after0
  coinsFillName coinsFillSpec coinsLeft coinsNext tapeAfter2 tapeAfter2_zero_eq)
open CryptoVerification.SignalSession.Cli.Slots (Stage2ContractsExt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (AllocContractsMem4K)

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegDhDefs

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private gen_decodes CryptoVerification.libsignalSessionCode_tree coinsFillExtBin
  [(ls_off% "signal_session_coins_fill") → (ls_off% "signal_session_coins_fill" + 116)]

namespace BS10

private theorem adrp_page_next_ext {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr coinsFillName + bv% 24) &&& bv% (2 ^ 64 - 4096)) =
      b + bv% (page% (ls_off% "signal_session_coins_fill" + 24)) := by
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "signal_session_coins_fill"), BitVec.add_assoc b,
    ProofLib.ObjectLoad.adrp_page_of_aligned hb]
  rfl

private theorem adrp_page_left_ext {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr coinsFillName + bv% 28) &&& bv% (2 ^ 64 - 4096)) =
      b + bv% (page% (ls_off% "signal_session_coins_fill" + 28)) := by
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "signal_session_coins_fill"), BitVec.add_assoc b,
    ProofLib.ObjectLoad.adrp_page_of_aligned hb]
  rfl

private theorem csel_min_eq_ext (rem len : Nat) (x1 : BitVec 64)
    (hrem : rem < 2 ^ 64) (hx1 : x1.toNat = len) :
    (if (BitVec.ofNat 64 rem).ult x1 = true then BitVec.ofNat 64 rem else x1) =
      BitVec.ofNat 64 (min len rem) := by
  have hx1_bv : x1 = BitVec.ofNat 64 len := by rw [← hx1]; simp
  split
  · rename_i hult
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrem, hx1, decide_eq_true_eq] at hult
    have hmin : min len rem = rem := by omega
    rw [hmin]
  · rename_i hult
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrem, hx1, decide_eq_true_eq] at hult
    have hmin : min len rem = len := by omega
    rw [hmin, hx1_bv]

private theorem bv_sub_of_le_ext {a k : Nat} (hk : k ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 k = BitVec.ofNat 64 (a - k) := by
  have ha : a = (a - k) + k := (Nat.sub_add_cancel hk).symm
  conv_lhs => rw [ha, BitVec.ofNat_add]
  bv_arith

private theorem reg_sub_of_le_ext {x1 : BitVec 64} {len k : Nat}
    (hx1 : x1.toNat = len) (hk : k ≤ len) :
    x1 - BitVec.ofNat 64 k = BitVec.ofNat 64 (len - k) := by
  have hx1_bv : x1 = BitVec.ofNat 64 len := by rw [← hx1]; simp
  rw [hx1_bv]
  exact bv_sub_of_le_ext hk

private theorem fill_bytes_eq_ext (rest : List (BitVec 8)) (len : Nat) :
    rest.take (min len rest.length) ++ List.replicate (len - min len rest.length) 0#8 =
      (rest ++ List.replicate len 0#8).take len := by
  rw [List.take_append]
  by_cases hle : len ≤ rest.length
  · have hmin : min len rest.length = len := Nat.min_eq_left hle
    have hsub1 : len - min len rest.length = 0 := by omega
    have hsub2 : len - rest.length = 0 := by omega
    rw [hsub1, hmin, hsub2]
    simp
  · have hge : rest.length ≤ len := by omega
    have hmin : min len rest.length = rest.length := Nat.min_eq_right hge
    have hmin2 : min (len - rest.length) len = len - rest.length := by omega
    rw [hmin, List.take_length, List.take_of_length_le hge, List.take_replicate, hmin2]

private theorem dst_bytes_merge_ext (dst : BitVec 64) (len : Nat) (rest : List (BitVec 8)) :
    (dst ↦ₛ rest.take (min len rest.length)) ∗
      ((dst + BitVec.ofNat 64 (min len rest.length)) ↦ₛ
        List.replicate (len - min len rest.length) 0#8) =
    (dst ↦ₛ List.take len (rest ++ List.replicate len 0#8)) := by
  have htake_len : (rest.take (min len rest.length)).length = min len rest.length :=
    List.length_take_of_le (Nat.min_le_right len rest.length)
  rw [← fill_bytes_eq_ext rest len, pointsToBytes_append, htake_len]

private theorem post_merge_ext (dst cur nx lf : BitVec 64) (len : Nat) (rest : List (BitVec 8)) :
    (dst ↦ₛ List.take (min len rest.length) rest) ∗
      ((dst + BitVec.ofNat 64 (min len rest.length)) ↦ₛ
        List.replicate (len - min len rest.length) 0#8) ∗
      (cur ↦ₛ List.take (min len rest.length) rest) ∗
      ((cur + BitVec.ofNat 64 (min len rest.length)) ↦ₛ
        List.drop (min len rest.length) rest) ∗
      (nx ↦₆₄ (cur + BitVec.ofNat 64 (min len rest.length))) ∗
      (lf ↦₆₄ BitVec.ofNat 64 (rest.length - min len rest.length)) ⊢
    (dst ↦ₛ List.take len (rest ++ List.replicate len 0#8)) ∗
      tapeAfter2 nx lf cur rest (min len rest.length) := by
  apply Entails.of_eq
  have htake_len : (rest.take (min len rest.length)).length = min len rest.length :=
    List.length_take_of_le (Nat.min_le_right len rest.length)
  have hcur : (cur ↦ₛ rest) =
      (cur ↦ₛ List.take (min len rest.length) rest) ∗
        ((cur + BitVec.ofNat 64 (min len rest.length)) ↦ₛ
          List.drop (min len rest.length) rest) := by
    conv_lhs => rw [(List.take_append_drop (min len rest.length) rest).symm]
    rw [pointsToBytes_append, htake_len]
  unfold tapeAfter2
  rw [← dst_bytes_merge_ext dst len rest, hcur]
  sep_ac_rfl

private theorem stackAt_split_bottom_coins_ext (sp : BitVec 64) (n d : Nat) (h : n + d ≤ 2 ^ 64) :
    stackAt sp (n + d) = stackAt (sp - BitVec.ofNat 64 n) d ∗ stackAt sp n := by
  simp only [stackAt]
  rw [show n + d = d + n by omega, memRegion_split _ d n (by omega)]
  congr 2
  · bv_arith
  · rw [BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 d), ← BitVec.sub_sub,
      BitVec.sub_add_cancel]

private theorem memRegion_80_words_ext (sp : BitVec 64) :
    memRegion (sp - 80#64) 80 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64,
        ∃∗ u8 : BitVec 64, ∃∗ u9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ u9) ∗ ((sp - 72#64) ↦₆₄ u8) ∗ ((sp - 64#64) ↦₆₄ u7) ∗
        ((sp - 56#64) ↦₆₄ u6) ∗ ((sp - 48#64) ↦₆₄ u5) ∗ ((sp - 40#64) ↦₆₄ u4) ∗
        ((sp - 32#64) ↦₆₄ u3) ∗ ((sp - 24#64) ↦₆₄ u2) ∗ ((sp - 16#64) ↦₆₄ u1) ∗
        ((sp - 8#64) ↦₆₄ u0)) := by
  rw [memRegion_split (sp - 80#64) 8 72 (by decide),
    memRegion_split (sp - 80#64 + 8#64) 8 64 (by decide),
    memRegion_split (sp - 80#64 + 8#64 + 8#64) 8 56 (by decide),
    memRegion_split (sp - 80#64 + 8#64 + 8#64 + 8#64) 8 48 (by decide),
    memRegion_split (sp - 80#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 40 (by decide),
    memRegion_split (sp - 80#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    memRegion_split (sp - 80#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    memRegion_split (sp - 80#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (sp - 80#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight]
  have h72 : sp - 80#64 + 8#64 = sp - 72#64 := by bv_arith
  have h64 : sp - 72#64 + 8#64 = sp - 64#64 := by bv_arith
  have h56 : sp - 64#64 + 8#64 = sp - 56#64 := by bv_arith
  have h48 : sp - 56#64 + 8#64 = sp - 48#64 := by bv_arith
  have h40 : sp - 48#64 + 8#64 = sp - 40#64 := by bv_arith
  have h32 : sp - 40#64 + 8#64 = sp - 32#64 := by bv_arith
  have h24 : sp - 32#64 + 8#64 = sp - 24#64 := by bv_arith
  have h16 : sp - 24#64 + 8#64 = sp - 16#64 := by bv_arith
  have h8 : sp - 16#64 + 8#64 = sp - 8#64 := by bv_arith
  simp only [h72, h64, h56, h48, h40, h32, h24, h16, h8,
    sepExists_sepConj_left, sepExists_sepConj_right]

private theorem memRegion_80_words_fold_ext (sp : BitVec 64)
    (v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 : BitVec 64) :
    (((sp - 80#64) ↦₆₄ v9) ∗ ((sp - 72#64) ↦₆₄ v8) ∗ ((sp - 64#64) ↦₆₄ v7) ∗
      ((sp - 56#64) ↦₆₄ v6) ∗ ((sp - 48#64) ↦₆₄ v5) ∗ ((sp - 40#64) ↦₆₄ v4) ∗
      ((sp - 32#64) ↦₆₄ v3) ∗ ((sp - 24#64) ↦₆₄ v2) ∗ ((sp - 16#64) ↦₆₄ v1) ∗
      ((sp - 8#64) ↦₆₄ v0)) ⊢
    memRegion (sp - 80#64) 80 := by
  rw [memRegion_80_words_ext sp]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
      (Entails.sepExists_right v6 (Entails.sepExists_right v7 (Entails.sepExists_right v8
        (Entails.sepExists_right v9 (Entails.refl _))))))))))

private theorem stackAt_coinsFill_split_ext (sp : BitVec 64) (stk : Nat)
    (hstk : 0x50 ≤ stk) (hstk' : stk ≤ 2 ^ 63) :
    stackAt sp stk =
      stackAt (sp - 80#64) (stk - 80) ∗
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64,
        ∃∗ u8 : BitVec 64, ∃∗ u9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ u9) ∗ ((sp - 72#64) ↦₆₄ u8) ∗ ((sp - 64#64) ↦₆₄ u7) ∗
        ((sp - 56#64) ↦₆₄ u6) ∗ ((sp - 48#64) ↦₆₄ u5) ∗ ((sp - 40#64) ↦₆₄ u4) ∗
        ((sp - 32#64) ↦₆₄ u3) ∗ ((sp - 24#64) ↦₆₄ u2) ∗ ((sp - 16#64) ↦₆₄ u1) ∗
        ((sp - 8#64) ↦₆₄ u0)) := by
  have heq : stk = 80 + (stk - 80) := by omega
  conv_lhs => rw [heq]
  rw [stackAt_split_bottom_coins_ext sp 80 (stk - 80) (by omega)]
  change stackAt (sp - 80#64) (stk - 80) ∗ memRegion (sp - 80#64) 80 = _
  rw [memRegion_80_words_ext sp]

private theorem stackAt_coinsFill_merge_ext (sp : BitVec 64) (stk : Nat)
    (hstk : 0x50 ≤ stk) (hstk' : stk ≤ 2 ^ 63)
    (v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 : BitVec 64) :
    stackAt (sp - 80#64) (stk - 80) ∗
      (((sp - 80#64) ↦₆₄ v9) ∗ ((sp - 72#64) ↦₆₄ v8) ∗ ((sp - 64#64) ↦₆₄ v7) ∗
        ((sp - 56#64) ↦₆₄ v6) ∗ ((sp - 48#64) ↦₆₄ v5) ∗ ((sp - 40#64) ↦₆₄ v4) ∗
        ((sp - 32#64) ↦₆₄ v3) ∗ ((sp - 24#64) ↦₆₄ v2) ∗ ((sp - 16#64) ↦₆₄ v1) ∗
        ((sp - 8#64) ↦₆₄ v0)) ⊢
    stackAt sp stk := by
  have heq : stk = 80 + (stk - 80) := by omega
  conv_rhs => rw [heq]
  rw [stackAt_split_bottom_coins_ext sp 80 (stk - 80) (by omega)]
  exact sepConj_mono_right (memRegion_80_words_fold_ext sp v9 v8 v7 v6 v5 v4 v3 v2 v1 v0)

private theorem session_memcpy_region_of_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsMem4K b A ext)
    (stk : Nat) (hstk : allocHookStack ≤ stk) (hstk' : stk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr coinsFillName +
        BitVec.ofNat 64 (num% (ls_off% "memcpy" - ls_off% "signal_session_coins_fill")))
      (withStack sessionMemcpyRegionSpec stk) := by
  have h := hA.session_memcpy_ok_at "signal_session_coins_fill"
    (num% (ls_off% "memcpy" - ls_off% "signal_session_coins_fill"))
    (by simp only [arm64_norm])
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp stk =
      stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) (stk - allocHookStack) ∗
        stackAt s0.sp allocHookStack := by
    have heq : stk = allocHookStack + (stk - allocHookStack) := by omega
    conv_lhs => rw [heq]
    exact stackAt_split_bottom_coins_ext s0.sp allocHookStack (stk - allocHookStack) (by omega)
  have hpre' : s0.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec allocHookStack).pre x s0 ∗
      (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) (stk - allocHookStack) ∗ R) := by
    dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec, libcMemcpySpec] at hpre ⊢
    rw [hsplit] at hpre
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  refine h.mono_outcome x
    (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) (stk - allocHookStack) ∗ R)
    s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec, libcMemcpySpec] at hpost ⊢
    rw [hsplit]
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hpost
  · exact (not_satisfies_false_sepConj hpan.2).elim
  · rcases hex with ⟨_, _, hex'⟩ | ⟨_, hoom⟩
    · exact (not_satisfies_false_sepConj hex').elim
    · exact (not_satisfies_false_sepConj hoom).elim

private theorem session_memset_region_of_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsMem4K b A ext)
    (stk : Nat) (hstk : allocHookStack ≤ stk) (hstk' : stk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr coinsFillName +
        BitVec.ofNat 64 (num% (ls_off% "memset" - ls_off% "signal_session_coins_fill")))
      (withStack sessionMemsetRegionSpec stk) := by
  have h := hA.session_memset_ok_at "signal_session_coins_fill"
    (num% (ls_off% "memset" - ls_off% "signal_session_coins_fill"))
    (by simp only [arm64_norm])
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp stk =
      stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) (stk - allocHookStack) ∗
        stackAt s0.sp allocHookStack := by
    have heq : stk = allocHookStack + (stk - allocHookStack) := by omega
    conv_lhs => rw [heq]
    exact stackAt_split_bottom_coins_ext s0.sp allocHookStack (stk - allocHookStack) (by omega)
  have hpre' : s0.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.sessionMemsetSpec allocHookStack).pre x s0 ∗
      (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) (stk - allocHookStack) ∗ R) := by
    dsimp only [withStack, sessionMemsetRegionSpec, memsetRegionSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemsetSpec, libcMemsetSpec] at hpre ⊢
    rw [hsplit] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    refine ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1⟩, ?_⟩
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre.2
  refine h.mono_outcome x
    (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) (stk - allocHookStack) ∗ R)
    s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, sessionMemsetRegionSpec, memsetRegionSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemsetSpec, libcMemsetSpec] at hpost ⊢
    rw [hsplit]
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hpost
  · exact (not_satisfies_false_sepConj hpan.2).elim
  · rcases hex with ⟨_, _, hex'⟩ | ⟨_, hoom⟩
    · exact (not_satisfies_false_sepConj hex').elim
    · exact (not_satisfies_false_sepConj hoom).elim

/-- `signal_session_coins_fill` meets `coinsFillSpec b stk` on `tripleRatchetProgAtExt b ext`
from any `(stk - 80)`-stack `memcpy`/`memset` hooks (`0x50 ≤ stk ≤ 2 ^ 63`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.BS10.coinsFill_ok_of_mem_hooks
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (stk : Nat) (hstk : 0x50 ≤ stk) (hstk' : stk ≤ 2 ^ 63)
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr coinsFillName +
        BitVec.ofNat 64 (num% (ls_off% "memcpy" - ls_off% "signal_session_coins_fill")))
      (withStack sessionMemcpyRegionSpec (stk - 80)))
    (hmemset : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr coinsFillName +
        BitVec.ofNat 64 (num% (ls_off% "memset" - ls_off% "signal_session_coins_fill")))
      (withStack sessionMemsetRegionSpec (stk - 80))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr coinsFillName) (coinsFillSpec b stk) := by
  have hfn : libsignalSessionCode.fnOff coinsFillName = num% (ls_off% "signal_session_coins_fill") :=
    ls_lemma% fnOff "signal_session_coins_fill"
  code_fetches CryptoVerification.libsignalSessionCode coinsFillExtBin b
    (Rust.withPanics ext) hfn (num% (ls_off% "signal_session_coins_fill")) 120
  clear hfn
  dsimp only [tripleRatchetProgAtExt] at *
  simp only [coinsFillSpec, coinsAfter, tapeAfter2_zero_eq]
  wp_init x s0
  have hpc' : s0.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr coinsFillName := by
    rw [Program.fnAddr_rebase, ls_lemma% fnOff "signal_session_coins_fill"]
    exact hpc
  clear hpc
  have hadrp_next := adrp_page_next_ext (H := Rust.withPanics ext) hb
  have hadrp_left := adrp_page_left_ext (H := Rust.withPanics ext) hb
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr coinsFillName = fnEntry
  examples_hide_fetches
  obtain ⟨dst, len, cur, rest⟩ := x
  dsimp only at *
  have hrest_lt64 : rest.length < 2 ^ 64 := by
    by_cases hpos : 0 < rest.length
    · have hmem_disj : s0.mem ⊨ (coinsNext b ↦₆₄ cur) ∗ ((cur ↦ₛ rest) ∗
          (memRegion dst len ∗ (coinsLeft b ↦₆₄ BitVec.ofNat 64 rest.length) ∗
            stackAt s0.sp stk ∗ R)) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpre
        sep_ac_rfl
      have hdisj := IsBlock.disjoint (IsBlock.pointsTo64 (coinsNext b) cur)
        (IsBlock.pointsToBytes cur rest) (by decide) hpos hmem_disj
      have h2 := hdisj.2
      have hlt : (coinsNext b - cur).toNat < 2 ^ 64 := (coinsNext b - cur).isLt
      omega
    · omega
  set k := min len rest.length
  have hx1 : (s0.readReg64 (Reg.gpr 1#5)).toNat = len := by assumption
  have hlen_lt64 : len < 2 ^ 64 := hx1 ▸ (s0.readReg64 (Reg.gpr 1#5)).isLt
  have hk_le_len : k ≤ len := Nat.min_le_left len rest.length
  have hk_le_rest : k ≤ rest.length := Nat.min_le_right len rest.length
  have htake_len : (rest.take k).length = k := List.length_take_of_le hk_le_rest
  have hcsel :
      (if (BitVec.ofNat 64 rest.length).ult (s0.readReg64 (Reg.gpr 1#5)) = true then
        BitVec.ofNat 64 rest.length
      else s0.readReg64 (Reg.gpr 1#5)) = BitVec.ofNat 64 k :=
    csel_min_eq_ext rest.length len (s0.readReg64 (Reg.gpr 1#5)) hrest_lt64 hx1
  have hrem_sub : BitVec.ofNat 64 rest.length - BitVec.ofNat 64 k =
      BitVec.ofNat 64 (rest.length - k) := bv_sub_of_le_ext hk_le_rest
  have hlen_sub : s0.readReg64 (Reg.gpr 1#5) - BitVec.ofNat 64 k =
      BitVec.ofNat 64 (len - k) := reg_sub_of_le_ext hx1 hk_le_len
  have hk_toNat : (BitVec.ofNat 64 k).toNat = (List.take k rest).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hk_le_len hlen_lt64), htake_len]
  have hrem_len_toNat : (BitVec.ofNat 64 (len - k)).toNat = len - k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len - k < 2 ^ 64)]
  have hdst_split : memRegion dst len =
      memRegion dst (rest.take k).length ∗ memRegion (dst + BitVec.ofNat 64 k) (len - k) := by
    have hlen_eq : len = k + (len - k) := by omega
    conv_lhs => rw [hlen_eq]
    rw [memRegion_split dst k (len - k) (by omega), htake_len]
  have hcur_split : (cur ↦ₛ rest) =
      (cur ↦ₛ rest.take k) ∗ ((cur + BitVec.ofNat 64 k) ↦ₛ rest.drop k) := by
    conv_lhs => rw [(List.take_append_drop k rest).symm]
    rw [pointsToBytes_append, htake_len]
  wp_conv_pre =>
    rw [stackAt_coinsFill_split_ext s0.sp stk hstk hstk']
  wp_pull_exists
  wp_conv_pre =>
    rw [hdst_split, hcur_split]
    simp only [sepConj_assoc]
  wp_steps
  wp_call hmemcpy
  wp_steps
  wp_call hmemset
  wp_steps
  have htr2 := hpost_1.trans hpost
  apply SepWP.fold (stackAt_coinsFill_merge_ext s0.sp stk hstk hstk' _ _ _ _ _ _ _ _ _ _) (by sep_focus)
  apply SepWP.fold (post_merge_ext dst cur (coinsNext b) (coinsLeft b) len rest) (by sep_focus)
  wp_done

/-- `coinsFillAtSpec` at `tryDecryptName + rel("signal_session_coins_fill")` from
`AllocContractsMem4K b A ext` (`4096`-byte `memcpy`/`memset` stack). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.BS10.coinsFillAt_ok_td_4k
    {b : BitVec 64} {A : RustAlloc} {cur : BitVec 64} {rest : List (BitVec 8)}
    {ext : String → Option (State → State)}
    (hA : AllocContractsMem4K b A ext) (hb : b &&& 0xfff#64 = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        bv% ((2 ^ 64 + ls_off% "signal_session_coins_fill" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64))
      (coinsFillAtSpec b tryDecryptSubStack cur rest) := by
  refine coinsFillAt_of_after0 (sub_ok_at_of_fnAddr (sym := "signal_session_coins_fill") ?_
    "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"
    (num% (ls_off% "signal_session_coins_fill" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))
    (by simp only [arm64_norm]))
  exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.BS10.coinsFill_ok_of_mem_hooks
    hb tryDecryptSubStack (by decide) (by decide)
    (session_memcpy_region_of_4k hA (tryDecryptSubStack - 80) (by decide) (by decide))
    (session_memset_region_of_4k hA (tryDecryptSubStack - 80) (by decide) (by decide))

/-- `coinsFillAtSpec.inImage img` at `tryDecryptName + rel("signal_session_coins_fill")` directly
from `CoinsFillOk_ext img ext` (stated structurally without importing `Trap/ExtDefs`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.BS10.coinsFillAt_ok_td_of_ok
    {img : Obj.Image} {cur : BitVec 64} {rest : List (BitVec 8)}
    {ext : String → Option (State → State)}
    (hcf : ∀ (stk : Nat), 0x50 + CryptoVerification.SignalSession.CliExt.memHookStack ≤ stk →
      stk ≤ 2 ^ 63 →
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr coinsFillName)
        ((coinsFillSpec img.base stk).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        bv% ((2 ^ 64 + ls_off% "signal_session_coins_fill" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64))
      ((coinsFillAtSpec img.base tryDecryptSubStack cur rest).inImage img) := by
  have h0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        bv% ((2 ^ 64 + ls_off% "signal_session_coins_fill" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64))
      ((coinsFillSpec img.base tryDecryptSubStack).inImage img) :=
    sub_ok_at_of_fnAddr (sym := "signal_session_coins_fill")
      (hcf tryDecryptSubStack (by decide) (by decide))
      "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"
      (num% (ls_off% "signal_session_coins_fill" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))
      (by simp only [arm64_norm])
  refine subroutine_ok_outcome_intro fun ⟨dst, len⟩ R s0 hpc hrun hpre hal => ?_
  refine h0.mono_outcome ⟨dst, len, cur, rest⟩ R s0 hpc hrun
    (by simpa only [Spec.inImage, coinsFillAtSpec, coinsFillSpec] using hpre) hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · exact Or.inl ⟨hret, hcc, by simpa only [Spec.inImage, coinsFillAtSpec, coinsFillSpec] using hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

private theorem session_memcpy_region_inImage_of_s2 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)} (hS2 : Stage2ContractsExt img C A ext)
    (stk : Nat) (hstk : CryptoVerification.SignalSession.CliExt.memHookStack ≤ stk)
    (hstk' : stk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr coinsFillName +
        BitVec.ofNat 64 (num% (ls_off% "memcpy" - ls_off% "signal_session_coins_fill")))
      ((withStack sessionMemcpyRegionSpec stk).inImage img) := by
  have h := hS2.session_memcpy_mem_ok_at "signal_session_coins_fill"
    (num% (ls_off% "memcpy" - ls_off% "signal_session_coins_fill"))
    (by simp only [arm64_norm]) stk hstk hstk'
  refine subroutine_ok_mono h (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
  · simpa only [Spec.inImage, CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec, libcMemcpySpec,
      withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc] using hpre
  · simpa only [Spec.inImage, CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec, libcMemcpySpec,
      withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc] using hpost

private theorem session_memset_region_inImage_of_s2 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)} (hS2 : Stage2ContractsExt img C A ext)
    (stk : Nat) (hstk : CryptoVerification.SignalSession.CliExt.memHookStack ≤ stk)
    (hstk' : stk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr coinsFillName +
        BitVec.ofNat 64 (num% (ls_off% "memset" - ls_off% "signal_session_coins_fill")))
      ((withStack sessionMemsetRegionSpec stk).inImage img) := by
  have h := hS2.session_memset_mem_ok_at "signal_session_coins_fill"
    (num% (ls_off% "memset" - ls_off% "signal_session_coins_fill"))
    (by simp only [arm64_norm]) stk hstk hstk'
  refine subroutine_ok_mono h (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
  · dsimp only [Spec.inImage, CryptoVerification.LibsignalTripleRatchet.sessionMemsetSpec, libcMemsetSpec,
      withStack, sessionMemsetRegionSpec, memsetRegionSpec] at hpre ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨hpre.1, ⟨hpre.2.1.1, hpre.2.1.2.1, hpre.2.1.2.2.1⟩, hpre.2.2⟩
  · simpa only [Spec.inImage, CryptoVerification.LibsignalTripleRatchet.sessionMemsetSpec, libcMemsetSpec,
      withStack, sessionMemsetRegionSpec, memsetRegionSpec, sepConj_assoc] using hpost

/-- `signal_session_coins_fill` meets `(coinsFillSpec img.base stk).inImage img` for every
`0x50 + CliExt.memHookStack ≤ stk ≤ 2 ^ 63` from `Stage2ContractsExt img C A ext`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.BS10.coinsFill_inImage_ok_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ext : String → Option (State → State)}
    (hS2 : Stage2ContractsExt img C A ext) (hb : img.base &&& 0xfff#64 = 0#64)
    (stk : Nat) (hstk : 0x50 + CryptoVerification.SignalSession.CliExt.memHookStack ≤ stk)
    (hstk' : stk ≤ 2 ^ 63) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr coinsFillName)
      ((coinsFillSpec img.base stk).inImage img) := by
  have hmemcpy := session_memcpy_region_inImage_of_s2 hS2 (stk - 80) (by omega) (by omega)
  have hmemset := session_memset_region_inImage_of_s2 hS2 (stk - 80) (by omega) (by omega)
  have hfn : libsignalSessionCode.fnOff coinsFillName = num% (ls_off% "signal_session_coins_fill") :=
    ls_lemma% fnOff "signal_session_coins_fill"
  code_fetches CryptoVerification.libsignalSessionCode coinsFillExtBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "signal_session_coins_fill")) 120
  clear hfn hS2
  dsimp only [tripleRatchetProgAtExt] at *
  simp only [Spec.inImage, coinsFillSpec, coinsAfter, tapeAfter2_zero_eq]
  wpp_init x s0
  have hpc' : s0.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr coinsFillName := by
    rw [Program.fnAddr_rebase, ls_lemma% fnOff "signal_session_coins_fill"]
    exact hpc
  clear hpc
  have hadrp_next := adrp_page_next_ext (H := Rust.withPanics ext) hb
  have hadrp_left := adrp_page_left_ext (H := Rust.withPanics ext) hb
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr coinsFillName = fnEntry
  examples_hide_fetches
  obtain ⟨dst, len, cur, rest⟩ := x
  dsimp only at *
  have hrest_lt64 : rest.length < 2 ^ 64 := by
    by_cases hpos : 0 < rest.length
    · have hmem_disj : s0.mem ⊨ (coinsNext img.base ↦₆₄ cur) ∗ ((cur ↦ₛ rest) ∗
          (memRegion dst len ∗ (coinsLeft img.base ↦₆₄ BitVec.ofNat 64 rest.length) ∗
            stackAt s0.sp stk ∗ R)) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpre
        sep_ac_rfl
      have hdisj := IsBlock.disjoint (IsBlock.pointsTo64 (coinsNext img.base) cur)
        (IsBlock.pointsToBytes cur rest) (by decide) hpos hmem_disj
      have h2 := hdisj.2
      have hlt : (coinsNext img.base - cur).toNat < 2 ^ 64 := (coinsNext img.base - cur).isLt
      omega
    · omega
  set k := min len rest.length
  have hx1 : (s0.readReg64 (Reg.gpr 1#5)).toNat = len := by assumption
  have hlen_lt64 : len < 2 ^ 64 := hx1 ▸ (s0.readReg64 (Reg.gpr 1#5)).isLt
  have hk_le_len : k ≤ len := Nat.min_le_left len rest.length
  have hk_le_rest : k ≤ rest.length := Nat.min_le_right len rest.length
  have htake_len : (rest.take k).length = k := List.length_take_of_le hk_le_rest
  have hcsel :
      (if (BitVec.ofNat 64 rest.length).ult (s0.readReg64 (Reg.gpr 1#5)) = true then
        BitVec.ofNat 64 rest.length
      else s0.readReg64 (Reg.gpr 1#5)) = BitVec.ofNat 64 k :=
    csel_min_eq_ext rest.length len (s0.readReg64 (Reg.gpr 1#5)) hrest_lt64 hx1
  have hrem_sub : BitVec.ofNat 64 rest.length - BitVec.ofNat 64 k =
      BitVec.ofNat 64 (rest.length - k) := bv_sub_of_le_ext hk_le_rest
  have hlen_sub : s0.readReg64 (Reg.gpr 1#5) - BitVec.ofNat 64 k =
      BitVec.ofNat 64 (len - k) := reg_sub_of_le_ext hx1 hk_le_len
  have hk_toNat : (BitVec.ofNat 64 k).toNat = (List.take k rest).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hk_le_len hlen_lt64), htake_len]
  have hrem_len_toNat : (BitVec.ofNat 64 (len - k)).toNat = len - k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len - k < 2 ^ 64)]
  have hdst_split : memRegion dst len =
      memRegion dst (rest.take k).length ∗ memRegion (dst + BitVec.ofNat 64 k) (len - k) := by
    have hlen_eq : len = k + (len - k) := by omega
    conv_lhs => rw [hlen_eq]
    rw [memRegion_split dst k (len - k) (by omega), htake_len]
  have hcur_split : (cur ↦ₛ rest) =
      (cur ↦ₛ rest.take k) ∗ ((cur + BitVec.ofNat 64 k) ↦ₛ rest.drop k) := by
    conv_lhs => rw [(List.take_append_drop k rest).symm]
    rw [pointsToBytes_append, htake_len]
  wp_conv_pre =>
    rw [stackAt_coinsFill_split_ext s0.sp stk (by omega) hstk', hdst_split, hcur_split]
    simp only [sepConj_assoc]
  apply CryptoVerification.SepWPp.of_sepWP_frozen ‹_› ‹_›
    (mid := fnEntry + bv% (ls_off% "memcpy" - ls_off% "signal_session_coins_fill"))
  wp_pull_exists
  wp_steps
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  intro hfl1 hsym1
  wpp_call hmemcpy
  apply CryptoVerification.SepWPp.of_sepWP_frozen ‹_› ‹_›
    (mid := fnEntry + bv% (ls_off% "memset" - ls_off% "signal_session_coins_fill"))
  wp_steps
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  intro hfl2 hsym2
  wpp_call hmemset
  apply SepWPp.of_sepWP_ret
  wp_steps
  have htr2 := hpost_1.trans hpost
  apply SepWP.fold (stackAt_coinsFill_merge_ext s0.sp stk (by omega) hstk' _ _ _ _ _ _ _ _ _ _) (by sep_focus)
  apply SepWP.fold (post_merge_ext dst cur (coinsNext img.base) (coinsLeft img.base) len rest) (by sep_focus)
  wp_done

/-- `coinsFillAtSpec.inImage img` at `tryDecryptName + rel("signal_session_coins_fill")` directly
from `Stage2ContractsExt img C A ext`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.BS10.coinsFillAt_ok_td_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {cur : BitVec 64} {rest : List (BitVec 8)}
    {ext : String → Option (State → State)}
    (hS2 : Stage2ContractsExt img C A ext) (hb : img.base &&& 0xfff#64 = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        bv% ((2 ^ 64 + ls_off% "signal_session_coins_fill" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64))
      ((coinsFillAtSpec img.base tryDecryptSubStack cur rest).inImage img) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.BS10.coinsFillAt_ok_td_of_ok
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.BS10.coinsFill_inImage_ok_ext hS2 hb)

/-- `<StaticSecret as Drop>::drop` at `tryDecryptName + rel(staticDropName)` from
`Stage2ContractsExt img C A ext` (`(withStack zeroizeSecretSpec extHookStack).inImage img`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.BS10.staticDrop_ok_at2_td_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ext : String → Option (State → State)}
    (hS2 : Stage2ContractsExt img C A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        bv% ((2 ^ 64 + ls_off% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64))
      ((withStack zeroizeSecretSpec extHookStack).inImage img) :=
  sub_ok_at_of_fnAddr
    (sym := "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop")
    hS2.static_drop
    "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"
    (num% (ls_off% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))
    (by simp only [arm64_norm])

end BS10

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegDhDefs
