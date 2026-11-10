/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtDefs
public import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtFindCmk
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.Callees
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropChain2Ext
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCreateChain
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCtPkEq
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtGenKeysMac
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtTrFromX
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.Common
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt
import LibsignalBinary.Proofs.TripleRatchet.Alloc.ChainKeyToPb
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Identity
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom

@[expose] public section

set_option autoImplicit false

/-!
# Contract-Backed Callees for Handshake `try_decrypt_with_state::<Coins>`

Discharges the 18 callee `subroutine_ok` obligations in `TryDecryptCallees_ext`
on `tripleRatchetProgAtExt img.base (cliExternsWith ext)` from `CliExternsOk P A ext`
and `Obj.Loads libsignalSessionImage img`.
-/

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (libsignalSessionCode libsignalSessionImage)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (AllocContractsX RemoteIdentityKeyOkExt
  TrApplyOkX sessionMemcpyRegionSpec sessionMemsetRegionSpec tripleRatchetProgAtExt withStack)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (DerivePublicKeyBytesOkX)
open CryptoVerification.SignalSession.Coins (coinsAfter coinsFillName coinsFillSpec coinsLeft
  coinsNext tapeAfter2 tapeAfter2_zero_eq)
open CryptoVerification.SignalSession.Cli.Slots (Stage2ContractsExt)

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtCallees

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private gen_decodes CryptoVerification.libsignalSessionCode_tree coinsFillCalleesBin
  [(ls_off% "signal_session_coins_fill") → (ls_off% "signal_session_coins_fill" + 116)]

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
  · simpa only [Spec.inImage, CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec,
      libcMemcpySpec, withStack, sessionMemcpyRegionSpec,
      memcpyRegionSpec, sepConj_assoc] using hpre
  · simpa only [Spec.inImage, CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec,
      libcMemcpySpec, withStack, sessionMemcpyRegionSpec,
      memcpyRegionSpec, sepConj_assoc] using hpost

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
  · dsimp only [Spec.inImage, CryptoVerification.LibsignalTripleRatchet.sessionMemsetSpec,
      libcMemsetSpec, withStack, sessionMemsetRegionSpec,
      memsetRegionSpec] at hpre ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨hpre.1, ⟨hpre.2.1.1, hpre.2.1.2.1, hpre.2.1.2.2.1⟩, hpre.2.2⟩
  · simpa only [Spec.inImage, CryptoVerification.LibsignalTripleRatchet.sessionMemsetSpec,
      libcMemsetSpec, withStack, sessionMemsetRegionSpec,
      memsetRegionSpec, sepConj_assoc] using hpost

/-- `signal_session_coins_fill` meets `CoinsFillOk_ext img (cliExternsWith ext)` under
`CliExternsOk P A ext` and `Obj.Loads libsignalSessionImage img`. -/
theorem coinsFill_ok_ext
    {P : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CryptoVerification.SignalSession.CliExternsOk P A ext)
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.CoinsFillOk_ext
      img (CryptoVerification.SignalSession.cliExternsWith ext) := by
  intro stk hstk hstk'
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.coinsFillStackExt] at hstk
  have hS2 : Stage2ContractsExt img P.C A (CryptoVerification.SignalSession.cliExternsWith ext) :=
    Stage2ContractsExt.of_externsOk hOk img
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hmemcpy := session_memcpy_region_inImage_of_s2 hS2 (stk - 80) (by omega) (by omega)
  have hmemset := session_memset_region_inImage_of_s2 hS2 (stk - 80) (by omega) (by omega)
  have hfn : libsignalSessionCode.fnOff coinsFillName = num% (ls_off% "signal_session_coins_fill") :=
    ls_lemma% fnOff "signal_session_coins_fill"
  code_fetches CryptoVerification.libsignalSessionCode coinsFillCalleesBin img.base
    (Rust.withPanics (CryptoVerification.SignalSession.cliExternsWith ext))
    hfn (num% (ls_off% "signal_session_coins_fill")) 120
  clear hfn hS2 hOk himg
  dsimp only [tripleRatchetProgAtExt] at *
  simp only [Spec.inImage, coinsFillSpec, coinsAfter, tapeAfter2_zero_eq]
  wpp_init x s0
  have hpc' : s0.pc =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (CryptoVerification.SignalSession.cliExternsWith ext))).fnAddr
        coinsFillName := by
    rw [Program.fnAddr_rebase, ls_lemma% fnOff "signal_session_coins_fill"]
    exact hpc
  clear hpc
  have hadrp_next := adrp_page_next_ext
    (H := Rust.withPanics (CryptoVerification.SignalSession.cliExternsWith ext)) hb
  have hadrp_left := adrp_page_left_ext
    (H := Rust.withPanics (CryptoVerification.SignalSession.cliExternsWith ext)) hb
  generalize_entry
    (libsignalSessionCode.rebase img.base
      (Rust.withPanics (CryptoVerification.SignalSession.cliExternsWith ext))).fnAddr
      coinsFillName = fnEntry
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

/-- `<PrivateKey>::derive_public_key_bytes` meets `DerivePublicKeyBytesOkX img P.C (cliExternsWith ext)`
under `CliExternsOk P A ext`. -/
theorem derivePk_ok_ext
    {P : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CryptoVerification.SignalSession.CliExternsOk P A ext)
    (img : Obj.Image) :
    DerivePublicKeyBytesOkX img P.C (CryptoVerification.SignalSession.cliExternsWith ext) :=
  CryptoVerification.LibsignalTripleRatchet.derive_public_key_bytes_ok_ext_x
    (Stage2ContractsExt.of_externsOk hOk img).toStage2ContractsX

/-- Contract-backed callee bundle for handshake `try_decrypt_with_state::<Coins>`, using `ExtFindCmk.FindReceiverChainKeyOkExt144` (`logOff img` in `pre`/`post`) and parametric in `cmk : CmkOkX`. -/
structure TryDecryptCalleesLog_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (ext : String → Option (State → State)) : Prop where
  localIk : CryptoVerification.LibsignalTripleRatchet.Decrypt.LocalIdentityKeyOkExt img A ext
  remoteIk : RemoteIdentityKeyOkExt img A ext
  sameAcc : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.IsSameAccountOk_ext img.base ext
  sameAccDistinct :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.IsSameAccountDistinctOk_ext img.base A ext
  clearUpk : CryptoVerification.LibsignalTripleRatchet.Decrypt.ClearUpkOkX img A ext
  dropChain : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk_ext img.base A ext
  chainKeyToPb : CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainKeyToPbOkX img A ext
  derivePk : DerivePublicKeyBytesOkX img C ext
  trFrom : CryptoVerification.LibsignalTripleRatchet.TrFromOkX img A ext
  trApply : TrApplyOkX img A ext
  findReceiverChainKey :
    CryptoVerification.Cli.LibsignalTripleRatchet.ExtFindCmk.FindReceiverChainKeyOkExt144 img A ext
  createChain : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.CreateChainOk_ext img C A ext
  genKeys : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.GenerateKeysOk_ext img C A ext
  pkSer : CryptoVerification.LibsignalTripleRatchet.PublicKeySerializeOkX img A ext
  verifyMac :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.VerifyMacWithAddressesOk_ext img C A parse ext
  cmk : CryptoVerification.LibsignalTripleRatchet.Decrypt.CmkOkX img C A ext
  growOne : CryptoVerification.LibsignalTripleRatchet.Decrypt.GrowOneChainOkX img A ext
  coinsFill : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.CoinsFillOk_ext img ext

/-- Discharge all 18 `TryDecryptCalleesLog_ext` obligations on
`tripleRatchetProgAtExt img.base (cliExternsWith ext)` from `CliExternsOk P A ext`,
`Obj.Loads libsignalSessionImage img`, and `hcmk : CmkOkX`. -/
theorem tryDecryptPqCallees_of_cmk_ext
    {P : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CryptoVerification.SignalSession.CliExternsOk P A ext)
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img)
    (hcmk : CryptoVerification.LibsignalTripleRatchet.Decrypt.CmkOkX img P.C A
      (CryptoVerification.SignalSession.cliExternsWith ext)) :
    TryDecryptCalleesLog_ext img P.C A uuidTryParse
      (CryptoVerification.SignalSession.cliExternsWith ext) := by
  let ext' := CryptoVerification.SignalSession.cliExternsWith ext
  have hAg := CryptoVerification.SignalSession.Cli.Slots.AgreeOnCliHooks.cliExternsWith ext
  have hMem4K :=
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4K.of_hooks
      img.base A ext'
      (CryptoVerification.SignalSession.Cli.Slots.ext_allocHooks hOk)
      (CryptoVerification.SignalSession.Cli.Slots.ext_shim hOk)
      (CryptoVerification.SignalSession.Cli.Slots.ext_memcpy hOk)
      (CryptoVerification.SignalSession.Cli.Slots.ext_memmove hOk)
      (CryptoVerification.SignalSession.Cli.Slots.ext_memset hOk)
  have hWeak := CryptoVerification.SignalSession.Cli.Slots.stage2ContractsWeak_of_externsOk hOk img
  have hA :=
    CryptoVerification.SignalSession.Cli.Slots.allocContractsX_cliExternsWith_of_externsOk hOk img
  have h_bb :=
    CryptoVerification.Cli.LibsignalTripleRatchet.ExtCtPkEq.hookSat_blackBox32_of_externsOk_on
      hOk hAg
  have h_comp :=
    CryptoVerification.Cli.LibsignalTripleRatchet.ExtCtPkEq.hookSat_compress256_of_externsOk_on
      hOk hAg
  have hHkdf :=
    CryptoVerification.Cli.LibsignalTripleRatchet.ExtCtPkEq.hkdfContractsExt_of_externsOk_on
      img hOk hAg
  refine
    { localIk :=
        CryptoVerification.LibsignalTripleRatchet.Getters.local_identity_key_ok_ext img A ext'
          (CryptoVerification.LibsignalTripleRatchet.pkTryFrom_ok_ext img ext' himg)
      remoteIk :=
        CryptoVerification.LibsignalTripleRatchet.Glue.remoteIdentityKeyOk_ext img A ext' himg
      sameAcc :=
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPqAssembly.isSameAccount_ok_ext32
          img.base h_bb
      sameAccDistinct :=
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountEqDistinct_ok_ext32
          img.base A ext' h_bb
      clearUpk :=
        CryptoVerification.LibsignalTripleRatchet.Glue.clear_unacknowledged_pre_key_message_ok_ext_x hA
      dropChain :=
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.drop_chain2_of_dealloc_ext hMem4K.dealloc
      chainKeyToPb :=
        CryptoVerification.LibsignalTripleRatchet.chain_key_to_pb_ok_ext_x hA
      derivePk := derivePk_ok_ext hOk img
      trFrom :=
        CryptoVerification.Cli.LibsignalTripleRatchet.trFrom_ok_of_allocX himg hA
      trApply :=
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPqAssembly.trApply_ok_ext_x hA
      findReceiverChainKey :=
        CryptoVerification.Cli.LibsignalTripleRatchet.ExtFindCmk.findReceiverChainKey_ok_ext144_x
          himg
          (CryptoVerification.Cli.LibsignalTripleRatchet.ExtCtPkEq.findIndex_ok_of_blackBox32
            himg h_bb)
      createChain :=
        CryptoVerification.Cli.LibsignalTripleRatchet.ExtCreateChain.createChain_ok_ext_x
          himg hWeak hHkdf
          (CryptoVerification.Cli.LibsignalTripleRatchet.ExtCtPkEq.ctEqRO_inImage_of_blackBox32
            img h_bb)
      genKeys :=
        CryptoVerification.Cli.LibsignalTripleRatchet.ExtGenKeysMac.generateKeys_ok_stacked_ext_x
          himg hHkdf hA
      pkSer :=
        CryptoVerification.LibsignalTripleRatchet.Glue.publicKeySerializeOk_ext_x hA
      verifyMac :=
        CryptoVerification.Cli.LibsignalTripleRatchet.ExtGenKeysMac.verifyMacWithAddresses_ok_stacked_ext32
          img himg P.C A ext' hA hHkdf h_bb h_comp
      cmk := hcmk
      growOne :=
        CryptoVerification.Cli.LibsignalTripleRatchet.ExtFindCmk.growOneChain_ok_tr_ext_x hA
      coinsFill := coinsFill_ok_ext hOk img himg }

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtCallees
