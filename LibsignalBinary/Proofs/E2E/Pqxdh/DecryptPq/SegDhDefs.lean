/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.HookTrace
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhHChain
import LibsignalBinary.Proofs.FnOffEq
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhH -- shake: keep

/-!
# Shared Definitions and `Chain` Array Helpers for `S3Spec`

Hook wrappers, 104-byte `chainAt` / `vecBuf` decomposition lemmas, pure `dhRatchetStep` helpers, and
the `+0x8ac` commit checkpoint specification (`S3CommitState`, `S3CommitSpec`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegB

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.DecryptPq
open CryptoVerification.LibsignalSession
open CryptoVerification.HookTrace

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[simp, wp_norm] theorem calleeSavedVRegs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    calleeSavedVRegs (s.writeReg64 r v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    calleeSavedVRegs (s.writeReg32 r v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_setPC (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_setPState (s : State) (ps : PState) :
    calleeSavedVRegs (s.setPState ps) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_setMem (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_0 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 0#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_1 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 1#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_2 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 2#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_3 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 3#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_4 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 4#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_5 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 5#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_6 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 6#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_7 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 7#5 v) = calleeSavedVRegs s := rfl

/-! ## 1. Fetch Macro and Hook Helpers on `tripleRatchetProgAt` -/

open Lean Elab Tactic in
/-- `code_fetches_from <code> <decPrefix> b H hfn off k0 len` adds `<code>_fetch_fnAddr`
    hypotheses for the instructions `k = k0, k0 + 4, …, k0 + len - 4` of the function at offset
    `off` (`hfn : <code>.fnOff name = off`), using `<decPrefix>_decode_0x<off+k>`. -/
elab "code_fetches_from " codeId:ident decPrefix:ident b:term:max H:term:max hfn:ident
    off:num k0:num len:num : tactic => do
  let off := off.getNat
  let k0 := k0.getNat
  let len := len.getNat
  let codeBase := codeId.getId.eraseMacroScopes
  let decBase := decPrefix.getId.eraseMacroScopes
  let fetchEntry := mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let hex := String.ofList (Nat.toDigits 16 (off + k))
    let dec := mkIdent (decBase.appendAfter s!"_decode_0x{hex}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

/-- Fetch hypotheses for `try_decrypt_with_state::<HookRng>` (`hfn : fnOff tryDecryptName =
0x6eff8`),
    from fn-relative offset `k0`, `len` bytes. -/
macro "td_fetches " b:term:max H:term:max hfn:ident k0:num len:num : tactic =>
  `(tactic| code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin $b $H $hfn 0x6eff8 $k0 $len)

/-- Add instruction-fetch hypotheses for a function in `libsignalSessionCode` on
  `tripleRatchetProgAt`. -/
macro "s2_fetches " b:term:max H:term:max hfn:ident off:num len:num : tactic =>
  `(tactic| code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin $b $H $hfn $off $len)

theorem tapeAfter_zero_eq (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    tapeAfter ctl cur rest 0 =
      (ctl ↦₆₄ cur) ∗ ((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ (cur ↦ₛ rest) := by
  unfold tapeAfter
  simp only [BitVec.add_zero, Nat.sub_zero]

theorem rngFillBytes_eq (rest : List (BitVec 8)) (len : Nat) :
    (rest ++ List.replicate len 0#8).take len =
      rest.take (min len rest.length) ++ List.replicate (len - min len rest.length) 0#8 := by
  by_cases hle : len ≤ rest.length
  · have hmin : min len rest.length = len := Nat.min_eq_left hle
    have hsub : len - len = 0 := Nat.sub_self len
    rw [hmin, hsub, List.replicate_zero, List.append_nil, List.take_append_of_le_length hle]
  · have hgt : rest.length < len := Nat.lt_of_not_ge hle
    have hmin : min len rest.length = rest.length := Nat.min_eq_right (Nat.le_of_lt hgt)
    rw [hmin, List.take_of_length_le (Nat.le_refl _), List.take_append,
        List.take_of_length_le (Nat.le_of_lt hgt), List.take_replicate,
        Nat.min_eq_left (Nat.sub_le len rest.length)]

/-- Specification of `libsignal_session_rng_fill` (`0x480d8`) starting directly from
`tapeAfter ctl cur rest 0` (without requiring `rest.length < 2^63`, since disjointness of
`ctl ↦₆₄ cur` and `cur ↦ₛ rest` already implies `rest.length < 2^64`). -/
def rngFillAfter0Spec (ctl : BitVec 64) :
    Spec (BitVec 64 × Nat × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, len, cur, rest) s =>
    ⌜s.readReg64 .x0 = dst ∧ (s.readReg64 .x1).toNat = len⌝ ∗
      memRegion dst len ∗ tapeAfter ctl cur rest 0
  post := fun (dst, len, cur, rest) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ (rest ++ List.replicate len 0#8).take len) ∗
      tapeAfter ctl cur rest (min len rest.length)

theorem hookRngFillAfter0_ok (ctl : BitVec 64) :
    HookOk (rngFillHook ctl) (rngFillAfter0Spec ctl) := by
  intro ⟨dst, len, cur, rest⟩ R s0 hrun hpre _
  simp only [rngFillAfter0Spec, tapeAfter_zero_eq, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hdst, hlen⟩, hmem⟩
  have hmem_ctl : s0.mem ⊨ (ctl ↦₆₄ cur) ∗
      (((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ memRegion dst len ∗ (cur ↦ₛ rest) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hmem
    ac_rfl
  have hcur : s0.mem.read64 ctl = cur := (IsBlock.pointsTo64 ctl cur).read hmem_ctl
  have hmem_c8 : s0.mem ⊨ ((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
      ((ctl ↦₆₄ cur) ∗ memRegion dst len ∗ (cur ↦ₛ rest) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hmem
    ac_rfl
  have hc8_raw : s0.mem.read64 (ctl + 8#64) = BitVec.ofNat 64 rest.length :=
    (IsBlock.pointsTo64 (ctl + 8#64) (BitVec.ofNat 64 rest.length)).read hmem_c8
  have hrest_lt64 : rest.length < 2 ^ 64 := by
    by_cases hpos : 0 < rest.length
    · have hmem_disj : s0.mem ⊨ (ctl ↦₆₄ cur) ∗ ((cur ↦ₛ rest) ∗
          (((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ memRegion dst len ∗ R)) := by
        refine Satisfies.mono (Entails.of_eq ?_) hmem
        ac_rfl
      have hdisj := IsBlock.disjoint (IsBlock.pointsTo64 ctl cur) (IsBlock.pointsToBytes cur rest)
        (by decide) hpos hmem_disj
      have h2 := hdisj.2
      have hlt : (ctl - cur).toNat < 2 ^ 64 := (ctl - cur).isLt
      omega
    · omega
  have hrem : (s0.mem.read64 (ctl + 8#64)).toNat = rest.length := by
    rw [hc8_raw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrest_lt64]
  set k := min len rest.length
  have hk_le_rest : k ≤ rest.length := Nat.min_le_right len rest.length
  have hk_le_len : k ≤ len := Nat.min_le_left len rest.length
  have hrest_split : rest = rest.take k ++ rest.drop k := (List.take_append_drop k rest).symm
  have htake_len : (rest.take k).length = k := List.length_take_of_le hk_le_rest
  have hmem_cur : s0.mem ⊨ (cur ↦ₛ rest.take k) ∗
      (((cur + BitVec.ofNat 64 k) ↦ₛ rest.drop k) ∗
        (ctl ↦₆₄ cur) ∗ ((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
        memRegion dst len ∗ R) := by
    have h1 : (cur ↦ₛ rest) =
        (cur ↦ₛ rest.take k) ∗ ((cur + BitVec.ofNat 64 k) ↦ₛ rest.drop k) := by
      conv_lhs => rw [hrest_split]
      rw [pointsToBytes_append, htake_len]
    refine Satisfies.mono (Entails.of_eq ?_) hmem
    rw [h1]
    ac_rfl
  obtain ⟨_, hread_cur_raw⟩ := (IsBlock.pointsToBytes cur (rest.take k)).read hmem_cur
  have hread_cur : s0.mem.readBytes cur k = rest.take k := by
    rwa [htake_len] at hread_cur_raw
  have hmem_dst : s0.mem ⊨ memRegion dst len ∗
      ((ctl ↦₆₄ cur) ∗ ((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ (cur ↦ₛ rest) ∗ R) :=
    hmem
  have hlen_le64 : len ≤ 2 ^ 64 := by
    by_cases hlen0 : 0 < len
    · have hmem_disj2 : s0.mem ⊨ (ctl ↦₆₄ cur) ∗ (memRegion dst len ∗
          (((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ (cur ↦ₛ rest) ∗ R)) := by
        refine Satisfies.mono (Entails.of_eq ?_) hmem
        ac_rfl
      have hdisj2 := IsBlock.disjoint (IsBlock.pointsTo64 ctl cur) (IsBlock.memRegion dst len)
        (by decide) hlen0 hmem_disj2
      have h2 := hdisj2.2
      have hlt : (ctl - dst).toNat < 2 ^ 64 := (ctl - dst).isLt
      omega
    · omega
  set bytes := rest.take k ++ List.replicate (len - k) 0#8
  have hbytes_len : bytes.length = len := by
    simp only [bytes, List.length_append, htake_len, List.length_replicate]
    omega
  set m1 := s0.mem.write64 ctl (cur + BitVec.ofNat 64 k)
  have hcur_cw : s0.mem.canWrite ctl 8 = true :=
    (IsBlock.pointsTo64 ctl cur).canWrite (by decide) hmem_ctl
  have hkf1 : Memory.KeepsFrozen s0.mem m1 :=
    Memory.keepsFrozen_write64 hcur_cw (cur + BitVec.ofNat 64 k)
  have hm1_raw : m1 ⊨ (ctl ↦₆₄ (cur + BitVec.ofNat 64 k)) ∗
      (((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ memRegion dst len ∗ (cur ↦ₛ rest) ∗ R) :=
    (IsBlock.pointsTo64 ctl cur).write64 hmem_ctl (cur + BitVec.ofNat 64 k)
  have hm1_c8 : m1 ⊨ ((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
      ((ctl ↦₆₄ (cur + BitVec.ofNat 64 k)) ∗ memRegion dst len ∗ (cur ↦ₛ rest) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm1_raw
    ac_rfl
  set m2 := m1.write64 (ctl + 8#64) (BitVec.ofNat 64 (rest.length - k))
  have hc8_cw : m1.canWrite (ctl + 8#64) 8 = true :=
    (IsBlock.pointsTo64 (ctl + 8#64) (BitVec.ofNat 64 rest.length)).canWrite (by decide) hm1_c8
  have hkf2 : Memory.KeepsFrozen m1 m2 :=
    Memory.keepsFrozen_write64 hc8_cw (BitVec.ofNat 64 (rest.length - k))
  have hm2_raw : m2 ⊨ ((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 (rest.length - k)) ∗
      ((ctl ↦₆₄ (cur + BitVec.ofNat 64 k)) ∗ memRegion dst len ∗ (cur ↦ₛ rest) ∗ R) :=
    (IsBlock.pointsTo64 (ctl + 8#64) (BitVec.ofNat 64 rest.length)).write64 hm1_c8
      (BitVec.ofNat 64 (rest.length - k))
  have hm2_dst : m2 ⊨ memRegion dst bytes.length ∗
      (tapeAfter ctl cur rest k ∗ R) := by
    rw [hbytes_len]
    refine Satisfies.mono (Entails.of_eq ?_) hm2_raw
    unfold tapeAfter
    ac_rfl
  have hbytes_le64 : bytes.length ≤ 2 ^ 64 := hbytes_len ▸ hlen_le64
  have hkf3 : Memory.KeepsFrozen m2 (m2.writeBytes dst bytes) :=
    keepsFrozen_writeBytes_of_memRegion bytes hbytes_le64 hm2_dst
  have hm3 : m2.writeBytes dst bytes ⊨ (dst ↦ₛ bytes) ∗ (tapeAfter ctl cur rest k ∗ R) :=
    satisfies_writeBytes bytes hbytes_le64 hm2_dst
  dsimp only [rngFillHook, retHook]
  refine ⟨?_, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl⟩, ?_⟩⟩
  · rw [hdst, hlen, hcur, hrem, hread_cur]
    exact (hkf1.trans hkf2).trans hkf3
  · dsimp only [rngFillAfter0Spec]
    rw [hdst, hlen, hcur, hrem, hread_cur, rngFillBytes_eq rest len]
    simp only [State.trace_setPC, State.trace_setMem, State.mem_setPC, State.mem_setMem,
      sepConj_assoc, satisfies_pure_sepConj, true_and]
    exact hm3

/-- `libsignal_session_rng_fill` (`0x480d8` =
  `295128`) meets `rngFillAfter0Spec ctl` on `tripleRatchetProgAt`. -/
theorem rngFill_ok_at_tripleRatchet {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff rngFillName := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      (rngFillAfter0Spec ctl) :=
  hook_ok_at (hname := rngFillName) rfl hk (by fnoff_eq)
    (by fnoff_eq) (by dsimp [rngFillName]; simp [Rust.isPanicSymbol])
    ⟨rngFillHook ctl, rfl, hookRngFillAfter0_ok ctl⟩

theorem zeroize32_hookOk : HookOk zeroizeSecretHook zeroizeSecretSpec := by
  refine retHook_ok fun a R s0 _ hpre _ => ?_
  simp only [zeroizeSecretSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hmem⟩
  have hlen : (List.replicate 32 0#8).length = 32 := List.length_replicate
  have hle : (List.replicate 32 0#8).length ≤ 2 ^ 64 := by rw [hlen]; decide
  have hmem' : s0.mem ⊨ memRegion a (List.replicate 32 0#8).length ∗ R := by
    rwa [hlen]
  refine ⟨?_, rfl, ‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · rw [hx0]
    exact keepsFrozen_writeBytes_of_memRegion (List.replicate 32 0#8) hle hmem'
  · simp only [zeroizeSecretSpec, retHook, State.trace_setPC, State.trace_setMem, State.mem_setMem, hx0,
      sepConj_assoc, satisfies_pure_sepConj, true_and]
    exact satisfies_writeBytes (List.replicate 32 0#8) hle hmem'

/-- `<StaticSecret as Drop>::drop` (`0x47ff0` =
  `294896`) meets `zeroizeSecretSpec` on `tripleRatchetProgAt`. -/
theorem staticDrop_ok_at_tripleRatchet {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff staticDropName := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      zeroizeSecretSpec :=
  hook_ok_at (hname := staticDropName) rfl hk (by fnoff_eq)
    (by fnoff_eq) (by dsimp [staticDropName]; simp [Rust.isPanicSymbol])
    ⟨zeroizeSecretHook, rfl, zeroize32_hookOk⟩

theorem hookSessionMemmove_ok (hookStack : Nat := 4096) :
    HookOk hookMemmove (sessionMemmoveSpec hookStack) := by
  refine HookOk.of_trace (hookMemmove_ok hookStack) fun _ _ _ ht hpost => ?_
  simp only [libcMemmoveSpec, sessionMemmoveSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1, ht⟩, hpost.2⟩

/-- `memmove` (`0x47f38` = `294712`) meets `sessionMemmoveSpec` on `tripleRatchetProgAt`. -/
theorem memmove_ok_at_tripleRatchet {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memmove" := by fnoff_eq)
    (stackSize : Nat := 4096) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemmoveSpec stackSize) :=
  hook_ok_at (hname := "memmove") rfl hk (by fnoff_eq)
    (by fnoff_eq) (by simp [Rust.isPanicSymbol])
    ⟨hookMemmove, rfl, hookSessionMemmove_ok (hookStack := stackSize)⟩

/-! ## 2. `chainAt` ↔ 104-Byte Block + Detached Inner Heap Buffers -/

/-- Padding byte count in `Option<chain::ChainKey>` (24 bytes when `none`, 4 bytes when `some`). -/
def optChainKeyPadLen : Option ChainKey → Nat
  | none => 24
  | some _ => 4

/-- The 32-byte in-struct representation of `Option<chain::ChainKey>` with padding `pad`. -/
def optChainKeyTailBytes (pin : VecPin) (o : Option ChainKey) (pad : List (BitVec 8)) :
    List (BitVec 8) :=
  match o with
  | none => unpack64 optChainKeyNone ++ pad
  | some ck => vecHeaderBytes pin.cap pin.ptr 32#64 ++ (unpack32 ck.index ++ pad)

theorem optChainKeyTailBytes_length (pin : VecPin) (o : Option ChainKey) {pad : List (BitVec 8)}
    (hpad : pad.length = optChainKeyPadLen o) :
    (optChainKeyTailBytes pin o pad).length = 32 := by
  cases o with
  | none =>
    simp [optChainKeyTailBytes, optChainKeyPadLen] at hpad ⊢
    omega
  | some ck =>
    simp [optChainKeyTailBytes, optChainKeyPadLen] at hpad ⊢
    omega

/-- Detached heap buffer of `Option<chain::ChainKey>`. -/
def optChainKeyHeap (A : RustAlloc) (pin : VecPin) : Option ChainKey → SepProp
  | none => emp
  | some ck => vecU8Buf A pin.cap pin.ptr (keyToBytes32 ck.key)

theorem optChainKeyAt_eq_exists_bytes (A : RustAlloc) (pin : VecPin) (o : Option ChainKey)
    (a : BitVec 64) :
    optChainKeyAt A pin o a =
      (∃∗ pad : List (BitVec 8),
        ⌜pad.length = optChainKeyPadLen o⌝ ∗ (a ↦ₛ optChainKeyTailBytes pin o pad)) ∗
      optChainKeyHeap A pin o := by
  cases o with
  | none =>
    simp only [optChainKeyAt, optChainKeyPadLen, optChainKeyTailBytes, optChainKeyHeap, sepConj_emp]
    rw [pointsTo64_eq_pointsToBytes, memRegion_eq_exists_bytes (a + 8#64) 24 (by decide),
        sepExists_sepConj_right]
    apply congrArg SepProp.sepExists
    funext pad
    have h8 : a + 8#64 = a + BitVec.ofNat 64 (unpack64 optChainKeyNone).length := by
      simp [unpack64_length]
    rw [sepConj_pure_left_comm, h8, ← pointsToBytes_append]
  | some ck =>
    simp only [optChainKeyAt, optChainKeyPadLen, optChainKeyTailBytes, optChainKeyHeap]
    rw [vecU8At_eq_header_sep_buf, vecHeader_eq_pointsToBytes, pointsTo32_eq_pointsToBytes,
        memRegion_eq_exists_bytes (a + 28#64) 4 (by decide)]
    simp only [length_keyToBytes32, sepConj_assoc]
    have hpull :
        ((a ↦ₛ vecHeaderBytes pin.cap pin.ptr 32#64) ∗
          vecU8Buf A pin.cap pin.ptr (keyToBytes32 ck.key) ∗
          ((a + 24#64) ↦ₛ unpack32 ck.index) ∗
          (∃∗ bs : List (BitVec 8), ⌜bs.length = 4⌝ ∗ ((a + 28#64) ↦ₛ bs))) =
        (((a ↦ₛ vecHeaderBytes pin.cap pin.ptr 32#64) ∗
          ((a + 24#64) ↦ₛ unpack32 ck.index) ∗
          (∃∗ bs : List (BitVec 8), ⌜bs.length = 4⌝ ∗ ((a + 28#64) ↦ₛ bs))) ∗
         vecU8Buf A pin.cap pin.ptr (keyToBytes32 ck.key)) := by
      ac_rfl
    rw [hpull]
    congr 1
    rw [sepExists_sepConj_right, sepExists_sepConj_right]
    apply congrArg SepProp.sepExists
    funext pad
    have h24 : a + 24#64 = a + BitVec.ofNat 64 (vecHeaderBytes pin.cap pin.ptr 32#64).length := by
      simp [vecHeaderBytes_length]
    have h28 : a + 28#64 = (a + 24#64) + BitVec.ofNat 64 (unpack32 ck.index).length := by
      simp [unpack32_length]
    have hpull2 :
        ((a ↦ₛ vecHeaderBytes pin.cap pin.ptr 32#64) ∗
          (((a + 24#64) ↦ₛ unpack32 ck.index) ∗
            (⌜pad.length = 4⌝ ∗ ((a + 28#64) ↦ₛ pad)))) =
        (⌜pad.length = 4⌝ ∗
          ((a ↦ₛ vecHeaderBytes pin.cap pin.ptr 32#64) ∗
            (((a + 24#64) ↦ₛ unpack32 ck.index) ∗ ((a + 28#64) ↦ₛ pad)))) := by
      ac_rfl
    rw [hpull2, h28, ← pointsToBytes_append, h24, ← pointsToBytes_append]

/-- The 72-byte prefix of a `session_structure::Chain` (three 24-byte `Vec` headers: `srk`, `priv`,
`message_keys`). -/
def chainHeaderBytes (gc : ChainGhost × ReceiverChain) : List (BitVec 8) :=
  vecHeaderBytes gc.1.srk.cap gc.1.srk.ptr (BitVec.ofNat 64 gc.1.srk.bytes.length) ++
    (vecHeaderBytes gc.1.priv.cap gc.1.priv.ptr (BitVec.ofNat 64 gc.1.priv.bytes.length) ++
      vecHeaderBytes gc.1.mkCap gc.1.mkPtr
        (BitVec.ofNat 64 (gc.1.keys.zip gc.2.messageKeys).length))

@[simp]
theorem chainHeaderBytes_length (gc : ChainGhost × ReceiverChain) :
    (chainHeaderBytes gc).length = 72 := by
  simp [chainHeaderBytes]

/-- The 104-byte in-buffer representation of a `session_structure::Chain` with padding `pad`. -/
def chainBytes (gc : ChainGhost × ReceiverChain) (pad : List (BitVec 8)) : List (BitVec 8) :=
  chainHeaderBytes gc ++ optChainKeyTailBytes gc.1.ck gc.2.chainKey pad

theorem chainBytes_length (gc : ChainGhost × ReceiverChain) {pad : List (BitVec 8)}
    (hpad : pad.length = optChainKeyPadLen gc.2.chainKey) :
    (chainBytes gc pad).length = 104 := by
  simp [chainBytes, optChainKeyTailBytes_length gc.1.ck gc.2.chainKey hpad]

theorem pointsToBytes_chainHeaderBytes (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    (a ↦ₛ chainHeaderBytes gc) =
      vecHeader a gc.1.srk.cap gc.1.srk.ptr (BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
        vecHeader (a + 24#64) gc.1.priv.cap gc.1.priv.ptr (BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
        vecHeader (a + 48#64) gc.1.mkCap gc.1.mkPtr
          (BitVec.ofNat 64 (gc.1.keys.zip gc.2.messageKeys).length) := by
  unfold chainHeaderBytes
  rw [pointsToBytes_append, pointsToBytes_append]
  simp only [vecHeaderBytes_length]
  rw [← vecHeader_eq_pointsToBytes, ← vecHeader_eq_pointsToBytes, ← vecHeader_eq_pointsToBytes]
  have h24 : a + BitVec.ofNat 64 24 = a + 24#64 := rfl
  have h48 : a + BitVec.ofNat 64 24 + BitVec.ofNat 64 24 = a + 48#64 := by bv_arith
  rw [h48, h24]

/-- Detached heap buffers owned by a `session_structure::Chain`,
  independent of its 104-byte slot. -/
def chainHeap (A : RustAlloc) (gc : ChainGhost × ReceiverChain) : SepProp :=
  ⌜PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
    gc.2.messageKeys.length ≤ maxMessageKeys ∧ gc.1.keys.length = gc.2.messageKeys.length ∧
    gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗
    vecU8Buf A gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes ∗
    vecU8Buf A gc.1.priv.cap gc.1.priv.ptr gc.1.priv.bytes ∗
    vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
    optChainKeyHeap A gc.1.ck gc.2.chainKey

theorem chainAt_eq_headers_sep_heap (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) :
    chainAt A gc a =
      (vecHeader a gc.1.srk.cap gc.1.srk.ptr (BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
        vecHeader (a + 24#64) gc.1.priv.cap gc.1.priv.ptr (BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
        vecHeader (a + 48#64) gc.1.mkCap gc.1.mkPtr
          (BitVec.ofNat 64 (gc.1.keys.zip gc.2.messageKeys).length) ∗
        (∃∗ pad : List (BitVec 8),
          ⌜pad.length = optChainKeyPadLen gc.2.chainKey⌝ ∗
            ((a + 72#64) ↦ₛ optChainKeyTailBytes gc.1.ck gc.2.chainKey pad))) ∗
      chainHeap A gc := by
  unfold chainAt chainHeap vecGhostAt vecAt
  rw [vecU8At_eq_header_sep_buf A a,
      vecU8At_eq_header_sep_buf A (a + 24#64),
      optChainKeyAt_eq_exists_bytes A gc.1.ck gc.2.chainKey (a + 72#64)]
  ac_rfl

/-- Decompose `chainAt A gc a` into an existential 104-byte slice `a ↦ₛ chainBytes gc pad`
and the detached inner buffers `chainHeap A gc`. -/
theorem chainAt_eq_exists_bytes (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    chainAt A gc a =
      (∃∗ pad : List (BitVec 8),
        ⌜pad.length = optChainKeyPadLen gc.2.chainKey⌝ ∗ (a ↦ₛ chainBytes gc pad)) ∗
      chainHeap A gc := by
  rw [chainAt_eq_headers_sep_heap]
  congr 1
  have hhdr :
      (vecHeader a gc.1.srk.cap gc.1.srk.ptr (BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
        vecHeader (a + 24#64) gc.1.priv.cap gc.1.priv.ptr (BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
        vecHeader (a + 48#64) gc.1.mkCap gc.1.mkPtr
          (BitVec.ofNat 64 (gc.1.keys.zip gc.2.messageKeys).length) ∗
        (∃∗ pad : List (BitVec 8),
          ⌜pad.length = optChainKeyPadLen gc.2.chainKey⌝ ∗
            ((a + 72#64) ↦ₛ optChainKeyTailBytes gc.1.ck gc.2.chainKey pad))) =
      (a ↦ₛ chainHeaderBytes gc) ∗
        (∃∗ pad : List (BitVec 8),
          ⌜pad.length = optChainKeyPadLen gc.2.chainKey⌝ ∗
            ((a + 72#64) ↦ₛ optChainKeyTailBytes gc.1.ck gc.2.chainKey pad)) := by
    rw [pointsToBytes_chainHeaderBytes]
    ac_rfl
  rw [hhdr, sepExists_sepConj_right]
  apply congrArg SepProp.sepExists
  funext pad
  have h72 : a + 72#64 = a + BitVec.ofNat 64 (chainHeaderBytes gc).length := by
    rw [chainHeaderBytes_length]
  rw [sepConj_pure_left_comm, h72, ← pointsToBytes_append]
  rfl

theorem chainAt_of_bytes (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64)
    {pad : List (BitVec 8)} (hpad : pad.length = optChainKeyPadLen gc.2.chainKey) :
    ((a ↦ₛ chainBytes gc pad) ∗ chainHeap A gc) ⊢ chainAt A gc a := by
  rw [chainAt_eq_exists_bytes]
  apply sepConj_mono_left
  exact Entails.sepExists_right pad (Entails.pure_right hpad (Entails.refl _))

/-- Detached heap buffers of a list of `Chain`s, in order. -/
def chainHeaps (A : RustAlloc) : List (ChainGhost × ReceiverChain) → SepProp
  | [] => emp
  | gc :: gcs => chainHeap A gc ∗ chainHeaps A gcs

@[simp]
theorem chainHeaps_nil (A : RustAlloc) : chainHeaps A [] = emp := rfl

@[simp]
theorem chainHeaps_cons (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (gcs : List (ChainGhost × ReceiverChain)) :
    chainHeaps A (gc :: gcs) = chainHeap A gc ∗ chainHeaps A gcs := rfl

/-- `ChainArrayBytes gcs bs` relates a list of `Chain`s `gcs` to the flat
`gcs.length * 104`-byte buffer slice `bs` holding their 104-byte struct representations. -/
inductive ChainArrayBytes : List (ChainGhost × ReceiverChain) → List (BitVec 8) → Prop
  | nil : ChainArrayBytes [] []
  | cons {gc : ChainGhost × ReceiverChain} {gcs : List (ChainGhost × ReceiverChain)}
      {pad bs : List (BitVec 8)}
      (hpad : pad.length = optChainKeyPadLen gc.2.chainKey)
      (hrest : ChainArrayBytes gcs bs) :
      ChainArrayBytes (gc :: gcs) (chainBytes gc pad ++ bs)

namespace ChainArrayBytes

theorem length_eq {gcs : List (ChainGhost × ReceiverChain)} {bs : List (BitVec 8)}
    (h : ChainArrayBytes gcs bs) :
    bs.length = gcs.length * 104 := by
  induction h with
  | nil => rfl
  | @cons gc gcs pad bs hpad _ ih =>
    rw [List.length_append, chainBytes_length gc hpad, ih, List.length_cons, Nat.succ_mul]
    omega

end ChainArrayBytes

theorem arrayAt_chainAt_entails_bytes (A : RustAlloc) (base : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) :
    arrayAt (chainAt A) 104 base gcs ⊢
      (∃∗ bs : List (BitVec 8), ⌜ChainArrayBytes gcs bs⌝ ∗ (base ↦ₛ bs)) ∗
        chainHeaps A gcs := by
  induction gcs generalizing base with
  | nil =>
    simp only [arrayAt_nil, chainHeaps_nil, sepConj_emp]
    apply Entails.sepExists_right []
    apply Entails.pure_right ChainArrayBytes.nil
    rw [pointsToBytes_nil]
    exact Entails.refl _
  | cons gc gcs ih =>
    rw [arrayAt_cons, chainAt_eq_exists_bytes, chainHeaps_cons]
    refine Entails.trans (sepConj_mono_right (ih (base + BitVec.ofNat 64 104))) ?_
    have hpull :
        (((∃∗ pad : List (BitVec 8),
            ⌜pad.length = optChainKeyPadLen gc.2.chainKey⌝ ∗ (base ↦ₛ chainBytes gc pad)) ∗
           chainHeap A gc) ∗
         ((∃∗ bs : List (BitVec 8), ⌜ChainArrayBytes gcs bs⌝ ∗
            ((base + BitVec.ofNat 64 104) ↦ₛ bs)) ∗
          chainHeaps A gcs)) =
        (((∃∗ pad : List (BitVec 8),
            ⌜pad.length = optChainKeyPadLen gc.2.chainKey⌝ ∗ (base ↦ₛ chainBytes gc pad)) ∗
          (∃∗ bs : List (BitVec 8), ⌜ChainArrayBytes gcs bs⌝ ∗
            ((base + BitVec.ofNat 64 104) ↦ₛ bs))) ∗
         (chainHeap A gc ∗ chainHeaps A gcs)) := by
      ac_rfl
    rw [hpull]
    apply sepConj_mono_left
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim
    intro pad
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim
    intro bs'
    have hpull2 :
        ((⌜pad.length = optChainKeyPadLen gc.2.chainKey⌝ ∗ (base ↦ₛ chainBytes gc pad)) ∗
          (⌜ChainArrayBytes gcs bs'⌝ ∗ ((base + BitVec.ofNat 64 104) ↦ₛ bs'))) =
        (⌜pad.length = optChainKeyPadLen gc.2.chainKey⌝ ∗
          (⌜ChainArrayBytes gcs bs'⌝ ∗
            ((base ↦ₛ chainBytes gc pad) ∗ ((base + BitVec.ofNat 64 104) ↦ₛ bs')))) := by
      ac_rfl
    rw [hpull2]
    apply Entails.pure_left
    intro hpad
    apply Entails.pure_left
    intro hrest
    apply Entails.sepExists_right (chainBytes gc pad ++ bs')
    apply Entails.pure_right (.cons hpad hrest)
    rw [pointsToBytes_append, chainBytes_length gc hpad]
    exact Entails.refl _

theorem arrayAt_chainAt_of_bytes (A : RustAlloc) (base : BitVec 64)
    {gcs : List (ChainGhost × ReceiverChain)} {bs : List (BitVec 8)}
    (hbs : ChainArrayBytes gcs bs) :
    ((base ↦ₛ bs) ∗ chainHeaps A gcs) ⊢ arrayAt (chainAt A) 104 base gcs := by
  induction hbs generalizing base with
  | nil =>
    simp only [pointsToBytes_nil, chainHeaps_nil, arrayAt_nil, emp_sepConj]
    exact Entails.refl _
  | @cons gc gcs pad bs' hpad _ ih =>
    rw [pointsToBytes_append, chainBytes_length gc hpad, chainHeaps_cons, arrayAt_cons]
    have hpull :
        (((base ↦ₛ chainBytes gc pad) ∗ ((base + BitVec.ofNat 64 104) ↦ₛ bs')) ∗
          (chainHeap A gc ∗ chainHeaps A gcs)) =
        (((base ↦ₛ chainBytes gc pad) ∗ chainHeap A gc) ∗
          (((base + BitVec.ofNat 64 104) ↦ₛ bs') ∗ chainHeaps A gcs)) := by
      ac_rfl
    rw [hpull]
    exact sepConj_mono (chainAt_of_bytes A gc base hpad) (ih (base + BitVec.ofNat 64 104))

theorem vecBuf_chainAt_entails_bytes (A : RustAlloc) (cap ptr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) (hcap : cap ≠ 0) :
    vecBuf A 104 8 (chainAt A) cap ptr gcs ⊢
      ∃∗ bs : List (BitVec 8),
        ⌜ChainArrayBytes gcs bs ∧ bs.length = gcs.length * 104 ∧
          gcs.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr (cap.toNat * 104) 8 ∗
        (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) ((cap.toNat - gcs.length) * 104) ∗
        chainHeaps A gcs := by
  rw [vecBuf_of_ne_zero A 104 8 (chainAt A) cap ptr gcs hcap]
  apply Entails.pure_left
  rintro ⟨hlen, hcap_lt, hptr⟩
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left (arrayAt_chainAt_entails_bytes A ptr gcs))) ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim
  intro bs
  have hpull :
      (A.live ptr (cap.toNat * 104) 8 ∗
        (((⌜ChainArrayBytes gcs bs⌝ ∗ (ptr ↦ₛ bs)) ∗ chainHeaps A gcs) ∗
         memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) ((cap.toNat - gcs.length) * 104))) =
      (⌜ChainArrayBytes gcs bs⌝ ∗
        (A.live ptr (cap.toNat * 104) 8 ∗
         (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) ((cap.toNat - gcs.length) * 104) ∗
         chainHeaps A gcs)) := by
    ac_rfl
  rw [hpull]
  apply Entails.pure_left
  intro hbs
  apply Entails.sepExists_right bs
  exact Entails.pure_right ⟨hbs, hbs.length_eq, hlen, hcap_lt, hptr⟩ (Entails.refl _)

theorem vecBuf_chainAt_of_bytes (A : RustAlloc) (cap ptr : BitVec 64)
    {gcs : List (ChainGhost × ReceiverChain)} {bs : List (BitVec 8)}
    (hcap : cap ≠ 0)
    (hbs : ChainArrayBytes gcs bs)
    (hlen : gcs.length ≤ cap.toNat)
    (hcap_lt : cap.toNat * 104 < 2 ^ 63)
    (hptr : ptr ≠ 0) :
    (A.live ptr (cap.toNat * 104) 8 ∗
      (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) ((cap.toNat - gcs.length) * 104) ∗
      chainHeaps A gcs) ⊢
      vecBuf A 104 8 (chainAt A) cap ptr gcs := by
  rw [vecBuf_of_ne_zero A 104 8 (chainAt A) cap ptr gcs hcap]
  apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
  have hpull :
      (A.live ptr (cap.toNat * 104) 8 ∗
        (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) ((cap.toNat - gcs.length) * 104) ∗
        chainHeaps A gcs) =
      (A.live ptr (cap.toNat * 104) 8 ∗
        (((ptr ↦ₛ bs) ∗ chainHeaps A gcs) ∗
         memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) ((cap.toNat - gcs.length) * 104))) :=
           by
    ac_rfl
  rw [hpull]
  exact sepConj_mono_right (sepConj_mono_left (arrayAt_chainAt_of_bytes A ptr hbs))

/-- Precondition bridge for `growOneSpec` on `Vec<Chain>`. -/
theorem vecBuf_chainAt_full_entails_grow_one (A : RustAlloc) (cap ptr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) (hfull : gcs.length = cap.toNat) :
    vecBuf A 104 8 (chainAt A) cap ptr gcs ⊢
      ∃∗ bs : List (BitVec 8),
        ⌜ChainArrayBytes gcs bs ∧ bs.length = cap.toNat * 104⌝ ∗
        (⌜cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (if cap = 0 then emp
           else A.live ptr (cap.toNat * 104) 8 ∗ (ptr ↦ₛ bs) ∗ ⌜bs.length = cap.toNat * 104⌝)) ∗
        chainHeaps A gcs := by
  by_cases hcap : cap = 0
  · subst hcap
    have hgcs : gcs = [] := List.eq_nil_of_length_eq_zero (by simpa using hfull)
    subst hgcs
    rw [vecBuf_zero, ← sepConj_emp ⌜([] : List (ChainGhost × ReceiverChain)) = [] ∧ ptr ≠ 0⌝]
    apply Entails.pure_left
    rintro ⟨_, hptr⟩
    apply Entails.sepExists_right []
    simp only [↓reduceIte, chainHeaps_nil, sepConj_emp]
    apply Entails.pure_right ⟨.nil, rfl⟩
    exact Entails.pure_right_only ⟨by decide, hptr⟩ (Entails.refl _)
  · refine Entails.trans (vecBuf_chainAt_entails_bytes A cap ptr gcs hcap) ?_
    apply Entails.sepExists_elim
    intro bs
    apply Entails.pure_left
    rintro ⟨hbs, hbs_len, _, hcap_lt, hptr⟩
    have hbs_cap : bs.length = cap.toNat * 104 := by rw [hbs_len, hfull]
    have hrem : (cap.toNat - gcs.length) * 104 = 0 := by omega
    rw [hrem, memRegion_zero]
    apply Entails.sepExists_right bs
    simp only [hcap, ↓reduceIte]
    apply Entails.pure_right ⟨hbs, hbs_cap⟩
    have hpull :
        (A.live ptr (cap.toNat * 104) 8 ∗ (ptr ↦ₛ bs) ∗ emp ∗ chainHeaps A gcs) =
        ((A.live ptr (cap.toNat * 104) 8 ∗ (ptr ↦ₛ bs)) ∗ chainHeaps A gcs) := by
      ac_rfl
    rw [hpull]
    apply sepConj_mono_left
    apply Entails.pure_right ⟨hcap_lt, hptr⟩
    apply sepConj_mono_right
    rw [sepConj_comm (ptr ↦ₛ bs)]
    exact Entails.pure_right hbs_cap (Entails.refl _)

/-- Postcondition bridge for `growOneSpec` on `Vec<Chain>`. -/
theorem vecBuf_chainAt_of_grow_one (A : RustAlloc) (cap newPtr : BitVec 64)
    {gcs : List (ChainGhost × ReceiverChain)} {bs : List (BitVec 8)}
    (hfull : gcs.length = cap.toNat)
    (hbs : ChainArrayBytes gcs bs)
    (hnewPtr : newPtr ≠ 0)
    (hnew_lt : max (2 * cap.toNat) 4 * 104 < 2 ^ 63) :
    let newCap := max (2 * cap.toNat) 4
    (A.live newPtr (newCap * 104) 8 ∗
      (newPtr ↦ₛ bs) ∗
      memRegion (newPtr + BitVec.ofNat 64 (cap.toNat * 104)) ((newCap - cap.toNat) * 104) ∗
      chainHeaps A gcs) ⊢
      vecBuf A 104 8 (chainAt A) (BitVec.ofNat 64 newCap) newPtr gcs := by
  intro newCap
  obtain ⟨hne0, htoNat, hlen_lt, hcap_lt⟩ := grow_one_newCap_props hfull hnew_lt
  have h := vecBuf_chainAt_of_bytes A (BitVec.ofNat 64 newCap) newPtr hne0 hbs
    (Nat.le_of_lt hlen_lt) hcap_lt hnewPtr
  rw [htoNat, hfull] at h
  exact h

/-- Split `vecBuf A 104 8 (chainAt A) cap ptr gcs` when `gcs.length < cap.toNat` to expose the
104-byte slot `memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) 104` for pushing a new `Chain`.
-/
theorem vecBuf_chainAt_push_split (A : RustAlloc) (cap ptr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) (hlen_lt : gcs.length < cap.toNat) :
    vecBuf A 104 8 (chainAt A) cap ptr gcs ⊢
      ⌜cap ≠ 0 ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (chainAt A) 104 ptr gcs ∗
        memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) 104 ∗
        memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
          ((cap.toNat - (gcs.length + 1)) * 104) := by
  have hcap : cap ≠ 0 := by intro h0; rw [h0] at hlen_lt; change gcs.length < 0 at hlen_lt; omega
  rw [vecBuf_of_ne_zero A 104 8 (chainAt A) cap ptr gcs hcap]
  apply Entails.pure_left
  rintro ⟨_, hcap_lt, hptr⟩
  apply Entails.pure_right ⟨hcap, hcap_lt, hptr⟩
  have hsplit_len : (cap.toNat - gcs.length) * 104 =
      104 + (cap.toNat - (gcs.length + 1)) * 104 := by
    have : cap.toNat - gcs.length = 1 + (cap.toNat - (gcs.length + 1)) := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have hoff :
      ptr + BitVec.ofNat 64 (gcs.length * 104) + BitVec.ofNat 64 104 =
        ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  rw [hsplit_len,
      memRegion_split (ptr + BitVec.ofNat 64 (gcs.length * 104)) 104 _ (by omega),
      hoff]
  have hpull :
      (A.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (chainAt A) 104 ptr gcs ∗
        (memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) 104 ∗
          memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
            ((cap.toNat - (gcs.length + 1)) * 104))) =
      (A.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (chainAt A) 104 ptr gcs ∗
        memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) 104 ∗
        memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
          ((cap.toNat - (gcs.length + 1)) * 104)) := by
    ac_rfl
  rw [hpull]
  exact Entails.refl _

/-- Reassemble `vecBuf A 104 8 (chainAt A) cap ptr (gcs ++ [gc])` after writing `chainAt A gc` at
`ptr + BitVec.ofNat 64 (gcs.length * 104)`. -/
theorem vecBuf_chainAt_push_reassemble (A : RustAlloc) (cap ptr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) (gc : ChainGhost × ReceiverChain)
    (hlen_lt : gcs.length < cap.toNat)
    (hcap_lt : cap.toNat * 104 < 2 ^ 63)
    (hptr : ptr ≠ 0) :
    (A.live ptr (cap.toNat * 104) 8 ∗
      arrayAt (chainAt A) 104 ptr gcs ∗
      chainAt A gc (ptr + BitVec.ofNat 64 (gcs.length * 104)) ∗
      memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
        ((cap.toNat - (gcs.length + 1)) * 104)) ⊢
      vecBuf A 104 8 (chainAt A) cap ptr (gcs ++ [gc]) := by
  have hcap : cap ≠ 0 := by intro h0; rw [h0] at hlen_lt; change gcs.length < 0 at hlen_lt; omega
  rw [vecBuf_of_ne_zero A 104 8 (chainAt A) cap ptr (gcs ++ [gc]) hcap,
      List.length_append, List.length_singleton, arrayAt_concat]
  apply Entails.pure_right ⟨by omega, hcap_lt, hptr⟩
  have hpull :
      (A.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (chainAt A) 104 ptr gcs ∗
        chainAt A gc (ptr + BitVec.ofNat 64 (gcs.length * 104)) ∗
        memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
          ((cap.toNat - (gcs.length + 1)) * 104)) =
      (A.live ptr (cap.toNat * 104) 8 ∗
        (arrayAt (chainAt A) 104 ptr gcs ∗
          chainAt A gc (ptr + BitVec.ofNat 64 (gcs.length * 104))) ∗
        memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
          ((cap.toNat - (gcs.length + 1)) * 104)) := by
    ac_rfl
  rw [hpull]
  exact Entails.refl _

/-- Expose `vecBuf A 104 8 (chainAt A) cap ptr (gc₀ :: gcs)` for removing element 0 in the
eviction loop: splits out the 104-byte header `b₀ = chainBytes gc₀ pad₀` at `ptr` and the tail
bytes `bs_rest` at `ptr + 104` (`ChainArrayBytes gcs bs_rest`), plus `chainHeap A gc₀` and
`chainHeaps A gcs`. -/
theorem vecBuf_chainAt_expose_for_remove0 (A : RustAlloc) (cap ptr : BitVec 64)
    (gc₀ : ChainGhost × ReceiverChain) (gcs : List (ChainGhost × ReceiverChain)) :
    vecBuf A 104 8 (chainAt A) cap ptr (gc₀ :: gcs) ⊢
      ∃∗ pad₀ : List (BitVec 8), ∃∗ bs_rest : List (BitVec 8),
        ⌜pad₀.length = optChainKeyPadLen gc₀.2.chainKey ∧
          ChainArrayBytes gcs bs_rest ∧ bs_rest.length = gcs.length * 104 ∧
          gcs.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0 ∧ cap ≠ 0⌝ ∗
        A.live ptr (cap.toNat * 104) 8 ∗
        (ptr ↦ₛ chainBytes gc₀ pad₀) ∗
        ((ptr + 104#64) ↦ₛ bs_rest) ∗
        memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
          ((cap.toNat - (gcs.length + 1)) * 104) ∗
        chainHeap A gc₀ ∗
        chainHeaps A gcs := by
  have hcap_or : cap = 0 ∨ cap ≠ 0 := Classical.em _
  rcases hcap_or with rfl | hcap
  · unfold vecBuf
    apply Entails.pure_left
    rintro ⟨hlen, _, _⟩
    simp at hlen
  · refine Entails.trans (vecBuf_chainAt_entails_bytes A cap ptr (gc₀ :: gcs) hcap) ?_
    apply Entails.sepExists_elim
    intro bs
    apply Entails.pure_left
    rintro ⟨hbs, _, hlen, hcap_lt, hptr⟩
    cases hbs with
    | @cons _ _ pad₀ bs_rest hpad₀ hrest =>
      simp only [List.length_cons, chainHeaps_cons] at hlen ⊢
      rw [pointsToBytes_append, chainBytes_length gc₀ hpad₀]
      apply Entails.sepExists_right pad₀
      apply Entails.sepExists_right bs_rest
      apply Entails.pure_right ⟨hpad₀, hrest, hrest.length_eq, hlen, hcap_lt, hptr, hcap⟩
      have hpull :
          (A.live ptr (cap.toNat * 104) 8 ∗
            ((ptr ↦ₛ chainBytes gc₀ pad₀) ∗ ((ptr + BitVec.ofNat 64 104) ↦ₛ bs_rest)) ∗
            memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
              ((cap.toNat - (gcs.length + 1)) * 104) ∗
            (chainHeap A gc₀ ∗ chainHeaps A gcs)) =
          (A.live ptr (cap.toNat * 104) 8 ∗
            (ptr ↦ₛ chainBytes gc₀ pad₀) ∗
            ((ptr + 104#64) ↦ₛ bs_rest) ∗
            memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
              ((cap.toNat - (gcs.length + 1)) * 104) ∗
            chainHeap A gc₀ ∗
            chainHeaps A gcs) := by
        ac_rfl
      rw [hpull]
      exact Entails.refl _

/-- After `memmove(ptr, ptr + 104, gcs.length * 104)` on `b₀ ++ bs_rest` (`b₀.length = 104`,
`bs_rest.length = gcs.length * 104`), `listMove (b₀ ++ bs_rest) 0 104 (gcs.length * 104)` is
`bs_rest` followed by 104 trailing bytes, reassembling `vecBuf A 104 8 (chainAt A) cap ptr gcs`. -/
theorem vecBuf_chainAt_of_remove0 (A : RustAlloc) (cap ptr : BitVec 64)
    {gcs : List (ChainGhost × ReceiverChain)} {b₀ bs_rest : List (BitVec 8)}
    (hb₀ : b₀.length = 104)
    (hrest : ChainArrayBytes gcs bs_rest)
    (hlen : gcs.length + 1 ≤ cap.toNat)
    (hcap_lt : cap.toNat * 104 < 2 ^ 63)
    (hptr : ptr ≠ 0) :
    (A.live ptr (cap.toNat * 104) 8 ∗
      (ptr ↦ₛ listMove (b₀ ++ bs_rest) 0 104 (gcs.length * 104)) ∗
      memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
        ((cap.toNat - (gcs.length + 1)) * 104) ∗
      chainHeaps A gcs) ⊢
      vecBuf A 104 8 (chainAt A) cap ptr gcs := by
  have hcap : cap ≠ 0 := by intro h0; rw [h0] at hlen; change gcs.length + 1 ≤ 0 at hlen; omega
  have hrest_len : bs_rest.length = gcs.length * 104 := hrest.length_eq
  have hmove : listMove (b₀ ++ bs_rest) 0 104 (gcs.length * 104) =
      bs_rest ++ (b₀ ++ bs_rest).drop (gcs.length * 104) := by
    unfold listMove
    simp only [List.take_zero, List.nil_append, Nat.zero_add]
    have hdrop104 : (b₀ ++ bs_rest).drop 104 = bs_rest := by
      rw [← hb₀, List.drop_left]
    rw [hdrop104, ← hrest_len, List.take_length]
  have htail_len : ((b₀ ++ bs_rest).drop (gcs.length * 104)).length = 104 := by
    rw [List.length_drop, List.length_append, hb₀, hrest_len]
    omega
  rw [hmove, pointsToBytes_append, hrest_len]
  have htail_reg := pointsToBytes_entails_memRegion
    (ptr + BitVec.ofNat 64 (gcs.length * 104)) ((b₀ ++ bs_rest).drop (gcs.length * 104))
  rw [htail_len] at htail_reg
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right htail_reg))) ?_
  have hsplit_len : (cap.toNat - gcs.length) * 104 =
      104 + (cap.toNat - (gcs.length + 1)) * 104 := by
    have : cap.toNat - gcs.length = 1 + (cap.toNat - (gcs.length + 1)) := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have hoff :
      ptr + BitVec.ofNat 64 (gcs.length * 104) + BitVec.ofNat 64 104 =
        ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  have hpull :
      (A.live ptr (cap.toNat * 104) 8 ∗
        ((ptr ↦ₛ bs_rest) ∗ memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) 104) ∗
        memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
          ((cap.toNat - (gcs.length + 1)) * 104) ∗
        chainHeaps A gcs) =
      (A.live ptr (cap.toNat * 104) 8 ∗
        (ptr ↦ₛ bs_rest) ∗
        (memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) 104 ∗
          memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
            ((cap.toNat - (gcs.length + 1)) * 104)) ∗
        chainHeaps A gcs) := by
    ac_rfl
  rw [hpull, ← hoff,
      ← memRegion_split (ptr + BitVec.ofNat 64 (gcs.length * 104)) 104 _ (by omega),
      ← hsplit_len]
  exact vecBuf_chainAt_of_bytes A cap ptr hcap hrest (by omega) hcap_lt hptr

/-! ## 3. Pure Model Lemmas for `S3Spec` -/

theorem exec_fromSessionState_eq (st : SessionState (List (BitVec 8))) :
    Mut.exec TripleRatchet.fromSessionState st =
      match st.remoteIdentity with
      | some remote =>
        (.ok ⟨⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩,
              st.pqRatchetState, st.localIdentity, remote⟩,
         { st with receiverChains := [], pqRatchetState := [] })
      | none =>
        (.error (.invalidSessionStructure .missingRemoteIdentity),
         { st with receiverChains := [], pqRatchetState := [] }) := by
  rcases st with ⟨_, _, _ | remote, _, _, _, _, _, _⟩ <;> rfl

private theorem match_except_ite {ε α : Type} (r : Except ε α) (n : Nat) :
    (if (True ∧ (match r with | .ok _ => true | .error _ => false) = true) then n else 0) =
      match r with | .ok _ => n | .error _ => 0 := by
  cases r <;> rfl

/-- When `Mut.exec TripleRatchet.fromSessionState st = (.ok tr, st1)` and
`tr.ratchet.findReceiverChainKey srk = .ok none`, `decryptDraws` simplifies to `0` if
`tr.ratchet.senderChain = none` or the receiving `rootCreateChain` fails, and `min 32 rest.length`
if `tr.ratchet.senderChain = some sc` and the receiving `rootCreateChain` succeeds. -/
theorem decryptDraws_eq_of_fromSessionState (C : Crypto) (st st1 : SessionState (List (BitVec 8)))
    (tr : TripleRatchet (List (BitVec 8))) (srk : PublicKey) (rest : List (BitVec 8))
    (hfrom : Mut.exec TripleRatchet.fromSessionState st = (.ok tr, st1))
    (hfind : tr.ratchet.findReceiverChainKey srk = .ok none) :
    decryptDraws C st srk rest =
      match tr.ratchet.senderChain with
      | none => 0
      | some sc =>
        match rootCreateChain C tr.ratchet.rootKey srk sc.ratchetKey.privateKey with
        | .ok _ => min 32 rest.length
        | .error _ => 0 := by
  rw [exec_fromSessionState_eq] at hfrom
  rcases st with ⟨sv, lik, _ | remIk, rk, pc, _ | sc, rcs, ppk, pqr⟩
  · cases hfrom
  · cases hfrom
  · cases hfrom
    unfold decryptDraws drawsCoins
    dsimp only at hfind ⊢
    rw [hfind]
    rfl
  · cases hfrom
    unfold decryptDraws drawsCoins
    dsimp only at hfind ⊢
    rw [hfind]
    simp only [Option.isSome_some, Bool.true_and]
    exact ( by
      generalize rootCreateChain C rk srk sc.ratchetKey.privateKey = r
      cases r <;> rfl )

theorem clampScalar_idem (v : List.Vector (BitVec 8) 32) :
    Ratchet.clampScalar (Ratchet.clampScalar v) = Ratchet.clampScalar v := by
  apply List.Vector.ext
  intro j
  by_cases h31 : j = 31
  · subst h31
    simp only [Ratchet.clampScalar, List.Vector.get_set_same]
    bv_slice
  · by_cases h0 : j = 0
    · subst h0
      simp only [Ratchet.clampScalar, List.Vector.get_set_of_ne (Ne.symm h31),
        List.Vector.get_set_same]
      bv_slice
    · simp only [Ratchet.clampScalar, List.Vector.get_set_of_ne (Ne.symm h31),
        List.Vector.get_set_of_ne (Ne.symm h0)]

theorem clampScalar_keyPair_generate (C : Crypto) (coins : BitVec 256) :
    Ratchet.clampScalar (KeyPair.generate C coins).privateKey.bytes =
      (KeyPair.generate C coins).privateKey.bytes :=
  clampScalar_idem (Ratchet.keyToBytesVec32 coins)

/-- For a non-empty list `c :: cs` with `(c :: cs).length ≥ 6`,
`RatchetState.evictReceiverChains (c :: cs)` equals `RatchetState.evictReceiverChains cs`. -/
theorem evictReceiverChains_cons_of_ge_six (c : ReceiverChain) (cs : List ReceiverChain)
    (h : 6 ≤ (c :: cs).length) :
    RatchetState.evictReceiverChains (c :: cs) = RatchetState.evictReceiverChains cs := by
  unfold RatchetState.evictReceiverChains
  simp only [List.length_cons] at h ⊢
  have hsub : cs.length + 1 - maxReceiverChains = (cs.length - maxReceiverChains) + 1 := by
    unfold maxReceiverChains at *; omega
  rw [hsub, List.drop_succ_cons]

theorem evictReceiverChains_of_le_five (cs : List ReceiverChain) (h : cs.length ≤ 5) :
    RatchetState.evictReceiverChains cs = cs := by
  unfold RatchetState.evictReceiverChains
  have hsub : cs.length - maxReceiverChains = 0 := by
    unfold maxReceiverChains; omega
  rw [hsub, List.drop_zero]

/-! ## 4. Mid-Segment Checkpoint (`+0x8ac` = `0x34c48`) for Commit + Push + Evict -/

/-- **S3 commit checkpoint PC (`+0x8ac` = `0x34c48`)**:
Entry to the state-commit, `PublicKey::serialize`, `ChainKey::to_pb`, `receiver_chains` push,
oldest-chain eviction loop, and `S4State` staging block (`+0x8ac .. +0xbfc → +0x3e4`),
reached when `cbz w8, 0x34c48` at `+0x7e0` sees `w8 = 0` (`Ok((finalRootKey, senderChainKey))`
from the sending `RootKey::create_chain` call at `+0x7d4`). -/
abbrev segS3CommitPC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x8ac#64

/-- **S3 commit checkpoint state (`segS3CommitPC img = +0x8ac`)**:
Both `RootKey::create_chain` calls (receiving at `+0x544` and sending at `+0x7d4`) and
`KeyPair::generate` (`rng_fill` + clamping + `derive_public_key_bytes` at `+0x77c..+0x7c0`)
have succeeded:
* `tr.ratchet.senderChain = some sc`, and `tr.ratchet.rootKey` in `sp + 0xb8..0xd8` has been
  zeroed (`{ tr.ratchet with rootKey := 0 }`);
* `draws = min 32 x.rest.length` bytes have been drawn from `tapeAfter`;
* `[sp + 0x190..0x1d8]` (`x25`) holds `createChainResultAt (sp + 0x190) (.ok (finalRootKey,
senderChainKey))`:
  `0#32` at `sp + 0x190`, `keyToBytes32 finalRootKey` at `sp + 0x194..0x1b4`, and
  `chainKeyBytes senderChainKey` at `sp + 0x1b4..0x1d8`;
* `[sp + 0x3d0..0x3f4]` (`x28`) holds `chainKeyBytes receiverChainKey` (`36` B), and its copies for
  `S4State` staging are already placed at `sp + 0x4c0..0x4d0` (`drop 20`, `[x28, #0xf0]`),
  `sp + 0x4d0..0x4e0` (`take 16`, `[x28, #0x100]`), and `sp + 0x10..0x14` (`(drop 16).take 4`);
* `[sp + 0x400..0x440]` holds `newSenderKey.publicKey` (`0x400..0x420`) and
  `newSenderKey.privateKey` (`0x420..0x440`);
* `[sp + 0x1c]` holds `msgW : BitVec 32` with `msgW.setWidth 8 = msgTypeByte x.msgType`. -/
def S3CommitState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8)))
    (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
    (finalRootKey : RootKey) (senderChainKey : ChainKey)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  let draws := min 32 x.rest.length
  s.pc = segS3CommitPC img ∧
  tryDecryptMidMeta img s0 s ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x500#64 ∧
  s.readReg64 .x25 = sp + 0x190#64 ∧
  s.readReg64 .x27 = sp + 0x38#64 ∧
  s.readReg64 .x28 = sp + 0x3d0#64 ∧
  ∃ (msgW : BitVec 32),
    msgW.setWidth 8 = msgTypeByte x.msgType ∧
    (s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := 0 } } ∗
      memRegion x.ret 48 ∗
      memRegion sp 0x10 ∗
      ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
      memRegion (sp + 0x14#64) 8 ∗
      ((sp + 0x1c#64) ↦₃₂ msgW) ∗
      ((sp + 0x20#64) ↦₆₄ x.locA) ∗
      ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
      memRegion (sp + 0x2c#64) 4 ∗
      ((sp + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 0x140#64) 0x50 ∗
      ((sp + 0x190#64) ↦₃₂ 0#32) ∗
      ((sp + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
      ((sp + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗
      memRegion (sp + 0x1d8#64) 0xd8 ∗
      memRegion (sp + 0x2b0#64) 0x10 ∗
      memRegion (sp + 0x2c0#64) 0x110 ∗
      ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
      memRegion (sp + 0x3f4#64) 12 ∗
      ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
      ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
      memRegion (sp + 0x440#64) 0x80 ∗
      ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
      ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
      memRegion (sp + 0x4e0#64) 0xa0 ∗
      tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-- **S3 commit sub-segment contract (`+0x8ac → +0x3e4` or panic)**:
From `S3CommitState` at `segS3CommitPC img` (`+0x8ac`) when `tr.ratchet.senderChain = some sc`,
execution updates `previous_counter` and `root_key`, serializes `x.msg.senderRatchetKey` via
`PublicKey::serialize` (`+0x8fc`), converts `receiverChainKey` via `ChainKey::to_pb` (`+0xa80`),
pushes the new `ReceiverChain` onto `tr.ratchet.receiverChains` (calling `grow_one<Chain>` at
`+0xa98` if `len = cap`), deallocates the temporary `PublicKey::serialize` box (`+0xaf0`),
evicts oldest chains via `Vec::remove(0)` (`memmove` + `drop_glue<Chain>`, `+0xb04..+0xb94`)
until `len ≤ 5`, commits `sender_chain = some ⟨newSenderKey, senderChainKey⟩`, stages
`receiverChainKey` across `sp + 0x2b0..0x2d4`, and branches (`+0xbfc: b 0x34780`) to `segS4PC img`
(`+0x3e4`) in `S4State`. -/
def S3CommitSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  PublicKeySerializeOk img.base C A ctl abs →
  ChainKeyToPbOk img.base C A ctl abs →
  GrowOneChainOk img C A ctl abs →
  DropChainOk img.base C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (sc : SenderChain)
      (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
      (finalRootKey : RootKey) (senderChainKey : ChainKey)
      (R : SepProp) (s0 s : State),
      tr.ratchet.senderChain = some sc →
      tr.ratchet.receiverChains.length < 2 ^ 32 →
      Ratchet.clampScalar newSenderKey.privateKey.bytes = newSenderKey.privateKey.bytes →
      S3CommitState A ctl img x trG tr st1 receiverChainKey newSenderKey
        finalRootKey senderChainKey R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      let newChain : ReceiverChain :=
        { senderRatchetKey := x.msg.senderRatchetKey
          chainKey := some receiverChainKey
          messageKeys := [] }
      let r1 : RatchetState :=
        { tr.ratchet with
          senderChain := some ⟨newSenderKey, senderChainKey⟩
          rootKey := finalRootKey
          previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)
          receiverChains :=
            RatchetState.evictReceiverChains (tr.ratchet.receiverChains ++ [newChain]) }
      ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
        ((∃ trG', S4State A ctl img x trG' { tr with ratchet := r1 } st1
            receiverChainKey (min 32 x.rest.length) R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

namespace BS10

end BS10

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegB
