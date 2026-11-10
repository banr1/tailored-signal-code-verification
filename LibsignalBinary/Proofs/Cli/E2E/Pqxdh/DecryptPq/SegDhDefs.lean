/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SignalSession.Coins.Fill
import ProofLib.SepLogic.WPp

/-!
# Segment `S3` (`dh_ratchet_step`) Definitions for CLI `try_decrypt_with_state::<Coins>`

Instruction-fetch macro `td_fetches_cli`, `S3CommitState` (`+0x8ac`) checkpoint predicate, and the
in-image `signal_session_coins_fill` callee bridge for Segment `S3` in `libsignalSessionImage`.
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

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Instruction-fetch macro for `try_decrypt_with_state::<signal_session_handshake::Coins>` covering `len` bytes from function-relative offset `k0`. -/
macro "td_fetches_cli " b:term:max H:term:max hfn:ident k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBinCli $b $H $hfn (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") $k0 $len)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.tapeAfter_zero_eq (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    tapeAfter ctl cur rest 0 =
      (ctl ↦₆₄ cur) ∗ ((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ (cur ↦ₛ rest) := by
  unfold tapeAfter
  simp only [BitVec.add_zero, Nat.sub_zero]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.hookRngFillAfter0_ok (ctl : BitVec 64) :
    HookOk (rngFillHook ctl) (rngFillAfter0Spec ctl) := by
  intro ⟨dst, len, cur, rest⟩ R s0 hrun hpre _
  simp only [rngFillAfter0Spec, CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.tapeAfter_zero_eq, sepConj_assoc, satisfies_pure_sepConj] at hpre
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

namespace ChainArrayBytes

end ChainArrayBytes

/-- Segment `S3` commit checkpoint PC (`+0x8ac`): state commit, `PublicKey::serialize`, `ChainKey::to_pb`, `receiver_chains` push/eviction, and `S4State` staging after sending `RootKey::create_chain` succeeds. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.segS3CommitPC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x8ac#64

/-- Segment `S3` commit checkpoint state (`+0x8ac`): both `RootKey::create_chain` calls and
`KeyPair::generate` (`signal_session_coins_fill` + clamping + `derive_public_key_bytes`) have
succeeded, `tr.ratchet.rootKey` at `sp + 0xb8..0xd8` is zeroed, `draws = min 32 x.rest.length`,
`[sp + 0x190..0x1d8]` holds `(finalRootKey, senderChainKey)`, `[sp + 0x3d0..0x3f4]` (and staging
copies at `sp + 0x4c0..0x4e0`, `sp + 0x10..0x14`) holds `receiverChainKey`, and
`[sp + 0x400..0x440]` holds `newSenderKey`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.S3CommitState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8)))
    (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
    (finalRootKey : RootKey) (senderChainKey : ChainKey)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  let draws := min 32 x.rest.length
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.segS3CommitPC img ∧
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
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

namespace BS10

/-- In-image `signal_session_coins_fill` (`+0x77c`) satisfies `coinsFillAtSpec b tryDecryptSubStack cur rest`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.BS10.coinsFillAt_ok_td
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl cur : BitVec 64}
    {rest : List (BitVec 8)} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) (hb : b &&& 0xfff#64 = 0#64) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off%
        "signal_session_coins_fill" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) % 2^64))
      (CryptoVerification.SignalSession.Coins.coinsFillAtSpec b tryDecryptSubStack cur rest) :=
  CryptoVerification.SignalSession.Coins.coinsFillAt_of_after0
    (CryptoVerification.SignalSession.Coins.coinsFill_ok_at (ext := tripleRatchetExterns C ctl abs)
      (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hA) hb tryDecryptSubStack (by decide) (by decide)
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
      (num% (ls_off% "signal_session_coins_fill" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))
      (by fnoff_eq))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.BS10.staticDrop_ok_at2_td {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off%
        "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) % 2^64))
      zeroizeSecretSpec :=
  hook_ok_at (hname := staticDropName) (off := (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) (stub :=
    num% (ls_off% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop")) (k :=
    num% (ls_off% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")))
    (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") rfl (by decide)
    (ls_hook% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop")
    (by dsimp [staticDropName]; simp [Rust.isPanicSymbol])
    ⟨zeroizeSecretHook, rfl, zeroize32_hookOk⟩

end BS10

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegB
