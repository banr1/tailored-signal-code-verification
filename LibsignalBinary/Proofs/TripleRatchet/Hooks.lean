/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
public import LibsignalBinary.Proofs.TripleRatchet.TrapRng
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalTripleRatchetProofDefs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.HookTrace
import LibsignalBinary.Proofs.TripleRatchet.InImage.Prost
import LibsignalBinary.Proofs.TripleRatchet.InImage.Spqr

/-!
# Triple-Ratchet Hook Satisfaction and Call-Site Lemmas

Proves `HookOk` and `subroutine_ok` call-site lemmas for concrete and abstract extern stubs
on `tripleRatchetProgAt`, along with panic-stub trap lemmas.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.HookTrace

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

/-! ## `HookOk` proofs for concrete hooks -/

theorem sessionShim_hookOk : HookOk hookNoop sessionShimSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  simp only [sessionShimSpec, hookNoop, retHook, id_eq, State.trace_setPC,
    satisfies_pure_sepConj, true_and, emp_sepConj] at hpre ⊢
  exact hpre

theorem hookMemcpy_region_trace_ok : HookOk hookMemcpy sessionMemcpyRegionSpec := by
  refine HookOk.of_trace hookMemcpy_region_ok fun _ _ _ ht hpost => ?_
  simp only [memcpyRegionSpec, sessionMemcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1, ht⟩, hpost.2⟩

theorem hookMemcpy_trace_ok (hookStack : Nat := 4096) :
    HookOk hookMemcpy (sessionMemcpySpec hookStack) := by
  refine HookOk.of_trace (hookMemcpy_ok hookStack) fun _ _ _ ht hpost => ?_
  simp only [libcMemcpySpec, sessionMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1, ht⟩, hpost.2⟩

theorem hookMemmove_trace_ok (hookStack : Nat := 4096) :
    HookOk hookMemmove (sessionMemmoveSpec hookStack) := by
  refine HookOk.of_trace (hookMemmove_ok hookStack) fun _ _ _ ht hpost => ?_
  simp only [libcMemmoveSpec, sessionMemmoveSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1, ht⟩, hpost.2⟩

theorem hookMemset_region_trace_ok : HookOk hookMemset sessionMemsetRegionSpec := by
  refine HookOk.of_trace hookMemset_region_ok fun _ _ _ ht hpost => ?_
  simp only [memsetRegionSpec, sessionMemsetRegionSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1, ht⟩, hpost.2⟩

theorem hookMemset_trace_ok (hookStack : Nat := 4096) (hstack : 0 < hookStack := by decide) :
    HookOk hookMemset (sessionMemsetSpec hookStack) := by
  refine HookOk.of_trace (hookMemset_ok hookStack hstack) fun _ _ _ ht hpost => ?_
  simp only [libcMemsetSpec, sessionMemsetSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1, ht⟩, hpost.2⟩

theorem blackBoxHook_ok : HookOk blackBoxHook blackBoxSpec := by
  unfold blackBoxHook
  refine retHook_ok fun v R s0 _ hpre _ => ?_
  simp only [blackBoxSpec, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hv, hR⟩
  subst hv
  refine ⟨Memory.KeepsFrozen.refl _, rfl, ‹_›,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [blackBoxSpec, retHook]
  rw [satisfies_pure_sepConj]
  exact ⟨⟨rfl, rfl⟩, hR⟩

theorem zeroizeSecretHook_ok : HookOk zeroizeSecretHook zeroizeSecretSpec := by
  unfold zeroizeSecretHook
  refine retHook_ok fun a R s0 _ hpre _ => ?_
  simp only [zeroizeSecretSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨ha, hmem⟩
  subst ha
  let zeros := List.replicate 32 (0#8 : BitVec 8)
  have hlen : zeros.length ≤ 2 ^ 64 := by decide
  have hmem_rep : s0.mem ⊨ memRegion (s0.readReg64 .x0) zeros.length ∗ R := by
    simpa [zeros] using hmem
  refine ⟨keepsFrozen_writeBytes_of_memRegion zeros hlen hmem_rep,
    rfl, ‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  change s0.mem.writeBytes (s0.readReg64 .x0) zeros ⊨
    (⌜s0.trace = s0.trace⌝ ∗ (s0.readReg64 .x0 ↦ₛ zeros)) ∗ R
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨rfl, satisfies_writeBytes zeros hlen hmem_rep⟩

private theorem readVec32_of_pointsToBytes {m : Memory} {a : BitVec 64}
    {v : List.Vector (BitVec 8) 32} {R : SepProp}
    (h : m ⊨ (a ↦ₛ v.toList) ∗ R) :
    readVec32 m a = v := by
  obtain ⟨_, hread⟩ := (IsBlock.pointsToBytes a v.toList).read h
  rw [v.toList_length] at hread
  apply Subtype.ext
  exact hread

theorem diffieHellmanHook_ok (X : Ratchet.X25519Fn) : HookOk (diffieHellmanHook X) (diffieHellmanSpec X) := by
  unfold diffieHellmanHook
  refine retHook_ok fun ⟨secA, sec, pubA, pub, ret⟩ R s0 _ hpre _ => ?_
  simp only [diffieHellmanSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8⟩, hmem⟩
  have hsec : readVec32 s0.mem secA = sec := readVec32_of_pointsToBytes hmem
  have hmem_pub : s0.mem ⊨ (pubA ↦ₛ pub.toList) ∗ ((secA ↦ₛ sec.toList) ∗ (memRegion ret 32 ∗ R)) := by
    rwa [← sepConj_assoc, sepConj_comm (secA ↦ₛ sec.toList), sepConj_assoc] at hmem
  have hpub : readVec32 s0.mem pubA = pub := readVec32_of_pointsToBytes hmem_pub
  have hmem_ret : s0.mem ⊨ memRegion ret (X sec pub).toList.length ∗
      ((secA ↦ₛ sec.toList) ∗ ((pubA ↦ₛ pub.toList) ∗ R)) := by
    rw [(X sec pub).toList_length]
    rwa [← sepConj_assoc, ← sepConj_assoc,
      sepConj_comm ((secA ↦ₛ sec.toList) ∗ (pubA ↦ₛ pub.toList)),
      sepConj_assoc, sepConj_assoc] at hmem
  have hlen : (X sec pub).toList.length ≤ 2 ^ 64 := by rw [(X sec pub).toList_length]; decide
  refine ⟨?_, rfl, ‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · dsimp only
    rw [hx0, hx1, hx8, hsec, hpub]
    exact keepsFrozen_writeBytes_of_memRegion (X sec pub).toList hlen hmem_ret
  · simp only [diffieHellmanSpec, retHook, State.trace_setPC, hx0, hx1, hx8, hsec, hpub,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨rfl, ?_⟩
    have hw := satisfies_writeBytes (X sec pub).toList hlen hmem_ret
    rwa [← sepConj_assoc (secA ↦ₛ sec.toList), ← sepConj_assoc,
      sepConj_comm (ret ↦ₛ (X sec pub).toList), sepConj_assoc, sepConj_assoc] at hw

theorem pubFromSecretHook_ok (pubKey : PubKeyFn) :
    HookOk (pubFromSecretHook pubKey) (pubFromSecretSpec pubKey) := by
  unfold pubFromSecretHook
  refine retHook_ok fun ⟨secA, sec, ret⟩ R s0 _ hpre _ => ?_
  simp only [pubFromSecretSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8⟩, hmem⟩
  have hsec : readVec32 s0.mem secA = sec := readVec32_of_pointsToBytes hmem
  have hmem_ret : s0.mem ⊨ memRegion ret (pubKey sec).toList.length ∗ ((secA ↦ₛ sec.toList) ∗ R) := by
    rw [(pubKey sec).toList_length]
    rwa [← sepConj_assoc, sepConj_comm (secA ↦ₛ sec.toList), sepConj_assoc] at hmem
  have hlen : (pubKey sec).toList.length ≤ 2 ^ 64 := by rw [(pubKey sec).toList_length]; decide
  refine ⟨?_, rfl, ‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · dsimp only
    rw [hx0, hx8, hsec]
    exact keepsFrozen_writeBytes_of_memRegion (pubKey sec).toList hlen hmem_ret
  · simp only [pubFromSecretSpec, retHook, State.trace_setPC, hx0, hx8, hsec,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨rfl, ?_⟩
    have hw := satisfies_writeBytes (pubKey sec).toList hlen hmem_ret
    rwa [← sepConj_assoc, sepConj_comm (ret ↦ₛ (pubKey sec).toList), sepConj_assoc] at hw

private theorem take_min_append_replicate {α : Type} (xs : List α) (len : Nat) (z : α) :
    xs.take (min len xs.length) ++ List.replicate (len - min len xs.length) z =
      (xs ++ List.replicate len z).take len := by
  by_cases h : len ≤ xs.length
  · rw [Nat.min_eq_left h, Nat.sub_self, List.replicate_zero, List.append_nil,
      List.take_append_of_le_length h]
  · have h' : xs.length ≤ len := by omega
    rw [Nat.min_eq_right h', List.take_of_length_le (Nat.le_refl _),
      List.take_append, List.take_of_length_le h', List.take_replicate,
      Nat.min_eq_left (by omega)]

private theorem keepsFrozen_write8_of_block {P R : SepProp} {a : BitVec 64} {Φ : Memory → Prop}
    {m : Memory} (hb : IsBlock P a 1 Φ) (h : m ⊨ P ∗ R) (v : BitVec 8) :
    m.KeepsFrozen (m.write8 a v) :=
  Memory.keepsFrozen_write8 (hb.canWrite (by decide) h) v

private theorem keepsFrozen_write64_of_block {P R : SepProp} {a : BitVec 64} {Φ : Memory → Prop}
    {m : Memory} (hb : IsBlock P a 8 Φ) (h : m ⊨ P ∗ R) (v : BitVec 64) :
    m.KeepsFrozen (m.write64 a v) :=
  Memory.keepsFrozen_write64 (hb.canWrite (by decide) h) v

private theorem readBytes_pointsToBytes_take {m : Memory} {p : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} {k : Nat} (hk : k ≤ bs.length) (h : m ⊨ (p ↦ₛ bs) ∗ R) :
    m.readBytes p k = bs.take k := by
  have hsplit : (p ↦ₛ bs) =
      (p ↦ₛ bs.take k) ∗ ((p + BitVec.ofNat 64 (bs.take k).length) ↦ₛ bs.drop k) := by
    conv_lhs => rw [← List.take_append_drop k bs, pointsToBytes_append]
  rw [hsplit, sepConj_assoc] at h
  have hread := ((IsBlock.pointsToBytes p (bs.take k)).read h).2
  rwa [List.length_take_of_le hk] at hread

private theorem readBytes_pointsToBytes_slice {m : Memory} {p : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} (k n : Nat) (hkn : k + n ≤ bs.length) (h : m ⊨ (p ↦ₛ bs) ∗ R) :
    m.readBytes (p + BitVec.ofNat 64 k) n = (bs.drop k).take n := by
  have hsplit : (p ↦ₛ bs) =
      (p ↦ₛ bs.take k) ∗ ((p + BitVec.ofNat 64 (bs.take k).length) ↦ₛ bs.drop k) := by
    conv_lhs => rw [← List.take_append_drop k bs, pointsToBytes_append]
  rw [hsplit, List.length_take_of_le (by omega), sepConj_assoc] at h
  have h' : m ⊨ ((p + BitVec.ofNat 64 k) ↦ₛ bs.drop k) ∗ ((p ↦ₛ bs.take k) ∗ R) := by
    rw [show ((p + BitVec.ofNat 64 k) ↦ₛ bs.drop k) ∗ ((p ↦ₛ bs.take k) ∗ R) =
      (p ↦ₛ bs.take k) ∗ (((p + BitVec.ofNat 64 k) ↦ₛ bs.drop k) ∗ R) by ac_rfl]
    exact h
  exact readBytes_pointsToBytes_take (by simp; omega) h'

private theorem shaState_toList_eq (h : ShaState) :
    h.toList = [h.get 0, h.get 1, h.get 2, h.get 3, h.get 4, h.get 5, h.get 6, h.get 7] := by
  rcases h with ⟨_ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩, hl⟩
  all_goals (first | rfl | (simp at hl))

private theorem shaStateBytes_length (h : ShaState) :
    (LibsignalHmac.shaStateBytes h).length = 32 := by
  rw [LibsignalHmac.shaStateBytes, shaState_toList_eq]
  rfl

private theorem read32_of_readBytes_toLEBytes_4 (m : Memory) (a : BitVec 64) (w : BitVec 32)
    (h : m.readBytes a 4 = LibsignalAesCbc.toLEBytes 4 w) : m.read32 a = w := by
  have h4 : m.readBytes a 4 =
      [m.read8 a, m.read8 (a + 1#64), m.read8 (a + 2#64), m.read8 (a + 3#64)] := by
    simp only [Memory.readBytes, BitVec.add_assoc]; rfl
  have hle : LibsignalAesCbc.toLEBytes 4 w =
      [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8] := rfl
  rw [h4, hle] at h
  simp only [List.cons.injEq, and_true] at h
  rcases h with ⟨h0, h1, h2, h3⟩
  dsimp only [Memory.read32]
  rw [BitVec.add_zero, h0, h1, h2, h3]
  bv_bits

private theorem readShaState_of_pointsToBytes {m : Memory} {a : BitVec 64} {st : ShaState}
    {R : SepProp} (h : m ⊨ (a ↦ₛ LibsignalHmac.shaStateBytes st) ∗ R) :
    LibsignalHmac.readShaState m a = st := by
  apply List.Vector.ext
  intro i
  simp only [LibsignalHmac.readShaState, List.Vector.get_ofFn]
  apply read32_of_readBytes_toLEBytes_4
  rw [readBytes_pointsToBytes_slice (4 * i.val) 4 (by rw [shaStateBytes_length]; omega) h]
  fin_cases i <;> (rw [LibsignalHmac.shaStateBytes, shaState_toList_eq]; rfl)

theorem compress256Hook_ok (F : ShaState → List (BitVec 8) → ShaState) :
    HookOk (LibsignalHmac.compress256Hook F) (compress256Spec F) := by
  change HookOk
    (retHook (fun s =>
      let st := LibsignalHmac.readShaState s.mem (s.readReg64 .x0)
      let bs := s.mem.readBytes (s.readReg64 .x1) (64 * (s.readReg64 .x2).toNat)
      s.setMem (s.mem.writeBytes (s.readReg64 .x0)
        (LibsignalHmac.shaStateBytes ((chunks64 bs).foldl F st)))))
    (compress256Spec F)
  refine retHook_ok fun ⟨stA, st, blkA, bs, n⟩ R s0 _ hpre _ => ?_
  simp only [compress256Spec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hbs_len⟩, hmem⟩
  have hst : LibsignalHmac.readShaState s0.mem stA = st :=
    readShaState_of_pointsToBytes hmem
  have hmem_blk : s0.mem ⊨ (blkA ↦ₛ bs) ∗ ((stA ↦ₛ LibsignalHmac.shaStateBytes st) ∗ R) := by
    rw [show (blkA ↦ₛ bs) ∗ ((stA ↦ₛ LibsignalHmac.shaStateBytes st) ∗ R) =
      (stA ↦ₛ LibsignalHmac.shaStateBytes st) ∗ ((blkA ↦ₛ bs) ∗ R) by ac_rfl]
    exact hmem
  have hbs : s0.mem.readBytes blkA (64 * n) = bs := by
    rw [← hbs_len]
    exact ((IsBlock.pointsToBytes blkA bs).read hmem_blk).2
  let outBytes := LibsignalHmac.shaStateBytes ((chunks64 bs).foldl F st)
  have hout_len : outBytes.length = (LibsignalHmac.shaStateBytes st).length := by
    simp only [outBytes, shaStateBytes_length]
  have hmem_reg : s0.mem ⊨ memRegion stA outBytes.length ∗ ((blkA ↦ₛ bs) ∗ R) := by
    rw [hout_len]
    exact Satisfies.mono (sepConj_mono_left (pointsToBytes_entails_memRegion stA _)) hmem
  have hlen32 : outBytes.length ≤ 2 ^ 64 := by
    simp only [outBytes, shaStateBytes_length]; decide
  refine ⟨?_, rfl, ‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · simp only [State.setMem, hx0, hx1, hx2, hst, hbs]
    exact keepsFrozen_writeBytes_of_memRegion outBytes hlen32 hmem_reg
  · simp only [compress256Spec, retHook, State.trace_setPC, State.setMem,
      hx0, hx1, hx2, hst, hbs, sepConj_assoc, satisfies_pure_sepConj, true_and]
    exact satisfies_writeBytes outBytes hlen32 hmem_reg

theorem rngFillHook_ok (ctl : BitVec 64) :
    HookOk (rngFillHook ctl) (rngFillSpec ctl) := by
  intro ⟨dst, len, cur, rest⟩ R s0 hrun hpre _
  simp only [rngFillSpec, tapeAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hpre⟩
  rw [sepConj_pure_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hrest_lt, hmem⟩
  have hlen_lt : len < 2 ^ 64 := hx1 ▸ (s0.readReg64 .x1).isLt
  have hmem_ctl : s0.mem ⊨ (ctl ↦₆₄ cur) ∗
      (memRegion dst len ∗ (((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ ((cur ↦ₛ rest) ∗ R))) := by
    rw [show (ctl ↦₆₄ cur) ∗ (memRegion dst len ∗ (((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ ((cur ↦ₛ rest) ∗ R))) =
      memRegion dst len ∗ ((ctl ↦₆₄ cur) ∗ (((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ ((cur ↦ₛ rest) ∗ R))) by ac_rfl]
    exact hmem
  have hcur : s0.mem.read64 ctl = cur := (IsBlock.pointsTo64 ctl cur).read hmem_ctl
  have hmem_rem : s0.mem ⊨ ((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
      ((ctl ↦₆₄ cur) ∗ (memRegion dst len ∗ ((cur ↦ₛ rest) ∗ R))) := by
    rw [show ((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ ((ctl ↦₆₄ cur) ∗ (memRegion dst len ∗ ((cur ↦ₛ rest) ∗ R))) =
      memRegion dst len ∗ ((ctl ↦₆₄ cur) ∗ (((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ ((cur ↦ₛ rest) ∗ R))) by ac_rfl]
    exact hmem
  have hrem64 : s0.mem.read64 (ctl + 8#64) = BitVec.ofNat 64 rest.length :=
    (IsBlock.pointsTo64 _ _).read hmem_rem
  have hrem : (s0.mem.read64 (ctl + 8#64)).toNat = rest.length := by
    rw [hrem64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmem_cur : s0.mem ⊨ (cur ↦ₛ rest) ∗
      (((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ ((ctl ↦₆₄ cur) ∗ (memRegion dst len ∗ R))) := by
    rw [show (cur ↦ₛ rest) ∗ (((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ ((ctl ↦₆₄ cur) ∗ (memRegion dst len ∗ R))) =
      memRegion dst len ∗ ((ctl ↦₆₄ cur) ∗ (((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ ((cur ↦ₛ rest) ∗ R))) by ac_rfl]
    exact hmem
  let k := min len rest.length
  have hread_cur : s0.mem.readBytes cur (min len rest.length) = rest.take (min len rest.length) :=
    readBytes_pointsToBytes_take (Nat.min_le_right len rest.length) hmem_cur
  let bytes := (rest ++ List.replicate len 0#8).take len
  have hbytes_eq :
      rest.take (min len rest.length) ++ List.replicate (len - min len rest.length) 0#8 = bytes :=
    take_min_append_replicate rest len 0#8
  have hbytes_len : bytes.length = len := by
    simp only [bytes, List.length_take, List.length_append, List.length_replicate]; omega
  have hlen_le : bytes.length ≤ 2 ^ 64 := by omega
  have hkf1 := keepsFrozen_write64_of_block (IsBlock.pointsTo64 ctl cur) hmem_ctl
    (cur + BitVec.ofNat 64 k)
  have hw1 := (IsBlock.pointsTo64 ctl cur).write64 hmem_ctl (cur + BitVec.ofNat 64 k)
  have hw1' : (s0.mem.write64 ctl (cur + BitVec.ofNat 64 k)) ⊨
      ((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
        (memRegion dst len ∗ ((ctl ↦₆₄ (cur + BitVec.ofNat 64 k)) ∗ ((cur ↦ₛ rest) ∗ R))) := by
    rw [show ((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
        (memRegion dst len ∗ ((ctl ↦₆₄ (cur + BitVec.ofNat 64 k)) ∗ ((cur ↦ₛ rest) ∗ R))) =
      (ctl ↦₆₄ (cur + BitVec.ofNat 64 k)) ∗
        (memRegion dst len ∗ (((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ ((cur ↦ₛ rest) ∗ R))) by ac_rfl]
    exact hw1
  have hkf2 := keepsFrozen_write64_of_block (IsBlock.pointsTo64 _ _) hw1'
    (BitVec.ofNat 64 (rest.length - k))
  have hw2 := (IsBlock.pointsTo64 _ _).write64 hw1' (BitVec.ofNat 64 (rest.length - k))
  have hw2' : ((s0.mem.write64 ctl (cur + BitVec.ofNat 64 k)).write64 (ctl + 8#64)
      (BitVec.ofNat 64 (rest.length - k))) ⊨
      memRegion dst bytes.length ∗
        ((ctl ↦₆₄ (cur + BitVec.ofNat 64 k)) ∗
          (((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 (rest.length - k)) ∗ ((cur ↦ₛ rest) ∗ R))) := by
    rw [hbytes_len, show memRegion dst len ∗
        ((ctl ↦₆₄ (cur + BitVec.ofNat 64 k)) ∗
          (((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 (rest.length - k)) ∗ ((cur ↦ₛ rest) ∗ R))) =
      ((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 (rest.length - k)) ∗
        (memRegion dst len ∗ ((ctl ↦₆₄ (cur + BitVec.ofNat 64 k)) ∗ ((cur ↦ₛ rest) ∗ R))) by ac_rfl]
    exact hw2
  have hkf3 := keepsFrozen_writeBytes_of_memRegion bytes hlen_le hw2'
  have hw3 := satisfies_writeBytes bytes hlen_le hw2'
  unfold rngFillHook
  simp only [hx0, hx1, hcur, hrem, hread_cur, hbytes_eq]
  refine ⟨hkf1.trans (hkf2.trans hkf3), rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
    by simp only [retHook, arm64_norm], ?_⟩⟩
  simp only [rngFillSpec, tapeAfter, retHook, State.trace_setPC, State.setMem,
    sepConj_assoc, satisfies_pure_sepConj, true_and]
  exact hw3

private theorem deserialize_take_min33 (bs : List (BitVec 8)) :
    PublicKey.deserialize (bs.take (min bs.length 33)) = PublicKey.deserialize bs := by
  have hmin : bs.take (min bs.length 33) = bs.take 33 := by
    by_cases h : bs.length ≤ 33
    · rw [Nat.min_eq_left h, List.take_of_length_le (Nat.le_refl _), List.take_of_length_le h]
    · rw [Nat.min_eq_right (by omega)]
  rw [hmin]
  cases bs with
  | nil => rfl
  | cons t rest =>
    by_cases h32 : 32 ≤ rest.length
    · simp only [List.take_succ_cons, PublicKey.deserialize]
      split
      · rfl
      · have hlen : 32 ≤ (rest.take 32).length := by simp [List.length_take, Nat.min_eq_left h32]
        simp only [hlen, ↓reduceDIte, List.take_take, Nat.min_self]
    · rw [List.take_of_length_le (by simp; omega)]

private theorem varintSlow_take_min10 (bs : List (BitVec 8)) :
    varintSlow (bs.take (min 10 bs.length)) = varintSlow bs := by
  simp only [varintSlow, List.take_take]
  by_cases h : 10 ≤ bs.length
  · rw [Nat.min_eq_left h, Nat.min_self]
  · rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega),
      List.take_length, List.take_of_length_le (by omega)]

private theorem stackAt_varintSlow_split (sp : BitVec 64) :
    stackAt sp varintSlowStack =
      stackAt (sp - 64#64) decodeErrorHookStack ∗
        (memRegion (sp - 64#64) 8 ∗
          (memRegion ((sp - 64#64) + 8#64) 40 ∗
            memRegion ((sp - 64#64) + 48#64) 16)) := by
  simp only [stackAt, varintSlowStack, decodeErrorHookStack, allocHookStack]
  rw [memRegion_split' (n := 8192) (k := 64) (b' := sp - 64#64) rfl (by bv_arith) (by decide),
    memRegion_split' (b := sp - 64#64) (n := 8) (k := 56) (b' := (sp - 64#64) + 8#64) rfl rfl (by decide),
    memRegion_split' (b := (sp - 64#64) + 8#64) (n := 40) (k := 16) (b' := (sp - 64#64) + 48#64)
      rfl (by bv_arith) (by decide)]
  exact congrArg₂ (· ∗ ·) (congrArg (memRegion · 8192) (by bv_arith)) rfl

private theorem stackAt_varintSlow_join (sp : BitVec 64) :
    stackAt (sp - 64#64) decodeErrorHookStack ∗
      (memRegion (sp - 64#64) 48 ∗ memRegion ((sp - 64#64) + 48#64) 16) =
    stackAt sp varintSlowStack := by
  simp only [stackAt, varintSlowStack, decodeErrorHookStack, allocHookStack]
  rw [← memRegion_split' (b := sp - 64#64) (n := 48) (k := 16) (b' := (sp - 64#64) + 48#64)
      rfl rfl (by decide),
    show memRegion (sp - 64#64 - BitVec.ofNat 64 (2 * 4096)) (2 * 4096) =
      memRegion (sp - BitVec.ofNat 64 (64 + 2 * 4096)) 8192 from
      congrArg (memRegion · 8192) (by bv_arith),
    ← memRegion_split' (n := 8192) (k := 64) (b' := sp - 64#64) rfl (by bv_arith) (by decide)]

theorem decodeVarintSlow_hookOk (A : RustAlloc)
    (abs : String → Option (State → State))
    (hFrom : HookSat abs decodeErrorFromName (decodeErrorFromSpec A)) :
    HookOk (decodeVarintSlowHook ((abs decodeErrorFromName).getD Rust.panicked))
      (decodeVarintSlowSpec A) := by
  rcases hFrom with ⟨fromHook, habs, hFromOk⟩
  rw [habs]; dsimp only [Option.getD]
  intro ⟨slotA, slot, ptr, bs⟩ R s0 hrun hpre hsp
  simp only [decodeVarintSlowSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hbs_lt⟩, hmem⟩
  have hslot : s0.mem.read64 slotA = slot := (IsBlock.pointsTo64 slotA slot).read hmem
  have hmem_slot : s0.mem ⊨ (slot ↦₆₄ ptr) ∗
      ((slotA ↦₆₄ slot) ∗ (((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((ptr ↦ₛ bs) ∗ (A.pool ∗ (stackAt s0.sp varintSlowStack ∗ R))))) := by
    rw [show (slot ↦₆₄ ptr) ∗
        ((slotA ↦₆₄ slot) ∗ (((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((ptr ↦ₛ bs) ∗ (A.pool ∗ (stackAt s0.sp varintSlowStack ∗ R))))) =
      (slotA ↦₆₄ slot) ∗ ((slot ↦₆₄ ptr) ∗ (((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((ptr ↦ₛ bs) ∗ (A.pool ∗ (stackAt s0.sp varintSlowStack ∗ R))))) by ac_rfl]
    exact hmem
  have hptr : s0.mem.read64 slot = ptr := (IsBlock.pointsTo64 slot ptr).read hmem_slot
  have hmem_len : s0.mem ⊨ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((slotA ↦₆₄ slot) ∗ ((slot ↦₆₄ ptr) ∗
        ((ptr ↦ₛ bs) ∗ (A.pool ∗ (stackAt s0.sp varintSlowStack ∗ R))))) := by
    rw [show ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((slotA ↦₆₄ slot) ∗ ((slot ↦₆₄ ptr) ∗
          ((ptr ↦ₛ bs) ∗ (A.pool ∗ (stackAt s0.sp varintSlowStack ∗ R))))) =
      (slotA ↦₆₄ slot) ∗ ((slot ↦₆₄ ptr) ∗ (((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((ptr ↦ₛ bs) ∗ (A.pool ∗ (stackAt s0.sp varintSlowStack ∗ R))))) by ac_rfl]
    exact hmem
  have hlen64 : s0.mem.read64 (slot + 8#64) = BitVec.ofNat 64 bs.length :=
    (IsBlock.pointsTo64 _ _).read hmem_len
  have hlen : (s0.mem.read64 (slot + 8#64)).toNat = bs.length := by
    rw [hlen64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbs_lt]
  have hmem_ptr : s0.mem ⊨ (ptr ↦ₛ bs) ∗
      ((slotA ↦₆₄ slot) ∗ ((slot ↦₆₄ ptr) ∗ (((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (A.pool ∗ (stackAt s0.sp varintSlowStack ∗ R))))) := by
    rw [show (ptr ↦ₛ bs) ∗
        ((slotA ↦₆₄ slot) ∗ ((slot ↦₆₄ ptr) ∗ (((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (A.pool ∗ (stackAt s0.sp varintSlowStack ∗ R))))) =
      (slotA ↦₆₄ slot) ∗ ((slot ↦₆₄ ptr) ∗ (((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((ptr ↦ₛ bs) ∗ (A.pool ∗ (stackAt s0.sp varintSlowStack ∗ R))))) by ac_rfl]
    exact hmem
  have hread : s0.mem.readBytes ptr (min 10 bs.length) = bs.take (min 10 bs.length) :=
    readBytes_pointsToBytes_take (Nat.min_le_right 10 bs.length) hmem_ptr
  have hvar : varintSlow (s0.mem.readBytes ptr (min 10 bs.length)) = varintSlow bs := by
    rw [hread, varintSlow_take_min10]
  have hadv (k : Nat) :
      s0.mem.KeepsFrozen
        ((s0.mem.write64 slot (ptr + BitVec.ofNat 64 k)).write64 (slot + 8#64)
          (BitVec.ofNat 64 (bs.length - k))) ∧
      ((s0.mem.write64 slot (ptr + BitVec.ofNat 64 k)).write64 (slot + 8#64)
        (BitVec.ofNat 64 (bs.length - k))) ⊨
        (slotA ↦₆₄ slot) ∗ ((slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
          (((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)) ∗
            ((ptr ↦ₛ bs) ∗ (A.pool ∗ (stackAt s0.sp varintSlowStack ∗ R))))) := by
    have hkf1 := keepsFrozen_write64_of_block (IsBlock.pointsTo64 slot ptr) hmem_slot
      (ptr + BitVec.ofNat 64 k)
    have hw1 := (IsBlock.pointsTo64 slot ptr).write64 hmem_slot (ptr + BitVec.ofNat 64 k)
    have hw1' : (s0.mem.write64 slot (ptr + BitVec.ofNat 64 k)) ⊨
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((slotA ↦₆₄ slot) ∗ ((slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
            ((ptr ↦ₛ bs) ∗ (A.pool ∗ (stackAt s0.sp varintSlowStack ∗ R))))) := by
      rw [show ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((slotA ↦₆₄ slot) ∗ ((slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
            ((ptr ↦ₛ bs) ∗ (A.pool ∗ (stackAt s0.sp varintSlowStack ∗ R))))) =
        (slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
          ((slotA ↦₆₄ slot) ∗ (((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            ((ptr ↦ₛ bs) ∗ (A.pool ∗ (stackAt s0.sp varintSlowStack ∗ R))))) by ac_rfl]
      exact hw1
    have hkf2 := keepsFrozen_write64_of_block (IsBlock.pointsTo64 _ _) hw1'
      (BitVec.ofNat 64 (bs.length - k))
    have hw2 := (IsBlock.pointsTo64 _ _).write64 hw1' (BitVec.ofNat 64 (bs.length - k))
    refine ⟨hkf1.trans hkf2, ?_⟩
    rw [show (slotA ↦₆₄ slot) ∗ ((slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
        (((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)) ∗
          ((ptr ↦ₛ bs) ∗ (A.pool ∗ (stackAt s0.sp varintSlowStack ∗ R))))) =
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)) ∗
        ((slotA ↦₆₄ slot) ∗ ((slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
          ((ptr ↦ₛ bs) ∗ (A.pool ∗ (stackAt s0.sp varintSlowStack ∗ R))))) by ac_rfl]
    exact hw2
  unfold decodeVarintSlowHook
  simp only [hx0, hslot, hptr, hlen, hvar]
  cases hvs : varintSlow bs with
  | some vk =>
    rcases vk with ⟨v, k⟩
    dsimp only
    rcases hadv k with ⟨hkf_k, hmem_k⟩
    refine ⟨hkf_k, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      by simp only [retHook, arm64_norm]; exact CallingConventionPreserved.rfl s0, ?_⟩⟩
    dsimp only [decodeVarintSlowSpec]
    simp only [hvs, retHook, State.setMem, arm64_norm, sepConj_assoc]
    rw [show (slotA ↦₆₄ slot) ∗ ((ptr ↦ₛ bs) ∗ (A.pool ∗ (stackAt s0.sp varintSlowStack ∗
        ((slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
          (((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)) ∗ R))))) =
      (slotA ↦₆₄ slot) ∗ ((slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
        (((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)) ∗
          ((ptr ↦ₛ bs) ∗ (A.pool ∗ (stackAt s0.sp varintSlowStack ∗ R))))) by ac_rfl]
    exact hmem_k
  | none =>
    dsimp only
    set k0 := min 10 bs.length
    set kindA := s0.sp - 64#64
    rcases hadv k0 with ⟨hkf_k0, hmem_k0⟩
    rw [stackAt_varintSlow_split s0.sp] at hmem_k0
    have hmem_kind :
        ((s0.mem.write64 slot (ptr + BitVec.ofNat 64 k0)).write64 (slot + 8#64)
          (BitVec.ofNat 64 (bs.length - k0))) ⊨
        memRegion kindA 8 ∗
          (memRegion (kindA + 8#64) 40 ∗ (A.pool ∗ (stackAt kindA decodeErrorHookStack ∗
            (memRegion (kindA + 48#64) 16 ∗ ((slotA ↦₆₄ slot) ∗
              ((slot ↦₆₄ (ptr + BitVec.ofNat 64 k0)) ∗
                (((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k0)) ∗
                  ((ptr ↦ₛ bs) ∗ R)))))))) := by
      rw [show memRegion kindA 8 ∗
          (memRegion (kindA + 8#64) 40 ∗ (A.pool ∗ (stackAt kindA decodeErrorHookStack ∗
            (memRegion (kindA + 48#64) 16 ∗ ((slotA ↦₆₄ slot) ∗
              ((slot ↦₆₄ (ptr + BitVec.ofNat 64 k0)) ∗
                (((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k0)) ∗
                  ((ptr ↦ₛ bs) ∗ R)))))))) =
        (slotA ↦₆₄ slot) ∗ ((slot ↦₆₄ (ptr + BitVec.ofNat 64 k0)) ∗
          (((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k0)) ∗
            ((ptr ↦ₛ bs) ∗ (A.pool ∗
              ((stackAt kindA decodeErrorHookStack ∗
                (memRegion kindA 8 ∗
                  (memRegion (kindA + 8#64) 40 ∗
                    memRegion (kindA + 48#64) 16))) ∗ R))))) by ac_rfl]
      exact hmem_k0
    have hkf_w := keepsFrozen_write64_of_block (IsBlock.memRegion kindA 8) hmem_kind
      invalidVarintWord
    have hw_kind := (IsBlock.memRegion kindA 8).write64 hmem_kind invalidVarintWord
    let R_frame : SepProp :=
      memRegion (kindA + 48#64) 16 ∗ ((slotA ↦₆₄ slot) ∗
        ((slot ↦₆₄ (ptr + BitVec.ofNat 64 k0)) ∗
          (((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k0)) ∗
            ((ptr ↦ₛ bs) ∗ R))))
    set m1 := ((s0.mem.write64 slot (ptr + BitVec.ofNat 64 k0)).write64 (slot + 8#64)
      (BitVec.ofNat 64 (bs.length - k0))).write64 kindA invalidVarintWord
    set s1 : State := { s0 with sp := kindA, mem := m1 }
    set s1' : State := s1.writeReg64 .x0 kindA
    have hs1'_run : s1'.status = .Running := hrun
    have hs1'_sp : s1'.spAligned = true := s0.spAligned_sub 64#64 hsp
    have hs1'_x0 : s1'.readReg64 .x0 = kindA := rfl
    have hs1'_pre : s1'.mem ⊨ (decodeErrorFromSpec A).pre (kindA, invalidVarintWord) s1' ∗ R_frame := by
      dsimp only [decodeErrorFromSpec]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hs1'_x0, by decide⟩, hw_kind⟩
    rcases hFromOk (kindA, invalidVarintWord) R_frame s1' hs1'_run hs1'_pre hs1'_sp with
      ⟨hkf_from, hsym_from, hout⟩
    set s2 := fromHook s1'
    have hkf_s2 : s0.mem.KeepsFrozen s2.mem := hkf_k0.trans (hkf_w.trans hkf_from)
    rcases hout with ⟨⟨hs2_pc, hs2_sp, hs2_run⟩, hcc, hpost⟩ | ⟨hs2_pan, hpan⟩ | ⟨code, hs2_exit, hexit⟩ | ⟨hs2_oom, hoom⟩
    · simp only [hs2_run]
      have hcc' : CallingConventionPreserved s0
          ((({ s2 with sp := s0.sp }.writeReg64 .x1 (s2.readReg64 .x0)).writeReg64 .x0 1#64).setPC
            (s0.readReg64 .lr)) := by
        simp only [arm64_norm]
        rcases hcc with ⟨_, hx18, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
        exact ⟨rfl, hx18, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
      refine ⟨hkf_s2, hsym_from, Or.inl ⟨⟨rfl, rfl, rfl⟩, hcc', ?_⟩⟩
      dsimp only [decodeErrorFromSpec] at hpost
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨⟨hx0_ne, htr⟩, hpost_mem⟩
      have htr' : s2.trace = s0.trace := htr
      dsimp only [decodeVarintSlowSpec]
      rw [hvs]
      change s2.mem ⊨
        (⌜s2.trace = s0.trace⌝ ∗
          (slotA ↦₆₄ slot) ∗ (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt s0.sp varintSlowStack ∗
            ⌜(1#64 : BitVec 64) = 1#64 ∧ s2.readReg64 .x0 ≠ 0#64⌝ ∗
            decodeErrorAtStackLen A (s2.readReg64 .x0) 0 ∗
            (slot ↦₆₄ (ptr + BitVec.ofNat 64 k0)) ∗
            ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k0))) ∗ R
      simp only [sepConj_assoc, satisfies_pure_sepConj, true_and]
      refine ⟨htr', ?_⟩
      rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
        sepConj_pure_left_comm, satisfies_pure_sepConj]
      refine ⟨hx0_ne, ?_⟩
      have hpost_mem' : s2.mem ⊨
          (slotA ↦₆₄ slot) ∗ ((ptr ↦ₛ bs) ∗ (A.pool ∗
            ((stackAt kindA decodeErrorHookStack ∗
              (memRegion kindA 48 ∗ memRegion (kindA + 48#64) 16)) ∗
              (decodeErrorAtStackLen A (s2.readReg64 .x0) 0 ∗
                ((slot ↦₆₄ (ptr + BitVec.ofNat 64 k0)) ∗
                  (((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k0)) ∗ R)))))) := by
        rw [show (slotA ↦₆₄ slot) ∗ ((ptr ↦ₛ bs) ∗ (A.pool ∗
            ((stackAt kindA decodeErrorHookStack ∗
              (memRegion kindA 48 ∗ memRegion (kindA + 48#64) 16)) ∗
              (decodeErrorAtStackLen A (s2.readReg64 .x0) 0 ∗
                ((slot ↦₆₄ (ptr + BitVec.ofNat 64 k0)) ∗
                  (((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k0)) ∗ R)))))) =
          decodeErrorAtStackLen A (s2.readReg64 .x0) 0 ∗ (memRegion kindA 48 ∗
            (A.pool ∗ (stackAt kindA decodeErrorHookStack ∗
              (memRegion (kindA + 48#64) 16 ∗ ((slotA ↦₆₄ slot) ∗
                ((slot ↦₆₄ (ptr + BitVec.ofNat 64 k0)) ∗
                  (((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k0)) ∗
                    ((ptr ↦ₛ bs) ∗ R)))))))) by ac_rfl]
        exact hpost_mem
      rwa [stackAt_varintSlow_join s0.sp] at hpost_mem'
    · simp only [hs2_pan]
      refine ⟨hkf_s2, hsym_from, Or.inr (Or.inl ⟨hs2_pan, ?_⟩)⟩
      dsimp only [decodeErrorFromSpec] at hpan
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
      rcases hpan with ⟨halloc, hpan_mem⟩
      dsimp only [decodeVarintSlowSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨halloc, ?_⟩
      repeat rw [← sepConj_assoc] at hpan_mem
      exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hpan_mem
    · dsimp only [decodeErrorFromSpec] at hexit
      rw [satisfies_pure_sepConj] at hexit
      exact False.elim hexit.1
    · dsimp only [decodeErrorFromSpec] at hoom
      rw [satisfies_pure_sepConj] at hoom
      exact False.elim hoom.1

/-! ## `HookSat` transfer to `tripleRatchetExterns C ctl abs` -/

private theorem hookSat_tripleRatchetExterns_trap {α : Type} (C : Crypto)
    (abs : String → Option (State → State)) {sym : String} {spec : Spec α}
    (heq : trTrapExterns C abs sym = abs sym)
    (h : HookSat abs sym spec) :
    HookSat (trTrapExterns C abs) sym spec := by
  unfold HookSat at *; rwa [heq]

private theorem hookSat_tripleRatchetExterns {α : Type} (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) {sym : String} {spec : Spec α}
    (heq : tripleRatchetExterns C ctl abs sym = abs sym)
    (h : HookSat abs sym spec) :
    HookSat (tripleRatchetExterns C ctl abs) sym spec := by
  unfold HookSat at *; rwa [heq]

/-! ## `<stub>_ok_at` lemmas for concrete stubs -/

theorem shim_ok_at_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) sessionShimSpec :=
  hook_ok_at (hname := shimName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) ⟨_, rfl, sessionShim_hookOk⟩


theorem shim_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) sessionShimSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (shim_ok_at_trap b C abs name k hk)

theorem session_shim_ok_at_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) sessionShimSpec :=
  shim_ok_at_trap b C abs name k hk


theorem session_shim_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) sessionShimSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (session_shim_ok_at_trap b C abs name k hk)

theorem memcpy_ok_at_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) (name : String) (k : Nat) (hookStack : Nat := 4096)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (libcMemcpySpec hookStack) :=
  hook_ok_at (hname := memcpyName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) ⟨_, rfl, hookMemcpy_ok hookStack⟩

theorem memcpy_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) (k : Nat) (hookStack : Nat := 4096)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (libcMemcpySpec hookStack) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (memcpy_ok_at_trap b C abs name k hookStack hk)

theorem session_memcpy_ok_at_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) (name : String) (k : Nat) (hookStack : Nat := 4096)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (sessionMemcpySpec hookStack) :=
  hook_ok_at (hname := memcpyName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) ⟨_, rfl, hookMemcpy_trace_ok hookStack⟩

theorem session_memcpy_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) (k : Nat) (hookStack : Nat := 4096)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (sessionMemcpySpec hookStack) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (session_memcpy_ok_at_trap b C abs name k hookStack hk)

theorem memcpy_region_ok_at_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) memcpyRegionSpec :=
  hook_ok_at (hname := memcpyName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) ⟨_, rfl, hookMemcpy_region_ok⟩


theorem memcpy_region_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) memcpyRegionSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (memcpy_region_ok_at_trap b C abs name k hk)

theorem session_memcpy_region_ok_at_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) sessionMemcpyRegionSpec :=
  hook_ok_at (hname := memcpyName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) ⟨_, rfl, hookMemcpy_region_trace_ok⟩


theorem session_memcpy_region_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) sessionMemcpyRegionSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (session_memcpy_region_ok_at_trap b C abs name k hk)

theorem memmove_ok_at_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) (name : String) (k : Nat) (hookStack : Nat := 4096)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memmoveName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (libcMemmoveSpec hookStack) :=
  hook_ok_at (hname := memmoveName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) ⟨_, rfl, hookMemmove_ok hookStack⟩

theorem memmove_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) (k : Nat) (hookStack : Nat := 4096)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memmoveName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (libcMemmoveSpec hookStack) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (memmove_ok_at_trap b C abs name k hookStack hk)

theorem session_memmove_ok_at_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) (name : String) (k : Nat) (hookStack : Nat := 4096)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memmoveName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (sessionMemmoveSpec hookStack) :=
  hook_ok_at (hname := memmoveName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) ⟨_, rfl, hookMemmove_trace_ok hookStack⟩

theorem session_memmove_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) (k : Nat) (hookStack : Nat := 4096)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memmoveName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (sessionMemmoveSpec hookStack) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (session_memmove_ok_at_trap b C abs name k hookStack hk)

theorem memset_ok_at_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) (name : String) (k : Nat) (hookStack : Nat := 4096)
    (hstack : 0 < hookStack := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (libcMemsetSpec hookStack) :=
  hook_ok_at (hname := memsetName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) ⟨_, rfl, hookMemset_ok hookStack hstack⟩

theorem memset_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) (k : Nat) (hookStack : Nat := 4096)
    (hstack : 0 < hookStack := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (libcMemsetSpec hookStack) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (memset_ok_at_trap b C abs name k hookStack hstack hk)

theorem session_memset_ok_at_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) (name : String) (k : Nat) (hookStack : Nat := 4096)
    (hstack : 0 < hookStack := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (sessionMemsetSpec hookStack) :=
  hook_ok_at (hname := memsetName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) ⟨_, rfl, hookMemset_trace_ok hookStack hstack⟩

theorem session_memset_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) (k : Nat) (hookStack : Nat := 4096)
    (hstack : 0 < hookStack := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (sessionMemsetSpec hookStack) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (session_memset_ok_at_trap b C abs name k hookStack hstack hk)

theorem memset_region_ok_at_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) memsetRegionSpec :=
  hook_ok_at (hname := memsetName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) ⟨_, rfl, hookMemset_region_ok⟩


theorem memset_region_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) memsetRegionSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (memset_region_ok_at_trap b C abs name k hk)

theorem session_memset_region_ok_at_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) sessionMemsetRegionSpec :=
  hook_ok_at (hname := memsetName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) ⟨_, rfl, hookMemset_region_trace_ok⟩


theorem session_memset_region_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) sessionMemsetRegionSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (session_memset_region_ok_at_trap b C abs name k hk)

theorem black_box_ok_at_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff blackBoxName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) blackBoxSpec :=
  hook_ok_at (hname := blackBoxName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) ⟨_, rfl, blackBoxHook_ok⟩


theorem black_box_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff blackBoxName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) blackBoxSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (black_box_ok_at_trap b C abs name k hk)

theorem compress256_ok_at_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff compress256Name) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (compress256Spec C.F) :=
  hook_ok_at (hname := compress256Name) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) ⟨_, rfl, compress256Hook_ok C.F⟩


theorem compress256_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff compress256Name) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (compress256Spec C.F) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (compress256_ok_at_trap b C abs name k hk)

theorem dh_ok_at_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff dhName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (diffieHellmanSpec C.X) :=
  hook_ok_at (hname := dhName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) ⟨_, rfl, diffieHellmanHook_ok C.X⟩


theorem dh_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff dhName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (diffieHellmanSpec C.X) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (dh_ok_at_trap b C abs name k hk)

theorem pub_from_secret_ok_at_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff pubFromSecretName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (pubFromSecretSpec C.pubKey) :=
  hook_ok_at (hname := pubFromSecretName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) ⟨_, rfl, pubFromSecretHook_ok C.pubKey⟩


theorem pub_from_secret_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff pubFromSecretName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (pubFromSecretSpec C.pubKey) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (pub_from_secret_ok_at_trap b C abs name k hk)

theorem static_drop_ok_at_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff staticDropName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) zeroizeSecretSpec :=
  hook_ok_at (hname := staticDropName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) ⟨_, rfl, zeroizeSecretHook_ok⟩


theorem static_drop_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff staticDropName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) zeroizeSecretSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (static_drop_ok_at_trap b C abs name k hk)

theorem shared_drop_ok_at_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff sharedDropName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) zeroizeSecretSpec :=
  hook_ok_at (hname := sharedDropName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) ⟨_, rfl, zeroizeSecretHook_ok⟩


theorem shared_drop_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff sharedDropName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) zeroizeSecretSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (shared_drop_ok_at_trap b C abs name k hk)

theorem rng_fill_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff rngFillName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (rngFillSpec ctl) :=
  hook_ok_at (hname := rngFillName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) ⟨_, rfl, rngFillHook_ok ctl⟩


/-! ## Call-site lemmas for in-image Prost and SPQR callees -/

theorem decode_varint_slow_ok_at_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff varintSlowName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (decodeVarintSlowSpec A) := by
  have h := decodeVarintSlow_ok_trap b C A abs hA
  rwa [← Program.fnAddr_rel rfl rfl hk]


theorem decode_varint_slow_ok_at (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff varintSlowName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (decodeVarintSlowSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (decode_varint_slow_ok_at_trap b C A abs hA name k hk)

theorem decode_error_from_ok_at_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff decodeErrorFromName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (decodeErrorFromSpec A) := by
  have h := decodeErrorFrom_ok_trap b C A abs hA
  rwa [← Program.fnAddr_rel rfl rfl hk]


theorem decode_error_from_ok_at (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff decodeErrorFromName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (decodeErrorFromSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (decode_error_from_ok_at_trap b C A abs hA name k hk)

theorem decode_error_push_ok_at_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff decodeErrorPushName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (decodeErrorPushSpec A) := by
  have h := decodeErrorPush_ok_trap b C A abs hA
  rwa [← Program.fnAddr_rel rfl rfl hk]


theorem decode_error_push_ok_at (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff decodeErrorPushName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (decodeErrorPushSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (decode_error_push_ok_at_trap b C A abs hA name k hk)

theorem decode_state_empty_ok_at_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff decodeStateName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (decodeStateEmptySpec A) := by
  have h := decodeStateEmpty_ok_trap b C A abs
  rwa [← Program.fnAddr_rel rfl rfl hk]


theorem decode_state_empty_ok_at (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff decodeStateName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (decodeStateEmptySpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (decode_state_empty_ok_at_trap b C A abs name k hk)

/-! ## `<stub>_ok_at` lemmas for abstract stubs (`AllocHooks` / `TripleRatchetHooks`) -/

theorem alloc_ok_at_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) :=
  hook_ok_at (hname := allocName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel)
    (hookSat_tripleRatchetExterns_trap C abs rfl hA.alloc)


theorem alloc_ok_at (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (alloc_ok_at_trap b C A abs hA name k hk)

theorem dealloc_ok_at_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff deallocName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (rustDeallocSpec A) :=
  hook_ok_at (hname := deallocName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel)
    (hookSat_tripleRatchetExterns_trap C abs rfl hA.dealloc)


theorem dealloc_ok_at (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff deallocName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (rustDeallocSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (dealloc_ok_at_trap b C A abs hA name k hk)

theorem realloc_ok_at_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff reallocName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (rustReallocSpec A) :=
  hook_ok_at (hname := reallocName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel)
    (hookSat_tripleRatchetExterns_trap C abs rfl hA.realloc)


theorem realloc_ok_at (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff reallocName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (rustReallocSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (realloc_ok_at_trap b C A abs hA name k hk)

theorem alloc_zeroed_ok_at_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hZero : HookSat abs allocZeroedName (rustAllocZeroedSpec A)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocZeroedName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (rustAllocZeroedSpec A) :=
  hook_ok_at (hname := allocZeroedName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel)
    (hookSat_tripleRatchetExterns_trap C abs rfl hZero)


theorem alloc_zeroed_ok_at (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hZero : HookSat abs allocZeroedName (rustAllocZeroedSpec A)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocZeroedName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (rustAllocZeroedSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (alloc_zeroed_ok_at_trap b C A abs hZero name k hk)

theorem aes_enc_ok_at_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hEnc : HookSat abs aesEncName (aesEncSpec C.E A)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff aesEncName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (aesEncSpec C.E A) :=
  hook_ok_at (hname := aesEncName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel)
    (hookSat_tripleRatchetExterns_trap C abs rfl hEnc)


theorem aes_enc_ok_at (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hEnc : HookSat abs aesEncName (aesEncSpec C.E A)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff aesEncName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (aesEncSpec C.E A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (aes_enc_ok_at_trap b C A abs hEnc name k hk)

theorem aes_dec_ok_at_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hDec : HookSat abs aesDecName (aesDecSpec C.D A)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff aesDecName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (aesDecSpec C.D A) :=
  hook_ok_at (hname := aesDecName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel)
    (hookSat_tripleRatchetExterns_trap C abs rfl hDec)


theorem aes_dec_ok_at (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hDec : HookSat abs aesDecName (aesDecSpec C.D A)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff aesDecName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (aesDecSpec C.D A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (aes_dec_ok_at_trap b C A abs hDec name k hk)

theorem format_inner_ok_at_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hFmt : HookSat abs formatInnerName (formatInnerSpec A)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff formatInnerName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (formatInnerSpec A) :=
  hook_ok_at (hname := formatInnerName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel)
    (hookSat_tripleRatchetExterns_trap C abs rfl hFmt)


theorem format_inner_ok_at (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hFmt : HookSat abs formatInnerName (formatInnerSpec A)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff formatInnerName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (formatInnerSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (format_inner_ok_at_trap b C A abs hFmt name k hk)

/-! ## `panic_at_*` lemmas for panic stubs -/

theorem panic_at_handle_error_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff handleErrorName) :
    (trTrapProgAt b C abs).externAt?
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) = some Rust.panicked :=
  panic_at_panicSymbol (hname := handleErrorName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel)


theorem panic_at_handle_error (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff handleErrorName) :
    (tripleRatchetProgAt b C ctl abs).externAt?
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) = some Rust.panicked := by
  have h := panic_at_handle_error_trap b C abs name k hk
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  rcases (trapsOnly_trTrap_kit b C ctl abs).hook ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) with
    heq | ⟨f, hf, ht⟩
  · exact heq.symm.trans h
  · cases h.symm.trans hf
    exact False.elim (ht default (ProofLib.Variant.OutcomeStatus.of_panicked rfl))

theorem panic_at_handle_alloc_error_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff handleAllocErrorName) :
    (trTrapProgAt b C abs).externAt?
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) = some Rust.panicked :=
  panic_at_panicSymbol (hname := handleAllocErrorName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel)


theorem panic_at_handle_alloc_error (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff handleAllocErrorName) :
    (tripleRatchetProgAt b C ctl abs).externAt?
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) = some Rust.panicked := by
  have h := panic_at_handle_alloc_error_trap b C abs name k hk
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  rcases (trapsOnly_trTrap_kit b C ctl abs).hook ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) with
    heq | ⟨f, hf, ht⟩
  · exact heq.symm.trans h
  · cases h.symm.trans hf
    exact False.elim (ht default (ProofLib.Variant.OutcomeStatus.of_panicked rfl))

theorem panic_at_vec_remove_assert_failed_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff vecRemoveAssertFailedName) :
    (trTrapProgAt b C abs).externAt?
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) = some Rust.panicked :=
  panic_at_hook (hname := vecRemoveAssertFailedName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) rfl


theorem panic_at_vec_remove_assert_failed (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff vecRemoveAssertFailedName) :
    (tripleRatchetProgAt b C ctl abs).externAt?
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) = some Rust.panicked := by
  have h := panic_at_vec_remove_assert_failed_trap b C abs name k hk
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  rcases (trapsOnly_trTrap_kit b C ctl abs).hook ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) with
    heq | ⟨f, hf, ht⟩
  · exact heq.symm.trans h
  · cases h.symm.trans hf
    exact False.elim (ht default (ProofLib.Variant.OutcomeStatus.of_panicked rfl))

theorem panic_at_sym_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (name sym : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff sym)
    (hs : libsignalSessionCode.fnOff sym < 2 ^ 64 := by simp only [arm64_norm])
    (hstub : ∀ H, (libsignalSessionCode.rebase 0 H).hookAtOff? (libsignalSessionCode.fnOff sym) = H sym :=
      by intro _; simp only [arm64_norm])
    (hp : Rust.isPanicSymbol sym = true := by rfl) :
    (trTrapProgAt b C abs).externAt?
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) = some Rust.panicked :=
  panic_at_panicSymbol (hname := sym) rfl hk hs hstub hp

theorem panic_at_sym (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (name sym : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff sym)
    (hs : libsignalSessionCode.fnOff sym < 2 ^ 64 := by simp only [arm64_norm])
    (hstub : ∀ H, (libsignalSessionCode.rebase 0 H).hookAtOff? (libsignalSessionCode.fnOff sym) = H sym :=
      by intro _; simp only [arm64_norm])
    (hp : Rust.isPanicSymbol sym = true := by rfl) :
    (tripleRatchetProgAt b C ctl abs).externAt?
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) = some Rust.panicked := by
  have h := panic_at_sym_trap b C abs name sym k hk hs hstub hp
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  rcases (trapsOnly_trTrap_kit b C ctl abs).hook ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) with
    heq | ⟨f, hf, ht⟩
  · exact heq.symm.trans h
  · cases h.symm.trans hf
    exact False.elim (ht default (ProofLib.Variant.OutcomeStatus.of_panicked rfl))

end CryptoVerification.LibsignalTripleRatchet
