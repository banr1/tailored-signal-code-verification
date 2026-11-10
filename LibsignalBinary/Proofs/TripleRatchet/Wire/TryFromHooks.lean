/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefs
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.Defs
import GeneratedLean.LibsignalSession -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import ProofLib.SepLogic.WPp

/-!
# `decode_varint_slow` hook proof and full `PublicKey::deserialize` spec/proof
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Wire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSession.FindReceiverChainIndex

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## `decode_varint_slow::<&mut &[u8]>` hook proof -/

theorem varintSlow_take_min10 (bs : List (BitVec 8)) :
    varintSlow (bs.take (min 10 bs.length)) = varintSlow bs := by
  simp only [varintSlow, List.take_take]
  have hmin : min 10 (min 10 bs.length) = min 10 bs.length := by omega
  have h10 : (bs.take (min 10 bs.length)) = bs.take 10 := by
    rw [List.take_eq_take_iff]
    omega
  rw [hmin, h10]

theorem stackAt_varintSlow_split (sp : BitVec 64) :
    stackAt sp varintSlowStack =
      stackAt (sp - 64#64) decodeErrorHookStack ∗
      (∃∗ w0 : BitVec 64, (sp - 64#64) ↦₆₄ w0) ∗
      memRegion (sp - 64#64 + 8#64) 40 ∗
      memRegion (sp - 64#64 + 48#64) 16 := by
  have h1 : stackAt sp varintSlowStack =
      stackAt (sp - 64#64) decodeErrorHookStack ∗ memRegion (sp - 64#64) 64 := by
    simp only [stackAt, varintSlowStack, decodeErrorHookStack, allocHookStack]
    have e1 : sp - 8256#64 = sp - 64#64 - 8192#64 := by bv_omega
    have e2 : sp - 64#64 = sp - 64#64 - 8192#64 + 8192#64 := by bv_omega
    rw [e1, memRegion_split' (n := 8192) (k := 64) rfl e2 (by decide)]
  have h2 : memRegion (sp - 64#64) 64 =
      (∃∗ w0 : BitVec 64, (sp - 64#64) ↦₆₄ w0) ∗
      memRegion (sp - 64#64 + 8#64) 40 ∗
      memRegion (sp - 64#64 + 48#64) 16 := by
    rw [memRegion_split' rfl rfl (n := 8) (k := 56) (by decide),
      memRegion_eight,
      memRegion_split' rfl (by bv_omega) (n := 40) (k := 16) (b' := sp - 64#64 + 48#64) (by decide)]
  rw [h1, h2]

theorem stackAt_varintSlow_fold (sp : BitVec 64) :
    stackAt (sp - 64#64) decodeErrorHookStack ∗
      (memRegion (sp - 64#64) 48 ∗
      memRegion (sp - 64#64 + 48#64) 16) =
    stackAt sp varintSlowStack := by
  have h1 : memRegion (sp - 64#64) 48 ∗ memRegion (sp - 64#64 + 48#64) 16 =
      memRegion (sp - 64#64) 64 :=
    (memRegion_split' rfl rfl (n := 48) (k := 16) (by decide)).symm
  rw [h1]
  simp only [stackAt, varintSlowStack, decodeErrorHookStack, allocHookStack]
  have e1 : sp - 8256#64 = sp - 64#64 - 8192#64 := by bv_omega
  have e2 : sp - 64#64 = sp - 64#64 - 8192#64 + 8192#64 := by bv_omega
  rw [e1, memRegion_split' (n := 8192) (k := 64) rfl e2 (by decide)]

local instance : Std.Associative SepProp.sepConj := ⟨sepConj_assoc⟩
local instance : Std.Commutative SepProp.sepConj := ⟨sepConj_comm⟩

theorem keepsFrozen_write64_of_pointsTo64 {m : Memory} {a v₀ : BitVec 64} {R : SepProp}
    (v : BitVec 64) (h : m ⊨ (a ↦₆₄ v₀) ∗ R) :
    m.KeepsFrozen (m.write64 a v) :=
  Memory.keepsFrozen_write64 ((IsBlock.pointsTo64 a v₀).canWrite (by decide) h) v

theorem satisfies_write64_of_pointsTo64 {m : Memory} {a v₀ : BitVec 64} {R : SepProp}
    (v : BitVec 64) (h : m ⊨ (a ↦₆₄ v₀) ∗ R) :
    m.write64 a v ⊨ (a ↦₆₄ v) ∗ R :=
  IsBlock.write64 (IsBlock.pointsTo64 a v₀) h v

theorem varintSlow_ok_ret_regs (s0 : State) (m' : Memory) (v : BitVec 64) :
    let sf := retHook (fun s => ((s.setMem m').writeReg64 .x0 0#64).writeReg64 .x1 v) s0
    sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v ∧ sf.trace = s0.trace :=
  ⟨rfl, rfl, rfl⟩

theorem decodeVarintSlow_hookOk {A : RustAlloc} {fromHook : State → State}
    (hFrom : HookOk fromHook (decodeErrorFromSpec A)) :
    HookOk (decodeVarintSlowHook fromHook) (decodeVarintSlowSpec A) := by
  intro ⟨slotA, slot, ptr, bs⟩ R s0 hrun hpre hsp
  simp only [decodeVarintSlowSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hlen_lt⟩, hmem⟩
  have hread_slotA := (IsBlock.pointsTo64 slotA slot).read hmem
  have hmem_slot : s0.mem ⊨ (slot ↦₆₄ ptr) ∗
      ((slotA ↦₆₄ slot) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt s0.sp varintSlowStack ∗ R) := by
    ac_nf at hmem ⊢
  have hread_slot := (IsBlock.pointsTo64 slot ptr).read hmem_slot
  have hmem_len : s0.mem ⊨ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((slot ↦₆₄ ptr) ∗ (slotA ↦₆₄ slot) ∗
        (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt s0.sp varintSlowStack ∗ R) := by
    ac_nf at hmem ⊢
  have hread_len := (IsBlock.pointsTo64 (slot + 8#64) (BitVec.ofNat 64 bs.length)).read hmem_len
  have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen_lt]
  have hbs_split : (ptr ↦ₛ bs) =
      (ptr ↦ₛ bs.take (min 10 bs.length)) ∗
      ((ptr + BitVec.ofNat 64 (bs.take (min 10 bs.length)).length) ↦ₛ bs.drop (min 10 bs.length)) := by
    conv_lhs => rw [← List.take_append_drop (min 10 bs.length) bs]
    exact pointsToBytes_append ptr _ _
  have hmem_bs : s0.mem ⊨ (ptr ↦ₛ bs.take (min 10 bs.length)) ∗
      (((ptr + BitVec.ofNat 64 (bs.take (min 10 bs.length)).length) ↦ₛ bs.drop (min 10 bs.length)) ∗
        (slotA ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.pool ∗ stackAt s0.sp varintSlowStack ∗ R) := by
    have hmem' := hmem
    rw [hbs_split] at hmem'
    ac_nf at hmem' ⊢
  obtain ⟨_, hread_bs⟩ := (IsBlock.pointsToBytes ptr (bs.take (min 10 bs.length))).read hmem_bs
  have htake_len : (bs.take (min 10 bs.length)).length = min 10 bs.length := by simp
  rw [htake_len] at hread_bs
  dsimp only [decodeVarintSlowHook]
  rw [hx0, hread_slotA, hread_slot, hread_len, hlen_toNat, hread_bs, varintSlow_take_min10]
  cases hvs : varintSlow bs with
  | some vk =>
    rcases vk with ⟨v, k⟩
    dsimp only
    have hkf1 := keepsFrozen_write64_of_pointsTo64 (ptr + BitVec.ofNat 64 k) hmem_slot
    have hw1 := satisfies_write64_of_pointsTo64 (ptr + BitVec.ofNat 64 k) hmem_slot
    have hmem1 : (s0.mem.write64 slot (ptr + BitVec.ofNat 64 k)) ⊨
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗ (slotA ↦₆₄ slot) ∗
          (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt s0.sp varintSlowStack ∗ R) := by
      ac_nf at hw1 ⊢
    have hkf2 := hkf1.trans (keepsFrozen_write64_of_pointsTo64 (BitVec.ofNat 64 (bs.length - k)) hmem1)
    have hw2 := satisfies_write64_of_pointsTo64 (BitVec.ofNat 64 (bs.length - k)) hmem1
    refine ⟨hkf2, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    have ⟨hr0, hr1, htr⟩ := varintSlow_ok_ret_regs s0
      ((s0.mem.write64 slot (ptr + BitVec.ofNat 64 k)).write64
        (slot + 8#64) (BitVec.ofNat 64 (bs.length - k))) v
    dsimp only [decodeVarintSlowSpec]
    rw [hvs, hr0, hr1, htr]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨rfl, ?_⟩
    have hw2' : (retHook
        (fun s =>
          ((s.setMem
                    ((s0.mem.write64 slot (ptr + BitVec.ofNat 64 k)).write64 (slot + 8#64)
                      (BitVec.ofNat 64 (bs.length - k)))).writeReg64
                Reg.x0 0#64).writeReg64
            Reg.x1 v)
        s0).mem ⊨
        (slotA ↦₆₄ slot) ∗ (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt s0.sp varintSlowStack ∗
        (slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)) ∗ R := by
      change ((s0.mem.write64 slot (ptr + BitVec.ofNat 64 k)).write64
        (slot + 8#64) (BitVec.ofNat 64 (bs.length - k))) ⊨ _
      ac_nf at hw2 ⊢
    simp only [sepConj_assoc, sepConj_pure_left_comm, satisfies_pure_sepConj, true_and]
    exact hw2'
  | none =>
    dsimp only
    set k := min 10 bs.length
    set kindA := s0.sp - 64#64
    have hmem_stk := hmem
    rw [stackAt_varintSlow_split s0.sp] at hmem_stk
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      satisfies_sepExists] at hmem_stk
    rcases hmem_stk with ⟨w0, hmem_stk⟩
    have hmem_slot1 : s0.mem ⊨ (slot ↦₆₄ ptr) ∗
        (((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (kindA ↦₆₄ w0) ∗
          (slotA ↦₆₄ slot) ∗ (ptr ↦ₛ bs) ∗ A.pool ∗
          stackAt kindA decodeErrorHookStack ∗
          memRegion (kindA + 8#64) 40 ∗ memRegion (kindA + 48#64) 16 ∗ R) := by
      dsimp only [kindA]; ac_nf at hmem_stk ⊢
    have hkf1 := keepsFrozen_write64_of_pointsTo64 (ptr + BitVec.ofNat 64 k) hmem_slot1
    have hw1 := satisfies_write64_of_pointsTo64 (ptr + BitVec.ofNat 64 k) hmem_slot1
    have hmem_slot2 : (s0.mem.write64 slot (ptr + BitVec.ofNat 64 k)) ⊨
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((kindA ↦₆₄ w0) ∗ (slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
          (slotA ↦₆₄ slot) ∗ (ptr ↦ₛ bs) ∗ A.pool ∗
          stackAt kindA decodeErrorHookStack ∗
          memRegion (kindA + 8#64) 40 ∗ memRegion (kindA + 48#64) 16 ∗ R) := by
      ac_nf at hw1 ⊢
    have hkf2 := hkf1.trans (keepsFrozen_write64_of_pointsTo64 (BitVec.ofNat 64 (bs.length - k)) hmem_slot2)
    have hw2 := satisfies_write64_of_pointsTo64 (BitVec.ofNat 64 (bs.length - k)) hmem_slot2
    have hmem_kind : ((s0.mem.write64 slot (ptr + BitVec.ofNat 64 k)).write64
        (slot + 8#64) (BitVec.ofNat 64 (bs.length - k))) ⊨
        (kindA ↦₆₄ w0) ∗
        (((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)) ∗
          (slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
          (slotA ↦₆₄ slot) ∗ (ptr ↦ₛ bs) ∗ A.pool ∗
          stackAt kindA decodeErrorHookStack ∗
          memRegion (kindA + 8#64) 40 ∗ memRegion (kindA + 48#64) 16 ∗ R) := by
      ac_nf at hw2 ⊢
    have hkf3 := hkf2.trans (keepsFrozen_write64_of_pointsTo64 invalidVarintWord hmem_kind)
    have hw3 := satisfies_write64_of_pointsTo64 invalidVarintWord hmem_kind
    set s1 : State :=
      ({ s0 with
          sp := kindA,
          mem := ((s0.mem.write64 slot (ptr + BitVec.ofNat 64 k)).write64
            (slot + 8#64) (BitVec.ofNat 64 (bs.length - k))).write64 kindA invalidVarintWord }).writeReg64
        .x0 kindA
    have hs1_run : s1.status = .Running := hrun
    have hs1_sp : s1.spAligned = true := s0.spAligned_sub 64#64 hsp
    have hkind_noHeap : KindNoHeap invalidVarintWord := by decide +kernel
    set R_from : SepProp :=
      (slotA ↦₆₄ slot) ∗ (ptr ↦ₛ bs) ∗
      (slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)) ∗
      memRegion (kindA + 48#64) 16 ∗ R
    have hs1_x0 : s1.readReg64 .x0 = kindA := rfl
    have hs1_sp_eq : s1.sp = kindA := rfl
    have hs1_tr_eq : s1.trace = s0.trace := rfl
    have hw3' : s1.mem ⊨
        (kindA ↦₆₄ invalidVarintWord) ∗ memRegion (kindA + 8#64) 40 ∗
        A.pool ∗ stackAt kindA decodeErrorHookStack ∗ R_from := by
      change ((s0.mem.write64 slot (ptr + BitVec.ofNat 64 k)).write64
        (slot + 8#64) (BitVec.ofNat 64 (bs.length - k))).write64 kindA invalidVarintWord ⊨ _
      dsimp only [R_from]
      ac_nf at hw3 ⊢
    have hs1_pre : s1.mem ⊨ (decodeErrorFromSpec A).pre (kindA, invalidVarintWord) s1 ∗ R_from := by
      simp only [decodeErrorFromSpec, hs1_sp_eq, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hs1_x0, hkind_noHeap⟩, hw3'⟩
    have ⟨hkf_s2, hsym_s2, hout⟩ := hFrom (kindA, invalidVarintWord) R_from s1 hs1_run hs1_pre hs1_sp
    set s2 := fromHook s1
    rcases hout with ⟨⟨_, _, hst_s2⟩, hcs_s2, hpost_s2⟩ | ⟨hpan_s2, hpost_s2⟩ | ⟨code, hex_s2, hpost_s2⟩ | ⟨hoom_s2, hpost_s2⟩
    · rw [hst_s2]
      dsimp only
      rcases hcs_s2 with ⟨_, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hvregs⟩
      refine ⟨hkf3.trans hkf_s2, hsym_s2,
        Or.inl ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hvregs⟩, ?_⟩⟩
      simp only [decodeErrorFromSpec, hs1_sp_eq, hs1_tr_eq, sepConj_assoc, satisfies_pure_sepConj] at hpost_s2
      rcases hpost_s2 with ⟨⟨hx0_ne, htr⟩, hmem_s2⟩
      dsimp only [decodeVarintSlowSpec]
      rw [hvs]
      change s2.mem ⊨
        (⌜s2.trace = s0.trace⌝ ∗ (slotA ↦₆₄ slot) ∗ (ptr ↦ₛ bs) ∗ A.pool ∗
          stackAt s0.sp varintSlowStack ∗
          (⌜1#64 = 1#64 ∧ s2.readReg64 .x0 ≠ 0#64⌝ ∗
            decodeErrorAtStackLen A (s2.readReg64 .x0) 0 ∗
            (slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
            ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)))) ∗ R
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨htr, ?_⟩
      simp only [sepConj_assoc, sepConj_pure_left_comm, satisfies_pure_sepConj, true_and]
      refine ⟨hx0_ne, ?_⟩
      have hmem_s2' : s2.mem ⊨
          (slotA ↦₆₄ slot) ∗ (ptr ↦ₛ bs) ∗ A.pool ∗
          (stackAt kindA decodeErrorHookStack ∗
            (memRegion kindA 48 ∗ memRegion (kindA + 48#64) 16)) ∗
          decodeErrorAtStackLen A (s2.readReg64 .x0) 0 ∗
          (slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
          ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)) ∗ R := by
        dsimp only [R_from] at hmem_s2
        ac_nf at hmem_s2 ⊢
      dsimp only [kindA] at hmem_s2'
      rw [stackAt_varintSlow_fold s0.sp] at hmem_s2'
      dsimp only [k] at hmem_s2' ⊢
      ac_nf at hmem_s2' ⊢
    · rw [hpan_s2]
      dsimp only
      refine ⟨hkf3.trans hkf_s2, hsym_s2, Or.inr (Or.inl ⟨hpan_s2, ?_⟩)⟩
      have hpan_eq :
          (decodeErrorFromSpec A).onPanic (kindA, invalidVarintWord) s1 s2 =
          (decodeVarintSlowSpec A).onPanic (slotA, slot, ptr, bs) s0 s2 := rfl
      rw [hpan_eq] at hpost_s2
      have hpost_s2' : s2.mem ⊨
          ((⌜allocFailedIn s0 s2 ∧ s0.trace <+: s2.trace⌝ ∗ anyHeap) ∗
            ((slotA ↦₆₄ slot) ∗ (ptr ↦ₛ bs) ∗
              (slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
              ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)) ∗
              memRegion (kindA + 48#64) 16)) ∗ R := by
        dsimp only [decodeVarintSlowSpec, R_from] at hpost_s2
        ac_nf at hpost_s2 ⊢
      exact Satisfies.mono (sepConj_mono_left (by
        rw [sepConj_assoc]
        exact sepConj_mono_right (entails_anyHeap _))) hpost_s2'
    · exfalso
      exact not_satisfies_false_sepConj hpost_s2
    · exfalso
      exact not_satisfies_false_sepConj hpost_s2

/-- `decode_varint_slow::<&mut &[u8]>` at call distance `k` from `name` on `libsignalSessionCode.rebase b H`
from a contract-backed `subroutine_ok` hypothesis. -/
theorem decodeVarintSlow_ok_at_of_contract {A : RustAlloc}
    {b : BitVec 64} {H : String → Option (State → State)}
    (hSlow : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr varintSlowName)
      (decodeVarintSlowSpec A))
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff varintSlowName := by fnoff_eq) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr name + BitVec.ofNat 64 k)
      (decodeVarintSlowSpec A) := by
  rw [← Program.fnAddr_rel rfl rfl hk]
  exact hSlow

/-- `decode_varint_slow::<&mut &[u8]>` at call distance `k` from `name` on `tripleRatchetProgAtW`. -/
theorem decodeVarintSlow_ok_at_tripleRatchet {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hS : TripleRatchetHooksW img C A S abs)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff varintSlowName := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      ((decodeVarintSlowSpecWithStack A (64 + 2 * extHookStack)).inImage img) := by
  rw [← Program.fnAddr_rel rfl rfl hk]
  exact hS.decodeVarintSlow

/-! ## Full `PublicKey::deserialize` (`0x3db50`) specification and proof -/

theorem pointsTo64_zero_byte0 (a : BitVec 64) :
    (a ↦₆₄ 0#64) = (a ↦₈ 0#8) ∗ ((a + 1#64) ↦ₛ List.replicate 7 0#8) := by
  rw [pointsTo64_eq_pointsToBytes]
  simp only [unpack64, List.replicate, pointsToBytes_cons, pointsToBytes_nil,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
  rfl

theorem pointsTo64_two_byte0 (a : BitVec 64) :
    (a ↦₆₄ 2#64) = (a ↦₈ 2#8) ∗ ((a + 1#64) ↦ₛ List.replicate 7 0#8) := by
  rw [pointsTo64_eq_pointsToBytes]
  simp only [unpack64, List.replicate, pointsToBytes_cons, pointsToBytes_nil,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
  rfl

/-- The 33-byte result written at `sret` by `PublicKey::deserialize` (`0x3db50`). -/
def deserializeResult33At (sret : BitVec 64) : Except SignalProtocolError PublicKey → SepProp
  | .ok pk => (sret ↦₈ 0#8) ∗ ((sret + 1#64) ↦ₛ pk.bytes.toList)
  | .error .noKeyTypeIdentifier =>
    (sret ↦₈ 1#8) ∗ memRegion (sret + 1#64) 7 ∗
      ((sret + 8#64) ↦₈ 0#8) ∗ memRegion (sret + 9#64) 24
  | .error (.badKeyType t) =>
    (sret ↦₈ 1#8) ∗ memRegion (sret + 1#64) 7 ∗
      ((sret + 8#64) ↦₈ 1#8) ∗ ((sret + 9#64) ↦₈ t) ∗ memRegion (sret + 10#64) 23
  | .error (.badKeyLength n) =>
    (sret ↦₈ 1#8) ∗ memRegion (sret + 1#64) 7 ∗
      ((sret + 8#64) ↦₈ 2#8) ∗ memRegion (sret + 9#64) 7 ∗
      ((sret + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗ memRegion (sret + 24#64) 9
  | .error _ => ⌜False⌝

/-- Full specification of `<libsignal_core::curve::PublicKey>::deserialize` (`0x3db50`)
covering both `.ok pk` and all three `.error` cases. Ghost: `(ptr, bs, sret)`. -/
def deserializeFullSpec (b : BitVec 64) : Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (ptr, bs, sret) s =>
    ⌜s.readReg64 .x0 = ptr ∧ (s.readReg64 .x1).toNat = bs.length ∧
      s.readReg64 .x8 = sret ∧ bs.length < 2 ^ 63 ∧
      b &&& 0xfff#64 = 0#64⌝ ∗
    (ptr ↦ₛ bs) ∗
    memRegion sret 33 ∗
    ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64)
  post := fun (ptr, bs, sret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (ptr ↦ₛ bs) ∗
    deserializeResult33At sret (PublicKey.deserialize bs) ∗
    ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64)

/-- Error-path specification of `PublicKey::deserialize` when `bs = []` (`.noKeyTypeIdentifier`). -/
private def deserializeEmptySpec (b : BitVec 64) :
    Spec (BitVec 64 × BitVec 64 × BitVec 8 × BitVec 64) where
  pre := fun (ptr, sret, tag0, w8) s =>
    ⌜s.readReg64 .x0 = ptr ∧ s.readReg64 .x1 = 0#64 ∧
      s.readReg64 .x8 = sret ∧ b &&& 0xfff#64 = 0#64⌝ ∗
    (sret ↦₈ tag0) ∗ ((sret + 8#64) ↦₆₄ w8)
  post := fun (_, sret, _, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (sret ↦₈ 1#8) ∗ ((sret + 8#64) ↦₆₄ 0#64)

private theorem deserializeEmpty_ok (b : BitVec 64) (H : String → Option (State → State)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr deserializeName)
      (deserializeEmptySpec b) := by
  simp only [deserializeEmptySpec, deserializeName]
  code_fetches libsignalSessionCode libsignalSessionBin b H (ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::deserialize") (num% (ls_off% "<libsignal_core::curve::PublicKey>::deserialize")) 272
  wp_init g s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨ptr, sret, tag0, w8⟩ := g
  dsimp only at *
  subst h_1 h_3
  wp_steps
  wp_done

/-- Error-path specification of `PublicKey::deserialize` when `bs = b0 :: b1` and `b0 ≠ 5#8`
(`.badKeyType b0`). -/
private def deserializeBadTypeSpec (b : BitVec 64) :
    Spec (BitVec 64 × BitVec 8 × Nat × BitVec 64 × BitVec 8 × BitVec 8 × BitVec 8) where
  pre := fun (ptr, b0, len1, sret, tag0, w8, w9) s =>
    ⌜s.readReg64 .x0 = ptr ∧ (s.readReg64 .x1).toNat = len1 + 1 ∧
      s.readReg64 .x8 = sret ∧ len1 + 1 < 2 ^ 63 ∧ b0 ≠ 5#8 ∧
      b &&& 0xfff#64 = 0#64⌝ ∗
    (ptr ↦₈ b0) ∗ (sret ↦₈ tag0) ∗ ((sret + 8#64) ↦₈ w8) ∗ ((sret + 9#64) ↦₈ w9)
  post := fun (ptr, b0, _, sret, _, _, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (ptr ↦₈ b0) ∗ (sret ↦₈ 1#8) ∗ ((sret + 8#64) ↦₈ 1#8) ∗ ((sret + 9#64) ↦₈ b0)

private theorem deserializeBadType_ok (b : BitVec 64) (H : String → Option (State → State)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr deserializeName)
      (deserializeBadTypeSpec b) := by
  simp only [deserializeBadTypeSpec, deserializeName]
  code_fetches libsignalSessionCode libsignalSessionBin b H (ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::deserialize") (num% (ls_off% "<libsignal_core::curve::PublicKey>::deserialize")) 272
  wp_init g s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨ptr, b0, len1, sret, tag0, w8, w9⟩ := g
  dsimp only at *
  subst h_1 h_3
  have hx1_ne : s0.readReg64 (Reg.gpr 1#5) ≠ 0#64 := by
    intro hc; rw [hc] at h_2; simp at h_2
  wp_steps
  wp_done

/-- Error-path specification of `PublicKey::deserialize` when `bs = 5#8 :: b1` and `b1.length < 32`
(`.badKeyLength (b1.length + 1)`). -/
private def deserializeBadLenSpec (b : BitVec 64) :
    Spec (BitVec 64 × Nat × BitVec 64 × BitVec 8 × BitVec 64 × BitVec 64) where
  pre := fun (ptr, len1, sret, tag0, w8, w16) s =>
    ⌜s.readReg64 .x0 = ptr ∧ (s.readReg64 .x1).toNat = len1 + 1 ∧
      s.readReg64 .x8 = sret ∧ len1 < 32 ∧
      b &&& 0xfff#64 = 0#64⌝ ∗
    (ptr ↦₈ 5#8) ∗ (sret ↦₈ tag0) ∗ ((sret + 8#64) ↦₆₄ w8) ∗ ((sret + 16#64) ↦₆₄ w16)
  post := fun (ptr, len1, sret, _, _, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (ptr ↦₈ 5#8) ∗ (sret ↦₈ 1#8) ∗ ((sret + 8#64) ↦₆₄ 2#64) ∗
    ((sret + 16#64) ↦₆₄ BitVec.ofNat 64 (len1 + 1))

private theorem deserializeBadLen_ok (b : BitVec 64) (H : String → Option (State → State)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr deserializeName)
      (deserializeBadLenSpec b) := by
  simp only [deserializeBadLenSpec, deserializeName]
  code_fetches libsignalSessionCode libsignalSessionBin b H (ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::deserialize") (num% (ls_off% "<libsignal_core::curve::PublicKey>::deserialize")) 272
  wp_init g s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨ptr, len1, sret, tag0, w8, w16⟩ := g
  dsimp only at *
  subst h_1 h_3
  have hx1_ne : s0.readReg64 (Reg.gpr 1#5) ≠ 0#64 := by
    intro hc; rw [hc] at h_2; simp at h_2
  have hx1_eq : s0.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (len1 + 1) := by
    rw [← h_2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  wp_steps
  wp_if hlo
  · wp_steps
    wp_done
  · exfalso
    simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      decide_eq_true_eq] at hlo
    omega

/-- Full `subroutine_ok` for `PublicKey::deserialize` (`0x3db50`). -/
theorem deserializeFull_ok (b : BitVec 64) (H : String → Option (State → State)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr deserializeName)
      (deserializeFullSpec b) := by
  refine subroutine_ok_intro fun ⟨ptr, bs, sret⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [deserializeFullSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hlen, hb⟩, hmem⟩
  rcases bs with _ | ⟨b0, b1⟩
  · -- bs = []
    have hsplit : memRegion sret 33 =
        (∃∗ tag0 : BitVec 8, sret ↦₈ tag0) ∗
        memRegion (sret + 1#64) 7 ∗
        (∃∗ w8 : BitVec 64, (sret + 8#64) ↦₆₄ w8) ∗
        memRegion (sret + 16#64) 17 := by
      rw [show (33 : Nat) = 1 + (7 + (8 + 17)) by decide,
        memRegion_split sret 1 32 (by decide),
        memRegion_split (sret + 1#64) 7 25 (by decide),
        memRegion_split (sret + 1#64 + 7#64) 8 17 (by decide),
        memRegion_one, memRegion_eight]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [pointsToBytes_nil, emp_sepConj, hsplit] at hmem
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      satisfies_sepExists] at hmem
    rcases hmem with ⟨w8, tag0, hmem⟩
    have hx1_zero : s0.readReg64 .x1 = 0#64 := by
      apply BitVec.eq_of_toNat_eq; simpa using hx1
    set F := memRegion (sret + 1#64) 7 ∗ memRegion (sret + 16#64) 17 ∗
      ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64)
    have hpre' : s0.mem ⊨ (deserializeEmptySpec b).pre (ptr, sret, tag0, w8) s0 ∗ (F ∗ R) := by
      dsimp only [deserializeEmptySpec]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1_zero, hx8, hb⟩, ?_⟩
      dsimp only [F]; ac_nf at hmem ⊢
    refine reaches_of_ghost (deserializeEmpty_ok b H) (ptr, sret, tag0, w8) F hpc hrun hsp hpre' ?_
    intro sf _ hpost
    dsimp only [deserializeEmptySpec, deserializeFullSpec, deserializeResult33At,
      PublicKey.deserialize] at hpost ⊢
    simp only [pointsToBytes_nil, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    refine ⟨htr, ?_⟩
    rw [pointsTo64_zero_byte0 (sret + 8#64)] at hpost
    have hpost' : sf.mem ⊨
        ((sret + 8#64 + 1#64) ↦ₛ List.replicate 7 0#8) ∗
        memRegion (sret + 16#64) 17 ∗
        ((sret ↦₈ 1#8) ∗ memRegion (sret + 1#64) 7 ∗
          ((sret + 8#64) ↦₈ 0#8) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ R) := by
      dsimp only [F] at hpost; ac_nf at hpost ⊢
    have h24 : (((sret + 8#64 + 1#64) ↦ₛ List.replicate 7 0#8) ∗ memRegion (sret + 16#64) 17) ⊢
        memRegion (sret + 9#64) 24 := by
      rw [show (24 : Nat) = 7 + 17 by decide, memRegion_split (sret + 9#64) 7 17 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact sepConj_mono_left (by
        simpa using pointsToBytes_entails_memRegion (sret + 9#64) (List.replicate 7 0#8))
    rw [← sepConj_assoc] at hpost'
    have hpost'' := Satisfies.mono (sepConj_mono_left h24) hpost'
    ac_nf at hpost'' ⊢
  · -- bs = b0 :: b1
    by_cases hb0 : b0 = 5#8
    · subst hb0
      by_cases hlen32 : b1.length < 32
      · -- bs = 5#8 :: b1, b1.length < 32 (.badKeyLength)
        have hsplit : memRegion sret 33 =
            (∃∗ tag0 : BitVec 8, sret ↦₈ tag0) ∗
            memRegion (sret + 1#64) 7 ∗
            (∃∗ w8 : BitVec 64, (sret + 8#64) ↦₆₄ w8) ∗
            (∃∗ w16 : BitVec 64, (sret + 16#64) ↦₆₄ w16) ∗
            memRegion (sret + 24#64) 9 := by
          rw [show (33 : Nat) = 1 + (7 + (8 + (8 + 9))) by decide,
            memRegion_split sret 1 32 (by decide),
            memRegion_split (sret + 1#64) 7 25 (by decide),
            memRegion_split (sret + 1#64 + 7#64) 8 17 (by decide),
            memRegion_split (sret + 1#64 + 7#64 + 8#64) 8 9 (by decide),
            memRegion_one, memRegion_eight, memRegion_eight]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
        rw [pointsToBytes_cons, hsplit] at hmem
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
          satisfies_sepExists] at hmem
        rcases hmem with ⟨w16, w8, tag0, hmem⟩
        set F := ((ptr + 1#64) ↦ₛ b1) ∗ memRegion (sret + 1#64) 7 ∗
          memRegion (sret + 24#64) 9 ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64)
        have hpre' : s0.mem ⊨ (deserializeBadLenSpec b).pre (ptr, b1.length, sret, tag0, w8, w16) s0 ∗ (F ∗ R) := by
          dsimp only [deserializeBadLenSpec]
          simp only [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hx0, hx1, hx8, hlen32, hb⟩, ?_⟩
          dsimp only [F]; ac_nf at hmem ⊢
        refine reaches_of_ghost (deserializeBadLen_ok b H) (ptr, b1.length, sret, tag0, w8, w16) F hpc hrun hsp hpre' ?_
        intro sf _ hpost
        have hdes : PublicKey.deserialize (5#8 :: b1) = .error (.badKeyLength (b1.length + 1)) := by
          simp [PublicKey.deserialize, djbType, hlen32]
        dsimp only [deserializeBadLenSpec, deserializeFullSpec] at hpost ⊢
        rw [hdes]
        simp only [deserializeResult33At, pointsToBytes_cons, sepConj_assoc,
          satisfies_pure_sepConj] at hpost ⊢
        rcases hpost with ⟨htr, hpost⟩
        refine ⟨htr, ?_⟩
        rw [pointsTo64_two_byte0 (sret + 8#64)] at hpost
        have hpost' : sf.mem ⊨
            ((sret + 8#64 + 1#64) ↦ₛ List.replicate 7 0#8) ∗
            ((ptr ↦₈ 5#8) ∗ ((ptr + 1#64) ↦ₛ b1) ∗
              (sret ↦₈ 1#8) ∗ memRegion (sret + 1#64) 7 ∗
              ((sret + 8#64) ↦₈ 2#8) ∗
              ((sret + 16#64) ↦₆₄ BitVec.ofNat 64 (b1.length + 1)) ∗
              memRegion (sret + 24#64) 9 ∗
              ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ R) := by
          dsimp only [F] at hpost; ac_nf at hpost ⊢
        have h7 : ((sret + 8#64 + 1#64) ↦ₛ List.replicate 7 0#8) ⊢ memRegion (sret + 9#64) 7 := by
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          simpa using pointsToBytes_entails_memRegion (sret + 9#64) (List.replicate 7 0#8)
        have hpost'' := Satisfies.mono (sepConj_mono_left h7) hpost'
        ac_nf at hpost'' ⊢
      · -- bs = 5#8 :: b1, 32 ≤ b1.length (.ok pk)
        have hge32 : 32 ≤ b1.length := Nat.le_of_not_lt hlen32
        set pk : PublicKey := ⟨⟨b1.take 32, by simp [hge32]⟩⟩
        have hdes : PublicKey.deserialize (5#8 :: b1) = .ok pk := by
          simp [PublicKey.deserialize, djbType, hge32, pk]
        have hsplit : memRegion sret 33 =
            (∃∗ tag0 : BitVec 8, sret ↦₈ tag0) ∗
            (∃∗ out32 : List (BitVec 8), ⌜out32.length = 32⌝ ∗ ((sret + 1#64) ↦ₛ out32)) := by
          rw [show (33 : Nat) = 1 + 32 by decide, memRegion_split sret 1 32 (by decide),
            memRegion_one, memRegion_eq_exists_bytes (sret + 1#64) 32 (by decide)]
        rw [hsplit] at hmem
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
          satisfies_sepExists, sepConj_pure_left_comm, satisfies_pure_sepConj] at hmem
        rcases hmem with ⟨out32, tag0, hout32, hmem⟩
        have hpre' : s0.mem ⊨ (deserializeSpec b).pre (ptr, 5#8 :: b1, pk, sret, tag0, out32) s0 ∗ (emp ∗ R) := by
          dsimp only [deserializeSpec]
          simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hx0, hx1, hx8, hlen, hdes, hout32, hb⟩, ?_⟩
          ac_nf at hmem ⊢
        refine reaches_of_ghost (deserialize_ok b H) (ptr, 5#8 :: b1, pk, sret, tag0, out32) emp hpc hrun hsp hpre' ?_
        intro sf _ hpost
        dsimp only [deserializeSpec, deserializeFullSpec] at hpost ⊢
        rw [hdes]
        simpa only [deserializeResult33At, emp_sepConj, sepConj_assoc] using hpost
    · -- bs = b0 :: b1, b0 ≠ 5#8 (.badKeyType b0)
      have hsplit : memRegion sret 33 =
          (∃∗ tag0 : BitVec 8, sret ↦₈ tag0) ∗
          memRegion (sret + 1#64) 7 ∗
          (∃∗ w8 : BitVec 8, (sret + 8#64) ↦₈ w8) ∗
          (∃∗ w9 : BitVec 8, (sret + 9#64) ↦₈ w9) ∗
          memRegion (sret + 10#64) 23 := by
        rw [show (33 : Nat) = 1 + (7 + (1 + (1 + 23))) by decide,
          memRegion_split sret 1 32 (by decide),
          memRegion_split (sret + 1#64) 7 25 (by decide),
          memRegion_split (sret + 1#64 + 7#64) 1 24 (by decide),
          memRegion_split (sret + 1#64 + 7#64 + 1#64) 1 23 (by decide),
          memRegion_one, memRegion_one, memRegion_one]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [pointsToBytes_cons, hsplit] at hmem
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        satisfies_sepExists] at hmem
      rcases hmem with ⟨w9, w8, tag0, hmem⟩
      set F := ((ptr + 1#64) ↦ₛ b1) ∗ memRegion (sret + 1#64) 7 ∗
        memRegion (sret + 10#64) 23 ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64)
      have hpre' : s0.mem ⊨ (deserializeBadTypeSpec b).pre (ptr, b0, b1.length, sret, tag0, w8, w9) s0 ∗ (F ∗ R) := by
        dsimp only [deserializeBadTypeSpec]
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hx0, hx1, hx8, hlen, hb0, hb⟩, ?_⟩
        dsimp only [F]; ac_nf at hmem ⊢
      refine reaches_of_ghost (deserializeBadType_ok b H) (ptr, b0, b1.length, sret, tag0, w8, w9) F hpc hrun hsp hpre' ?_
      intro sf _ hpost
      have hdes : PublicKey.deserialize (b0 :: b1) = .error (.badKeyType b0) := by
        simp [PublicKey.deserialize, djbType, hb0]
      dsimp only [deserializeBadTypeSpec, deserializeFullSpec] at hpost ⊢
      rw [hdes]
      simp only [deserializeResult33At, pointsToBytes_cons, sepConj_assoc,
        satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨htr, hpost⟩
      refine ⟨htr, ?_⟩
      dsimp only [F] at hpost
      ac_nf at hpost ⊢

/-- `PublicKey::deserialize` (`0x3db50`) at call distance `k` from `name` on `tripleRatchetProgAtW`. -/
theorem deserializeFull_ok_at_tripleRatchet {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "<libsignal_core::curve::PublicKey>::deserialize")) :
    subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      ((deserializeFullSpec img.base).inImage img) := by
  rw [← Program.fnAddr_rel hfn (ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::deserialize") hk]
  exact subroutine_ok_inImage_of_subroutine_ok img (deserializeFull_ok img.base (Rust.withPanics abs))

/-! ## Relocatable `[LibsignalPlacement]` `PublicKey::deserialize` contract (Block `201`) -/

def deserializeFullPlacedSpec [LibsignalPlacement] : Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (ptr, bs, sret) s =>
    ⌜s.readReg64 .x0 = ptr ∧ (s.readReg64 .x1).toNat = bs.length ∧
      s.readReg64 .x8 = sret ∧ bs.length < 2 ^ 63⌝ ∗
    (ptr ↦ₛ bs) ∗
    memRegion sret 33 ∗
    (lsLogFilterAddr ↦₆₄ 0#64)
  post := fun (ptr, bs, sret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (ptr ↦ₛ bs) ∗
    deserializeResult33At sret (PublicKey.deserialize bs) ∗
    (lsLogFilterAddr ↦₆₄ 0#64)

private def deserializeEmptyPlacedSpec :
    Spec (BitVec 64 × BitVec 64 × BitVec 8 × BitVec 64) where
  pre := fun (ptr, sret, tag0, w8) s =>
    ⌜s.readReg64 .x0 = ptr ∧ s.readReg64 .x1 = 0#64 ∧
      s.readReg64 .x8 = sret⌝ ∗
    (sret ↦₈ tag0) ∗ ((sret + 8#64) ↦₆₄ w8)
  post := fun (_, sret, _, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (sret ↦₈ 1#8) ∗ ((sret + 8#64) ↦₆₄ 0#64)

private theorem deserializeEmpty_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (blkPl_201).base
      deserializeEmptyPlacedSpec := by
  simp only [deserializeEmptyPlacedSpec]
  wp_init g s0
  obtain ⟨ptr, sret, tag0, w8⟩ := g
  dsimp only at *
  subst h_1 h
  wp_steps
  wp_done

private def deserializeBadTypePlacedSpec :
    Spec (BitVec 64 × BitVec 8 × Nat × BitVec 64 × BitVec 8 × BitVec 8 × BitVec 8) where
  pre := fun (ptr, b0, len1, sret, tag0, w8, w9) s =>
    ⌜s.readReg64 .x0 = ptr ∧ (s.readReg64 .x1).toNat = len1 + 1 ∧
      s.readReg64 .x8 = sret ∧ len1 + 1 < 2 ^ 63 ∧ b0 ≠ 5#8⌝ ∗
    (ptr ↦₈ b0) ∗ (sret ↦₈ tag0) ∗ ((sret + 8#64) ↦₈ w8) ∗ ((sret + 9#64) ↦₈ w9)
  post := fun (ptr, b0, _, sret, _, _, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (ptr ↦₈ b0) ∗ (sret ↦₈ 1#8) ∗ ((sret + 8#64) ↦₈ 1#8) ∗ ((sret + 9#64) ↦₈ b0)

private theorem deserializeBadType_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (blkPl_201).base
      deserializeBadTypePlacedSpec := by
  simp only [deserializeBadTypePlacedSpec]
  wp_init g s0
  obtain ⟨ptr, b0, len1, sret, tag0, w8, w9⟩ := g
  dsimp only at *
  subst h_1 h_3
  have hx1_ne : s0.readReg64 (Reg.gpr 1#5) ≠ 0#64 := by
    intro hc; rw [hc] at h_2; simp at h_2
  wp_steps
  wp_done

private def deserializeBadLenPlacedSpec :
    Spec (BitVec 64 × Nat × BitVec 64 × BitVec 8 × BitVec 64 × BitVec 64) where
  pre := fun (ptr, len1, sret, tag0, w8, w16) s =>
    ⌜s.readReg64 .x0 = ptr ∧ (s.readReg64 .x1).toNat = len1 + 1 ∧
      s.readReg64 .x8 = sret ∧ len1 < 32⌝ ∗
    (ptr ↦₈ 5#8) ∗ (sret ↦₈ tag0) ∗ ((sret + 8#64) ↦₆₄ w8) ∗ ((sret + 16#64) ↦₆₄ w16)
  post := fun (ptr, len1, sret, _, _, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (ptr ↦₈ 5#8) ∗ (sret ↦₈ 1#8) ∗ ((sret + 8#64) ↦₆₄ 2#64) ∗
    ((sret + 16#64) ↦₆₄ BitVec.ofNat 64 (len1 + 1))

private theorem deserializeBadLen_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (blkPl_201).base
      deserializeBadLenPlacedSpec := by
  simp only [deserializeBadLenPlacedSpec]
  wp_init g s0
  obtain ⟨ptr, len1, sret, tag0, w8, w16⟩ := g
  dsimp only at *
  subst h_1 h_3
  have hx1_ne : s0.readReg64 (Reg.gpr 1#5) ≠ 0#64 := by
    intro hc; rw [hc] at h_2; simp at h_2
  have hx1_eq : s0.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (len1 + 1) := by
    rw [← h_2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  wp_steps
  wp_if hlo
  · wp_steps
    wp_done
  · exfalso
    simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      decide_eq_true_eq] at hlo
    omega

theorem deserializeFull_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (blkPl_201).base
      deserializeFullPlacedSpec := by
  refine subroutine_ok_intro fun ⟨ptr, bs, sret⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [deserializeFullPlacedSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hlen⟩, hmem⟩
  rcases bs with _ | ⟨b0, b1⟩
  · -- bs = []
    have hsplit : memRegion sret 33 =
        (∃∗ tag0 : BitVec 8, sret ↦₈ tag0) ∗
        memRegion (sret + 1#64) 7 ∗
        (∃∗ w8 : BitVec 64, (sret + 8#64) ↦₆₄ w8) ∗
        memRegion (sret + 16#64) 17 := by
      rw [show (33 : Nat) = 1 + (7 + (8 + 17)) by decide,
        memRegion_split sret 1 32 (by decide),
        memRegion_split (sret + 1#64) 7 25 (by decide),
        memRegion_split (sret + 1#64 + 7#64) 8 17 (by decide),
        memRegion_one, memRegion_eight]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [pointsToBytes_nil, emp_sepConj, hsplit] at hmem
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      satisfies_sepExists] at hmem
    rcases hmem with ⟨w8, tag0, hmem⟩
    have hx1_zero : s0.readReg64 .x1 = 0#64 := by
      apply BitVec.eq_of_toNat_eq; simpa using hx1
    set F := memRegion (sret + 1#64) 7 ∗ memRegion (sret + 16#64) 17 ∗
      (lsLogFilterAddr ↦₆₄ 0#64)
    have hpre' : s0.mem ⊨ deserializeEmptyPlacedSpec.pre (ptr, sret, tag0, w8) s0 ∗ (F ∗ R) := by
      dsimp only [deserializeEmptyPlacedSpec]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1_zero, hx8⟩, ?_⟩
      dsimp only [F]; ac_nf at hmem ⊢
    refine reaches_of_ghost (deserializeEmpty_placed_ok H) (ptr, sret, tag0, w8) F hpc hrun hsp hpre' ?_
    intro sf _ hpost
    dsimp only [deserializeEmptyPlacedSpec, deserializeFullPlacedSpec, deserializeResult33At,
      PublicKey.deserialize] at hpost ⊢
    simp only [pointsToBytes_nil, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    refine ⟨htr, ?_⟩
    rw [pointsTo64_zero_byte0 (sret + 8#64)] at hpost
    have hpost' : sf.mem ⊨
        ((sret + 8#64 + 1#64) ↦ₛ List.replicate 7 0#8) ∗
        memRegion (sret + 16#64) 17 ∗
        ((sret ↦₈ 1#8) ∗ memRegion (sret + 1#64) 7 ∗
          ((sret + 8#64) ↦₈ 0#8) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ R) := by
      dsimp only [F] at hpost; ac_nf at hpost ⊢
    have h24 : (((sret + 8#64 + 1#64) ↦ₛ List.replicate 7 0#8) ∗ memRegion (sret + 16#64) 17) ⊢
        memRegion (sret + 9#64) 24 := by
      rw [show (24 : Nat) = 7 + 17 by decide, memRegion_split (sret + 9#64) 7 17 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact sepConj_mono_left (by
        simpa using pointsToBytes_entails_memRegion (sret + 9#64) (List.replicate 7 0#8))
    rw [← sepConj_assoc] at hpost'
    have hpost'' := Satisfies.mono (sepConj_mono_left h24) hpost'
    ac_nf at hpost'' ⊢
  · -- bs = b0 :: b1
    by_cases hb0 : b0 = 5#8
    · subst hb0
      by_cases hlen32 : b1.length < 32
      · -- bs = 5#8 :: b1, b1.length < 32 (.badKeyLength)
        have hsplit : memRegion sret 33 =
            (∃∗ tag0 : BitVec 8, sret ↦₈ tag0) ∗
            memRegion (sret + 1#64) 7 ∗
            (∃∗ w8 : BitVec 64, (sret + 8#64) ↦₆₄ w8) ∗
            (∃∗ w16 : BitVec 64, (sret + 16#64) ↦₆₄ w16) ∗
            memRegion (sret + 24#64) 9 := by
          rw [show (33 : Nat) = 1 + (7 + (8 + (8 + 9))) by decide,
            memRegion_split sret 1 32 (by decide),
            memRegion_split (sret + 1#64) 7 25 (by decide),
            memRegion_split (sret + 1#64 + 7#64) 8 17 (by decide),
            memRegion_split (sret + 1#64 + 7#64 + 8#64) 8 9 (by decide),
            memRegion_one, memRegion_eight, memRegion_eight]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
        rw [pointsToBytes_cons, hsplit] at hmem
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
          satisfies_sepExists] at hmem
        rcases hmem with ⟨w16, w8, tag0, hmem⟩
        set F := ((ptr + 1#64) ↦ₛ b1) ∗ memRegion (sret + 1#64) 7 ∗
          memRegion (sret + 24#64) 9 ∗ (lsLogFilterAddr ↦₆₄ 0#64)
        have hpre' : s0.mem ⊨ deserializeBadLenPlacedSpec.pre (ptr, b1.length, sret, tag0, w8, w16) s0 ∗ (F ∗ R) := by
          dsimp only [deserializeBadLenPlacedSpec]
          simp only [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hx0, hx1, hx8, hlen32⟩, ?_⟩
          dsimp only [F]; ac_nf at hmem ⊢
        refine reaches_of_ghost (deserializeBadLen_placed_ok H) (ptr, b1.length, sret, tag0, w8, w16) F hpc hrun hsp hpre' ?_
        intro sf _ hpost
        have hdes : PublicKey.deserialize (5#8 :: b1) = .error (.badKeyLength (b1.length + 1)) := by
          simp [PublicKey.deserialize, djbType, hlen32]
        dsimp only [deserializeBadLenPlacedSpec, deserializeFullPlacedSpec] at hpost ⊢
        rw [hdes]
        simp only [deserializeResult33At, pointsToBytes_cons, sepConj_assoc,
          satisfies_pure_sepConj] at hpost ⊢
        rcases hpost with ⟨htr, hpost⟩
        refine ⟨htr, ?_⟩
        rw [pointsTo64_two_byte0 (sret + 8#64)] at hpost
        have hpost' : sf.mem ⊨
            ((sret + 8#64 + 1#64) ↦ₛ List.replicate 7 0#8) ∗
            ((ptr ↦₈ 5#8) ∗ ((ptr + 1#64) ↦ₛ b1) ∗
              (sret ↦₈ 1#8) ∗ memRegion (sret + 1#64) 7 ∗
              ((sret + 8#64) ↦₈ 2#8) ∗
              ((sret + 16#64) ↦₆₄ BitVec.ofNat 64 (b1.length + 1)) ∗
              memRegion (sret + 24#64) 9 ∗
              (lsLogFilterAddr ↦₆₄ 0#64) ∗ R) := by
          dsimp only [F] at hpost; ac_nf at hpost ⊢
        have h7 : ((sret + 8#64 + 1#64) ↦ₛ List.replicate 7 0#8) ⊢ memRegion (sret + 9#64) 7 := by
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          simpa using pointsToBytes_entails_memRegion (sret + 9#64) (List.replicate 7 0#8)
        have hpost'' := Satisfies.mono (sepConj_mono_left h7) hpost'
        ac_nf at hpost'' ⊢
      · -- bs = 5#8 :: b1, 32 ≤ b1.length (.ok pk)
        have hge32 : 32 ≤ b1.length := Nat.le_of_not_lt hlen32
        set pk : PublicKey := ⟨⟨b1.take 32, by simp [hge32]⟩⟩
        have hdes : PublicKey.deserialize (5#8 :: b1) = .ok pk := by
          simp [PublicKey.deserialize, djbType, hge32, pk]
        have hsplit : memRegion sret 33 =
            (∃∗ tag0 : BitVec 8, sret ↦₈ tag0) ∗
            (∃∗ out32 : List (BitVec 8), ⌜out32.length = 32⌝ ∗ ((sret + 1#64) ↦ₛ out32)) := by
          rw [show (33 : Nat) = 1 + 32 by decide, memRegion_split sret 1 32 (by decide),
            memRegion_one, memRegion_eq_exists_bytes (sret + 1#64) 32 (by decide)]
        rw [hsplit] at hmem
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
          satisfies_sepExists, sepConj_pure_left_comm, satisfies_pure_sepConj] at hmem
        rcases hmem with ⟨out32, tag0, hout32, hmem⟩
        have hpre' : s0.mem ⊨ deserializePlacedSpec.pre (ptr, 5#8 :: b1, pk, sret, tag0, out32) s0 ∗ (emp ∗ R) := by
          dsimp only [deserializePlacedSpec]
          simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hx0, hx1, hx8, hlen, hdes, hout32⟩, ?_⟩
          ac_nf at hmem ⊢
        refine reaches_of_ghost (deserialize_placed_ok H) (ptr, 5#8 :: b1, pk, sret, tag0, out32) emp hpc hrun hsp hpre' ?_
        intro sf _ hpost
        dsimp only [deserializePlacedSpec, deserializeFullPlacedSpec] at hpost ⊢
        rw [hdes]
        simpa only [deserializeResult33At, emp_sepConj, sepConj_assoc] using hpost
    · -- bs = b0 :: b1, b0 ≠ 5#8 (.badKeyType b0)
      have hsplit : memRegion sret 33 =
          (∃∗ tag0 : BitVec 8, sret ↦₈ tag0) ∗
          memRegion (sret + 1#64) 7 ∗
          (∃∗ w8 : BitVec 8, (sret + 8#64) ↦₈ w8) ∗
          (∃∗ w9 : BitVec 8, (sret + 9#64) ↦₈ w9) ∗
          memRegion (sret + 10#64) 23 := by
        rw [show (33 : Nat) = 1 + (7 + (1 + (1 + 23))) by decide,
          memRegion_split sret 1 32 (by decide),
          memRegion_split (sret + 1#64) 7 25 (by decide),
          memRegion_split (sret + 1#64 + 7#64) 1 24 (by decide),
          memRegion_split (sret + 1#64 + 7#64 + 1#64) 1 23 (by decide),
          memRegion_one, memRegion_one, memRegion_one]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [pointsToBytes_cons, hsplit] at hmem
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        satisfies_sepExists] at hmem
      rcases hmem with ⟨w9, w8, tag0, hmem⟩
      set F := ((ptr + 1#64) ↦ₛ b1) ∗ memRegion (sret + 1#64) 7 ∗
        memRegion (sret + 10#64) 23 ∗ (lsLogFilterAddr ↦₆₄ 0#64)
      have hpre' : s0.mem ⊨ deserializeBadTypePlacedSpec.pre (ptr, b0, b1.length, sret, tag0, w8, w9) s0 ∗ (F ∗ R) := by
        dsimp only [deserializeBadTypePlacedSpec]
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hx0, hx1, hx8, hlen, hb0⟩, ?_⟩
        dsimp only [F]; ac_nf at hmem ⊢
      refine reaches_of_ghost (deserializeBadType_placed_ok H) (ptr, b0, b1.length, sret, tag0, w8, w9) F hpc hrun hsp hpre' ?_
      intro sf _ hpost
      have hdes : PublicKey.deserialize (b0 :: b1) = .error (.badKeyType b0) := by
        simp [PublicKey.deserialize, djbType, hb0]
      dsimp only [deserializeBadTypePlacedSpec, deserializeFullPlacedSpec] at hpost ⊢
      rw [hdes]
      simp only [deserializeResult33At, pointsToBytes_cons, sepConj_assoc,
        satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨htr, hpost⟩
      refine ⟨htr, ?_⟩
      dsimp only [F] at hpost
      ac_nf at hpost ⊢

theorem deserializeFull_ok_at_placed [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok (tryFromPlacedProg H)
      ((blkPl_85).ρ deserializeName)
      (withLsCodeRoLoaded lsmpl deserializeFullPlacedSpec) := by
  have h1 := keys_ls_subroutine_ok_of_block_cro (callerProg := tryFromPlacedProg H)
    (subroutine_ok_withLsCodeRoLoaded_of_plain (deserializeFull_placed_ok H))
  simp only [deserializeName, arm64_norm]
  exact h1

end CryptoVerification.LibsignalTripleRatchet.Wire
