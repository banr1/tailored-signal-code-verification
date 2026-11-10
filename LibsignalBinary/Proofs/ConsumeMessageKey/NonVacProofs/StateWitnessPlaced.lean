/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.NonVacProofs.StateWitness
public import LibsignalBinary.Proofs.ConsumeMessageKey.NonVacProofs.AllocWitnessPlaced
public import LibsignalBinary.Proofs.ConsumeMessageKey.RunOfCallees

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalSession.NonVacuityWitness

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalSession

/-! ## Relocatable `[LibsignalPlacement]` State and Non-Vacuity Witness -/

/-- Base memory assumptions for a `[LibsignalPlacement]` witness: loaded code and `.rodata` with
`lsLogFilterAddr` (8 B) and a 2 MiB arena at `B` unmapped and disjoint. -/
structure PlacedWitnessBase [LibsignalPlacement] (B : BitVec 64) (m₀ : Memory) : Prop where
  codeLoaded : LibsignalCodeLoaded lsmpl m₀
  roLoaded : LibsignalRoLoaded lsmpl m₀
  aligned : B.toNat % 4096 = 0
  wrap : B.toNat + 2097152 ≤ 2 ^ 64
  unmapped_log : Unmapped m₀ lsLogFilterAddr 8
  unmapped_arena : Unmapped m₀ B 2097152
  disj_log_arena : ∀ a, InRegion lsLogFilterAddr 8 a → ¬ InRegion B 2097152 a

/-- Initial memory mapping `lsLogFilterAddr` (8 B) and `[B, B + 16384)` read-write over `m₀`. -/
def baseMemPlaced [LibsignalPlacement] (B : BitVec 64) (m₀ : Memory) : Memory :=
  (m₀.mapFresh lsLogFilterAddr 8 Perm.rw).mapFresh B 16384 Perm.rw

theorem baseMemPlaced_keepsFrozen [LibsignalPlacement] (B : BitVec 64) (m₀ : Memory) :
    m₀.KeepsFrozen (baseMemPlaced B m₀) :=
  (Memory.keepsFrozen_mapFresh m₀ lsLogFilterAddr 8 Perm.rw).trans
    (Memory.keepsFrozen_mapFresh _ B 16384 Perm.rw)

theorem baseMemPlaced_satisfies_initial_regions [LibsignalPlacement] {B : BitVec 64} {m₀ : Memory}
    (hb : PlacedWitnessBase B m₀) :
    baseMemPlaced B m₀ ⊨ memRegion lsLogFilterAddr 8 ∗ memRegion B 16384 := by
  have hsat₁ : m₀.mapFresh lsLogFilterAddr 8 Perm.rw ⊨ memRegion lsLogFilterAddr 8 := by
    have h := satisfies_mapFresh_unmapped (satisfies_emp m₀) hb.unmapped_log
    rwa [sepConj_emp] at h
  have hunm₁ : Unmapped (m₀.mapFresh lsLogFilterAddr 8 Perm.rw) B 16384 := by
    intro a ha
    have ha2 : InRegion B 2097152 a := by
      unfold InRegion at ha ⊢
      omega
    have hdisj : ¬ InRegion lsLogFilterAddr 8 a := fun hlog => hb.disj_log_arena a hlog ha2
    have hum0 : (m₀.perm a).mapped = false := hb.unmapped_arena a ha2
    have hperm_eq : (m₀.mapFresh lsLogFilterAddr 8 Perm.rw).perm a = m₀.perm a := by
      rw [Memory.perm_mapFresh]
      have hdec : decide ((a - lsLogFilterAddr).toNat < 8) = false :=
        decide_eq_false hdisj
      simp only [hdec, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    change ((m₀.mapFresh lsLogFilterAddr 8 Perm.rw).perm a).mapped = false
    rw [hperm_eq]
    exact hum0
  have hsat₂ := satisfies_mapFresh_unmapped hsat₁ hunm₁
  rwa [sepConj_comm] at hsat₂

theorem baseMemPlaced_unmapped_arena [LibsignalPlacement] {B : BitVec 64} {m₀ : Memory}
    (hb : PlacedWitnessBase B m₀) :
    Unmapped (baseMemPlaced B m₀) (B + 1048576#64) (2 ^ 20) := by
  intro a ha
  have hwrap := hb.wrap
  have ha_sub : 1048576 ≤ (a - B).toNat ∧ (a - B).toNat < 2097152 := by
    unfold InRegion at ha
    bv_omega
  have ha2 : InRegion B 2097152 a := ha_sub.2
  have hdisj : ¬ InRegion lsLogFilterAddr 8 a := fun hlog => hb.disj_log_arena a hlog ha2
  have hum0 : (m₀.perm a).mapped = false := hb.unmapped_arena a ha2
  have hperm1 : (m₀.mapFresh lsLogFilterAddr 8 Perm.rw).perm a = m₀.perm a := by
    rw [Memory.perm_mapFresh]
    have hdec : decide ((a - lsLogFilterAddr).toNat < 8) = false := decide_eq_false hdisj
    simp only [hdec, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  have hperm2 : (baseMemPlaced B m₀).perm a = (m₀.mapFresh lsLogFilterAddr 8 Perm.rw).perm a := by
    unfold baseMemPlaced
    rw [Memory.perm_mapFresh]
    have hdec : decide ((a - B).toNat < 16384) = false :=
      decide_eq_false (by omega)
    simp only [hdec, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  change ((baseMemPlaced B m₀).perm a).mapped = false
  rw [hperm2, hperm1]
  exact hum0

def ValidMemPlaced (mBase : Memory) (_B : BitVec 64) (P : SepProp) : Prop :=
  ∃ m : Memory, m ⊨ P ∧ m.perm = mBase.perm ∧ mBase.KeepsFrozen m

theorem ValidMemPlaced.init [LibsignalPlacement] {B : BitVec 64} {m₀ : Memory}
    (hb : PlacedWitnessBase B m₀) :
    ValidMemPlaced (baseMemPlaced B m₀) B
      (memRegion (B + BitVec.ofNat 64 0) 16384 ∗ (lsLogFilterAddr ↦₆₄ 0#64)) := by
  have h0 := baseMemPlaced_satisfies_initial_regions hb
  have hlen : (bytesOf64 0#64).length = 8 := rfl
  have hle : (bytesOf64 0#64).length ≤ 2 ^ 64 := by decide
  have h0' : baseMemPlaced B m₀ ⊨
      memRegion lsLogFilterAddr (bytesOf64 0#64).length ∗ memRegion B 16384 := by
    rwa [hlen]
  refine ⟨(baseMemPlaced B m₀).writeBytes lsLogFilterAddr (bytesOf64 0#64), ?_,
    Memory.perm_writeBytes _ _ _,
    keepsFrozen_writeBytes_of_memRegion (bytesOf64 0#64) hle h0'⟩
  have hw := satisfies_writeBytes (bytesOf64 0#64) hle h0'
  rw [← pointsTo64_eq_pointsToBytes, sepConj_comm] at hw
  have hz : B + BitVec.ofNat 64 0 = B := BitVec.add_zero _
  rwa [hz]

theorem ValidMemPlaced.stepBytes {mBase : Memory} {B : BitVec 64} {off off' rem' rem : Nat}
    {R : SepProp}
    (k : Nat) (bs : List (BitVec 8)) (hlen : bs.length = k)
    (h : ValidMemPlaced mBase B (memRegion (B + BitVec.ofNat 64 off) rem ∗ R))
    (hc : decide (off + k = off' ∧ k + rem' = rem ∧ rem ≤ 2 ^ 64) = true := by decide) :
    ValidMemPlaced mBase B (memRegion (B + BitVec.ofNat 64 off') rem' ∗
      (((B + BitVec.ofNat 64 off) ↦ₛ bs) ∗ R)) := by
  rcases h with ⟨m, hsat, hperm, hfr⟩
  have ⟨_, hrem, hle⟩ := of_decide_eq_true hc
  have hbs_le : bs.length ≤ 2 ^ 64 := by omega
  rw [split_arena_region B hc, sepConj_assoc, ← hlen] at hsat
  refine ⟨m.writeBytes (B + BitVec.ofNat 64 off) bs, ?_,
    (Memory.perm_writeBytes _ _ _).trans hperm,
    hfr.trans (keepsFrozen_writeBytes_of_memRegion bs hbs_le hsat)⟩
  have hw := satisfies_writeBytes bs hbs_le hsat
  rwa [sepConj_left_comm] at hw

theorem ValidMemPlaced.step64 {mBase : Memory} {B : BitVec 64} {off off' rem' rem : Nat}
    {R : SepProp}
    (v : BitVec 64)
    (h : ValidMemPlaced mBase B (memRegion (B + BitVec.ofNat 64 off) rem ∗ R))
    (hc : decide (off + 8 = off' ∧ 8 + rem' = rem ∧ rem ≤ 2 ^ 64) = true := by decide) :
    ValidMemPlaced mBase B (memRegion (B + BitVec.ofNat 64 off') rem' ∗
      (((B + BitVec.ofNat 64 off) ↦₆₄ v) ∗ R)) := by
  rw [pointsTo64_eq_pointsToBytes]
  exact h.stepBytes 8 (bytesOf64 v) rfl hc

theorem ValidMemPlaced.step32 {mBase : Memory} {B : BitVec 64} {off off' rem' rem : Nat}
    {R : SepProp}
    (v : BitVec 32)
    (h : ValidMemPlaced mBase B (memRegion (B + BitVec.ofNat 64 off) rem ∗ R))
    (hc : decide (off + 4 = off' ∧ 4 + rem' = rem ∧ rem ≤ 2 ^ 64) = true := by decide) :
    ValidMemPlaced mBase B (memRegion (B + BitVec.ofNat 64 off') rem' ∗
      (((B + BitVec.ofNat 64 off) ↦₃₂ v) ∗ R)) := by
  rw [pointsTo32_eq_pointsToBytes]
  exact h.stepBytes 4 (bytesOf32 v) rfl hc

theorem ValidMemPlaced.stepSkip {mBase : Memory} {B : BitVec 64} {off off' rem' rem : Nat}
    {R : SepProp}
    (k : Nat)
    (h : ValidMemPlaced mBase B (memRegion (B + BitVec.ofNat 64 off) rem ∗ R))
    (hc : decide (off + k = off' ∧ k + rem' = rem ∧ rem ≤ 2 ^ 64) = true := by decide) :
    ValidMemPlaced mBase B (memRegion (B + BitVec.ofNat 64 off') rem' ∗
      (memRegion (B + BitVec.ofNat 64 off) k ∗ R)) := by
  rcases h with ⟨m, hsat, hperm, hfr⟩
  rw [split_arena_region B hc, sepConj_assoc, sepConj_left_comm] at hsat
  exact ⟨m, hsat, hperm, hfr⟩

theorem ValidMemPlaced.stepDrop {mBase : Memory} {B : BitVec 64} {off off' rem' rem : Nat}
    {R : SepProp}
    (k : Nat)
    (h : ValidMemPlaced mBase B (memRegion (B + BitVec.ofNat 64 off) rem ∗ R))
    (hc : decide (off + k = off' ∧ k + rem' = rem ∧ rem ≤ 2 ^ 64) = true := by decide) :
    ValidMemPlaced mBase B (memRegion (B + BitVec.ofNat 64 off') rem' ∗ R) := by
  rcases h with ⟨m, hsat, hperm, hfr⟩
  rw [split_arena_region B hc, sepConj_assoc] at hsat
  exact ⟨m, Satisfies.of_sep_right hsat, hperm, hfr⟩

private theorem placed_add_176_ne_zero {B : BitVec 64} (hwrap : B.toNat + 2097152 ≤ 2 ^ 64) :
    B + 176#64 ≠ 0 := by
  bv_omega

private theorem placed_add_280_ne_zero {B : BitVec 64} (hwrap : B.toNat + 2097152 ≤ 2 ^ 64) :
    B + 280#64 ≠ 0 := by
  bv_omega

private theorem placed_add_100000_ne_zero {B : BitVec 64} (hwrap : B.toNat + 2097152 ≤ 2 ^ 64) :
    B + 1048576#64 ≠ 0 := by
  bv_omega

private theorem placed_add_100000_mod_8 {B : BitVec 64}
    (halign : B.toNat % 4096 = 0) :
    (B + 1048576#64).toNat % 8 = 0 := by
  bv_omega

private theorem placed_add_16384_aligned {B : BitVec 64}
    (halign : B.toNat % 4096 = 0) :
    ((B + 16384#64) &&& 15#64 == 0#64) = true := by
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (15#64 : BitVec 64).toNat = 2 ^ 4 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_add]
  have h16 : (16384#64 : BitVec 64).toNat = 16384 := rfl
  have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
  rw [h16, h0]
  omega

theorem validMemPlaced_populated [LibsignalPlacement] {B : BitVec 64} {m₀ : Memory}
    (hb : PlacedWitnessBase B m₀) :
    ValidMemPlaced (baseMemPlaced B m₀) B
      (ratchetAt A₀ B (G0 B) st0 ∗
        ((B + 313#64) ↦ₛ pk0.bytes.toList) ∗ ((B + 345#64) ↦ₛ chainKeyBytes ck0) ∗
        memRegion (B + 381#64) 88 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        stackAt (B + 16384#64) cmkStack ∗ A₀.pool) := by
  have h0 : ValidMemPlaced (baseMemPlaced B m₀) B
      (memRegion (B + BitVec.ofNat 64 0) 16384 ∗ (lsLogFilterAddr ↦₆₄ 0#64)) :=
    ValidMemPlaced.init hb
  have h1 := h0.step64 (off' := 8) (rem' := 16376) 1#64
  have h2 := h1.step64 (off' := 16) (rem' := 16368) (B + 176#64)
  have h3 := h2.step64 (off' := 24) (rem' := 16360) 1#64
  have h4 := h3.stepBytes (off' := 128) (rem' := 16256) 104
    (optSenderChainBytes none (List.replicate 100 0#8)) (by simp [optSenderChainBytes, leBytes])
  have h5 := h4.stepBytes (off' := 160) (rem' := 16224) 32
    (keyToBytes32 0#256) (by simp [keyToBytes32])
  have h6 := h5.step64 (off' := 168) (rem' := 16216) (BitVec.ofNat 64 25000)
  have h7 := h6.step32 (off' := 172) (rem' := 16212) 0#32
  have h8 := h7.stepSkip (off' := 176) (rem' := 16208) 4
  have h9 := h8.step64 (off' := 184) (rem' := 16200) 33#64
  have h10 := h9.step64 (off' := 192) (rem' := 16192) (B + 280#64)
  have h11 := h10.step64 (off' := 200) (rem' := 16184) 33#64
  have h12 := h11.step64 (off' := 208) (rem' := 16176) 0#64
  have h13 := h12.step64 (off' := 216) (rem' := 16168) 1#64
  have h14 := h13.step64 (off' := 224) (rem' := 16160) 0#64
  have h15 := h14.step64 (off' := 232) (rem' := 16152) 0#64
  have h16 := h15.step64 (off' := 240) (rem' := 16144) 8#64
  have h17 := h16.step64 (off' := 248) (rem' := 16136) 0#64
  have h18 := h17.step64 (off' := 256) (rem' := 16128) optChainKeyNone
  have h19 := h18.stepSkip (off' := 280) (rem' := 16104) 24
  have h20 := h19.stepBytes (off' := 313) (rem' := 16071) 33
    pk0.serialize pk0_serialize_length
  have h21 := h20.stepBytes (off' := 345) (rem' := 16039) 32
    pk0.bytes.toList (by simp [pk0])
  have h22 := h21.stepBytes (off' := 381) (rem' := 16003) 36
    (chainKeyBytes ck0) (by simp [chainKeyBytes, keyToBytes32, leBytes])
  have h23 := h22.stepSkip (off' := 469) (rem' := 15915) 88
  have h24 := h23.stepDrop (off' := 8192) (rem' := 8192) 7723
  rcases h24 with ⟨m, hsat, hperm, hfr⟩
  refine ⟨m, ?_, hperm, hfr⟩
  have hsp_eq : B + 16384#64 - BitVec.ofNat 64 cmkStack = B + BitVec.ofNat 64 8192 := by
    change B + 16384#64 - 8192#64 = B + 8192#64
    bv_omega
  rw [ratchetAt_G0_st0_eq B (placed_add_176_ne_zero hb.wrap) (placed_add_280_ne_zero hb.wrap)]
  unfold stackAt cmkStack A₀
  rw [hsp_eq]
  simp only [BitVec.add_zero] at hsat ⊢
  refine Eq.mp (congrArg (fun P => m ⊨ P) ?_) hsat
  ac_rfl

/-- Relocatable non-vacuity statement for `cmkPlacedRoSpec`. -/
def CmkPlacedNonVacStmt [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (B : BitVec 64) (m₀ : Memory) : Prop :=
  PlacedWitnessBase B m₀ →
    ∃ (A : RustAlloc) (H : LibsignalHooks),
      CmkAllocHooks A H ∧
      H "memmove" = some hookMemmove ∧
      H "memcpy" = some hookMemcpy ∧
      H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook ∧
      H lsHandleAllocErrorSymNonVac = some Rust.panicked ∧
      HookSat H lsRustReallocSym (rustReallocSpec A) ∧
      HookSat H lsRustNoAllocShimSym LibsignalTripleRatchet.noAllocShimSpec ∧
      AllocSucceedsWithRoomPlaced A H ∧
      ∃ (x : ConsumeMessageKeyGhost) (s0 : State), s0.status = .Running ∧ s0.spAligned = true ∧
        (s0.mem ⊨ (cmkPlacedRoSpec F A).pre x s0) ∧
        (∃ p : BitVec 64, p ≠ 0 ∧ p.toNat % 8 = 0 ∧ Unmapped s0.mem p (2 ^ 20)) ∧
        x.counter.toNat > x.ck.index.toNat + 1 ∧
        (∃ i, x.st.findReceiverChainIndex x.their = some i ∧
          ∃ (h : i < x.G.chains.length), x.G.chains[i].mkCap = 0) ∧
        ∃ k, (x.model F).1 = .ok k

theorem cmkPlacedNonVacStmt_proof [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (B : BitVec 64) (m₀ : Memory) :
    CmkPlacedNonVacStmt F B m₀ := by
  intro hb
  obtain ⟨m, hsat, hperm, hfr⟩ := validMemPlaced_populated hb
  refine ⟨A₀, witnessHooksPlaced, witnessHooksPlaced_cmkAllocHooks,
    witnessHooksPlaced_memmove_eq, witnessHooksPlaced_memcpy_eq,
    witnessHooksPlaced_blackBox, witnessHooksPlaced_handleAllocError_eq,
    witnessHooksPlaced_rustRealloc, witnessHooksPlaced_noAllocShim,
    witnessHooksPlaced_succeedsWithRoom, witnessGhost B, ?_⟩
  let s0 : State :=
    { regs := ⟨fun i =>
        if i = 0#5 then B
        else if i = 1#5 then B + 313#64
        else if i = 2#5 then B + 345#64
        else if i = 3#5 then 5#64
        else if i = 4#5 then 2#64
        else if i = 8#5 then B + 381#64
        else 0#64⟩
      sp := B + 16384#64
      mem := m
      status := .Running }
  have hk_all : m₀.KeepsFrozen m := (baseMemPlaced_keepsFrozen B m₀).trans hfr
  refine ⟨s0, rfl, placed_add_16384_aligned hb.aligned, ?_, ?_,
    witnessGhost_counter_gt B, ⟨0, witnessGhost_findIdx B⟩, witnessGhost_model_ok F B⟩
  · dsimp only [cmkPlacedRoSpec, cmkPlacedSpec, withLsCodeLoaded, Obj.MultiPlacedLib.withCodeLoaded]
    rw [sepConj_comm _ ⌜LibsignalRoLoaded lsmpl s0.mem⌝, satisfies_pure_sepConj]
    refine ⟨libsignalRoLoaded_of_keepsFrozen hb.roLoaded hk_all, ?_⟩
    rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl s0.mem⌝, satisfies_pure_sepConj]
    refine ⟨hb.codeLoaded.of_keepsFrozen hk_all, ?_⟩
    rw [satisfies_pure_sepConj]
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, hsat⟩
  · refine ⟨B + 1048576#64, placed_add_100000_ne_zero hb.wrap,
      placed_add_100000_mod_8 hb.aligned, ?_⟩
    intro a ha
    have hunm := baseMemPlaced_unmapped_arena hb a ha
    change (m.perm a).mapped = false
    rw [hperm]
    exact hunm

end CryptoVerification.LibsignalSession.NonVacuityWitness
