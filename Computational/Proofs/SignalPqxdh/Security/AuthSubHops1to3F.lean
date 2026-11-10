/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhB
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# PQXDH authentication sub-hop 1 (`G3.5 → G3.6`, `RootKdfRO`): cutoff hybrid

Defines `rootRoCache` collision bounds, the parameterized `G3.5 ↔ G3.6` cutoff experiment
`authRkCutoffExp`, and its `SlotM` pre-sampling equivalence `evalDist_preSample_authRk_eq_cutoff`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped ENNReal BigOperators
open OracleComp OracleSpec MeasureTheory
open SignalPqxdh SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh

namespace SignalPqxdh.Security.AuthSubHops1to3

/-! ## `RootKdfRO` cache helpers and collision bound -/

def filterOutRk (rkStar : Bytes) (cache : List ((Bytes × Bytes) × (Bytes × Bytes))) :
    List ((Bytes × Bytes) × (Bytes × Bytes)) :=
  cache.filter (fun e => e.1.1 != rkStar)

def cacheHasRk (rkStar : Bytes) (cache : List ((Bytes × Bytes) × (Bytes × Bytes))) : Bool :=
  cache.any (fun e => e.1.1 == rkStar)

theorem find?_eq_find?_filterOutRk (rkStar rk dh : Bytes)
    (hNe : (rk == rkStar) = false) :
    ∀ (cache : List ((Bytes × Bytes) × (Bytes × Bytes))),
      cache.find? (fun (inp, _) => inp == (rk, dh)) =
        (filterOutRk rkStar cache).find? (fun (inp, _) => inp == (rk, dh))
  | [] => rfl
  | ((rk', dh'), out) :: rest => by
    rw [filterOutRk, List.filter_cons]
    by_cases hEq : (rk' != rkStar) = true
    · simp only [hEq, ↓reduceIte, List.find?]
      rw [← filterOutRk, find?_eq_find?_filterOutRk rkStar rk dh hNe rest]
    · simp only [hEq, Bool.false_eq_true, ↓reduceIte]
      have hrk' : rk' = rkStar := by revert hEq; simp
      have hne_pair : ((rk', dh') == (rk, dh)) = false := by
        rw [hrk', beq_eq_false_iff_ne]
        intro heq
        rcases Prod.mk.inj heq with ⟨rfl, _⟩
        revert hNe; simp
      rw [List.find?, hne_pair, ← filterOutRk]
      exact find?_eq_find?_filterOutRk rkStar rk dh hNe rest

theorem cacheHasRk_evalRootKdfOrRo_self (P : Primitives) (rk dh : Bytes)
    (cache : List ((Bytes × Bytes) × (Bytes × Bytes))) :
    ∀ x ∈ support (evalRootKdfOrRo true P cache rk dh),
      cacheHasRk rk x.2 = true := by
  intro x hx
  unfold evalRootKdfOrRo at hx
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hx
  cases hfind : cache.find? (fun (inp, _) => inp == (rk, dh)) with
  | some p =>
    rcases p with ⟨⟨rk', dh'⟩, out⟩
    rw [hfind] at hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx
    have hmem := List.find?_some hfind
    have hin : ((rk', dh'), out) ∈ cache := List.mem_of_find?_eq_some hfind
    simp only [beq_iff_eq] at hmem
    rcases Prod.mk.inj hmem with ⟨rfl, rfl⟩
    unfold cacheHasRk
    rw [List.any_eq_true]
    exact ⟨((rk', dh'), out), hin, by simp⟩
  | none =>
    rw [hfind] at hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨rk1, _, ck1, _, rfl⟩
    unfold cacheHasRk
    simp

theorem evalRootKdfOrRo_length_le (P : Primitives) (rk dh : Bytes)
    (cache : List ((Bytes × Bytes) × (Bytes × Bytes))) :
    ∀ x ∈ support (evalRootKdfOrRo true P cache rk dh),
      x.2.length ≤ cache.length + 1 := by
  intro x hx
  unfold evalRootKdfOrRo at hx
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hx
  cases hfind : cache.find? (fun (inp, _) => inp == (rk, dh)) with
  | some p =>
    rcases p with ⟨_, out⟩
    rw [hfind] at hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx; dsimp only; omega
  | none =>
    rw [hfind] at hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨rk1, _, ck1, _, rfl⟩
    simp

theorem RelProbUpToBad.bind_right {β α : Type} {R : α → α → Prop} {bad : α → Bool}
    (mx : ProbComp β) {m5 : ProbComp α} {f6 : β → ProbComp α}
    (h : ∀ b, RelProbUpToBad R bad m5 (f6 b)) :
    RelProbUpToBad R bad m5 (mx >>= f6) := by
  refine ⟨fun w5 w6 hw5 hw6 hle => ?_, fun w6 w5 hw6 hle => ?_⟩
  · rw [probExpect_bind]
    calc probExpect m5 w5
        = probExpect mx (fun _ => probExpect m5 w5) := (probExpect_const mx _).symm
      _ ≤ probExpect mx (fun b => probExpect (f6 b) w6) :=
          probExpect_mono_of_support mx _ _ (fun b _ => (h b).1 w5 w6 hw5 hw6 hle)
  · rw [probExpect_bind]
    calc probExpect mx (fun b => probExpect (f6 b) w6)
        ≤ probExpect mx (fun _ => probExpect m5 w5) :=
          probExpect_mono_of_support mx _ _ (fun b _ => (h b).2 w6 w5 hw6 hle)
      _ = probExpect m5 w5 := probExpect_const mx _

theorem RelProbUpToBad.bind_const_right {β α : Type} {R : α → α → Prop} {bad : α → Bool}
    (mx : ProbComp β) {m5 m6 : ProbComp α}
    (h : RelProbUpToBad R bad m5 m6) :
    RelProbUpToBad R bad m5 (mx >>= fun _ => m6) := by
  refine ⟨fun w5 w6 hw5 hw6 hle => ?_, fun w6 w5 hw6 hle => ?_⟩
  · rw [probExpect_bind, probExpect_const]
    exact h.1 w5 w6 hw5 hw6 hle
  · rw [probExpect_bind, probExpect_const]
    exact h.2 w6 w5 hw6 hle

def bytesToWord256Nat : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * bytesToWord256Nat bs

def encodeLEBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, x => UInt8.ofNat (x % 256) :: encodeLEBytes n (x / 256)

theorem encodeLEBytes_succ (n x : Nat) :
    encodeLEBytes (n + 1) x = UInt8.ofNat (x % 256) :: encodeLEBytes n (x / 256) := rfl

theorem bytesToWord256Nat_encodeLEBytes : ∀ (n x : Nat), x < 256 ^ n →
    bytesToWord256Nat (encodeLEBytes n x) = x
  | 0, x, hx => by simp at hx; simp [encodeLEBytes, bytesToWord256Nat, hx]
  | n + 1, x, hx => by
    rw [encodeLEBytes_succ, bytesToWord256Nat]
    have hdiv : x / 256 < 256 ^ n := by rw [pow_succ'] at hx; omega
    rw [bytesToWord256Nat_encodeLEBytes n (x / 256) hdiv]
    have hmod : (UInt8.ofNat (x % 256)).toNat = x % 256 := by simp
    omega

theorem word256ToBytes_eq_encodeLEBytes (w : BitVec 256) :
    word256ToBytes w = encodeLEBytes 32 w.toNat := by
  unfold word256ToBytes
  have hgen : ∀ (k : Nat) (x : Nat),
      List.ofFn (fun (i : Fin k) => UInt8.ofNat ((x >>> (8 * i.val)) % 256)) =
        encodeLEBytes k x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [List.ofFn_succ, encodeLEBytes_succ]
      congr 1
      rw [← ih (x / 256)]
      congr 1
      funext i
      simp only [Fin.val_succ, Nat.shiftRight_eq_div_pow]
      rw [Nat.div_div_eq_div_mul]
      have hpow : 256 * 2 ^ (8 * i.val) = 2 ^ (8 * (i.val + 1)) := by
        rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_add]
        congr 1; ring
      rw [hpow]
  exact hgen 32 w.toNat

theorem word256ToBytes_injective : Function.Injective word256ToBytes := by
  intro w1 w2 h
  rw [word256ToBytes_eq_encodeLEBytes, word256ToBytes_eq_encodeLEBytes] at h
  have h1 := bytesToWord256Nat_encodeLEBytes 32 w1.toNat (by have := w1.isLt; simpa using this)
  have h2 := bytesToWord256Nat_encodeLEBytes 32 w2.toNat (by have := w2.isLt; simpa using this)
  apply BitVec.eq_of_toNat_eq
  rw [← h1, ← h2, h]

theorem evalDist_sampleBytes32_beq_le (target : Bytes) :
    𝒟[sampleBytes32 >>= fun rk => pure (target == rk)] {true} ≤
      ENNReal.ofReal (1 / (2 : ℝ) ^ 256) := by
  unfold sampleBytes32
  have hmap : ((word256ToBytes <$> ($ᵗ BitVec 256)) >>= fun rk => pure (target == rk)) =
      (fun x : BitVec 256 => target == word256ToBytes x) <$> ($ᵗ BitVec 256) := by
    simp [map_eq_bind_pure_comp]
  rw [hmap, evalDist_map ($ᵗ BitVec 256) Measurable.of_discrete,
    Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true),
    SampleableType.evalDist_bitVec]
  have hpre : ((fun x : BitVec 256 => target == word256ToBytes x) ⁻¹' {true}) =
      {x : BitVec 256 | target == word256ToBytes x} := by
    ext x; simp
  rw [hpre, ProbabilityTheory.uniformOn_univ_apply_setOf]
  have hcard : (Finset.filter (fun x : BitVec 256 =>
      (target == word256ToBytes x) = true) Finset.univ).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, beq_iff_eq] at ha hb
    exact word256ToBytes_injective (ha.symm.trans hb)
  have hinv : (1 : ℝ≥0∞) / (Fintype.card (BitVec 256) : ℝ≥0∞) =
      ENNReal.ofReal (1 / (2 : ℝ) ^ 256) := by
    rw [Fintype.card_bitVec, div_eq_mul_inv, one_mul, one_div,
        ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_ofNat]
    simp; norm_num
  rw [← hinv]
  exact ENNReal.div_le_div_right (by exact_mod_cast hcard) _

theorem evalDist_sampleBytes32_any_le :
    ∀ (L : List Bytes),
      𝒟[sampleBytes32 >>= fun rk => pure (L.any (fun x => x == rk))] {true} ≤
        (L.length : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 256)
  | [] => by simp
  | t :: ts => by
    have h_le :
        𝒟[sampleBytes32 >>= fun rk => pure ((t :: ts).any (fun x => x == rk))] {true} ≤
        𝒟[sampleBytes32 >>= fun rk => pure (t == rk)] {true} +
        𝒟[sampleBytes32 >>= fun rk => pure (ts.any (fun x => x == rk))] {true} := by
      rw [evalDist_bind_true_eq_probExpect, evalDist_bind_true_eq_probExpect,
          evalDist_bind_true_eq_probExpect]
      let _ : MeasurableSpace Bytes := ⊤
      have _ : DiscreteMeasurableSpace Bytes := ⟨fun _ => trivial⟩
      unfold probExpect
      rw [← MeasureTheory.lintegral_add_left Measurable.of_discrete]
      apply MeasureTheory.lintegral_mono
      intro rk
      simp only [List.any_cons]
      by_cases h1 : (t == rk) = true
      · simp [h1]
      · simp [h1]
    calc 𝒟[sampleBytes32 >>= fun rk => pure ((t :: ts).any (fun x => x == rk))] {true}
        ≤ 𝒟[sampleBytes32 >>= fun rk => pure (t == rk)] {true} +
          𝒟[sampleBytes32 >>= fun rk => pure (ts.any (fun x => x == rk))] {true} := h_le
      _ ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 256) +
          (ts.length : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 256) :=
        add_le_add (evalDist_sampleBytes32_beq_le t) (evalDist_sampleBytes32_any_le ts)
      _ = ((t :: ts).length : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 256) := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring

theorem evalDist_sampleBytes32_cacheHasRk_le
    (cache : List ((Bytes × Bytes) × (Bytes × Bytes))) :
    𝒟[sampleBytes32 >>= fun rk => pure (cacheHasRk rk cache)] {true} ≤
      (cache.length : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 256) := by
  have heq : (sampleBytes32 >>= fun rk => pure (cacheHasRk rk cache)) =
      (sampleBytes32 >>= fun rk => pure ((cache.map (fun e => e.1.1)).any (fun x => x == rk))) := by
    congr 1; funext rk; congr 1
    unfold cacheHasRk
    rw [List.any_map]
    rfl
  rw [heq]
  simpa using evalDist_sampleBytes32_any_le (cache.map (fun e => e.1.1))

theorem not_mem_of_contains_false {α : Type} [BEq α] [LawfulBEq α]
    {x : α} {xs : List α} (h : xs.contains x = false) : x ∉ xs := by
  intro hm
  have hc : xs.contains x = true := List.contains_iff_mem.mpr hm
  rw [h] at hc; cases hc

theorem eq_of_mem_of_hasDuplicateBytes_map_false {α : Type} (f : α → Bytes) :
    ∀ {L : List α}, hasDuplicateBytes (L.map f) = false →
      ∀ {x y : α}, x ∈ L → y ∈ L → f x = f y → x = y
  | [], _, _, _, hx, _, _ => nomatch hx
  | a :: as, hdup, x, y, hx, hy, hfeq => by
    simp only [List.map_cons, hasDuplicateBytes, Bool.or_eq_false_iff] at hdup
    have hnot : f a ∉ as.map f := not_mem_of_contains_false hdup.1
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact False.elim (hnot (hfeq ▸ List.mem_map_of_mem hy'))
    · exact False.elim (hnot (hfeq.symm ▸ List.mem_map_of_mem hx'))
    · exact eq_of_mem_of_hasDuplicateBytes_map_false f hdup.2 hx' hy' hfeq

/-! ## `G3.5 ↔ G3.6` cutoff execution and `SlotM` bridge -/

def getRkAtSlot (idx slotIdx : Nat) : SlotM Bytes Bytes :=
  if slotIdx == idx then
    SlotM.getSlot sampleBytes32
  else
    liftM sampleBytes32

theorem slotComp_getRkAtSlot_bind_liftM {α : Type} (idx slotIdx : Nat) (f : Bytes → ProbComp α) :
    SlotM.SlotComp sampleBytes32 (getRkAtSlot idx slotIdx >>= fun rk => liftM (f rk)) := by
  unfold getRkAtSlot
  split
  · exact (SlotM.SlotComp.getSlot sampleBytes32).bind
      (fun rk => SlotM.SlotComp.liftComp sampleBytes32 (f rk))
  · exact (SlotM.SlotComp.liftComp sampleBytes32 _).bind
      (fun rk => SlotM.SlotComp.liftComp sampleBytes32 (f rk))

theorem run'_getRkAtSlot_bind_liftM_some {α : Type}
    (idx slotIdx : Nat) (rkStar : Bytes) (f : Bytes → ProbComp α) :
    (getRkAtSlot idx slotIdx >>= fun rk => (liftM (f rk) : SlotM Bytes α)).run' (some rkStar) =
      ((if slotIdx == idx then pure rkStar else sampleBytes32) >>= f) := by
  unfold getRkAtSlot
  split
  · rw [SlotM.run'_getSlot_bind_some, SlotM.run'_liftComp, pure_bind]
  · rw [SlotM.run'_liftComp_bind]
    simp only [SlotM.run'_liftComp]

theorem run'_getRkAtSlot_bind_liftM_none {α : Type}
    (idx slotIdx : Nat) (f : Bytes → ProbComp α) :
    (getRkAtSlot idx slotIdx >>= fun rk => (liftM (f rk) : SlotM Bytes α)).run' none =
      (sampleBytes32 >>= f) := by
  unfold getRkAtSlot
  split
  · rw [SlotM.run'_getSlot_bind_none]
    simp only [SlotM.run'_liftComp]
  · rw [SlotM.run'_liftComp_bind]
    simp only [SlotM.run'_liftComp]

theorem SlotFireAtAuth.getRkAtSlot_bind_liftM {S : Setup} (idx slotIdx : Nat)
    (f : Bytes → ProbComp (AuthResponse × AuthHybridStateFixed S))
    (hFire : slotIdx = idx → ∀ rk, ∀ x ∈ support (f rk), authSlotFired S idx x.2 = true) :
    SlotFireAtAuth S idx (getRkAtSlot idx slotIdx >>= fun rk => liftM (f rk)) := by
  intro y hy hSome
  unfold getRkAtSlot at hy
  by_cases hEq : (slotIdx == idx) = true
  · simp only [hEq, ↓reduceIte, StateT.run_bind, SlotM.getSlot_run_none, bind_assoc, pure_bind,
      StateT.run_monadLift, monadLift_self,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨rk, _, x, hx, rfl⟩
    rw [beq_iff_eq] at hEq
    exact hFire hEq rk x hx
  · simp only [hEq, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨rk, _, x, _, rfl⟩
    cases hSome

def finishAuthSendAfterRk {S : Setup} (P : Primitives) (useIdealRkAt : Nat → Bool)
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk dhRatchet ck pk : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (rk : Bytes) :
    ProbComp (AuthResponse × AuthHybridStateFixed S) := do
  let st := hst.toAuthHybridState.base
  let drKey : DRKey := { rootKey := rk, chainKey := ck, pqrKey := pk }
  let ((rk1, ck1_0), rootRoCache') ←
    if useIdealRkAt (sessionSlotIndex sid) then do
      let r ← sampleBytes32
      let c ← sampleBytes32
      pure ((r, c), st.rootRoCache)
    else
      evalRootKdfOrRo true P st.rootRoCache rk dhRatchet
  let mkSeed := P.chainKdfSeed ck1_0
  let ck1_1 := P.chainKdfNext ck1_0
  let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
  let isFreshPeer : Bool :=
    match peerPrincipal? with
    | some (_, pEntry) => !pEntry.corrupted
    | none             => false
  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
  let aeadCt := P.aeadEnc deriveMessageKeys ad msgPlain
  let (resp, hst') := finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
    spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain st.roCache rootRoCache'
    hst.toAuthHybridState
  pure (resp, { toAuthHybridState := hst', recvCount := hst.recvCount })

def authRkSendWith (S : Setup) (P : Primitives)
    (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) : ProbComp (AuthResponse × AuthHybridStateFixed S) := do
  let st := hst.toAuthHybridState.base
  if st.hasWonAuth then
    pure (.noneResp, hst)
  else if m0.length != m1.length then
    pure (.noneResp, hst)
  else if st.usedSendSessions.contains sid then
    pure (.noneResp, hst)
  else
    match st.principals.find? (fun (i, _) => i == u.val) with
    | none => pure (.noneResp, hst)
    | some (_, uEntry) =>
      let peerPrincipal? := findHonestPrincipal P st.principals bundle.ikB
      let isFreshPeer : Bool :=
        match peerPrincipal? with
        | some (_, pEntry) => !pEntry.corrupted
        | none             => false
      if !isFreshPeer && m0 != m1 then
        pure (.noneResp, hst)
      else
        let msgPlain := if isFreshPeer then (if st.secb then m1 else m0) else m0
        if !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle then
          pure (.noneResp, hst)
        else
          let ekASk ← sampleScalar32
          let kemCoins ← sampleCoins32
          let ephASk ← sampleScalar32
          let spqrCoins ← sampleCoins32
          let sigPkB := resolveSigPk P st.principals bundle.ikB
          if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
               P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig) then
            pure (.noneResp, hst)
          else
            match P.kemEncaps bundle.pqspkB kemCoins with
            | none => pure (.noneResp, hst)
            | some (ss, kemCt) =>
              let ekAPk := P.x25519Base ekASk
              let ephAPk := P.x25519Base ephASk
              let dhRatchet := P.x25519 ephASk bundle.spkB
              let prov :=
                checkBundleProvenanceExact P st.principals st.spkBundles st.opkEntries bundle
              let spkHonIdeal := checkBundleSpkHonIdeal P st.principals st.spkBundles bundle
              let isIdealSend : Bool :=
                isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && prov.2.2)
              if isIdealSend then
                let ck ← sampleBytes32
                let pk ← sampleBytes32
                match P.spqrInitSend pk spqrCoins with
                | none => pure (.noneResp, hst)
                | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
                  let rk ← sampRkAt (sessionSlotIndex sid)
                  finishAuthSendAfterRk P useIdealRkAt sid uEntry peerPrincipal? bundle m0 m1
                    ekASk ekAPk ss kemCt ephASk ephAPk dhRatchet ck pk spqrSalt? pqRatchetMsg
                    msgPlain hst rk
              else
                let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
                let dh2 := P.x25519 ekASk bundle.ikB
                let dh3 := P.x25519 ekASk bundle.spkB
                let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
                let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
                let (drKey, roCache') ← evalHkdfOrRo true P st.roCache secrets
                let ((rk1, ck1_0), rootRoCache') ←
                  evalRootKdfOrRo true P st.rootRoCache drKey.rootKey dhRatchet
                let mkSeed := P.chainKdfSeed ck1_0
                let ck1_1 := P.chainKdfNext ck1_0
                match P.spqrInitSend drKey.pqrKey spqrCoins with
                | none => pure (.noneResp, hst)
                | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
                  let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
                  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
                  let aeadCt := P.aeadEnc deriveMessageKeys ad msgPlain
                  let (resp, hst') :=
                    finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
                    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
                    spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache'
                    hst.toAuthHybridState
                  pure (resp, { toAuthHybridState := hst', recvCount := hst.recvCount })

def authRkSendSlot (S : Setup) (P : Primitives) (idx : Nat) (useIdealRkAt : Nat → Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) : SlotM Bytes (AuthResponse × AuthHybridStateFixed S) := do
  let st := hst.toAuthHybridState.base
  if st.hasWonAuth then
    pure (.noneResp, hst)
  else if m0.length != m1.length then
    pure (.noneResp, hst)
  else if st.usedSendSessions.contains sid then
    pure (.noneResp, hst)
  else
    match st.principals.find? (fun (i, _) => i == u.val) with
    | none => pure (.noneResp, hst)
    | some (_, uEntry) =>
      let peerPrincipal? := findHonestPrincipal P st.principals bundle.ikB
      let isFreshPeer : Bool :=
        match peerPrincipal? with
        | some (_, pEntry) => !pEntry.corrupted
        | none             => false
      if !isFreshPeer && m0 != m1 then
        pure (.noneResp, hst)
      else
        let msgPlain := if isFreshPeer then (if st.secb then m1 else m0) else m0
        if !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle then
          pure (.noneResp, hst)
        else
          let ekASk ← liftM sampleScalar32
          let kemCoins ← liftM sampleCoins32
          let ephASk ← liftM sampleScalar32
          let spqrCoins ← liftM sampleCoins32
          let sigPkB := resolveSigPk P st.principals bundle.ikB
          if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
               P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig) then
            pure (.noneResp, hst)
          else
            match P.kemEncaps bundle.pqspkB kemCoins with
            | none => pure (.noneResp, hst)
            | some (ss, kemCt) =>
              let ekAPk := P.x25519Base ekASk
              let ephAPk := P.x25519Base ephASk
              let dhRatchet := P.x25519 ephASk bundle.spkB
              let prov :=
                checkBundleProvenanceExact P st.principals st.spkBundles st.opkEntries bundle
              let spkHonIdeal := checkBundleSpkHonIdeal P st.principals st.spkBundles bundle
              let isIdealSend : Bool :=
                isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && prov.2.2)
              if isIdealSend then
                let ck ← liftM sampleBytes32
                let pk ← liftM sampleBytes32
                match P.spqrInitSend pk spqrCoins with
                | none => pure (.noneResp, hst)
                | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
                  let rk ← getRkAtSlot idx (sessionSlotIndex sid)
                  liftM (finishAuthSendAfterRk P useIdealRkAt sid uEntry peerPrincipal? bundle m0 m1
                    ekASk ekAPk ss kemCt ephASk ephAPk dhRatchet ck pk spqrSalt? pqRatchetMsg
                    msgPlain hst rk)
              else
                let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
                let dh2 := P.x25519 ekASk bundle.ikB
                let dh3 := P.x25519 ekASk bundle.spkB
                let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
                let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
                let (drKey, roCache') ← liftM (evalHkdfOrRo true P st.roCache secrets)
                let ((rk1, ck1_0), rootRoCache') ←
                  liftM (evalRootKdfOrRo true P st.rootRoCache drKey.rootKey dhRatchet)
                let mkSeed := P.chainKdfSeed ck1_0
                let ck1_1 := P.chainKdfNext ck1_0
                match P.spqrInitSend drKey.pqrKey spqrCoins with
                | none => pure (.noneResp, hst)
                | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
                  let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
                  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
                  let aeadCt := P.aeadEnc deriveMessageKeys ad msgPlain
                  let (resp, hst') :=
                    finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
                    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
                    spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache'
                    hst.toAuthHybridState
                  pure (resp, { toAuthHybridState := hst', recvCount := hst.recvCount })

def finishAuthRecvRk {S : Setup} (P : Primitives) (msg : PreKeyMsg) (prep : PreparedAuthRecv S)
    (drKey : DRKey) (rk1 ck1_0 : Bytes)
    (roCache' : List (Bytes × DRKey))
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (recvCount' : Nat) : AuthResponse × AuthHybridStateFixed S :=
  let mkSeed := P.chainKdfSeed ck1_0
  let ck1_1 := P.chainKdfNext ck1_0
  let res? :=
    match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
    | none => none
    | some (_pqrStB, spqrSalt?) =>
      let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
      let ad := firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
      match P.aeadDec deriveMessageKeys ad msg.aeadCt with
      | none => none
      | some pt => some (drKey, rk1, ck1_1, pt, roCache', rootRoCache')
  let (resp, hst') := prep.finish res?
  (resp, { toAuthHybridState := hst', recvCount := recvCount' })

def finishAuthRecvUnmatchedAfterRk {S : Setup} (P : Primitives) (useIdealRkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep : PreparedAuthRecv S) (rSlot recvCount' : Nat) (rk : Bytes) :
    ProbComp (AuthResponse × AuthHybridStateFixed S) := do
  let st := prep.hstDec.base
  let ck ← sampleBytes32
  let pk ← sampleBytes32
  let drKey : DRKey := { rootKey := rk, chainKey := ck, pqrKey := pk }
  let ((rk1, ck1_0), rootRoCache') ←
    if useIdealRkAt rSlot then do
      let r ← sampleBytes32
      let c ← sampleBytes32
      pure ((r, c), st.rootRoCache)
    else
      evalRootKdfOrRo true P st.rootRoCache rk prep.dhRatchet
  pure (finishAuthRecvRk P msg prep drKey rk1 ck1_0 st.roCache rootRoCache' recvCount')

def authRkRecvWith (S : Setup) (P : Primitives)
    (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) : ProbComp (AuthResponse × AuthHybridStateFixed S) := do
  let recvCount' := hst.recvCount + 1
  match prep? with
  | none => pure (.noneResp, { hst with recvCount := recvCount' })
  | some prep =>
    let st := prep.hstDec.base
    let useIdealBranch : Bool := prep.matchedSess?.isSome || prep.isUncorruptedHonestSender
    if useIdealBranch then
      match prep.matchedSess? with
      | some s =>
        let ((rk1, ck1_0), rootRoCache') ←
          if useIdealRkAt (sessionSlotIndex s.sid) then
            if prep.sameEph then
              pure ((s.rk1, s.ck1_0), st.rootRoCache)
            else do
              let r ← sampleBytes32
              let c ← sampleBytes32
              pure ((r, c), st.rootRoCache)
          else
            evalRootKdfOrRo true P st.rootRoCache s.drKey.rootKey prep.dhRatchet
        pure (finishAuthRecvRk P msg prep s.drKey rk1 ck1_0 st.roCache rootRoCache' recvCount')
      | none =>
        let rSlot := S.N_send_tot + hst.recvCount
        let rk ← sampRkAt rSlot
        finishAuthRecvUnmatchedAfterRk P useIdealRkAt msg prep rSlot recvCount' rk
    else
      let (drKey, roCache') ← evalHkdfOrRo true P st.roCache prep.secrets
      let ((rk1, ck1_0), rootRoCache') ←
        evalRootKdfOrRo true P st.rootRoCache drKey.rootKey prep.dhRatchet
      pure (finishAuthRecvRk P msg prep drKey rk1 ck1_0 roCache' rootRoCache' recvCount')

def authRkRecvSlot (S : Setup) (P : Primitives) (idx : Nat) (useIdealRkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) : SlotM Bytes (AuthResponse × AuthHybridStateFixed S) := do
  let recvCount' := hst.recvCount + 1
  match prep? with
  | none => pure (.noneResp, { hst with recvCount := recvCount' })
  | some prep =>
    let st := prep.hstDec.base
    let useIdealBranch : Bool := prep.matchedSess?.isSome || prep.isUncorruptedHonestSender
    if useIdealBranch then
      match prep.matchedSess? with
      | some s =>
        liftM (do
          let ((rk1, ck1_0), rootRoCache') ←
            if useIdealRkAt (sessionSlotIndex s.sid) then
              if prep.sameEph then
                pure ((s.rk1, s.ck1_0), st.rootRoCache)
              else do
                let r ← sampleBytes32
                let c ← sampleBytes32
                pure ((r, c), st.rootRoCache)
            else
              evalRootKdfOrRo true P st.rootRoCache s.drKey.rootKey prep.dhRatchet
          pure (finishAuthRecvRk P msg prep s.drKey rk1 ck1_0 st.roCache rootRoCache' recvCount'))
      | none =>
        let rSlot := S.N_send_tot + hst.recvCount
        let rk ← getRkAtSlot idx rSlot
        liftM (finishAuthRecvUnmatchedAfterRk P useIdealRkAt msg prep rSlot recvCount' rk)
    else
      liftM (do
        let (drKey, roCache') ← evalHkdfOrRo true P st.roCache prep.secrets
        let ((rk1, ck1_0), rootRoCache') ←
          evalRootKdfOrRo true P st.rootRoCache drKey.rootKey prep.dhRatchet
        pure (finishAuthRecvRk P msg prep drKey rk1 ck1_0 roCache' rootRoCache' recvCount'))

def authRkStepWith (S : Setup) (P : Primitives)
    (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    ProbComp ((authSpec S).Range q × AuthHybridStateFixed S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.noneResp, hst)
    else authRkSendWith S P sampRkAt useIdealRkAt (.sendOPK u i) u bundle m0 m1 hst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.noneResp, hst)
    else authRkSendWith S P sampRkAt useIdealRkAt (.sendNoOPK u i) u bundle m0 m1 hst
  | .recvOPK k j o msg =>
    authRkRecvWith S P sampRkAt useIdealRkAt msg
      (prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState) hst
  | .recvNoOPK k j l msg =>
    authRkRecvWith S P sampRkAt useIdealRkAt msg
      (prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState) hst
  | qOther =>
    authCkOtherStep S P qOther hst

def authRkStepSlot (S : Setup) (P : Primitives) (idx : Nat) (useIdealRkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotM Bytes ((authSpec S).Range q × AuthHybridStateFixed S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.noneResp, hst)
    else authRkSendSlot S P idx useIdealRkAt (.sendOPK u i) u bundle m0 m1 hst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.noneResp, hst)
    else authRkSendSlot S P idx useIdealRkAt (.sendNoOPK u i) u bundle m0 m1 hst
  | .recvOPK k j o msg =>
    authRkRecvSlot S P idx useIdealRkAt msg
      (prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState) hst
  | .recvNoOPK k j l msg =>
    authRkRecvSlot S P idx useIdealRkAt msg
      (prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState) hst
  | qOther =>
    liftM (authCkOtherStep S P qOther hst)

theorem authRkSendSlot_slotComp (S : Setup) (P : Primitives) (idx : Nat) (useIdealRkAt : Nat → Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    SlotM.SlotComp sampleBytes32 (authRkSendSlot S P idx useIdealRkAt sid u bundle m0 m1 hst) := by
  unfold authRkSendSlot; dsimp only
  repeat (first
    | apply SlotM.SlotComp.pure
    | apply SlotM.SlotComp.liftComp
    | apply slotComp_getRkAtSlot_bind_liftM
    | (apply SlotM.SlotComp.liftComp_bind; intro _)
    | split)

theorem authRkRecvSlot_slotComp (S : Setup) (P : Primitives) (idx : Nat) (useIdealRkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) :
    SlotM.SlotComp sampleBytes32 (authRkRecvSlot S P idx useIdealRkAt msg prep? hst) := by
  unfold authRkRecvSlot; dsimp only
  repeat (first
    | apply SlotM.SlotComp.pure
    | apply SlotM.SlotComp.liftComp
    | apply slotComp_getRkAtSlot_bind_liftM
    | split)

theorem authRkStepSlot_slotComp (S : Setup) (P : Primitives) (idx : Nat) (useIdealRkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotM.SlotComp sampleBytes32 (authRkStepSlot S P idx useIdealRkAt q hst) := by
  cases q <;> unfold authRkStepSlot <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · exact SlotM.SlotComp.pure sampleBytes32 _
    · exact authRkSendSlot_slotComp S P idx useIdealRkAt (.sendOPK u i) u bundle m0 m1 hst
  case sendNoOPK u i bundle m0 m1 =>
    split
    · exact SlotM.SlotComp.pure sampleBytes32 _
    · exact authRkSendSlot_slotComp S P idx useIdealRkAt (.sendNoOPK u i) u bundle m0 m1 hst
  case recvOPK k j o msg =>
    exact authRkRecvSlot_slotComp S P idx useIdealRkAt msg _ hst
  case recvNoOPK k j l msg =>
    exact authRkRecvSlot_slotComp S P idx useIdealRkAt msg _ hst
  all_goals
    exact SlotM.SlotComp.liftComp sampleBytes32 _

theorem authRkSendSlot_run'_some (S : Setup) (P : Primitives) (idx : Nat)
    (useIdealRkAt : Nat → Bool) (rkStar : Bytes) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    (authRkSendSlot S P idx useIdealRkAt sid u bundle m0 m1 hst).run' (some rkStar) =
      authRkSendWith S P (fun s => if s == idx then pure rkStar else sampleBytes32) useIdealRkAt
        sid u bundle m0 m1 hst := by
  unfold authRkSendSlot authRkSendWith; dsimp only
  cases hst.base.hasWonAuth <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
  repeat (first
    | rfl
    | rw [SlotM.run'_pure]
    | rw [run'_getRkAtSlot_bind_liftM_some]
    | (rw [SlotM.run'_liftComp_bind]; congr 1; funext _)
    | split)

theorem authRkRecvSlot_run'_some (S : Setup) (P : Primitives) (idx : Nat)
    (useIdealRkAt : Nat → Bool)
    (rkStar : Bytes) (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) :
    (authRkRecvSlot S P idx useIdealRkAt msg prep? hst).run' (some rkStar) =
      authRkRecvWith S P (fun s => if s == idx then pure rkStar else sampleBytes32) useIdealRkAt
        msg prep? hst := by
  unfold authRkRecvSlot authRkRecvWith; dsimp only
  repeat (first
    | rfl
    | rw [SlotM.run'_pure]
    | rw [SlotM.run'_liftComp]
    | rw [run'_getRkAtSlot_bind_liftM_some]
    | split)

theorem authRkStepSlot_run'_some (S : Setup) (P : Primitives) (idx : Nat)
    (useIdealRkAt : Nat → Bool)
    (rkStar : Bytes) (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    (authRkStepSlot S P idx useIdealRkAt q hst).run' (some rkStar) =
      authRkStepWith S P (fun s => if s == idx then pure rkStar else sampleBytes32) useIdealRkAt
        q hst := by
  cases q <;> unfold authRkStepSlot authRkStepWith <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · rw [SlotM.run'_pure]
    · exact authRkSendSlot_run'_some S P idx useIdealRkAt rkStar (.sendOPK u i) u bundle m0 m1 hst
  case sendNoOPK u i bundle m0 m1 =>
    split
    · rw [SlotM.run'_pure]
    · exact authRkSendSlot_run'_some S P idx useIdealRkAt rkStar (.sendNoOPK u i) u bundle m0 m1 hst
  case recvOPK k j o msg =>
    exact authRkRecvSlot_run'_some S P idx useIdealRkAt rkStar msg _ hst
  case recvNoOPK k j l msg =>
    exact authRkRecvSlot_run'_some S P idx useIdealRkAt rkStar msg _ hst
  all_goals
    rw [SlotM.run'_liftComp]

theorem authRkSendSlot_run'_none (S : Setup) (P : Primitives) (idx : Nat)
    (useIdealRkAt : Nat → Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    (authRkSendSlot S P idx useIdealRkAt sid u bundle m0 m1 hst).run' none =
      authRkSendWith S P (fun _ => sampleBytes32) useIdealRkAt sid u bundle m0 m1 hst := by
  unfold authRkSendSlot authRkSendWith; dsimp only
  cases hst.base.hasWonAuth <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
  repeat (first
    | rfl
    | rw [SlotM.run'_pure]
    | rw [run'_getRkAtSlot_bind_liftM_none]
    | (rw [SlotM.run'_liftComp_bind]; congr 1; funext _)
    | split)

theorem authRkRecvSlot_run'_none (S : Setup) (P : Primitives) (idx : Nat)
    (useIdealRkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) :
    (authRkRecvSlot S P idx useIdealRkAt msg prep? hst).run' none =
      authRkRecvWith S P (fun _ => sampleBytes32) useIdealRkAt msg prep? hst := by
  unfold authRkRecvSlot authRkRecvWith; dsimp only
  repeat (first
    | rfl
    | rw [SlotM.run'_pure]
    | rw [SlotM.run'_liftComp]
    | rw [run'_getRkAtSlot_bind_liftM_none]
    | split)

theorem authRkStepSlot_run'_none (S : Setup) (P : Primitives) (idx : Nat)
    (useIdealRkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    (authRkStepSlot S P idx useIdealRkAt q hst).run' none =
      authRkStepWith S P (fun _ => sampleBytes32) useIdealRkAt q hst := by
  cases q <;> unfold authRkStepSlot authRkStepWith <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · rw [SlotM.run'_pure]
    · exact authRkSendSlot_run'_none S P idx useIdealRkAt (.sendOPK u i) u bundle m0 m1 hst
  case sendNoOPK u i bundle m0 m1 =>
    split
    · rw [SlotM.run'_pure]
    · exact authRkSendSlot_run'_none S P idx useIdealRkAt (.sendNoOPK u i) u bundle m0 m1 hst
  case recvOPK k j o msg =>
    exact authRkRecvSlot_run'_none S P idx useIdealRkAt msg _ hst
  case recvNoOPK k j l msg =>
    exact authRkRecvSlot_run'_none S P idx useIdealRkAt msg _ hst
  all_goals
    rw [SlotM.run'_liftComp]

theorem authSlotFired_finishAuthSendAfterRk_self {S : Setup} (P : Primitives)
    (useIdealRkAt : Nat → Bool) (idx : Nat)
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk dhRatchet ck pk : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (rk : Bytes)
    (hSlot : sendSlotIndex? sid = some idx) :
    ∀ x ∈ support (finishAuthSendAfterRk P useIdealRkAt sid uEntry peerPrincipal? bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk dhRatchet ck pk spqrSalt? pqRatchetMsg msgPlain hst rk),
      authSlotFired S idx x.2 = true := by
  intro x hx
  have hlt : idx < S.N_send_tot := sendSlotIndex?_lt hSlot
  unfold finishAuthSendAfterRk at hx
  dsimp only at hx
  split at hx
  · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨rk1, _, ck1_0, _, _, rfl, rfl⟩
    unfold authSlotFired finishAuthHybridSend
    simp [hlt, hSlot]
  · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨⟨rk1, ck1_0⟩, rootRoCache'⟩, _, rfl⟩
    unfold authSlotFired finishAuthHybridSend
    simp [hlt, hSlot]

theorem authSlotFired_finishAuthRecvUnmatchedAfterRk_self {S : Setup} (P : Primitives)
    (useIdealRkAt : Nat → Bool) (idx : Nat)
    (msg : PreKeyMsg) (prep : PreparedAuthRecv S)
    (hst : AuthHybridStateFixed S) (rk : Bytes)
    (hSlot : S.N_send_tot + hst.recvCount = idx) :
    ∀ x ∈ support (finishAuthRecvUnmatchedAfterRk P useIdealRkAt msg prep
      (S.N_send_tot + hst.recvCount) (hst.recvCount + 1) rk),
      authSlotFired S idx x.2 = true := by
  intro x hx
  unfold finishAuthRecvUnmatchedAfterRk finishAuthRecvRk at hx
  dsimp only at hx
  simp only [MonadAttach.mem_support_bind] at hx
  rcases hx with ⟨c, _, pk, _, hx⟩
  have hge : ¬ (idx < S.N_send_tot) := by omega
  split at hx
  · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨rk1, _, ck1_0, _, _, rfl, rfl⟩
    unfold authSlotFired
    simp only [hge, ↓reduceIte, decide_eq_true_eq]
    omega
  · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨⟨rk1, ck1_0⟩, rootRoCache'⟩, _, rfl⟩
    unfold authSlotFired
    simp only [hge, ↓reduceIte, decide_eq_true_eq]
    omega

theorem SlotFireAtAuth.getRkAtSlot_send {S : Setup} (P : Primitives)
    (useIdealRkAt : Nat → Bool) (idx : Nat)
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk dhRatchet ck pk : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S)
    (hSend : sendSlotIndex? sid = some (sessionSlotIndex sid)) :
    SlotFireAtAuth S idx
      (getRkAtSlot idx (sessionSlotIndex sid) >>= fun rk =>
        liftM (finishAuthSendAfterRk P useIdealRkAt sid uEntry peerPrincipal? bundle m0 m1
          ekASk ekAPk ss kemCt ephASk ephAPk dhRatchet ck pk
          spqrSalt? pqRatchetMsg msgPlain hst rk)) :=
  SlotFireAtAuth.getRkAtSlot_bind_liftM idx (sessionSlotIndex sid) _
    (fun hEq rk x hx => authSlotFired_finishAuthSendAfterRk_self P useIdealRkAt idx sid
      uEntry peerPrincipal? bundle m0 m1 ekASk ekAPk ss kemCt ephASk ephAPk dhRatchet ck pk
      spqrSalt? pqRatchetMsg msgPlain hst rk (hEq ▸ hSend) x hx)

theorem SlotFireAtAuth.getRkAtSlot_recv {S : Setup} (P : Primitives)
    (useIdealRkAt : Nat → Bool) (idx : Nat)
    (msg : PreKeyMsg) (prep : PreparedAuthRecv S)
    (hst : AuthHybridStateFixed S) :
    SlotFireAtAuth S idx
      (getRkAtSlot idx (S.N_send_tot + hst.recvCount) >>= fun rk =>
        liftM (finishAuthRecvUnmatchedAfterRk P useIdealRkAt msg prep
          (S.N_send_tot + hst.recvCount) (hst.recvCount + 1) rk)) :=
  SlotFireAtAuth.getRkAtSlot_bind_liftM idx (S.N_send_tot + hst.recvCount) _
    (fun hEq rk x hx =>
      authSlotFired_finishAuthRecvUnmatchedAfterRk_self P useIdealRkAt idx msg prep hst rk hEq x hx)

theorem authRkSendSlot_fire (S : Setup) (P : Primitives) (idx : Nat) (useIdealRkAt : Nat → Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S)
    (hSend : sendSlotIndex? sid = some (sessionSlotIndex sid)) :
    SlotFireAtAuth S idx (authRkSendSlot S P idx useIdealRkAt sid u bundle m0 m1 hst) := by
  unfold authRkSendSlot; dsimp only
  repeat (first
    | apply SlotFireAtAuth.pure
    | apply SlotFireAtAuth.liftComp
    | (apply SlotFireAtAuth.liftComp_bind; intro _)
    | (apply SlotFireAtAuth.getRkAtSlot_send; exact hSend)
    | split)

theorem authRkRecvSlot_fire (S : Setup) (P : Primitives) (idx : Nat) (useIdealRkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) :
    SlotFireAtAuth S idx (authRkRecvSlot S P idx useIdealRkAt msg prep? hst) := by
  unfold authRkRecvSlot; dsimp only
  repeat (first
    | apply SlotFireAtAuth.pure
    | apply SlotFireAtAuth.liftComp
    | apply SlotFireAtAuth.getRkAtSlot_recv
    | split)

theorem authRkStepSlot_fire (S : Setup) (P : Primitives) (idx : Nat) (useIdealRkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotFireAtAuth S idx (authRkStepSlot S P idx useIdealRkAt q hst) := by
  cases q <;> unfold authRkStepSlot <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · exact SlotFireAtAuth.pure idx _
    · exact authRkSendSlot_fire S P idx useIdealRkAt (.sendOPK u i) u bundle m0 m1 hst rfl
  case sendNoOPK u i bundle m0 m1 =>
    split
    · exact SlotFireAtAuth.pure idx _
    · exact authRkSendSlot_fire S P idx useIdealRkAt (.sendNoOPK u i) u bundle m0 m1 hst rfl
  case recvOPK k j o msg =>
    exact authRkRecvSlot_fire S P idx useIdealRkAt msg _ hst
  case recvNoOPK k j l msg =>
    exact authRkRecvSlot_fire S P idx useIdealRkAt msg _ hst
  all_goals
    exact SlotFireAtAuth.liftComp idx _

theorem authRkSendWith_congr_slot {S : Setup} (P : Primitives)
    (samp1 samp2 : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S)
    (hEq : samp1 (sessionSlotIndex sid) = samp2 (sessionSlotIndex sid)) :
    authRkSendWith S P samp1 useIdealRkAt sid u bundle m0 m1 hst =
      authRkSendWith S P samp2 useIdealRkAt sid u bundle m0 m1 hst := by
  unfold authRkSendWith
  simp only [hEq]

theorem authRkRecvWith_congr_slot {S : Setup} (P : Primitives)
    (samp1 samp2 : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S)
    (hEq : samp1 (S.N_send_tot + hst.recvCount) = samp2 (S.N_send_tot + hst.recvCount)) :
    authRkRecvWith S P samp1 useIdealRkAt msg prep? hst =
      authRkRecvWith S P samp2 useIdealRkAt msg prep? hst := by
  unfold authRkRecvWith
  simp only [hEq]

theorem authRkSendWith_slotFired_mono (S : Setup) (P : Primitives) (idx : Nat)
    (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S)
    (hFired : authSlotFired S idx hst = true) :
    AuthSlotFiredAt S idx (authRkSendWith S P sampRkAt useIdealRkAt sid u bundle m0 m1 hst) := by
  unfold authRkSendWith finishAuthSendAfterRk; dsimp only
  cases hst.base.hasWonAuth <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
  repeat (first
    | (with_reducible apply AuthSlotFiredAt.pure;
       first
       | exact hFired
       | exact authSlotFired_finishAuthHybridSend_mono P idx sid _ _ _ bundle m0 m1
           _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hst hFired)
    | (with_reducible apply AuthSlotFiredAt.bind; intro _)
    | split)

theorem authRkRecvWith_slotFired_mono (S : Setup) (P : Primitives) (idx : Nat)
    (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S)
    (hPrepUsed : ∀ prep, prep? = some prep →
      ∀ res?, (prep.finish res?).2.base.usedSendSessions =
        hst.toAuthHybridState.base.usedSendSessions)
    (hFired : authSlotFired S idx hst = true) :
    AuthSlotFiredAt S idx (authRkRecvWith S P sampRkAt useIdealRkAt msg prep? hst) := by
  cases hPrep : prep? with
  | none =>
    unfold authRkRecvWith; dsimp only
    apply AuthSlotFiredAt.pure
    exact authSlotFired_of_usedSendSessions_eq_and_recvCount_le hFired rfl (Nat.le_succ _)
  | some prep =>
    have hUsed : ∀ res?, (prep.finish res?).2.base.usedSendSessions =
        hst.toAuthHybridState.base.usedSendSessions := hPrepUsed prep hPrep
    have hFinish : ∀ res?,
        authSlotFired S idx
          { toAuthHybridState := (prep.finish res?).2, recvCount := hst.recvCount + 1 } = true :=
      fun res? =>
        authSlotFired_of_usedSendSessions_eq_and_recvCount_le hFired (hUsed res?) (Nat.le_succ _)
    unfold authRkRecvWith finishAuthRecvUnmatchedAfterRk finishAuthRecvRk; dsimp only
    repeat (first
      | (with_reducible apply AuthSlotFiredAt.pure; exact hFinish _)
      | (with_reducible apply AuthSlotFiredAt.bind; intro _)
      | split)

theorem authRkStepWith_slotFired_mono (S : Setup) (P : Primitives) (idx : Nat)
    (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hFired : authSlotFired S idx hst = true) :
    AuthSlotFiredAt S idx (authRkStepWith S P sampRkAt useIdealRkAt q hst) := by
  cases q <;> unfold authRkStepWith <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · exact AuthSlotFiredAt.pure hFired
    · exact authRkSendWith_slotFired_mono S P idx sampRkAt useIdealRkAt
        (.sendOPK u i) u bundle m0 m1 hst hFired
  case sendNoOPK u i bundle m0 m1 =>
    split
    · exact AuthSlotFiredAt.pure hFired
    · exact authRkSendWith_slotFired_mono S P idx sampRkAt useIdealRkAt
        (.sendNoOPK u i) u bundle m0 m1 hst hFired
  case recvOPK k j o msg =>
    exact authRkRecvWith_slotFired_mono S P idx sampRkAt useIdealRkAt msg _ hst
      (fun prep hPrep res? =>
        prepareAuthHybridRecvOPK_usedSendSessions true P k j o msg
          hst.toAuthHybridState hPrep res?)
      hFired
  case recvNoOPK k j l msg =>
    exact authRkRecvWith_slotFired_mono S P idx sampRkAt useIdealRkAt msg _ hst
      (fun prep hPrep res? =>
        prepareAuthHybridRecvNoOPK_usedSendSessions true P k j l msg
          hst.toAuthHybridState hPrep res?)
      hFired
  all_goals
    exact authCkOtherStep_slotFired_mono S P idx _ hst
      (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h) hFired

theorem authRkStepWith_after (S : Setup) (P : Primitives) (idx : Nat) (useIdealRkAt : Nat → Bool)
    (rkStar : Bytes) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hFired : authSlotFired S idx hst = true) :
    authRkStepWith S P (fun s => if s == idx then pure rkStar else sampleBytes32)
        useIdealRkAt q hst =
      authRkStepWith S P (fun _ => sampleBytes32) useIdealRkAt q hst ∧
    ∀ x ∈ support (authRkStepWith S P (fun _ => sampleBytes32) useIdealRkAt q hst),
      authSlotFired S idx x.2 = true := by
  refine ⟨?_, authRkStepWith_slotFired_mono S P idx _ useIdealRkAt q hst hFired⟩
  have hSendEq : ∀ (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
      (m0 m1 : Bytes), sendSlotIndex? sid = some (sessionSlotIndex sid) →
      authRkSendWith S P (fun s => if s == idx then pure rkStar else sampleBytes32)
        useIdealRkAt sid u bundle m0 m1 hst =
        authRkSendWith S P (fun _ => sampleBytes32) useIdealRkAt sid u bundle m0 m1 hst := by
    intro sid u bundle m0 m1 hSend
    by_cases hEq : (sessionSlotIndex sid == idx) = true
    · rw [beq_iff_eq] at hEq
      have hCont : hst.toAuthHybridState.base.usedSendSessions.contains sid = true :=
        contains_sid_of_authSlotFired hFired (hEq ▸ hSend)
      unfold authRkSendWith
      simp only [hCont, ↓reduceIte]
    · apply authRkSendWith_congr_slot
      simp only [hEq, Bool.false_eq_true, ↓reduceIte]
  cases q
  case sendOPK u i bundle m0 m1 =>
    unfold authRkStepWith; dsimp only
    split
    · rfl
    · exact hSendEq (.sendOPK u i) u bundle m0 m1 rfl
  case sendNoOPK u i bundle m0 m1 =>
    unfold authRkStepWith; dsimp only
    split
    · rfl
    · exact hSendEq (.sendNoOPK u i) u bundle m0 m1 rfl
  case recvOPK k' j o msg =>
    unfold authRkStepWith; dsimp only
    have hne : S.N_send_tot + hst.recvCount ≠ idx := recvSlot_ne_of_authSlotFired hFired
    have hEqF : (S.N_send_tot + hst.recvCount == idx) = false := beq_eq_false_iff_ne.mpr hne
    apply authRkRecvWith_congr_slot
    simp only [hEqF, Bool.false_eq_true, ↓reduceIte]
  case recvNoOPK k' j l msg =>
    unfold authRkStepWith; dsimp only
    have hne : S.N_send_tot + hst.recvCount ≠ idx := recvSlot_ne_of_authSlotFired hFired
    have hEqF : (S.N_send_tot + hst.recvCount == idx) = false := beq_eq_false_iff_ne.mpr hne
    apply authRkRecvWith_congr_slot
    simp only [hEqF, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

def authRkCutoffImpl (S : Setup) (P : Primitives) (cutoff : Nat) :
    QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) :=
  fun q => StateT.mk (authRkStepWith S P (fun _ => sampleBytes32) (fun s => decide (s < cutoff)) q)

def rootRoAuthImpl (S : Setup) (P : Primitives) (idx : Nat) (rkStar : Bytes) :
    QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) :=
  fun q => StateT.mk (authRkStepWith S P (fun s => if s == idx then pure rkStar else sampleBytes32)
    (fun s => decide (s < idx)) q)

noncomputable def authRkCutoffExp (S : Setup) (P : Primitives) (cutoff : Nat)
    (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthHybridStateFixed.empty S secb
  let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (AuthHybridStateFixed S) ProbComp) + authRkCutoffImpl S P cutoff
  let (b', finalSt) ← (simulateQ fullImpl A.run).run initSt
  finalizeAuthFixed P secb b' finalSt.toAuthHybridState

noncomputable def authRkCutoffAdv (S : Setup) (P : Primitives) (cutoff : Nat)
    (A : AuthAdversary S) : ℝ :=
  (𝒟[authRkCutoffExp S P cutoff A].boolBias).toReal

/-- `SlotM` pre-sampling equivalence for `G3.5 ↔ G3.6` at slot `idx`. -/
theorem evalDist_preSample_authRk_eq_cutoff (S : Setup) (P : Primitives)
    (idx : Nat) (A : AuthAdversary S) :
    𝒟[do
        let rkStar ← sampleBytes32
        let secb ← $ᵗ Bool
        let initSt := AuthHybridStateFixed.empty S secb
        let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (AuthHybridStateFixed S) ProbComp) + rootRoAuthImpl S P idx rkStar
        let (b', finalSt) ← (simulateQ fullImpl A.run).run initSt
        finalizeAuthFixed P secb b' finalSt.toAuthHybridState] =
      𝒟[authRkCutoffExp S P idx A] := by
  unfold authRkCutoffExp
  rw [OracleComp.evalDist_bind_bind_swap]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  exact SlotM.evalDist_preSample_eq_lazy_of_slotStep
    sampleBytes32
    (authSlotFired S idx)
    (authRkCutoffImpl S P idx)
    (fun rkStar => rootRoAuthImpl S P idx rkStar)
    (authRkStepSlot S P idx (fun s => decide (s < idx)))
    (authRkStepSlot_slotComp S P idx (fun s => decide (s < idx)))
    (authRkStepSlot_run'_some S P idx (fun s => decide (s < idx)))
    (fun q hst g => by
      dsimp only [authRkCutoffImpl, StateT.run_mk]
      rw [authRkStepSlot_run'_none S P idx (fun s => decide (s < idx)) q hst])
    (fun rkStar q hst hFired =>
      authRkStepWith_after S P idx (fun s => decide (s < idx)) rkStar q hst hFired)
    (authRkStepSlot_fire S P idx (fun s => decide (s < idx)))
    A.run
    (AuthHybridStateFixed.empty S secb)
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)

end SignalPqxdh.Security.AuthSubHops1to3
