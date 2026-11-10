/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.CostedTablesCompat
public import Computational.Proofs.ReductionDsl.Size
import Mathlib.Algebra.Order.Ring.Star

/-!
# Legacy PQXDH `ReductionDsl` Tables

**Checked by Lean.** Proves `OpsSizeHonest pqxdhOps`, `SampSizeHonest pqSamplers`, codec roundtrips,
and generic `GRedBlockBounded` / `GRed2BlockBounded` output bounds for the proof-only legacy tables
in `CostedTablesCompat.lean`.
-/

@[expose] public section

namespace SignalPqxdh.LegacyCosted

open _root_.ReductionDsl OracleSpec OracleComp

/-! ## Block-size and bit-length helpers -/

theorem blocks_bytes_le_iff (w : ℕ+) (x : Bytes) (M : ℕ) :
    PSort.blocks (.bytes w) x ≤ M ↔ x.length ≤ M * w := by
  have hw : 0 < (w : ℕ) := w.pos
  have hmul : (M + 1) * (w : ℕ) = M * w + w := by ring
  rw [PSort.blocks, ← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hw, hmul]
  omega

theorem fits_bytes_iff (w : ℕ+) (M : ℕ) (x : Bytes) :
    (B w).Fits M x ↔ x.length ≤ M * w :=
  blocks_bytes_le_iff w x M

theorem bits_le_self {M : ℕ} (hM : 1 ≤ M) : bits M ≤ M :=
  bits_le_of_lt Nat.lt_two_pow_self hM

private theorem pbVarint_go_length_le :
    ∀ (k f n : ℕ), n < 2 ^ k → (pbVarint.go f n).length ≤ k + 1
  | 0, 0, n, _ => by simp [pbVarint.go]
  | 0, f + 1, n, hn => by
    have : n < 128 := by simp at hn; omega
    simp [pbVarint.go, this]
  | k + 1, 0, n, _ => by simp [pbVarint.go]
  | k + 1, f + 1, n, hn => by
    unfold pbVarint.go
    split
    · simp
    · have hdiv : n / 128 < 2 ^ k := by
        rw [pow_succ'] at hn
        omega
      have ih := pbVarint_go_length_le k f (n / 128) hdiv
      simp only [List.length_cons]
      omega

theorem pbVarint_length_le_bits (n : ℕ) : (pbVarint n).length ≤ bits n + 1 :=
  pbVarint_go_length_le (bits n) n n (lt_two_pow_bits n)

/-! ## Operation size honesty -/

theorem pqBytesOps_sizeHonest : OpsSizeHonest pqBytesOps := by
  intro o x M hx
  cases o with
  | lit w v =>
    change (B w).Fits (M + (w + v.length)) v
    rw [fits_bytes_iff]
    have hw : 1 ≤ (w : ℕ) := w.pos
    have : v.length ≤ (M + ((w : ℕ) + v.length)) * 1 := by omega
    exact le_trans this (Nat.mul_le_mul_left _ hw)
  | cat m n =>
    rcases x with ⟨x₁, x₂⟩
    have hx₁ : x₁.length ≤ M * m := (fits_bytes_iff m M x₁).1 hx.1
    have hx₂ : x₂.length ≤ M * n := (fits_bytes_iff n M x₂).1 hx.2
    change (B (m + n)).Fits (M + (m + n)) (x₁ ++ x₂)
    rw [fits_bytes_iff]
    simp only [PNat.add_coe]
    calc (x₁ ++ x₂).length
        = x₁.length + x₂.length := List.length_append
      _ ≤ M * (m : ℕ) + M * (n : ℕ) := by omega
      _ = M * ((m : ℕ) + n) := by ring
      _ ≤ (M + ((m : ℕ) + n)) * ((m : ℕ) + n) :=
          Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  | cons b w =>
    have hxw : x.length ≤ M * w := (fits_bytes_iff w M x).1 hx
    change (B (w + 1)).Fits (M + (w + 1)) (b :: x)
    rw [fits_bytes_iff]
    simp only [List.length_cons, PNat.add_coe, PNat.val_ofNat]
    have : M * (w : ℕ) + 1 ≤ (M + ((w : ℕ) + 1)) * ((w : ℕ) + 1) := by nlinarith
    omega
  | widen w d =>
    have hxw : x.length ≤ M * w := (fits_bytes_iff w M x).1 hx
    change (B (w + d)).Fits (M + (w + d)) x
    rw [fits_bytes_iff]
    simp only [PNat.add_coe]
    have : M * (w : ℕ) ≤ (M + ((w : ℕ) + d)) * ((w : ℕ) + d) := by nlinarith
    omega
  | takeK w k =>
    change (B k).Fits (M + (w + k)) (x.take k)
    rw [fits_bytes_iff]
    have hlen : (x.take k).length ≤ (k : ℕ) := List.length_take_le k x
    have hk : 1 ≤ M + ((w : ℕ) + k) := by have := w.pos; omega
    calc (x.take k).length
        ≤ 1 * (k : ℕ) := by omega
      _ ≤ (M + ((w : ℕ) + k)) * k := Nat.mul_le_mul_right _ hk
  | take w =>
    rcases x with ⟨n, s⟩
    have hs : s.length ≤ M * w := (fits_bytes_iff w M s).1 hx.2
    change (B w).Fits (M + (w + 1)) (s.take n)
    rw [fits_bytes_iff]
    have hlen : (s.take n).length ≤ s.length := List.length_take_le' n s
    have : M * (w : ℕ) ≤ (M + ((w : ℕ) + 1)) * w :=
      Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    omega
  | drop w =>
    rcases x with ⟨n, s⟩
    have hs : s.length ≤ M * w := (fits_bytes_iff w M s).1 hx.2
    change (B w).Fits (M + (w + 1)) (s.drop n)
    rw [fits_bytes_iff, List.length_drop]
    have : M * (w : ℕ) ≤ (M + ((w : ℕ) + 1)) * w :=
      Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    omega
  | len w =>
    have hxw : x.length ≤ M * w := (fits_bytes_iff w M x).1 hx
    simp only [Ty.Fits]
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · have hx0 : x.length = 0 := by omega
      have h1 : bits 0 = 1 := rfl
      have hbw := one_le_bits w
      rw [hx0, h1]
      omega
    · have h1 : bits x.length ≤ bits ((w : ℕ) * M) :=
        bits_mono (by rw [Nat.mul_comm]; exact hxw)
      have h2 := bits_mul w M
      have h3 := bits_le_self hM
      omega
  | eq m n => trivial
  | varint =>
    simp only [Ty.Fits] at hx
    change (B 10).Fits (M + 10) (pbVarint x)
    rw [fits_bytes_iff]
    have hlen := pbVarint_length_le_bits x
    simp only [PNat.val_ofNat]
    omega

theorem pqU32Ops_sizeHonest : OpsSizeHonest pqU32Ops := by
  intro o x M hx
  cases o with
  | lit k =>
    simp only [Ty.Fits, PSort.blocks]
    omega
  | ofNat =>
    simp only [Ty.Fits, PSort.blocks]
    omega
  | toNat =>
    simp only [Ty.Fits]
    have hlt : x.toNat < 2 ^ 32 := x.toBitVec.isLt
    have hb : bits x.toNat ≤ 32 := bits_le_of_lt hlt (by omega)
    omega
  | eq => trivial

theorem pqO_sizeHonest : OpsSizeHonest pqxdhOps :=
  OpsSizeHonest.sum pqBytesOps_sizeHonest pqU32Ops_sizeHonest

/-! ## Sampler size honesty -/

theorem word256ToBytes_length (w : BitVec 256) : (word256ToBytes w).length = 32 := by
  simp [word256ToBytes]

theorem word128ToBytes_length (w : BitVec 128) : (word128ToBytes w).length = 16 := by
  simp [word128ToBytes]

theorem mem_support_sampleBytes32 {x : Bytes} (hx : x ∈ support sampleBytes32) :
    x.length = 32 := by
  simp only [sampleBytes32, support_map, Set.mem_image] at hx
  obtain ⟨w, -, rfl⟩ := hx
  exact word256ToBytes_length w

theorem mem_support_sampleRandom64 {x : Bytes} (hx : x ∈ support sampleRandom64) :
    x.length = 64 := by
  simp only [sampleRandom64, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hx
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hx
  simp [mem_support_sampleBytes32 hb₁, mem_support_sampleBytes32 hb₂]

theorem mem_support_sampleDRKey96 {k : DRKey} (hk : k ∈ support sampleDRKey96) :
    k.rootKey.length = 32 ∧ k.chainKey.length = 32 ∧ k.pqrKey.length = 32 := by
  simp only [sampleDRKey96, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hk
  obtain ⟨rk, hrk, ck, hck, pk, hpk, rfl⟩ := hk
  exact ⟨mem_support_sampleBytes32 hrk, mem_support_sampleBytes32 hck,
    mem_support_sampleBytes32 hpk⟩

theorem mem_support_sampleMessageKeys80 {k : MessageKeys}
    (hk : k ∈ support sampleMessageKeys80) :
    k.cipherKey.length = 32 ∧ k.macKey.length = 32 ∧ k.iv.length = 16 := by
  simp only [sampleMessageKeys80, mem_support_bind_iff, support_map, Set.mem_image,
    support_pure, Set.mem_singleton_iff] at hk
  obtain ⟨ck, hck, mk, hmk, iv, ⟨w, -, rfl⟩, rfl⟩ := hk
  exact ⟨mem_support_sampleBytes32 hck, mem_support_sampleBytes32 hmk, word128ToBytes_length w⟩

theorem mem_support_sampleIndex {N y : ℕ} (hy : y ∈ support (sampleIndex N)) :
    bits y ≤ bits N := by
  unfold sampleIndex at hy
  split at hy
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hy
    obtain ⟨x, -, rfl⟩ := hy
    exact bits_mono (Nat.le_of_lt x.isLt)
  · simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact one_le_bits N

private theorem fits_bytes_of_length_eq (w : ℕ+) {M : ℕ} (hM : 1 ≤ M) {x : Bytes}
    (hx : x.length = w) : (B w).Fits M x := by
  rw [fits_bytes_iff, hx]
  simpa using Nat.mul_le_mul_right (w : ℕ) hM

theorem pqSamplers_sizeHonest : SampSizeHonest pqSamplers := by
  intro s _ M _ y hy
  cases s with
  | bool => trivial
  | bytes32 =>
    exact fits_bytes_of_length_eq 32 (by simp [pqSamplers, PSamp.cost, Ty.wd])
      (mem_support_sampleBytes32 hy)
  | random64 =>
    exact fits_bytes_of_length_eq 64 (by simp [pqSamplers, PSamp.cost, Ty.wd])
      (mem_support_sampleRandom64 hy)
  | drKey96 =>
    simp only [pqSamplers, PSamp.run, support_map] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    obtain ⟨h1, h2, h3⟩ := mem_support_sampleDRKey96 hk
    have hM : 1 ≤ M + pqSamplers.sCost .drKey96 := by
      simp [pqSamplers, PSamp.cost, Ty.wd]
    exact ⟨fits_bytes_of_length_eq 32 hM h1, fits_bytes_of_length_eq 32 hM h2,
      fits_bytes_of_length_eq 32 hM h3⟩
  | msgKeys80 =>
    simp only [pqSamplers, PSamp.run, support_map] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    obtain ⟨h1, h2, h3⟩ := mem_support_sampleMessageKeys80 hk
    have hM : 1 ≤ M + pqSamplers.sCost .msgKeys80 := by
      simp [pqSamplers, PSamp.cost, Ty.wd]
    exact ⟨fits_bytes_of_length_eq 32 hM h1, fits_bytes_of_length_eq 32 hM h2,
      fits_bytes_of_length_eq 16 hM h3⟩
  | index N =>
    have := mem_support_sampleIndex hy
    simp only [pqSamplers, PSamp.ty, PSamp.cost, Ty.Fits]
    omega

/-! ## Codec roundtrips -/

@[simp] theorem bundleOfV_bundleV (b : PreKeyBundleInput) : bundleOfV (bundleV b) = b := rfl

/-- Inverse of `keyIndRdec`. -/
def keyIndRenc : KeyIndResponse → keyIndRT.denote
  | .noneResp => .inl ()
  | .initPrinResp ik s => .inr (.inl (ik, s))
  | .pkResp pk => .inr (.inr (.inl pk))
  | .corrResp ik s => .inr (.inr (.inr (.inl (ik, s))))
  | .bundleResp b => .inr (.inr (.inr (.inr (.inl (bundleV b)))))
  | .hdrResp h => .inr (.inr (.inr (.inr (.inr (.inl (hdrV h))))))
  | .initUnfreshResp dk h =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inl (drKeyV dk, hdrV h)))))))
  | .acceptFreshResp =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ())))))))
  | .drKeyResp dk =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (drKeyV dk)))))))))
  | .dhSecretsResp l1 l2 l3 l4 =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (l1, (l2, (l3, l4))))))))))))
  | .spkSkResp sk =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr sk)))))))))

@[simp] theorem keyIndRdec_keyIndRenc (r : KeyIndResponse) :
    keyIndRdec (keyIndRenc r) = r := by
  cases r <;> rfl

/-- Inverse of `authRdec`. -/
def authRenc : AuthResponse → authRT.denote
  | .noneResp => .inl ()
  | .initPrinResp ik s => .inr (.inl (ik, s))
  | .pkResp pk => .inr (.inr (.inl pk))
  | .corrResp ik s => .inr (.inr (.inr (.inl (ik, s))))
  | .bundleResp b => .inr (.inr (.inr (.inr (.inl (bundleV b)))))
  | .sendFreshResp m => .inr (.inr (.inr (.inr (.inr (.inl (preKeyMsgV m))))))
  | .sendUnfreshResp dk rk ck m =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inl (drKeyV dk, (rk, (ck, preKeyMsgV m)))))))))
  | .recvHonestResp =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ())))))))
  | .recvUnfreshResp dk rk ck pt =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (drKeyV dk, (rk, (ck, pt)))))))))))
  | .drKeyResp dk =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (drKeyV dk))))))))))
  | .rootKdfResp rk ck =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (rk, ck)))))))))))
  | .dhSecretsResp l1 l2 l3 l4 =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (l1, (l2, (l3, l4)))))))))))))

@[simp] theorem authRdec_authRenc (r : AuthResponse) :
    authRdec (authRenc r) = r := by
  cases r <;> rfl

/-! ## Legacy output block-size bounds -/

theorem valFits_iff_fits {S : Sig} (B : ℕ) :
    ∀ (t : Ty S) (x : t.denote), ValFits B t x ↔ t.Fits B x
  | .base _, _ => Iff.rfl
  | .unit, _ => Iff.rfl
  | .bool, _ => Iff.rfl
  | .nat, _ => Iff.rfl
  | .opt _, none => Iff.rfl
  | .opt t, some a => valFits_iff_fits B t a
  | .prod t u, x => and_congr (valFits_iff_fits B t x.1) (valFits_iff_fits B u x.2)
  | .sum t _, .inl a => valFits_iff_fits B t a
  | .sum _ u, .inr b => valFits_iff_fits B u b
  | .list t, _ => and_congr Iff.rfl
      (forall_congr' fun x => imp_congr_right fun _ => valFits_iff_fits B t x)
  | .tbl t, m => forall_congr' fun i => valFits_iff_fits B t (m i)

theorem pqOpsSizeHonest : PqOpsSizeHonest pqxdhOps := by
  intro o x B hx
  rw [valFits_iff_fits] at hx ⊢
  exact pqO_sizeHonest o x B hx

theorem pqSampSizeHonest : PqSampSizeHonest pqSamplers := by
  intro s x B hx y hy
  rw [valFits_iff_fits] at hx ⊢
  exact pqSamplers_sizeHonest s x B hx y hy

theorem one_le_pqSamplers_sCost (s : PSamp) : 1 ≤ pqSamplers.sCost s := by
  cases s <;> simp [pqSamplers, PSamp.cost]

theorem one_le_pqPrimIface_qCost (g : pqPrimIface.Tag) : 1 ≤ pqPrimIface.qCost g := by
  simp only [pqPrimIface]; omega

theorem one_le_pqChalIface_qCost {C : ChallengerOracle} (g : (pqChalIface C).Tag) :
    1 ≤ (pqChalIface C).qCost g := by
  cases g <;> simp only [pqChalIface, ChallengerOracle.qCost] <;> omega

theorem comp_nq_le_cost {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    (hq : ∀ g, 1 ≤ I.qCost g) (hs : ∀ s, 1 ≤ I.smp.sCost s)
    {Γ : List (Ty pqSig)} {t : Ty pqSig} (c : Comp pqxdhOps I Γ t) : c.nq ≤ c.cost := by
  induction c with
  | ret _ => simp [Comp.nq, Comp.queries, Comp.cost]
  | bind c k ihc ihk => dsimp only [Comp.nq, Comp.queries, Comp.cost] at *; omega
  | ite _ c d ihc ihd => dsimp only [Comp.nq, Comp.queries, Comp.cost] at *; omega
  | caseOpt _ n s ihn ihs => dsimp only [Comp.nq, Comp.queries, Comp.cost] at *; omega
  | caseSum _ l r ihl ihr => dsimp only [Comp.nq, Comp.queries, Comp.cost] at *; omega
  | sample s _ => have := hs s; dsimp only [Comp.nq, Comp.queries, Comp.cost]; omega
  | query g _ => have := hq g; dsimp only [Comp.nq, Comp.queries, Comp.cost]; omega
  | iter n _ body ih =>
    dsimp only [Comp.nq] at ih ⊢
    dsimp only [Comp.queries, Comp.cost]
    have h1 : Comp.queries (fun _ => 1) (fun _ => 1) body ≤ body.cost + 1 := by omega
    have := Nat.mul_le_mul_left n h1
    omega
  | findM K _ p ih | anyM K _ p ih | mapM K _ p ih | foldM K _ _ p ih =>
    dsimp only [Comp.nq] at ih ⊢
    dsimp only [Comp.queries, Comp.cost]
    have h1 : Comp.queries (fun _ => 1) (fun _ => 1) p ≤ p.cost + 1 := by omega
    have := Nat.mul_le_mul_left K h1
    omega
  | consumeFirstM K _ p mk ih =>
    dsimp only [Comp.nq] at ih ⊢
    dsimp only [Comp.queries, Comp.cost]
    have h1 : Comp.queries (fun _ => 1) (fun _ => 1) p ≤ p.cost + mk.cost + 1 := by omega
    have := Nat.mul_le_mul_left K h1
    omega

theorem gred_nq_le_totalCost {ι κ : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {G : OracleSpec κ} {C : GameCodec pqSig G} {rIn aIn aOut out : Ty pqSig}
    (hq : ∀ g, 1 ≤ I.qCost g) (hs : ∀ s, 1 ≤ I.smp.sCost s)
    (R : CostedReduction pqxdhOps I G C rIn aIn aOut out) (q : ℕ) :
    R.nq q ≤ R.totalCost q := by
  have hI := comp_nq_le_cost hq hs R.init
  have hH := comp_nq_le_cost hq hs R.handle
  have hF := comp_nq_le_cost hq hs R.finish
  have hMax : R.handle.nq ≤ max I.uCost (R.handle.cost + C.codecCost) :=
    le_trans hH (le_trans (Nat.le_add_right _ _) (le_max_right _ _))
  have hMul := Nat.mul_le_mul_left q hMax
  dsimp only [CostedReduction.nq, CostedReduction.totalQueries, CostedReduction.totalCost, Comp.nq] at *
  omega

/-- Derives `GRedBlockBounded` from `R.totalCost b.q_total ≤ stepCostBudget S b`. -/
theorem gredBlockBounded_of_totalCost_le {ι κ : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {G : OracleSpec κ} {C : GameCodec pqSig G} {rIn out : Ty pqSig}
    (hS : SampSizeHonest I.smp) (hqCost : ∀ g, 1 ≤ I.qCost g) (hsCost : ∀ s, 1 ≤ I.smp.sCost s)
    (S : Setup) (b : QueryBudget) (ℓ : Nat)
    (R : CostedReduction pqxdhOps I G C rIn .unit .bool out)
    (hCost : R.totalCost b.q_total ≤ stepCostBudget S b) :
    GRedBlockBounded S b ℓ R := by
  intro hq henc A hA x hx y hy
  rw [valFits_iff_fits]
  have hq' : ∀ g x u, (I.cod g).Fits ℓ (I.dec g x u) := fun g x u =>
    (valFits_iff_fits ℓ _ _).1 (hq g x u)
  have henc' : ∀ t, C.Q.Fits ℓ (C.qenc t) := fun t =>
    (valFits_iff_fits ℓ _ _).1 (henc t)
  have hx' : rIn.Fits ℓ x := (valFits_iff_fits ℓ _ _).1 hx
  have hA' : ∀ u, (A u).IsQueryBoundP (_root_.ReductionDsl.isGameQuery (G := G)) b.q_total := by
    intro u
    convert hA u using 1
    funext q; cases q <;> simp [_root_.ReductionDsl.isGameQuery, _root_.SignalPqxdh.isGameQuery]
  have hEval := R.fits_eval pqO_sizeHonest hS ℓ hq' ℓ henc' 0 (fun _ => trivial)
    A b.q_total ℓ hA' x hx' y hy
  have hNq := le_trans (gred_nq_le_totalCost hqCost hsCost R b.q_total) hCost
  refine Ty.fits_mono ?_ out y hEval
  unfold outputSizeBudget
  nlinarith

/-- Derives `GRed2BlockBounded` from `R.totalCost b.q_total ≤ stepCostBudget S b`. -/
theorem gred2BlockBounded_of_totalCost_le {ι κ : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {G : OracleSpec κ} {C : GameCodec pqSig G} {rIn ch rIn2 out : Ty pqSig}
    (hS : SampSizeHonest I.smp) (hqCost : ∀ g, 1 ≤ I.qCost g) (hsCost : ∀ s, 1 ≤ I.smp.sCost s)
    (S : Setup) (b : QueryBudget) (ℓ : Nat)
    (R : TwoStageCostedReduction pqxdhOps I G C rIn .unit .bool ch rIn2 out)
    (hCost : R.totalCost b.q_total ≤ stepCostBudget S b) :
    GRed2BlockBounded S b ℓ R := by
  intro hq henc A x hx cm hcm
  have hq' : ∀ g x u, (I.cod g).Fits ℓ (I.dec g x u) := fun g x u =>
    (valFits_iff_fits ℓ _ _).1 (hq g x u)
  have henc' : ∀ t, C.Q.Fits ℓ (C.qenc t) := fun t =>
    (valFits_iff_fits ℓ _ _).1 (henc t)
  have hx' : rIn.Fits ℓ x := (valFits_iff_fits ℓ _ _).1 hx
  have ⟨hc1, hm1⟩ := R.fits_eval1 pqO_sizeHonest hS ℓ hq' ℓ henc' 0 (fun _ => trivial)
    A b.q_total ℓ x hx' false cm hcm
  have hI := comp_nq_le_cost hqCost hsCost R.init
  have hPre := comp_nq_le_cost hqCost hsCost R.handlePre
  have hPost := comp_nq_le_cost hqCost hsCost R.handlePost
  have hDone := comp_nq_le_cost hqCost hsCost R.chDone
  have hRes := comp_nq_le_cost hqCost hsCost R.resume
  have hFin := comp_nq_le_cost hqCost hsCost R.finish
  have hPreC : R.handlePre.cost ≤
      max I.uCost (max R.handlePre.cost R.handlePost.cost + C.codecCost) :=
    le_trans (le_max_left _ _) (le_trans (Nat.le_add_right _ _) (le_max_right _ _))
  have hPostC : R.handlePost.cost ≤
      max I.uCost (max R.handlePre.cost R.handlePost.cost + C.codecCost) :=
    le_trans (le_max_right _ _) (le_trans (Nat.le_add_right _ _) (le_max_right _ _))
  have hMaxH : max R.handlePre.nq R.handlePost.nq ≤
      max I.uCost (max R.handlePre.cost R.handlePost.cost + C.codecCost) :=
    max_le (le_trans hPre hPreC) (le_trans hPost hPostC)
  have hMaxCR : max R.chDone.nq R.resume.nq ≤ max R.chDone.cost R.resume.cost :=
    max_le (le_trans hDone (le_max_left _ _)) (le_trans hRes (le_max_right _ _))
  have hMulH := Nat.mul_le_mul_left b.q_total hMaxH
  have hMulPreC := Nat.mul_le_mul_left b.q_total hPreC
  have hMulPostC := Nat.mul_le_mul_left b.q_total hPostC
  have hMulPreN := Nat.mul_le_mul_left b.q_total (le_trans hPre hPreC)
  have hMulPostN := Nat.mul_le_mul_left b.q_total (le_trans hPost hPostC)
  have hNqLe : R.nq b.q_total ≤ stepCostBudget S b := by
    dsimp only [TwoStageCostedReduction.nq, TwoStageCostedReduction.totalQueries, TwoStageCostedReduction.totalCost, Comp.nq] at *
    omega
  have hB1Le : R.init.cost + b.q_total * R.handlePre.cost ≤ stepCostBudget S b := by
    dsimp only [TwoStageCostedReduction.totalCost] at hCost; omega
  have hN1Le : R.init.nq + b.q_total * R.handlePre.nq ≤ stepCostBudget S b := by
    dsimp only [TwoStageCostedReduction.totalCost] at hCost; omega
  have hB2Le : R.resume.cost + b.q_total * R.handlePost.cost + R.finish.cost ≤ stepCostBudget S b := by
    have : R.resume.cost ≤ max R.chDone.cost R.resume.cost := le_max_right _ _
    dsimp only [TwoStageCostedReduction.totalCost] at hCost; omega
  have hN2Le : R.resume.nq + b.q_total * R.handlePost.nq + R.finish.nq ≤ stepCostBudget S b := by
    have : R.resume.nq ≤ max R.chDone.cost R.resume.cost := le_trans hRes (le_max_right _ _)
    dsimp only [TwoStageCostedReduction.totalCost] at hCost; omega
  refine ⟨?_, fun y hy z hz => ?_⟩
  · rw [valFits_iff_fits]
    refine Ty.fits_mono ?_ ch cm.1 hc1
    unfold outputSizeBudget
    nlinarith
  · rw [valFits_iff_fits]
    have hy' : rIn2.Fits ℓ y := (valFits_iff_fits ℓ _ _).1 hy
    have hz' := R.fits_eval2 pqO_sizeHonest hS ℓ hq' ℓ henc' 0 (fun _ => trivial)
      cm.2 _ hm1 y ℓ hy' b.q_total false z hz
    refine Ty.fits_mono ?_ out z hz'
    unfold outputSizeBudget
    nlinarith

end SignalPqxdh.LegacyCosted
