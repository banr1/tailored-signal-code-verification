/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.AtomicOps
public import Computational.Specifications.Reductions.ReductionDsl.TargetCodecs
import Mathlib.Algebra.Order.Ring.Star

/-!
# Size Honesty and Codec Roundtrips for `AtomicOps` and `TargetCodecs`

**Checked by Lean.** Proves `SampSizeHonest` and `OpsSizeHonest` for the base, cryptographic, and
composed DSL operation tables (`atomicAdapterOps`, `atomicFsOps`, `atomicFig8Ops`,
`atomicSessionOps`, `atomicE2EOps`) together with response-codec roundtrips for `pqKeyIndCodec`.
-/

@[expose] public section

set_option autoImplicit false

namespace ReductionDsl

open List Option Bool Prod Sum Fin OracleSpec OracleComp
open CryptoVerification CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoGames
open Ratchet LibsignalInst LibsignalSession LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM CKA

/-! ## Block-size characterizations and list helpers -/

private theorem lt_two_pow_bits (n : ℕ) : n < 2 ^ bits n :=
  Nat.lt_pow_succ_log_self (by norm_num) n

private theorem one_le_bits (n : ℕ) : 1 ≤ bits n := by
  unfold bits; omega

private theorem bits_le_of_lt {n k : ℕ} (h : n < 2 ^ k) (hk : 1 ≤ k) : bits n ≤ k := by
  unfold bits
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp; omega
  · have := Nat.log_lt_of_lt_pow (b := 2) hn.ne' h; omega

private theorem bits_mono {a b : ℕ} (h : a ≤ b) : bits a ≤ bits b := by
  unfold bits; have := Nat.log_mono_right (b := 2) h; omega

private theorem bits_mul (k a : ℕ) : bits (k * a) ≤ bits k + bits a := by
  apply bits_le_of_lt _ (by have := one_le_bits k; omega)
  rw [pow_add]
  exact Nat.mul_lt_mul'' (lt_two_pow_bits k) (lt_two_pow_bits a)

private theorem opsSizeHonest_sum {S : Sig} {O₁ O₂ : Ops S}
    (h₁ : OpsSizeHonest O₁) (h₂ : OpsSizeHonest O₂) :
    OpsSizeHonest (O₁.sum O₂)
  | .inl o, x, B, hx => h₁ o x B hx
  | .inr o, x, B, hx => h₂ o x B hx

private theorem sampleIndex_fits {S : Sig} (N B : ℕ) :
    ∀ y ∈ support (sampleIndex N), (Ty.nat (S := S)).Fits (B + (bits N + 1)) y := by
  intro y hy
  simp only [sampleIndex] at hy
  split_ifs at hy with h
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hy
    obtain ⟨x, -, rfl⟩ := hy
    have hle : x.val ≤ N := Nat.le_of_lt x.isLt
    have hb := bits_mono hle
    simp only [Ty.Fits]; omega
  · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
    have h0 : bits 0 = 1 := rfl
    simp only [Ty.Fits]; omega

private theorem sampSizeHonest_unifSamplers {S : Sig} {B : Type} (f : B → S.Base)
    (w : B → ℕ) [∀ b, SampleableType (S.den (f b))]
    (hw : ∀ b y, S.sz (f b) y ≤ w b := by intros; exact le_rfl) :
    SampSizeHonest (unifSamplers (S := S) f w)
  | .bool, _, _, _, _, _ => trivial
  | .index N, _, B₀, _, y, hy => sampleIndex_fits N B₀ y hy
  | .base b, _, B₀, _, y, _ => by
    change S.sz (f b) y ≤ B₀ + w b
    have := hw b y; omega

theorem blocks_pbytes_le_iff (ℓ : ℕ) (Pt : Type) (w : ℕ+) (x : SignalPqxdh.Bytes) (M : ℕ) :
    AtomicSort.blocks ℓ Pt (.pbytes w) x ≤ M ↔ x.length ≤ M * w := by
  have hw : 0 < (w : ℕ) := w.pos
  have hmul : (M + 1) * (w : ℕ) = M * w + w := by ring
  rw [AtomicSort.blocks, ← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hw, hmul]
  omega

theorem fits_pbytes_iff (ℓ : ℕ) (Pt : Type) (w : ℕ+) (M : ℕ) (x : SignalPqxdh.Bytes) :
    (PB (ℓ := ℓ) (Pt := Pt) w).Fits M x ↔ x.length ≤ M * w :=
  blocks_pbytes_le_iff ℓ Pt w x M

theorem blocks_bytes_le_iff (ℓ : ℕ) (Pt : Type) (w : ℕ+) (x : Bytes) (M : ℕ) :
    AtomicSort.blocks ℓ Pt (.bytes w) x ≤ M ↔ x.length ≤ M * w := by
  have hw : 0 < (w : ℕ) := w.pos
  have hmul : (M + 1) * (w : ℕ) = M * w + w := by ring
  rw [AtomicSort.blocks, ← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hw, hmul]
  omega

theorem fits_bytes_iff (ℓ : ℕ) (Pt : Type) (w : ℕ+) (M : ℕ) (x : Bytes) :
    (B (ℓ := ℓ) (Pt := Pt) w).Fits M x ↔ x.length ≤ M * w :=
  blocks_bytes_le_iff ℓ Pt w x M

private theorem fits_pbytes_take (ℓ : ℕ) (Pt : Type) (w : ℕ+) {K M : ℕ} (hKM : K ≤ M)
    (x : SignalPqxdh.Bytes) :
    (PB (ℓ := ℓ) (Pt := Pt) w).Fits M (x.take ((w : ℕ) * K)) := by
  rw [fits_pbytes_iff]
  have hlen : (x.take ((w : ℕ) * K)).length ≤ (w : ℕ) * K := List.length_take_le _ x
  calc (x.take ((w : ℕ) * K)).length
      ≤ (w : ℕ) * K := hlen
    _ = K * (w : ℕ) := Nat.mul_comm _ _
    _ ≤ M * (w : ℕ) := Nat.mul_le_mul_right _ hKM

private theorem fits_bytes_take (ℓ : ℕ) (Pt : Type) (w : ℕ+) {K M : ℕ} (hKM : K ≤ M)
    (x : Bytes) : (B (ℓ := ℓ) (Pt := Pt) w).Fits M (x.take ((w : ℕ) * K)) := by
  rw [fits_bytes_iff]
  have hlen : (x.take ((w : ℕ) * K)).length ≤ (w : ℕ) * K := List.length_take_le _ x
  calc (x.take ((w : ℕ) * K)).length
      ≤ (w : ℕ) * K := hlen
    _ = K * (w : ℕ) := Nat.mul_comm _ _
    _ ≤ M * (w : ℕ) := Nat.mul_le_mul_right _ hKM

private theorem fits_pbytes_of_len (ℓ : ℕ) (Pt : Type) (w : ℕ+) {M : ℕ} (hM : 1 ≤ M)
    {x : SignalPqxdh.Bytes} (hx : x.length ≤ (w : ℕ)) :
    (PB (ℓ := ℓ) (Pt := Pt) w).Fits M x := by
  rw [fits_pbytes_iff]
  calc x.length ≤ 1 * (w : ℕ) := by omega
    _ ≤ M * (w : ℕ) := Nat.mul_le_mul_right _ hM

private theorem fits_bytes_of_len (ℓ : ℕ) (Pt : Type) (w : ℕ+) {M : ℕ} (hM : 1 ≤ M)
    {x : Bytes} (hx : x.length ≤ (w : ℕ)) :
    (B (ℓ := ℓ) (Pt := Pt) w).Fits M x := by
  rw [fits_bytes_iff]
  calc x.length ≤ 1 * (w : ℕ) := by omega
    _ ≤ M * (w : ℕ) := Nat.mul_le_mul_right _ hM

private theorem bits_le_self {M : ℕ} (hM : 1 ≤ M) : bits M ≤ M :=
  bits_le_of_lt Nat.lt_two_pow_self hM

private theorem pbVarint_go_length_le :
    ∀ (k f n : ℕ), n < 2 ^ k → (SignalPqxdh.pbVarint.go f n).length ≤ k + 1
  | 0, 0, _, _ => by simp [SignalPqxdh.pbVarint.go]
  | 0, _ + 1, n, hn => by
    have : n < 128 := by simp at hn; omega
    simp [SignalPqxdh.pbVarint.go, this]
  | _ + 1, 0, _, _ => by simp [SignalPqxdh.pbVarint.go]
  | k + 1, f + 1, n, hn => by
    unfold SignalPqxdh.pbVarint.go
    split
    · simp
    · have hdiv : n / 128 < 2 ^ k := by
        rw [pow_succ'] at hn
        omega
      have ih := pbVarint_go_length_le k f (n / 128) hdiv
      simp only [List.length_cons]
      omega

theorem pbVarint_length_le_bits (n : ℕ) : (SignalPqxdh.pbVarint n).length ≤ bits n + 1 :=
  pbVarint_go_length_le (bits n) n n (lt_two_pow_bits n)

private theorem foldr_max_ge_init {α : Type} (f : α → ℕ) :
    ∀ (l : List α) (z : ℕ), z ≤ l.foldr (fun x acc => max acc (f x)) z
  | [], _ => le_rfl
  | _ :: xs, z => le_trans (foldr_max_ge_init f xs z) (le_max_left _ _)

private theorem foldr_max_mem_le {α : Type} (f : α → ℕ) :
    ∀ (l : List α) (z : ℕ) {x : α}, x ∈ l → f x ≤ l.foldr (fun y acc => max acc (f y)) z
  | [], _, _, hx => nomatch hx
  | y :: ys, z, x, hx => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hx with rfl | hmem
    · exact le_max_right _ _
    · exact le_trans (foldr_max_mem_le f ys z hmem) (le_max_left _ _)

private theorem foldr_max_le {α : Type} (f : α → ℕ) :
    ∀ (l : List α) (z M : ℕ), z ≤ M → (∀ x ∈ l, f x ≤ M) →
      l.foldr (fun x acc => max acc (f x)) z ≤ M
  | [], z, M, hz, _ => hz
  | x :: xs, z, M, hz, hxs => by
    simp only [List.foldr_cons, max_le_iff]
    exact ⟨foldr_max_le f xs z M hz (fun y hy => hxs y (List.mem_cons_of_mem x hy)),
      hxs x List.mem_cons_self⟩

theorem splitSpqrPrev_fst_length_le :
    ∀ (fuel : ℕ) (bs : Bytes), (splitSpqrPrev fuel bs).1.length ≤ fuel
  | 0, bs => by simp [splitSpqrPrev]
  | fuel + 1, bs => by
    unfold splitSpqrPrev
    split
    · simp
    · have ih := splitSpqrPrev_fst_length_le fuel (bs.drop 36)
      simp only [List.length_cons]
      omega

theorem splitSpqrPrev_snd_length_le :
    ∀ (fuel : ℕ) (bs : Bytes), (splitSpqrPrev fuel bs).2.length ≤ 35
  | 0, bs => by simp [splitSpqrPrev]
  | fuel + 1, bs => by
    unfold splitSpqrPrev
    split
    · dsimp only; omega
    · exact splitSpqrPrev_snd_length_le fuel (bs.drop 36)

theorem splitSpqrPrev_fst_length_le_div36 :
    ∀ (fuel : ℕ) (bs : Bytes), (splitSpqrPrev fuel bs).1.length ≤ bs.length / 36
  | 0, _ => Nat.zero_le _
  | fuel + 1, bs => by
    unfold splitSpqrPrev
    split
    · simp
    · next hlt =>
      have hge : 36 ≤ bs.length := Nat.le_of_not_lt hlt
      have ih := splitSpqrPrev_fst_length_le_div36 fuel (bs.drop 36)
      rw [List.length_drop] at ih
      have hdiv : bs.length / 36 = (bs.length - 36) / 36 + 1 :=
        Nat.div_eq_sub_div (by decide) hge
      simp only [List.length_cons]
      omega

private theorem flatMap_prev_length :
    ∀ (entries : List (BitVec 32 × BitVec 256)),
      (entries.flatMap fun (idx, key) =>
        HMAC.toBEBytes 4 idx ++ HMAC.keyToBytes32 key).length = 36 * entries.length
  | [] => rfl
  | (idx, key) :: rest => by
    have hhead : (HMAC.toBEBytes 4 idx ++ HMAC.keyToBytes32 key).length = 36 := by
      simp [HMAC.toBEBytes, HMAC.keyToBytes32]
    rw [List.flatMap_cons, List.length_append, hhead, flatMap_prev_length rest]
    simp only [List.length_cons]
    ring

theorem joinSpqrPrev_length_le (entries : List (BitVec 32 × BitVec 256)) (tail : Bytes) :
    (joinSpqrPrev entries tail).length ≤ 36 * entries.length + 35 := by
  simp only [joinSpqrPrev, List.length_append, flatMap_prev_length]
  have ht := List.length_take_le 35 tail
  omega

/-! ## Sampler size honesty -/

@[simp] theorem atomicBaseSamplers_sDom_eq_unit (ℓ : ℕ) (Pt : Type)
    (s : (atomicBaseSamplers ℓ Pt).Samp) :
    (atomicBaseSamplers ℓ Pt).sDom s = .unit := rfl

theorem atomicBaseSamplers_sizeHonest (ℓ : ℕ) (Pt : Type) :
    SampSizeHonest (atomicBaseSamplers ℓ Pt) :=
  sampSizeHonest_unifSamplers (S := atomicSig ℓ Pt) AtomicBaseUnif.sort AtomicBaseUnif.cost
    (fun b _ => by cases b <;> rfl)

@[simp] theorem atomicSamplers_sDom_eq_unit (ℓ : ℕ) (Pt : Type) [SampleableType Pt]
    (s : (atomicSamplers ℓ Pt).Samp) :
    (atomicSamplers ℓ Pt).sDom s = .unit := rfl

theorem atomicSamplers_sizeHonest (ℓ : ℕ) (Pt : Type) [SampleableType Pt] :
    SampSizeHonest (atomicSamplers ℓ Pt) :=
  sampSizeHonest_unifSamplers (S := atomicSig ℓ Pt) AtomicUnifBase.sort AtomicUnifBase.cost
    (fun b _ => by cases b <;> rfl)

/-! ## Wire, SPQR, and session-state helper bounds -/

private theorem fits_hdrV (ℓ : ℕ) (Pt : Type) {M : ℕ} (hM : 1 ≤ M)
    (m : PreKeyMessageFields) :
    (hdrT (ℓ := ℓ) (Pt := Pt)).Fits M (hdrV (e2eHdrOfPreKeyMsg m)) := by
  have hik : (vecU8 m.idPub).length ≤ 32 := by simp [vecU8, toU8]
  have hek : (vecU8 m.baseKey).length ≤ 32 := by simp [vecU8, toU8]
  have hct : (vecU8 m.kyberCt).length ≤ 1568 := by simp [vecU8, toU8]
  dsimp only [hdrV, e2eHdrOfPreKeyMsg]
  refine ⟨fits_pbytes_of_len ℓ Pt 32 hM hik, fits_pbytes_of_len ℓ Pt 32 hM hek, hM, ?_, hM,
    fits_pbytes_of_len ℓ Pt 1568 hM hct⟩
  rcases m.opkId with _ | _
  · trivial
  · exact hM

private theorem fits_bytes_take48000 (ℓ : ℕ) (Pt : Type) {M : ℕ} (hM : 1500 ≤ M) (x : Bytes) :
    (B (ℓ := ℓ) (Pt := Pt) 32).Fits M (x.take 48000) := by
  rw [fits_bytes_iff]
  have hlen : (x.take 48000).length ≤ 48000 := List.length_take_le 48000 x
  simp only [PNat.val_ofNat]
  omega

private theorem fits_bytes_take64000 (ℓ : ℕ) (Pt : Type) {M : ℕ} (hM : 2000 ≤ M) (x : Bytes) :
    (B (ℓ := ℓ) (Pt := Pt) 32).Fits M (x.take 64000) := by
  rw [fits_bytes_iff]
  have hlen : (x.take 64000).length ≤ 64000 := List.length_take_le 64000 x
  simp only [PNat.val_ofNat]
  omega

private theorem e2eWireInnerBytes_length_le (c : Bytes) {inner : Bytes}
    (h : e2eWireInnerBytes c = some inner) : inner.length ≤ c.length := by
  unfold e2eWireInnerBytes at h
  rcases hm : e2eDecodePreKeyMsg c with _ | m
  · rw [hm] at h
    rcases c with _ | ⟨t, body⟩
    · simp at h
    · dsimp only at h
      split at h
      · injection h with h'; subst h'; simp
      · simp at h
  · rw [hm] at h
    injection h with h'; subst h'
    exact List.length_take_le c.length m.inner

private theorem e2ePartneredInnerBytes_length_le (bobAcc : Bool) (regIdA : BitVec 32)
    (hdr : SignalPqxdh.HandshakeHdr) (c : Bytes) {inner : Bytes}
    (h : e2ePartneredInnerBytes bobAcc regIdA hdr c = some inner) : inner.length ≤ c.length := by
  unfold e2ePartneredInnerBytes at h
  split at h
  · rcases hm : e2eDecodePreKeyMsg c with _ | m
    · rw [hm] at h; simp at h
    · rw [hm] at h; dsimp only at h
      split at h
      · injection h with h'; subst h'; exact List.length_take_le c.length m.inner
      · simp at h
  · rcases hm : e2eDecodePreKeyMsg c with _ | m
    · rw [hm] at h
      rcases c with _ | ⟨t, body⟩
      · simp at h
      · dsimp only at h
        split at h
        · injection h with h'; subst h'; simp
        · simp at h
    · rw [hm] at h; dsimp only at h
      split at h
      · injection h with h'; subst h'; exact List.length_take_le c.length m.inner
      · simp at h

private theorem fits_spqrParamsToV (ℓ : ℕ) (Pt : Type) {M : ℕ} (hM : 1 ≤ M)
    (p : LibsignalSpqrV1.ChainParamsPB) :
    (spqrParamsT (ℓ := ℓ) (Pt := Pt)).Fits M (spqrParamsToV p) :=
  ⟨hM, hM⟩

private theorem fits_spqrVnToV (ℓ : ℕ) (Pt : Type) {M : ℕ} (hM : 2 ≤ M)
    (vn : LibsignalSpqrV1.VersionNegotiationPB) :
    (spqrVnT (ℓ := ℓ) (Pt := Pt)).Fits M (spqrVnToV vn) := by
  have h1 : 1 ≤ M := by omega
  dsimp only [spqrVnToV]
  refine ⟨fits_bytes_take ℓ Pt 32 (K := 2) hM vn.authKey, h1, h1, ?_⟩
  rcases vn.chainParams with _ | p
  · trivial
  · exact fits_spqrParamsToV ℓ Pt h1 p

private theorem fits_spqrDirToV_of_bound (ℓ : ℕ) (Pt : Type) {M : ℕ} (hM : 2 ≤ M)
    {d : LibsignalSpqrV1.EpochDirectionPB}
    (hd : (splitSpqrPrev 2201 d.prev).1.length ≤ M) :
    (spqrDirT (ℓ := ℓ) (Pt := Pt)).Fits M (spqrDirToV d) := by
  have h1 : 1 ≤ M := by omega
  dsimp only [spqrDirToV]
  refine ⟨h1, fits_bytes_take ℓ Pt 32 (K := 2) hM d.next, ⟨hd, fun _ _ => ⟨h1, h1⟩⟩, ?_⟩
  exact fits_bytes_of_len ℓ Pt 35 h1 (splitSpqrPrev_snd_length_le 2201 d.prev)

private theorem fits_spqrChainToV_2201 (ℓ : ℕ) (Pt : Type) {M : ℕ} (hM : 2201 ≤ M)
    (c : LibsignalSpqrV1.ChainPB) :
    (spqrChainT (ℓ := ℓ) (Pt := Pt)).Fits M (spqrChainToV c) := by
  have h1 : 1 ≤ M := by omega
  have h2 : 2 ≤ M := by omega
  dsimp only [spqrChainToV]
  refine ⟨h1, h1, ⟨?_, ?_⟩, fits_bytes_take ℓ Pt 32 (K := 2) h2 c.nextRoot, h1, ?_⟩
  · simp only [List.length_map]
    exact le_trans (List.length_take_le 4 c.links) (by omega)
  · intro lk hlk
    simp only [List.mem_map] at hlk
    obtain ⟨orig, -, rfl⟩ := hlk
    constructor
    · rcases orig.send with _ | s
      · trivial
      · exact fits_spqrDirToV_of_bound ℓ Pt h2
          (le_trans (splitSpqrPrev_fst_length_le 2201 s.prev) hM)
    · rcases orig.recv with _ | r
      · trivial
      · exact fits_spqrDirToV_of_bound ℓ Pt h2
          (le_trans (splitSpqrPrev_fst_length_le 2201 r.prev) hM)
  · rcases c.params with _ | p
    · trivial
    · exact fits_spqrParamsToV ℓ Pt h1 p

private theorem fits_ghostSplitEval (ℓ : ℕ) (Pt : Type) (M : ℕ) (g : GhostState Bytes)
    (hg : ghostStBlocks g ≤ M) :
    (ghostPartsT (ℓ := ℓ) (Pt := Pt)).Fits (M + 16) (ghostSplitEval g) := by
  dsimp only [ghostStBlocks] at hg
  simp only [Nat.max_le] at hg
  obtain ⟨-, hpq, hrc, hce, hep⟩ := hg
  have h1 : 1 ≤ M + 16 := by omega
  have h2 : 2 ≤ M + 16 := by omega
  dsimp only [ghostSplitEval]
  refine ⟨trivial, h1, h2, ?_, h1, h1, trivial, by simp [Ty.Fits]; omega, ?_, ?_, ?_, ?_⟩
  · rcases g.session.remoteIdentity with _ | _
    · trivial
    · exact h2
  · refine ⟨le_trans (foldr_max_ge_init bits g.chainEpochs g.chainEpochs.length) (by omega), ?_⟩
    intro e he
    have := le_trans (foldr_max_mem_le bits g.chainEpochs g.chainEpochs.length he) hce
    simp only [Ty.Fits]; omega
  · rcases g.session.senderChain with _ | _
    · trivial
    · exact ⟨⟨h2, h1⟩, ⟨h1, h1⟩⟩
  · refine ⟨?_, ?_⟩
    · simp only [List.length_map]
      exact le_trans (List.length_take_le 5 g.session.receiverChains) (by omega)
    · intro rcV hrcV
      simp only [List.mem_map] at hrcV
      obtain ⟨rc, hrcTake, rfl⟩ := hrcV
      have hrcMem := List.mem_of_mem_take hrcTake
      refine ⟨h2, ?_, ?_⟩
      · rcases rc.chainKey with _ | _
        · trivial
        · exact ⟨h1, h1⟩
      · refine ⟨?_, fun mkV hmkV => ?_⟩
        · simp only [List.length_map]
          have hrcLe := le_trans (foldr_max_mem_le
            (fun rc : ReceiverChain => rc.messageKeys.foldr
              (fun mk m => max m ((mk.seed.length + 31) / 32)) rc.messageKeys.length)
            g.session.receiverChains g.session.receiverChains.length hrcMem) hrc
          have hmkInit := foldr_max_ge_init (fun mk : MessageKeyGenerator =>
            (mk.seed.length + 31) / 32) rc.messageKeys rc.messageKeys.length
          omega
        · simp only [List.mem_map] at hmkV
          obtain ⟨_, -, rfl⟩ := hmkV
          exact ⟨h1, h1⟩
  · change (g.session.pqRatchetState.length + 32 - 1) / 32 ≤ M + 16
    omega

private theorem fits_ghostJoinEval (ℓ : ℕ) (Pt : Type) (M : ℕ)
    (p : (ghostPartsT (ℓ := ℓ) (Pt := Pt)).denote)
    (hp : (ghostPartsT (ℓ := ℓ) (Pt := Pt)).Fits M p) :
    (GhostStT (ℓ := ℓ) (Pt := Pt)).Fits (M + 16) (ghostJoinEval p) := by
  rcases p with ⟨isB, ver, locId, remId?, rk, prevCtr, pend, ep, cEps, sc?, rcs, pqSt⟩
  rcases hp with ⟨-, _, _, _, _, _, -, hep, hcEps, _, hrcs, hpqSt⟩
  dsimp only at hep hcEps hrcs hpqSt
  change ghostStBlocks (ghostJoinEval (ℓ := ℓ) (Pt := Pt) (isB, (ver, (locId, (remId?, (rk,
    (prevCtr, (pend, (ep, (cEps, (sc?, (rcs, pqSt)))))))))))) ≤ M + 16
  dsimp only [ghostStBlocks, ghostJoinEval]
  have hpq : (pqSt.length + 31) / 32 ≤ M + 16 := by
    change (pqSt.length + 32 - 1) / 32 ≤ M at hpqSt
    omega
  have hce : cEps.foldr (fun e acc => max acc (bits e)) cEps.length ≤ M + 16 := by
    apply foldr_max_le bits cEps cEps.length (M + 16) (by have := hcEps.1; omega)
    intro e he
    have := hcEps.2 e he
    simp only [Ty.Fits] at this
    omega
  simp only [Ty.Fits] at hep
  simp only [Nat.max_le]
  refine ⟨by omega, hpq, ?_, hce, by omega⟩
  apply foldr_max_le
    (fun rc : ReceiverChain => rc.messageKeys.foldr
      (fun mk m => max m ((mk.seed.length + 31) / 32)) rc.messageKeys.length)
    _ _ (M + 16)
    (by simp only [List.length_map]; exact le_trans (List.length_take_le 5 rcs) (by omega))
  intro rc hrcMem
  simp only [List.mem_map] at hrcMem
  obtain ⟨⟨srk, ck?, mks⟩, hTake, rfl⟩ := hrcMem
  have hMem := List.mem_of_mem_take hTake
  have hEntry := hrcs.2 (srk, (ck?, mks)) hMem
  have hlenMks : mks.length ≤ M := hEntry.2.2.1
  apply foldr_max_le (fun mk : MessageKeyGenerator => (mk.seed.length + 31) / 32)
    _ _ (M + 16) (by simp only [List.length_map]; omega)
  intro mk hmkMem
  simp only [List.mem_map] at hmkMem
  obtain ⟨⟨sd, _⟩, -, rfl⟩ := hmkMem
  have hlen : (HMAC.keyToBytes32 sd).length = 32 := by simp [HMAC.keyToBytes32]
  rw [hlen]
  omega

private theorem mem_snd_of_mem_zip {α β : Type} :
    ∀ {xs : List α} {ys : List β} {p : α × β}, p ∈ xs.zip ys → p.2 ∈ ys
  | [], _, _, hp => by simp at hp
  | _, [], _, hp => by simp at hp
  | _ :: _, y :: _, _, hp => by
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hmem
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem y (mem_snd_of_mem_zip hmem)

private theorem fits_e2eEncodeSessionRecord (ℓ : ℕ) (Pt : Type) (M : ℕ)
    (inp : ((U32 (ℓ := ℓ) (Pt := Pt)).denote × (U32 (ℓ := ℓ) (Pt := Pt)).denote ×
      (U32 (ℓ := ℓ) (Pt := Pt)).denote × (hdrT (ℓ := ℓ) (Pt := Pt)).denote) × GhostState Bytes)
    (hinp : (Ty.prod (.prod U32 (.prod U32 (.prod U32 hdrT)))
      (GhostStT (ℓ := ℓ) (Pt := Pt))).Fits M inp) :
    (BinStT (ℓ := ℓ) (Pt := Pt)).Fits (M + 24576) (e2eEncodeSessionRecord inp) := by
  rcases inp with ⟨meta0, g⟩
  have hg : ghostStBlocks g ≤ M := hinp.2
  dsimp only [ghostStBlocks] at hg
  simp only [Nat.max_le] at hg
  obtain ⟨-, -, -, hce, hep⟩ := hg
  change binStBlocks (e2eEncodeSessionRecord (ℓ := ℓ) (Pt := Pt) (meta0, g)) ≤ M + 24576
  dsimp only [binStBlocks, e2eEncodeSessionRecord, binStateOfUnderExtras, EpochGhost.ofGhost]
  have hbBlk : (((encodeRecordUnderExtras
      (e2eRecordExtras meta0.1 meta0.2.1 meta0.2.2.1 (hdrOfV meta0.2.2.2)) g).take
      (32 * 24000)).length + 31) / 32 ≤ M + 24576 := by
    have ht := List.length_take_le (32 * 24000)
      (encodeRecordUnderExtras
        (e2eRecordExtras meta0.1 meta0.2.1 meta0.2.2.1 (hdrOfV meta0.2.2.2)) g)
    omega
  have hchBlk : ((g.session.receiverChains.map (·.senderRatchetKey)).zip g.chainEpochs).foldr
      (fun p acc => max acc (bits p.2))
      ((g.session.receiverChains.map (·.senderRatchetKey)).zip g.chainEpochs).length ≤ M + 24576 := by
    apply foldr_max_le (fun p : PublicKey × ℕ => bits p.2) _ _ (M + 24576)
    · rw [List.length_zip]
      have hinit := foldr_max_ge_init bits g.chainEpochs g.chainEpochs.length
      omega
    · intro p hp
      have hm := mem_snd_of_mem_zip hp
      have hle := le_trans (foldr_max_mem_le bits g.chainEpochs g.chainEpochs.length hm) hce
      omega
  simp only [Nat.max_le]
  exact ⟨by omega, hbBlk, hchBlk, by omega⟩

/-! ## Pure and curve operation table size honesty -/

theorem atomicPureOps_sizeHonest (ℓ : ℕ) (Pt : Type) : OpsSizeHonest (atomicPureOps ℓ Pt) := by
  intro o x M hx
  cases o with
  | pbytesLit w v =>
    change (PB (ℓ := ℓ) (Pt := Pt) w).Fits (M + (w + v.length)) v
    rw [fits_pbytes_iff]
    have hw : 1 ≤ (w : ℕ) := w.pos
    have h1 : v.length ≤ (M + ((w : ℕ) + v.length)) * 1 := by omega
    exact le_trans h1 (Nat.mul_le_mul_left _ hw)
  | pbytesCat m n =>
    rcases x with ⟨x₁, x₂⟩
    have hx₁ : x₁.length ≤ M * m := (fits_pbytes_iff ℓ Pt m M x₁).1 hx.1
    have hx₂ : x₂.length ≤ M * n := (fits_pbytes_iff ℓ Pt n M x₂).1 hx.2
    change (PB (ℓ := ℓ) (Pt := Pt) (m + n)).Fits (M + (m + n)) (x₁ ++ x₂)
    rw [fits_pbytes_iff, List.length_append]
    simp only [PNat.add_coe]
    calc x₁.length + x₂.length
        ≤ M * (m : ℕ) + M * (n : ℕ) := by omega
      _ = M * ((m : ℕ) + n) := by ring
      _ ≤ (M + ((m : ℕ) + n)) * ((m : ℕ) + n) := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  | pbytesCons b w =>
    have hxw : x.length ≤ M * w := (fits_pbytes_iff ℓ Pt w M x).1 hx
    change (PB (ℓ := ℓ) (Pt := Pt) (w + 1)).Fits (M + (w + 1)) (b :: x)
    rw [fits_pbytes_iff]
    simp only [List.length_cons, PNat.add_coe, PNat.val_ofNat]
    have : M * (w : ℕ) + 1 ≤ (M + ((w : ℕ) + 1)) * ((w : ℕ) + 1) := by nlinarith
    omega
  | pbytesWiden w d =>
    have hxw : x.length ≤ M * w := (fits_pbytes_iff ℓ Pt w M x).1 hx
    change (PB (ℓ := ℓ) (Pt := Pt) (w + d)).Fits (M + (w + d)) x
    rw [fits_pbytes_iff]
    simp only [PNat.add_coe]
    have : M * (w : ℕ) ≤ (M + ((w : ℕ) + d)) * ((w : ℕ) + d) := by nlinarith
    omega
  | pbytesTakeK w k =>
    change (PB (ℓ := ℓ) (Pt := Pt) k).Fits (M + (w + k)) (x.take k)
    rw [fits_pbytes_iff]
    have hlen : (x.take k).length ≤ (k : ℕ) := List.length_take_le k x
    have hk : 1 ≤ M + ((w : ℕ) + k) := by have := w.pos; omega
    calc (x.take k).length ≤ 1 * (k : ℕ) := by omega
      _ ≤ (M + ((w : ℕ) + k)) * k := Nat.mul_le_mul_right _ hk
  | pbytesTake w =>
    rcases x with ⟨n, s⟩
    have hs : s.length ≤ M * w := (fits_pbytes_iff ℓ Pt w M s).1 hx.2
    change (PB (ℓ := ℓ) (Pt := Pt) w).Fits (M + (w + 1)) (s.take n)
    rw [fits_pbytes_iff]
    have hlen : (s.take n).length ≤ s.length := List.length_take_le' n s
    have : M * (w : ℕ) ≤ (M + ((w : ℕ) + 1)) * w := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    omega
  | pbytesDrop w =>
    rcases x with ⟨n, s⟩
    have hs : s.length ≤ M * w := (fits_pbytes_iff ℓ Pt w M s).1 hx.2
    change (PB (ℓ := ℓ) (Pt := Pt) w).Fits (M + (w + 1)) (s.drop n)
    rw [fits_pbytes_iff, List.length_drop]
    have : M * (w : ℕ) ≤ (M + ((w : ℕ) + 1)) * w := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    omega
  | pbytesLen w =>
    have hxw : x.length ≤ M * w := (fits_pbytes_iff ℓ Pt w M x).1 hx
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost, Ty.Fits]
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · have hx0 : x.length = 0 := by omega
      have h1 : bits 0 = 1 := rfl
      have hbw := one_le_bits w
      rw [hx0, h1]; omega
    · have h1 : bits x.length ≤ bits ((w : ℕ) * M) :=
        bits_mono (by rw [Nat.mul_comm]; exact hxw)
      have h2 := bits_mul w M
      have h3 := bits_le_self hM
      omega
  | pbVarint =>
    dsimp only [atomicPureOps, AtomicPureOp.dom, Ty.Fits] at hx
    change (PB (ℓ := ℓ) (Pt := Pt) 10).Fits (M + 10) (SignalPqxdh.pbVarint x)
    rw [fits_pbytes_iff]
    have hlen := pbVarint_length_le_bits x
    simp only [PNat.val_ofNat]
    omega
  | bytesLit w v =>
    change (B (ℓ := ℓ) (Pt := Pt) w).Fits (M + (w + v.length)) v
    rw [fits_bytes_iff]
    have hw : 1 ≤ (w : ℕ) := w.pos
    have h1 : v.length ≤ (M + ((w : ℕ) + v.length)) * 1 := by omega
    exact le_trans h1 (Nat.mul_le_mul_left _ hw)
  | bytesCat m n =>
    rcases x with ⟨x₁, x₂⟩
    have hx₁ : x₁.length ≤ M * m := (fits_bytes_iff ℓ Pt m M x₁).1 hx.1
    have hx₂ : x₂.length ≤ M * n := (fits_bytes_iff ℓ Pt n M x₂).1 hx.2
    change (B (ℓ := ℓ) (Pt := Pt) (m + n)).Fits (M + (m + n)) (x₁ ++ x₂)
    rw [fits_bytes_iff, List.length_append]
    simp only [PNat.add_coe]
    calc x₁.length + x₂.length
        ≤ M * (m : ℕ) + M * (n : ℕ) := by omega
      _ = M * ((m : ℕ) + n) := by ring
      _ ≤ (M + ((m : ℕ) + n)) * ((m : ℕ) + n) := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  | bytesAppend8 =>
    rcases x with ⟨x₁, x₂⟩
    have hx₁ : x₁.length ≤ M * 32 := (fits_bytes_iff ℓ Pt 32 M x₁).1 hx.1
    have hx₂ : (x₂.take 8).length ≤ 8 := List.length_take_le 8 x₂
    change (B (ℓ := ℓ) (Pt := Pt) 32).Fits (M + 2) (x₁ ++ x₂.take 8)
    rw [fits_bytes_iff, List.length_append]
    simp only [PNat.val_ofNat] at hx₁ ⊢
    omega
  | bytesAppend16 =>
    rcases x with ⟨x₁, x₂⟩
    have hx₁ : x₁.length ≤ M * 32 := (fits_bytes_iff ℓ Pt 32 M x₁).1 hx.1
    have hx₂ : (x₂.take 16).length ≤ 16 := List.length_take_le 16 x₂
    change (B (ℓ := ℓ) (Pt := Pt) 32).Fits (M + 2) (x₁ ++ x₂.take 16)
    rw [fits_bytes_iff, List.length_append]
    simp only [PNat.val_ofNat] at hx₁ ⊢
    omega
  | bytesCons b w =>
    have hxw : x.length ≤ M * w := (fits_bytes_iff ℓ Pt w M x).1 hx
    change (B (ℓ := ℓ) (Pt := Pt) (w + 1)).Fits (M + (w + 1)) (b :: x)
    rw [fits_bytes_iff]
    simp only [List.length_cons, PNat.add_coe, PNat.val_ofNat]
    have : M * (w : ℕ) + 1 ≤ (M + ((w : ℕ) + 1)) * ((w : ℕ) + 1) := by nlinarith
    omega
  | bytesWiden w d =>
    have hxw : x.length ≤ M * w := (fits_bytes_iff ℓ Pt w M x).1 hx
    change (B (ℓ := ℓ) (Pt := Pt) (w + d)).Fits (M + (w + d)) x
    rw [fits_bytes_iff]
    simp only [PNat.add_coe]
    have : M * (w : ℕ) ≤ (M + ((w : ℕ) + d)) * ((w : ℕ) + d) := by nlinarith
    omega
  | bytesTakeK w k =>
    change (B (ℓ := ℓ) (Pt := Pt) k).Fits (M + (w + k)) (x.take k)
    rw [fits_bytes_iff]
    have hlen : (x.take k).length ≤ (k : ℕ) := List.length_take_le k x
    have hk : 1 ≤ M + ((w : ℕ) + k) := by have := w.pos; omega
    calc (x.take k).length ≤ 1 * (k : ℕ) := by omega
      _ ≤ (M + ((w : ℕ) + k)) * k := Nat.mul_le_mul_right _ hk
  | bytesTake w =>
    rcases x with ⟨n, s⟩
    have hs : s.length ≤ M * w := (fits_bytes_iff ℓ Pt w M s).1 hx.2
    change (B (ℓ := ℓ) (Pt := Pt) w).Fits (M + (w + 1)) (s.take n)
    rw [fits_bytes_iff]
    have hlen : (s.take n).length ≤ s.length := List.length_take_le' n s
    have : M * (w : ℕ) ≤ (M + ((w : ℕ) + 1)) * w := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    omega
  | bytesDrop w =>
    rcases x with ⟨n, s⟩
    have hs : s.length ≤ M * w := (fits_bytes_iff ℓ Pt w M s).1 hx.2
    change (B (ℓ := ℓ) (Pt := Pt) w).Fits (M + (w + 1)) (s.drop n)
    rw [fits_bytes_iff, List.length_drop]
    have : M * (w : ℕ) ≤ (M + ((w : ℕ) + 1)) * w := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    omega
  | bytesLen w =>
    have hxw : x.length ≤ M * w := (fits_bytes_iff ℓ Pt w M x).1 hx
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost, Ty.Fits]
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · have hx0 : x.length = 0 := by omega
      have h1 : bits 0 = 1 := rfl
      have hbw := one_le_bits w
      rw [hx0, h1]; omega
    · have h1 : bits x.length ≤ bits ((w : ℕ) * M) :=
        bits_mono (by rw [Nat.mul_comm]; exact hxw)
      have h2 := bits_mul w M
      have h3 := bits_le_self hM
      omega
  | pbytesToBytes w =>
    have hxw : x.length ≤ M * w := (fits_pbytes_iff ℓ Pt w M x).1 hx
    change (B (ℓ := ℓ) (Pt := Pt) w).Fits (M + w) (ofU8 x)
    rw [fits_bytes_iff]
    have hlen : (ofU8 x).length = x.length := by simp [ofU8]
    have : M * (w : ℕ) ≤ (M + (w : ℕ)) * w := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    omega
  | bytesToPbytes w =>
    have hxw : x.length ≤ M * w := (fits_bytes_iff ℓ Pt w M x).1 hx
    change (PB (ℓ := ℓ) (Pt := Pt) w).Fits (M + w) (toU8 x)
    rw [fits_pbytes_iff]
    have hlen : (toU8 x).length = x.length := by simp [toU8]
    have : M * (w : ℕ) ≤ (M + (w : ℕ)) * w := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    omega
  | pu32Lit _ | pu32OfNat | pu32ToU32 | u32ToPu32 | u8Lit _ | u8OfNat | u64Trunc8
  | u32Lit _ | u32OfNat | u32Add | u32Sub | u64Lit _ | u64OfNat | u64Add | u64Sub | bytesToU64Le
  | bv128Lit _ | bv128Xor | bytesToBv128 | bv256Lit _ | pbytesToBv256 | bytesToBv256
  | bv512Lit _ | idKeyOfPbytes | pkOfPbytes | plainDefault | fitPlain =>
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost,
      Ty.Fits, AtomicSort.blocks]
    omega
  | pu32ToNat =>
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost, Ty.Fits]
    have hb : bits x.toNat ≤ 32 := bits_le_of_lt x.toBitVec.isLt (by omega)
    omega
  | u8ToNat =>
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost, Ty.Fits]
    have hb : bits x.toNat ≤ 8 := bits_le_of_lt x.isLt (by omega)
    omega
  | u32ToNat =>
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost, Ty.Fits]
    have hb : bits x.toNat ≤ 32 := bits_le_of_lt x.isLt (by omega)
    omega
  | u64ToNat =>
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost, Ty.Fits]
    have hb : bits x.toNat ≤ 64 := bits_le_of_lt x.isLt (by omega)
    omega
  | finVal n =>
    dsimp only [atomicPureOps, AtomicPureOp.dom, AtomicPureOp.cod, AtomicPureOp.eval,
      AtomicPureOp.cost, Ty.Fits, AtomicSort.blocks] at hx ⊢
    omega
  | u32BeBytes =>
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost]
    apply fits_bytes_of_len ℓ Pt 4 (by omega)
    simp [HMAC.toBEBytes]
  | u64LeBytes =>
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost]
    apply fits_bytes_of_len ℓ Pt 8 (by omega)
    simp [toLEBytes]
  | bv128ToBytes16 =>
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost]
    apply fits_bytes_of_len ℓ Pt 16 (by omega)
    simp [toLEBytes]
  | bv256ToPbytes32 =>
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost]
    apply fits_pbytes_of_len ℓ Pt 32 (by omega)
    simp [SignalPqxdh.word256ToBytes]
  | bv256ToBytes32 =>
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost]
    apply fits_bytes_of_len ℓ Pt 32 (by omega)
    simp [HMAC.keyToBytes32]
  | bv512ToBytes64 =>
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost]
    apply fits_bytes_of_len ℓ Pt 64 (by omega)
    simp [LibsignalSpqrV1.coinBytes_length]
  | bv512ToPbytes64 =>
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost]
    apply fits_pbytes_of_len ℓ Pt 64 (by omega)
    simp [toU8, LibsignalSpqrV1.coinBytes_length]
  | idKeySerialize =>
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost]
    apply fits_bytes_of_len ℓ Pt 33 (by omega)
    simp [IdentityKey.serialize, PublicKey.serialize]
  | pkSerialize =>
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost]
    apply fits_bytes_of_len ℓ Pt 33 (by omega)
    simp [PublicKey.serialize]
  | pkDeserialize =>
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost]
    rcases (PublicKey.deserialize x).toOption with _ | _
    · trivial
    · dsimp only [Ty.Fits, AtomicSort.blocks]; omega
  | plainToBytes =>
    change (B (ℓ := ℓ) (Pt := Pt) 32).Fits (M + (ℓ / 32 + 2)) x.toList
    rw [fits_bytes_iff]
    simp only [List.Vector.toList_length, PNat.val_ofNat]
    omega
  | bytesToPlain =>
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost]
    split
    · dsimp only [Ty.Fits, AtomicSort.blocks]; omega
    · trivial
  | parsePreKeyWire =>
    have hxc : x.length ≤ M * 32 := (fits_bytes_iff ℓ Pt 32 M x).1 hx
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost]
    rcases e2eDecodePreKeyMsg x with _ | m
    · trivial
    · dsimp only [Option.map]
      have h1 : 1 ≤ M + 96 := by omega
      refine ⟨h1, fits_hdrV ℓ Pt h1 m, ?_⟩
      rw [fits_bytes_iff]
      have ht := List.length_take_le x.length m.inner
      simp only [PNat.val_ofNat] at hxc ⊢
      omega
  | partneredInnerBytes =>
    rcases x with ⟨bobAcc, regIdA, hdr, c⟩
    have hcc : c.length ≤ M * 32 := (fits_bytes_iff ℓ Pt 32 M c).1 hx.2.2.2
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost]
    rcases h : e2ePartneredInnerBytes bobAcc regIdA (hdrOfV hdr) c with _ | inner
    · trivial
    · change (B (ℓ := ℓ) (Pt := Pt) 32).Fits (M + 128) inner
      rw [fits_bytes_iff]
      have hlen := e2ePartneredInnerBytes_length_le bobAcc regIdA (hdrOfV hdr) c h
      simp only [PNat.val_ofNat] at hcc ⊢
      omega
  | wireInnerBytes =>
    have hxc : x.length ≤ M * 32 := (fits_bytes_iff ℓ Pt 32 M x).1 hx
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost]
    rcases h : e2eWireInnerBytes x with _ | inner
    · trivial
    · change (B (ℓ := ℓ) (Pt := Pt) 32).Fits (M + 96) inner
      rw [fits_bytes_iff]
      have hlen := e2eWireInnerBytes_length_le x h
      simp only [PNat.val_ofNat] at hxc ⊢
      omega
  | splitWhisperWire =>
    have hxc : x.length ≤ M * 32 := (fits_bytes_iff ℓ Pt 32 M x).1 hx
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost]
    rcases x with _ | ⟨t, body⟩
    · trivial
    · dsimp only
      split
      · change (B (ℓ := ℓ) (Pt := Pt) 32).Fits (M + 2) body
        rw [fits_bytes_iff]
        simp only [List.length_cons, PNat.val_ofNat] at hxc ⊢
        omega
      · trivial
  | signalMsgParse =>
    have hxb : x.length ≤ M * 32 := (fits_bytes_iff ℓ Pt 32 M x).1 hx
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost]
    rcases SignalMessage.tryFrom protoSignalCodec x with _ | m
    · trivial
    · have h1 : 1 ≤ M + (ℓ / 32 + 18) := by omega
      have h2 : 2 ≤ M + (ℓ / 32 + 18) := by omega
      have hslice : ∀ s : Bytes,
          (B (ℓ := ℓ) (Pt := Pt) 32).Fits (M + (ℓ / 32 + 18)) (s.take x.length) := by
        intro s
        rw [fits_bytes_iff]
        have ht := List.length_take_le x.length s
        simp only [PNat.val_ofNat] at hxb ⊢
        omega
      refine ⟨⟨h1, h2, h1, h1⟩, hslice m.ciphertext, hslice m.pqRatchet, ?_⟩
      rcases m.addresses with _ | addr
      · trivial
      · exact hslice addr
  | wrapWhisperWire =>
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost]
    split
    · rw [fits_bytes_iff]; simp
    · exact fits_bytes_take ℓ Pt 32 (K := 2 * (ℓ / 32) + 26) (by omega) _
  | wrapPreKeyWire =>
    rcases x with ⟨regIdA, hdr, inner⟩
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost]
    split
    · rw [fits_bytes_iff]; simp
    · exact fits_bytes_take ℓ Pt 32 (K := 2 * (ℓ / 32) + 84) (by omega) _
  | spqrParsePreamble =>
    have hxm : x.length ≤ M * 32 := (fits_bytes_iff ℓ Pt 32 M x).1 hx
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost]
    rcases LibsignalSpqrV1.msgPreamble x with _ | p
    · trivial
    · have h1 : 1 ≤ M + 4 := by omega
      dsimp only [Option.map]
      refine ⟨h1, h1, h1, ?_⟩
      rw [fits_bytes_iff]
      have ht := List.length_take_le x.length p.remaining
      simp only [PNat.val_ofNat] at hxm ⊢
      omega
  | spqrAssembleMsg =>
    rcases x with ⟨ep, idx, sfx⟩
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost]
    exact fits_bytes_take ℓ Pt 32 (K := 3) (by omega)
      (LibsignalSpqrV1.encode_varint (idx.zeroExtend 64)
        (LibsignalSpqrV1.encode_varint ep [1#8]) ++ sfx.take 64)
  | spqrStateSplit =>
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost, spqrSplitEval]
    rcases LibsignalSpqrV1.Proto.spqrDecodeState x with _ | st
    · trivial
    · dsimp only
      refine ⟨?_, ?_, ?_⟩
      · rcases st.inner with _ | ⟨⟨v⟩⟩
        · trivial
        · dsimp only [Option.map]
          exact fits_bytes_take64000 ℓ Pt (by omega) (LibsignalSpqrV1.V1State.encodeRaw v)
      · rcases st.versionNegotiation with _ | vn
        · trivial
        · dsimp only [Option.map]
          exact fits_spqrVnToV ℓ Pt (by omega) vn
      · rcases st.chain with _ | c
        · trivial
        · dsimp only [Option.map]
          exact fits_spqrChainToV_2201 ℓ Pt (by omega) c
  | spqrStateJoin =>
    dsimp only [atomicPureOps, AtomicPureOp.cod, AtomicPureOp.eval, AtomicPureOp.cost]
    exact fits_bytes_take ℓ Pt 32 (K := 11000) (by omega) _
  | ghostStateSplit =>
    exact fits_ghostSplitEval ℓ Pt M x hx
  | ghostStateJoin =>
    exact fits_ghostJoinEval ℓ Pt M x hx
  | encodeSessionRecord =>
    exact fits_e2eEncodeSessionRecord ℓ Pt M x hx
  | pbytesEq _ _ | bytesEq _ _ | bytesLtOp _ _ | pu32Eq | u8Eq | u8Lt | u32Eq | u32Lt
  | u64Eq | u64Lt | finEq _ | bv128Eq | bv256Eq | idKeyEq | pkEq | plainEq
  | checkShortCiphertext | isValidSignalWire =>
    trivial

theorem atomicCurveCheckOps_sizeHonest (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    OpsSizeHonest (atomicCurveCheckOps ℓ decT encT) := by
  intro o _ _ _
  cases o <;> trivial

theorem atomicPtEncOps_sizeHonest (ℓ : ℕ) {Pt : Type} (encT : Pt → PublicKey) :
    OpsSizeHonest (atomicPtEncOps ℓ encT) := by
  intro o _ M _
  cases o
  dsimp only [atomicPtEncOps, Ty.Fits, AtomicSort.blocks]
  omega

theorem atomicPtDecOps_sizeHonest (ℓ : ℕ) {Pt : Type} (decT : PublicKey → Option Pt) :
    OpsSizeHonest (atomicPtDecOps ℓ decT) := by
  intro o x M _
  cases o
  dsimp only [atomicPtDecOps]
  rcases decT x with _ | _
  · trivial
  · dsimp only [Ty.Fits, AtomicSort.blocks]; omega

/-! ## Cryptographic and composed operation table size honesty -/

theorem atomicSymOps_sizeHonest (ℓ : ℕ) (Pt : Type) (C : Crypto) :
    OpsSizeHonest (atomicSymOps ℓ Pt C) := by
  intro o x M _
  cases o with
  | sessionKeyPairGen | deriveMsgKeys | hmacSha256Op _ | aes256EncBlock | aes256DecBlock =>
    dsimp only [atomicSymOps, AtomicSymOp.cod, AtomicSymOp.eval, AtomicSymOp.cost,
      Ty.Fits, AtomicSort.blocks]
    omega
  | sessionRootCreateChain =>
    dsimp only [atomicSymOps, AtomicSymOp.cod, AtomicSymOp.eval, AtomicSymOp.cost]
    rcases LibsignalSession.rootCreateChain C x.1 x.2.1
        ⟨Ratchet.keyToBytesVec32 x.2.2⟩ with _ | ⟨_, _⟩
    · trivial
    · dsimp only [Ty.Fits, AtomicSort.blocks]; omega
  | chainStep =>
    dsimp only [atomicSymOps, AtomicSymOp.cod, AtomicSymOp.eval, AtomicSymOp.cost]
    rcases LibsignalSession.ChainKey.nextChainKey C.F { key := x.1, index := x.2 } with _ | _
    · trivial
    · dsimp only [Ty.Fits, AtomicSort.blocks]; omega
  | aes256CbcEnc =>
    dsimp only [atomicSymOps, AtomicSymOp.cod, AtomicSymOp.eval, AtomicSymOp.cost]
    exact fits_bytes_take ℓ Pt 32 (K := ℓ / 32 + 2) (by omega) _
  | aes256CbcDec =>
    dsimp only [atomicSymOps, AtomicSymOp.cod, AtomicSymOp.eval, AtomicSymOp.cost]
    rcases aesCbcDecrypt C.D x.1 x.2.1 x.2.2 with _ | _
    · trivial
    · dsimp only [Option.map, Ty.Fits, AtomicSort.blocks]; omega
  | signalMsgEncode =>
    dsimp only [atomicSymOps, AtomicSymOp.cod, AtomicSymOp.eval, AtomicSymOp.cost]
    exact fits_bytes_take ℓ Pt 32 (K := 2 * (ℓ / 32) + 24) (by omega) _
  | signalMsgVerifyMac =>
    trivial

theorem atomicGroupOps_sizeHonest (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (lam : Pt := 0) :
    OpsSizeHonest (atomicGroupOps ℓ Pt C Dh encPt lam) := by
  intro o x M _
  cases o with
  | ptBase | ptLam | ptDh | extractPrfTag | rootExpandPrg =>
    dsimp only [atomicGroupOps, AtomicGroupOp.cod, AtomicGroupOp.eval, AtomicGroupOp.cost,
      Ty.Fits, AtomicSort.blocks]
    omega
  | ptEncBytes =>
    dsimp only [atomicGroupOps, AtomicGroupOp.cod, AtomicGroupOp.eval, AtomicGroupOp.cost]
    exact fits_bytes_take ℓ Pt 32 (K := 1) (by omega) (encPt x)
  | ptIsZero | ptEq =>
    trivial

private theorem linksFromPb_prev_bound {ℓ : ℕ} {Pt : Type} {M : ℕ} :
    ∀ {pbs : List ((spqrEpochLinkT (ℓ := ℓ) (Pt := Pt)).denote)}
      {links : List LibsignalSpqrV1.ChainEpoch},
      (∀ p ∈ pbs, (spqrEpochLinkT (ℓ := ℓ) (Pt := Pt)).Fits M p) →
      LibsignalSpqrV1.Chain.linksFromPb
        (pbs.map fun (s?, r?) =>
          ({ send := s?.map spqrDirOfV, recv := r?.map spqrDirOfV } :
            LibsignalSpqrV1.ChainEpochPB)) = .ok links →
      ∀ lk ∈ links,
        lk.send.prev.data.length ≤ 36 * M + 35 ∧ lk.recv.prev.data.length ≤ 36 * M + 35
  | [], _, _, hok, lk, hlk => by
    simp [LibsignalSpqrV1.Chain.linksFromPb] at hok
    subst hok; simp at hlk
  | (s?, r?) :: rest, _, hpbs, hok, lk, hlk => by
    simp only [List.map_cons, LibsignalSpqrV1.Chain.linksFromPb] at hok
    rcases s? with _ | sv
    · simp [Bind.bind, Except.bind] at hok
    · rcases r? with _ | rv
      · rcases heq : LibsignalSpqrV1.ChainEpochDirection.fromPb (spqrDirOfV sv) with _ | _ <;>
          simp [heq, Bind.bind, Except.bind] at hok
      · simp only [Option.map_some, Bind.bind, Except.bind, Pure.pure, Except.pure] at hok
        rcases hs : LibsignalSpqrV1.ChainEpochDirection.fromPb (spqrDirOfV sv) with _ | sendCed
        · rw [hs] at hok; simp at hok
        · rw [hs] at hok; dsimp only at hok
          rcases hr : LibsignalSpqrV1.ChainEpochDirection.fromPb (spqrDirOfV rv) with _ | recvCed
          · rw [hr] at hok; simp at hok
          · rw [hr] at hok; dsimp only at hok
            rcases ht : LibsignalSpqrV1.Chain.linksFromPb
                (rest.map fun (s?, r?) =>
                  { send := s?.map spqrDirOfV, recv := r?.map spqrDirOfV }) with _ | tail
            · rw [ht] at hok; simp at hok
            · rw [ht] at hok; dsimp only at hok
              injection hok with hEq; subst hEq
              rcases List.mem_cons.1 hlk with rfl | hmem
              · have hhead := hpbs (some sv, some rv) List.mem_cons_self
                have hsEq : sendCed.prev.data = (spqrDirOfV sv).prev := by
                  unfold LibsignalSpqrV1.ChainEpochDirection.fromPb at hs
                  split at hs
                  · simp at hs
                  · injection hs with hs'; rw [← hs']
                have hrEq : recvCed.prev.data = (spqrDirOfV rv).prev := by
                  unfold LibsignalSpqrV1.ChainEpochDirection.fromPb at hr
                  split at hr
                  · simp at hr
                  · injection hr with hr'; rw [← hr']
                have hsvLen : sv.2.2.1.length ≤ M := hhead.1.2.2.1.1
                have hrvLen : rv.2.2.1.length ≤ M := hhead.2.2.2.1.1
                have hsJ := joinSpqrPrev_length_le sv.2.2.1 sv.2.2.2
                have hrJ := joinSpqrPrev_length_le rv.2.2.1 rv.2.2.2
                simp only [spqrDirOfV] at hsEq hrEq
                rw [hsEq, hrEq]
                exact ⟨by omega, by omega⟩
              · exact linksFromPb_prev_bound
                  (fun p hp => hpbs p (List.mem_cons_of_mem _ hp)) ht lk hmem

private theorem fits_spqrChainFromVnEval (ℓ : ℕ) (Pt : Type) (M : ℕ) (F : ShaCompress)
    (vn : (spqrVnT (ℓ := ℓ) (Pt := Pt)).denote) :
    (Ty.opt (spqrChainT (ℓ := ℓ) (Pt := Pt))).Fits (M + 16) (spqrChainFromVnEval F vn) := by
  unfold spqrChainFromVnEval LibsignalSpqrV1.chainFromVersionNegotiation
  rcases LibsignalSpqrV1.Direction.fromI32? (spqrVnOfV vn).direction with _ | _
  · trivial
  · simp only [Bind.bind, Except.bind]
    rcases (spqrVnOfV vn).chainParams with _ | _
    · trivial
    · simp only [LibsignalSpqrV1.Chain.new, LibsignalSpqrV1.Chain.intoPb,
        LibsignalSpqrV1.Chain.cedForDirection, LibsignalSpqrV1.ChainEpochDirection.new,
        LibsignalSpqrV1.ChainEpochDirection.intoPb, LibsignalSpqrV1.KeyHistory.new]
      have h1 : 1 ≤ M + 16 := by omega
      have h2 : 2 ≤ M + 16 := by omega
      dsimp only [spqrChainToV]
      refine ⟨h1, h1, ⟨by simp, ?_⟩, fits_bytes_take ℓ Pt 32 (K := 2) h2 _, h1, ⟨h1, h1⟩⟩
      intro lk hlk
      dsimp only [List.take, List.map] at hlk
      simp only [List.mem_singleton] at hlk
      subst hlk
      have hdir : ∀ nextBytes : Bytes,
          (spqrDirT (ℓ := ℓ) (Pt := Pt)).Fits (M + 16)
            (spqrDirToV { ctr := 0#32, next := nextBytes, prev := [] }) :=
        fun _ => fits_spqrDirToV_of_bound ℓ Pt h2 (by simp [splitSpqrPrev])
      exact ⟨hdir _, hdir _⟩

private theorem fits_spqrChainAddEpochEval (ℓ : ℕ) (Pt : Type) (M : ℕ) (F : ShaCompress)
    (ch : (spqrChainT (ℓ := ℓ) (Pt := Pt)).denote) (ep : BitVec 64) (sec : BitVec 256)
    (hch : (spqrChainT (ℓ := ℓ) (Pt := Pt)).Fits M ch) :
    (Ty.prod .bool (.opt (spqrChainT (ℓ := ℓ) (Pt := Pt)))).Fits (M + 24)
      (spqrChainAddEpochEval F ch ep sec) := by
  refine ⟨trivial, ?_⟩
  unfold spqrChainAddEpochEval
  rcases hfrom : LibsignalSpqrV1.Chain.fromPb (spqrChainOfV ch) with _ | c0
  · trivial
  · dsimp only
    rcases hadd : c0.addEpoch (LibsignalSpqrV1.spqrHkdfWith F)
        ⟨ep, HMAC.keyToBytes32 sec⟩ with _ | c1
    · trivial
    · dsimp only
      have hc0Links : ∀ lk ∈ c0.links,
          lk.send.prev.data.length ≤ 36 * M + 35 ∧ lk.recv.prev.data.length ≤ 36 * M + 35 := by
        unfold LibsignalSpqrV1.Chain.fromPb at hfrom
        rcases hd : LibsignalSpqrV1.Direction.fromI32? (spqrChainOfV ch).direction with _ | _
        · rw [hd] at hfrom; simp [Bind.bind, Except.bind] at hfrom
        · rw [hd] at hfrom
          simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hfrom
          rcases hlinks : LibsignalSpqrV1.Chain.linksFromPb (spqrChainOfV ch).links with _ | _
          · rw [hlinks] at hfrom; simp at hfrom
          · rw [hlinks] at hfrom; dsimp only at hfrom
            rcases hp : (spqrChainOfV ch).params with _ | _
            · rw [hp] at hfrom; simp at hfrom
            · rw [hp] at hfrom; dsimp only at hfrom
              injection hfrom with hc0Eq; subst hc0Eq
              exact linksFromPb_prev_bound hch.2.2.1.2 hlinks
      have hc1Links : ∀ lk ∈ c1.links,
          lk.send.prev.data.length ≤ 36 * M + 35 ∧ lk.recv.prev.data.length ≤ 36 * M + 35 := by
        unfold LibsignalSpqrV1.Chain.addEpoch at hadd
        split at hadd
        · simp at hadd
        · split at hadd
          · simp at hadd
          · injection hadd with hc1Eq; subst hc1Eq
            intro lk hlk
            rcases List.mem_append.1 hlk with hmem | hnew
            · exact hc0Links lk hmem
            · simp only [List.mem_singleton] at hnew
              subst hnew
              simp [LibsignalSpqrV1.Chain.cedForDirection,
                LibsignalSpqrV1.ChainEpochDirection.new, LibsignalSpqrV1.KeyHistory.new]
      have h1 : 1 ≤ M + 24 := by omega
      have h2 : 2 ≤ M + 24 := by omega
      dsimp only [spqrChainToV]
      refine ⟨h1, h1, ⟨?_, ?_⟩, fits_bytes_take ℓ Pt 32 (K := 2) h2 _, h1, ?_⟩
      · simp only [List.length_map]
        exact le_trans (List.length_take_le 4 c1.intoPb.links) (by omega)
      · intro lkV hlkV
        simp only [List.mem_map] at hlkV
        obtain ⟨lkPb, hlkTake, rfl⟩ := hlkV
        have hlkIn := List.mem_of_mem_take hlkTake
        simp only [LibsignalSpqrV1.Chain.intoPb, List.mem_map] at hlkIn
        obtain ⟨lk, hlkMem, rfl⟩ := hlkIn
        obtain ⟨hsLen, hrLen⟩ := hc1Links lk hlkMem
        have hsDiv : (splitSpqrPrev 2201 lk.send.intoPb.prev).1.length ≤ M + 24 := by
          have h1 := splitSpqrPrev_fst_length_le_div36 2201 lk.send.intoPb.prev
          simp only [LibsignalSpqrV1.ChainEpochDirection.intoPb] at h1 ⊢
          omega
        have hrDiv : (splitSpqrPrev 2201 lk.recv.intoPb.prev).1.length ≤ M + 24 := by
          have h1 := splitSpqrPrev_fst_length_le_div36 2201 lk.recv.intoPb.prev
          simp only [LibsignalSpqrV1.ChainEpochDirection.intoPb] at h1 ⊢
          omega
        exact ⟨fits_spqrDirToV_of_bound ℓ Pt h2 hsDiv, fits_spqrDirToV_of_bound ℓ Pt h2 hrDiv⟩
      · rcases c1.intoPb.params with _ | p
        · trivial
        · exact fits_spqrParamsToV ℓ Pt h1 p

theorem atomicSpqrKemOps_sizeHonest (ℓ : ℕ) (Pt : Type) (C : Crypto)
    (K : LibsignalSpqrV1.MlKem) :
    OpsSizeHonest (atomicSpqrKemOps ℓ Pt C K) := by
  intro o x M hx
  cases o with
  | spqrV1InitOp =>
    dsimp only [atomicSpqrKemOps, AtomicSpqrKemOp.cod, AtomicSpqrKemOp.eval, AtomicSpqrKemOp.cost]
    exact fits_bytes_take ℓ Pt 32 (K := 16) (by omega) _
  | spqrNegotiateInit =>
    rcases x with ⟨verByte, dirI32, authKey⟩
    dsimp only [atomicSpqrKemOps, AtomicSpqrKemOp.cod, AtomicSpqrKemOp.eval, AtomicSpqrKemOp.cost]
    unfold spqrNegotiateInitEval
    rcases LibsignalSpqrV1.Version.fromU8? verByte with _ | v
    · exact ⟨trivial, trivial⟩
    · dsimp only
      rcases LibsignalSpqrV1.Direction.fromI32? dirI32 with _ | dir
      · exact ⟨trivial, trivial⟩
      · dsimp only
        rcases LibsignalSpqrV1.initInner (LibsignalSpqrV1.spqrDeps C.F K) v dir authKey
            with _ | pb?
        · exact ⟨trivial, trivial⟩
        · dsimp only
          rcases pb? with _ | pb
          · exact ⟨trivial, trivial⟩
          · dsimp only [Option.map]
            exact ⟨trivial, fits_bytes_take48000 ℓ Pt (by omega) pb.encodeRaw⟩
  | spqrBraidSend =>
    rcases x with ⟨v1Raw, coins⟩
    dsimp only [atomicSpqrKemOps, AtomicSpqrKemOp.cod, AtomicSpqrKemOp.eval, AtomicSpqrKemOp.cost]
    unfold spqrBraidSendEval
    rcases LibsignalSpqrV1.V1State.decode v1Raw with _ | pb
    · exact ⟨trivial, trivial⟩
    · dsimp only
      rcases LibsignalSpqrV1.States.from_pb LibsignalSpqrV1.spqrPolyApi
          (LibsignalSpqrV1.spqrAuthApi C.F) pb with ⟨_ | _⟩ | st0
      · exact ⟨trivial, trivial⟩
      · exact ⟨trivial, trivial⟩
      · dsimp only
        rcases st0.send K (LibsignalSpqrV1.coinBytes coins) with ⟨_ | _⟩ | ⟨sOut, _⟩
        · exact ⟨trivial, trivial⟩
        · exact ⟨trivial, trivial⟩
        · dsimp only
          have h1 : 1 ≤ M + 3072 := by omega
          refine ⟨trivial, fits_bytes_take64000 ℓ Pt (by omega) _, h1, ?_, ?_⟩
          · rcases sOut.key with _ | _
            · trivial
            · exact ⟨h1, h1⟩
          · apply fits_bytes_of_len ℓ Pt 64 h1
            unfold spqrMsgPayloadSuffix
            exact List.length_take_le 64 _
  | spqrBraidRecv =>
    rcases x with ⟨v1Raw, msgEpoch, rem⟩
    dsimp only [atomicSpqrKemOps, AtomicSpqrKemOp.cod, AtomicSpqrKemOp.eval, AtomicSpqrKemOp.cost]
    unfold spqrBraidRecvEval
    rcases LibsignalSpqrV1.Message.deserialize LibsignalSpqrV1.spqrPolyApi msgEpoch rem
        with _ | sckaMsg
    · exact ⟨trivial, trivial, trivial⟩
    · dsimp only
      rcases LibsignalSpqrV1.V1State.decode v1Raw with _ | pb
      · exact ⟨trivial, trivial, trivial⟩
      · dsimp only
        rcases LibsignalSpqrV1.States.from_pb LibsignalSpqrV1.spqrPolyApi
            (LibsignalSpqrV1.spqrAuthApi C.F) pb with ⟨_ | _⟩ | st0
        · exact ⟨trivial, trivial, trivial⟩
        · exact ⟨trivial, trivial, trivial⟩
        · dsimp only
          rcases st0.recv K sckaMsg with ⟨_ | _⟩ | rOut
          · exact ⟨trivial, trivial, trivial⟩
          · exact ⟨trivial, trivial, trivial⟩
          · dsimp only
            have h1 : 1 ≤ M + 3072 := by omega
            refine ⟨trivial, trivial, ?_, fits_bytes_take64000 ℓ Pt (by omega) _⟩
            rcases rOut.key with _ | _
            · trivial
            · exact ⟨h1, h1⟩
  | spqrChainFromVn =>
    exact fits_spqrChainFromVnEval ℓ Pt M C.F x
  | spqrChainAddEpoch =>
    rcases x with ⟨ch, ep, sec⟩
    exact fits_spqrChainAddEpochEval ℓ Pt M C.F ch ep sec hx.1
  | spqrChainNextKey =>
    rcases x with ⟨next, ctr⟩
    dsimp only [atomicSpqrKemOps, AtomicSpqrKemOp.cod, AtomicSpqrKemOp.eval, AtomicSpqrKemOp.cost]
    refine ⟨trivial, ?_⟩
    unfold spqrChainNextKeyEval
    rcases LibsignalSpqrV1.ChainEpochDirection.nextKeyInternal
        (LibsignalSpqrV1.spqrHkdfWith C.F) next ctr with _ | ⟨next', _, _, _⟩
    · trivial
    · have h1 : 1 ≤ M + 12 := by omega
      exact ⟨fits_bytes_take ℓ Pt 32 (K := 1) h1 next', h1, h1⟩
  | kem768FromSeed =>
    dsimp only [atomicSpqrKemOps, AtomicSpqrKemOp.cod, AtomicSpqrKemOp.eval, AtomicSpqrKemOp.cost]
    have h1 : 1 ≤ M + 160 := by omega
    exact ⟨fits_bytes_of_len ℓ Pt 64 h1 (by simp),
      fits_bytes_of_len ℓ Pt 1152 h1 (by simp),
      fits_bytes_of_len ℓ Pt 2400 h1 (by simp)⟩
  | kem768Encaps1 =>
    dsimp only [atomicSpqrKemOps, AtomicSpqrKemOp.cod, AtomicSpqrKemOp.eval, AtomicSpqrKemOp.cost]
    rcases K.encaps1 x.1 (Ratchet.keyToBytesVec32 x.2) with _ | ⟨ct1, es, _⟩
    · trivial
    · have h1 : 1 ≤ M + 160 := by omega
      dsimp only [Option.map]
      exact ⟨fits_bytes_of_len ℓ Pt 960 h1 (by simp),
        fits_bytes_of_len ℓ Pt 2080 h1 (by simp), h1⟩
  | kem768Encaps2 =>
    rcases x with ⟨es, ek⟩
    dsimp only [atomicSpqrKemOps, AtomicSpqrKemOp.cod, AtomicSpqrKemOp.eval, AtomicSpqrKemOp.cost]
    split
    · split
      · exact fits_bytes_of_len ℓ Pt 128 (by omega) (by simp)
      · trivial
    · trivial
  | kem768Decaps =>
    rcases x with ⟨dk, ct1, ct2⟩
    dsimp only [atomicSpqrKemOps, AtomicSpqrKemOp.cod, AtomicSpqrKemOp.eval, AtomicSpqrKemOp.cost]
    split
    · split
      · split
        · dsimp only [Ty.Fits, AtomicSort.blocks]; omega
        · trivial
      · trivial
    · trivial
  | kem768ValidPk =>
    trivial

theorem atomicPqxdhOps_sizeHonest (ℓ : ℕ) (Pt : Type) (P : SignalPqxdh.Primitives) :
    OpsSizeHonest (atomicPqxdhOps ℓ Pt P) := by
  intro o x M _
  cases o with
  | x25519 | x25519Base | pow8 | sigPkGen =>
    dsimp only [atomicPqxdhOps, AtomicPqxdhOp.cod, AtomicPqxdhOp.eval, AtomicPqxdhOp.cost]
    exact fits_pbytes_take ℓ Pt 32 (K := 1) (by omega) _
  | sigSign =>
    dsimp only [atomicPqxdhOps, AtomicPqxdhOp.cod, AtomicPqxdhOp.eval, AtomicPqxdhOp.cost]
    exact fits_pbytes_take ℓ Pt 64 (K := 1) (by omega) _
  | kemKeyGen =>
    dsimp only [atomicPqxdhOps, AtomicPqxdhOp.cod, AtomicPqxdhOp.eval, AtomicPqxdhOp.cost]
    have h1 : 1 ≤ M + 160 := by omega
    exact ⟨fits_pbytes_take ℓ Pt 1568 (K := 1) h1 _, fits_pbytes_take ℓ Pt 3168 (K := 1) h1 _⟩
  | kemEncaps =>
    dsimp only [atomicPqxdhOps, AtomicPqxdhOp.cod, AtomicPqxdhOp.eval, AtomicPqxdhOp.cost]
    rcases P.kemEncaps x.1 x.2 with _ | ⟨ss, ct⟩
    · trivial
    · have h1 : 1 ≤ M + 160 := by omega
      exact ⟨fits_pbytes_take ℓ Pt 32 (K := 1) h1 ss, fits_pbytes_take ℓ Pt 1568 (K := 1) h1 ct⟩
  | kemDecaps =>
    dsimp only [atomicPqxdhOps, AtomicPqxdhOp.cod, AtomicPqxdhOp.eval, AtomicPqxdhOp.cost]
    rcases P.kemDecaps x.1 x.2 with _ | ss
    · trivial
    · exact fits_pbytes_take ℓ Pt 32 (K := 1) (by omega) ss
  | hkdfDerive96 =>
    dsimp only [atomicPqxdhOps, AtomicPqxdhOp.cod, AtomicPqxdhOp.eval, AtomicPqxdhOp.cost]
    have h1 : 1 ≤ M + 16 := by omega
    exact ⟨fits_pbytes_take ℓ Pt 32 (K := 1) h1 _,
      fits_pbytes_take ℓ Pt 32 (K := 1) h1 _,
      fits_pbytes_take ℓ Pt 32 (K := 1) h1 _⟩
  | isCanonical | sigVerify =>
    trivial

theorem atomicAdapterOps_sizeHonest (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    OpsSizeHonest (atomicAdapterOps ℓ decT encT) :=
  opsSizeHonest_sum (atomicPureOps_sizeHonest ℓ Pt) (atomicCurveCheckOps_sizeHonest ℓ decT encT)

theorem atomicFsOps_sizeHonest (ℓ : ℕ) (Pt : Type) (C : Crypto) (encT : Pt → PublicKey) :
    OpsSizeHonest (atomicFsOps ℓ Pt C encT) :=
  opsSizeHonest_sum (atomicPureOps_sizeHonest ℓ Pt)
    (opsSizeHonest_sum (atomicPtEncOps_sizeHonest ℓ encT) (atomicSymOps_sizeHonest ℓ Pt C))

theorem atomicFig8Ops_sizeHonest (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (lam : Pt := 0) :
    OpsSizeHonest (atomicFig8Ops ℓ Pt C Dh encPt encT lam) :=
  opsSizeHonest_sum (atomicFsOps_sizeHonest ℓ Pt C encT)
    (atomicGroupOps_sizeHonest ℓ Pt C Dh encPt lam)

theorem atomicSessionOps_sizeHonest (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt := 0) :
    OpsSizeHonest (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) :=
  opsSizeHonest_sum
    (opsSizeHonest_sum (atomicFig8Ops_sizeHonest ℓ Pt C Dh encPt encT lam)
      (opsSizeHonest_sum (atomicPtDecOps_sizeHonest ℓ decT)
        (atomicCurveCheckOps_sizeHonest ℓ decT encT)))
    (atomicSpqrKemOps_sizeHonest ℓ Pt C K)

/-- Size honesty of the full end-to-end operation bundle `atomicE2EOps ℓ P C K decT encT`. -/
theorem atomicE2EOps_sizeHonest (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    OpsSizeHonest (atomicE2EOps ℓ P C K decT encT) :=
  opsSizeHonest_sum (atomicAdapterOps_sizeHonest ℓ decT encT)
    (opsSizeHonest_sum
      (opsSizeHonest_sum (atomicPtEncOps_sizeHonest ℓ encT) (atomicPtDecOps_sizeHonest ℓ decT))
      (opsSizeHonest_sum (atomicSymOps_sizeHonest ℓ Pt C)
        (opsSizeHonest_sum (atomicSpqrKemOps_sizeHonest ℓ Pt C K)
          (atomicPqxdhOps_sizeHonest ℓ Pt P))))

theorem pqAtomicOps_sizeHonest : OpsSizeHonest pqAtomicOps :=
  atomicPureOps_sizeHonest 0 Empty

theorem pqAtomicSamplers_sizeHonest : SampSizeHonest pqAtomicSamplers :=
  atomicBaseSamplers_sizeHonest 0 Empty

/-- Encoding of `SignalPqxdh.KeyIndResponse` into `keyIndRT` (inverse of `keyIndRdec`). -/
def pqKeyIndRenc {ℓ : ℕ} {Pt : Type} :
    SignalPqxdh.KeyIndResponse → (keyIndRT (ℓ := ℓ) (Pt := Pt)).denote
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

@[simp] theorem keyIndRdec_pqKeyIndRenc {ℓ : ℕ} {Pt : Type} (r : SignalPqxdh.KeyIndResponse) :
    keyIndRdec (ℓ := ℓ) (Pt := Pt) (pqKeyIndRenc r) = r := by
  cases r <;> rfl

end ReductionDsl
