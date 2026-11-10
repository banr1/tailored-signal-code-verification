/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
public import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.SpqrSendEmptyCodeSym
public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeStateEmpty.Proof
import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.Fetch
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Verification of `spqr::send::<HookRng>` on an Empty State

Proves that on an empty post-quantum state (`x.st.bytes = []`), `spqr::send::<libsignal_session::HookRng>`
(`0x3085c`) satisfies `spqrSendEmptySpec` in-image (`spqrSendEmpty_run'`) and `spqrSendEmptyPlacedSpec`
under `[LibsignalPlacement]` (blocks 325 and 124).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 3200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Region arithmetic -/

theorem mr_cut' (sp : BitVec 64) (c c' n k N : Nat) (hN : n + k = N) (hc' : c - n = c')
    (hn : n ≤ c) (hc : c < 2 ^ 64) (h : N ≤ 2 ^ 64) :
    memRegion (sp - BitVec.ofNat 64 c) N =
      memRegion (sp - BitVec.ofNat 64 c) n ∗ memRegion (sp - BitVec.ofNat 64 c') k := by
  subst hN hc'
  refine memRegion_split' rfl ?_ h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have h1 : c % 2 ^ 64 = c := Nat.mod_eq_of_lt hc
  have h2 : (c - n) % 2 ^ 64 = c - n := Nat.mod_eq_of_lt (by omega)
  have h3 : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2, h3]
  omega

theorem mr_cut_add (a : BitVec 64) (c n k : Nat) (h : n + k ≤ 2 ^ 64) :
    memRegion (a + BitVec.ofNat 64 c) (n + k) =
      memRegion (a + BitVec.ofNat 64 c) n ∗ memRegion (a + BitVec.ofNat 64 (c + n)) k := by
  refine memRegion_split' rfl ?_ h
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## The stack layout -/

/-- The stack of `spqr::send::<HookRng>` on the empty-state path, cut at the cells it touches
(offsets below `sp`; `sp_f = sp - 8064` is the frame base). -/
theorem stackAt_spqr (sp : BitVec 64) :
    stackAt sp spqrSendStack =
      memRegion (sp - 131072#64) 106624 ∗
      stackAt (sp - 8064#64) extHookStack ∗
      (∃∗ v2 : BitVec 64, (sp - 8064#64) ↦₆₄ v2) ∗
      memRegion (sp - 8056#64) 40 ∗
      (∃∗ v4 : BitVec 64, (sp - 8016#64) ↦₆₄ v4) ∗
      (∃∗ v5 : BitVec 64, (sp - 8008#64) ↦₆₄ v5) ∗
      (∃∗ v6 : BitVec 64, (sp - 8000#64) ↦₆₄ v6) ∗
      (∃∗ v7 : BitVec 64, (sp - 7992#64) ↦₆₄ v7) ∗
      memRegion (sp - 7984#64) 320 ∗
      (∃∗ v13 : BitVec 64, (sp - 7664#64) ↦₆₄ v13) ∗
      (∃∗ v14 : BitVec 64, (sp - 7656#64) ↦₆₄ v14) ∗
      (∃∗ v15 : BitVec 64, (sp - 7648#64) ↦₆₄ v15) ∗
      memRegion (sp - 7640#64) 3448 ∗
      (∃∗ v17 : BitVec 64, (sp - 4192#64) ↦₆₄ v17) ∗
      memRegion (sp - 4184#64) 824 ∗
      memRegion (sp - 3360#64) 352 ∗
      memRegion (sp - 3008#64) 2912 ∗
      (∃∗ v29 : BitVec 64, (sp - 96#64) ↦₆₄ v29) ∗
      (∃∗ v30 : BitVec 64, (sp - 88#64) ↦₆₄ v30) ∗
      (∃∗ v31 : BitVec 64, (sp - 80#64) ↦₆₄ v31) ∗
      (∃∗ v32 : BitVec 64, (sp - 72#64) ↦₆₄ v32) ∗
      (∃∗ v33 : BitVec 64, (sp - 64#64) ↦₆₄ v33) ∗
      (∃∗ v34 : BitVec 64, (sp - 56#64) ↦₆₄ v34) ∗
      (∃∗ v35 : BitVec 64, (sp - 48#64) ↦₆₄ v35) ∗
      (∃∗ v36 : BitVec 64, (sp - 40#64) ↦₆₄ v36) ∗
      (∃∗ v37 : BitVec 64, (sp - 32#64) ↦₆₄ v37) ∗
      (∃∗ v38 : BitVec 64, (sp - 24#64) ↦₆₄ v38) ∗
      (∃∗ v39 : BitVec 64, (sp - 16#64) ↦₆₄ v39) ∗
      (∃∗ v40 : BitVec 64, (sp - 8#64) ↦₆₄ v40) := by
  show memRegion (sp - BitVec.ofNat 64 131072) 131072 = _
  rw [mr_cut' sp 131072 24448 106624 24448 131072 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 24448 8064 16384 8064 24448 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 8064 8056 8 8056 8064 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 8056 8016 40 8016 8056 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 8016 8008 8 8008 8016 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 8008 8000 8 8000 8008 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 8000 7992 8 7992 8000 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 7992 7984 8 7984 7992 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 7984 7664 320 7664 7984 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 7664 7656 8 7656 7664 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 7656 7648 8 7648 7656 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 7648 7640 8 7640 7648 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 7640 4192 3448 4192 7640 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 4192 4184 8 4184 4192 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 4184 3360 824 3360 4184 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 3360 3008 352 3008 3360 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 3008 96 2912 96 3008 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 96 88 8 88 96 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 88 80 8 80 88 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 80 72 8 72 80 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 72 64 8 64 72 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 64 56 8 56 64 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 56 48 8 48 56 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 48 40 8 40 48 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 40 32 8 32 40 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 32 24 8 24 32 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 24 16 8 16 24 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 16 8 8 8 16 rfl rfl (by decide) (by decide) (by decide)]
  have hstk : memRegion (sp - BitVec.ofNat 64 24448) 16384 = stackAt (sp - 8064#64) extHookStack := by
    simp only [stackAt, extHookStack]; congr 1; bv_omega
  rw [hstk]
  simp only [memRegion_eight]

/-! ## The program -/

/-- The triple-ratchet hooks under `Rust.withPanics`. -/
abbrev externsWithPanics (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : String → Option (State → State) :=
  Rust.withPanics (tripleRatchetExterns C ctl abs)

/-- The triple-ratchet session program rebased at `b`. -/
noncomputable abbrev rebasedTripleRatchetProg (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Program :=
  libsignalSessionCode.rebase b (externsWithPanics C ctl abs)

/-! ## The callees -/

/-- `decodeStateEmptyAt` at the decode result buffer `sp - 3360`, cut at the words
`spqr::send` reads (word 0, which is `-1`, and the three words after it) and the two `None`
niches. -/
theorem decodeEmpty_split (t : BitVec 64) :
    decodeStateEmptyAt (t - 3360#64) =
      ((t - 3360#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
      (∃∗ a1 : BitVec 64, (t - 3352#64) ↦₆₄ a1) ∗ (∃∗ a2 : BitVec 64, (t - 3344#64) ↦₆₄ a2) ∗
      (∃∗ a3 : BitVec 64, (t - 3336#64) ↦₆₄ a3) ∗ memRegion (t - 3328#64) 16 ∗
      ((t - 3312#64) ↦₆₄ pqChainNone) ∗ memRegion (t - 3304#64) 72 ∗
      ((t - 3232#64) ↦₆₄ pqInnerNone) ∗ memRegion (t - 3224#64) 216 := by
  unfold decodeStateEmptyAt
  simp (disch := decide) only [bv_sub_add_lit, Nat.reduceSub]
  rw [mr_cut' t 3352 3344 8 32 40 rfl rfl (by decide) (by decide) (by decide),
    mr_cut' t 3344 3336 8 24 32 rfl rfl (by decide) (by decide) (by decide),
    mr_cut' t 3336 3328 8 16 24 rfl rfl (by decide) (by decide) (by decide)]
  simp only [memRegion_eight, sepConj_assoc]

/-- The 72-byte `send` result buffer, cut at the seven words the `Ok` path writes. -/
theorem ret_split (r : BitVec 64) :
    memRegion r 72 =
      (∃∗ a0 : BitVec 64, r ↦₆₄ a0) ∗ (∃∗ a1 : BitVec 64, (r + 8#64) ↦₆₄ a1) ∗
      (∃∗ a2 : BitVec 64, (r + 16#64) ↦₆₄ a2) ∗ (∃∗ a3 : BitVec 64, (r + 24#64) ↦₆₄ a3) ∗
      (∃∗ a4 : BitVec 64, (r + 32#64) ↦₆₄ a4) ∗ (∃∗ a5 : BitVec 64, (r + 40#64) ↦₆₄ a5) ∗
      (∃∗ a6 : BitVec 64, (r + 48#64) ↦₆₄ a6) ∗ memRegion (r + 56#64) 16 := by
  have hs : ∀ (b : BitVec 64) (k : Nat), k ≤ 64 →
      memRegion b (8 + k) = memRegion b 8 ∗ memRegion (b + 8#64) k :=
    fun b k hk => memRegion_split' rfl rfl (by omega)
  rw [hs r 64 (by decide), hs _ 56 (by decide), hs _ 48 (by decide), hs _ 40 (by decide),
    hs _ 32 (by decide), hs _ 24 (by decide), hs _ 16 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, memRegion_eight]

/-! ## The `memcpy` of the decode payload -/

/-- The 320-byte decode payload at `a` as `spqr::send` reads it: the words at `+16` (`chain`)
and `+96` (`inner`) are kept; the rest is opaque. -/
def pcs (a c i : BitVec 64) : SepProp :=
  memRegion a 16 ∗ ((a + 16#64) ↦₆₄ c) ∗ memRegion (a + 24#64) 72 ∗ ((a + 96#64) ↦₆₄ i) ∗
    memRegion (a + 104#64) 216

theorem pcs_of_bytes (a c i : BitVec 64) (b1 b3 b5 : List (BitVec 8)) (h1 : b1.length = 16)
    (h3 : b3.length = 72) (h5 : b5.length = 216) :
    (a ↦ₛ (b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5))))) ⊢ pcs a c i := by
  simp only [pointsToBytes_append, unpack64_length, h1, h3, BitVec.add_assoc, BitVec.reduceAdd,
    ← pointsTo64_eq_pointsToBytes, pcs]
  have e1 := pointsToBytes_entails_memRegion a b1
  have e3 := pointsToBytes_entails_memRegion (a + 24#64) b3
  have e5 := pointsToBytes_entails_memRegion (a + 104#64) b5
  rw [h1] at e1; rw [h3] at e3; rw [h5] at e5
  exact sepConj_mono e1 (sepConj_mono (Entails.refl _) (sepConj_mono e3
    (sepConj_mono (Entails.refl _) e5)))

theorem bytes_of_pcs (a c i : BitVec 64) :
    pcs a c i ⊢ ∃∗ bs : List (BitVec 8), ⌜bs.length = 320 ∧ ∃ b1 b3 b5 : List (BitVec 8),
      b1.length = 16 ∧ b3.length = 72 ∧ b5.length = 216 ∧
      bs = b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5)))⌝ ∗ (a ↦ₛ bs) := by
  unfold pcs
  rw [memRegion_eq_exists_bytes a 16 (by decide), sepExists_sepConj_left]
  refine Entails.sepExists_elim fun b1 => ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun h1 => ?_
  rw [memRegion_eq_exists_bytes (a + 24#64) 72 (by decide), sepExists_sepConj_left,
    sepExists_sepConj_right, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun b3 => ?_
  rw [sepConj_assoc, sepConj_pure_left_comm, sepConj_pure_left_comm]
  refine Entails.pure_left fun h3 => ?_
  rw [memRegion_eq_exists_bytes (a + 104#64) 216 (by decide)]
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun b5 => ?_
  simp only [sepConj_pure_left_comm]
  refine Entails.pure_left fun h5 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro
    (P := fun bs : List (BitVec 8) => ⌜bs.length = 320 ∧ ∃ b1 b3 b5 : List (BitVec 8),
      b1.length = 16 ∧ b3.length = 72 ∧ b5.length = 216 ∧
      bs = b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5)))⌝ ∗ (a ↦ₛ bs))
    (b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5)))))
  refine Entails.pure_right ⟨by simp [h1, h3, h5, unpack64_length], b1, b3, b5, h1, h3, h5, rfl⟩ ?_
  simp only [pointsToBytes_append, unpack64_length, h1, h3, BitVec.add_assoc, BitVec.reduceAdd,
    ← pointsTo64_eq_pointsToBytes]
  exact Entails.refl _

theorem pcs_src (t c i : BitVec 64) :
    pcs (t - 3328#64) c i = (memRegion (t - 3328#64) 16 ∗ ((t - 3312#64) ↦₆₄ c) ∗
      memRegion (t - 3304#64) 72 ∗ ((t - 3232#64) ↦₆₄ i) ∗ memRegion (t - 3224#64) 216) := by
  unfold pcs
  simp (disch := decide) only [bv_sub_add_lit, Nat.reduceSub]

theorem pcs_dst (t c i : BitVec 64) :
    pcs (t - 7984#64) c i = (memRegion (t - 7984#64) 16 ∗ ((t - 7968#64) ↦₆₄ c) ∗
      memRegion (t - 7960#64) 72 ∗ ((t - 7888#64) ↦₆₄ i) ∗ memRegion (t - 7880#64) 216) := by
  unfold pcs
  simp (disch := decide) only [bv_sub_add_lit, Nat.reduceSub]

/-- `memcpy(t - 7984, t - 3328, 320)`: copies the decode payload (ghosts: the caller's `sp` `t`,
the `chain` word `c`, the `inner` word `i`) and keeps the trace. -/
def memcpyPcsSpec : Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (t, c, i) s0 =>
    ⌜s0.readReg64 .x0 = t - 7984#64 ∧ s0.readReg64 .x1 = t - 3328#64 ∧
      s0.readReg64 .x2 = 320#64⌝ ∗
    memRegion (t - 7984#64) 320 ∗
    (memRegion (t - 3328#64) 16 ∗ ((t - 3312#64) ↦₆₄ c) ∗
      memRegion (t - 3304#64) 72 ∗ ((t - 3232#64) ↦₆₄ i) ∗ memRegion (t - 3224#64) 216)
  post := fun (t, c, i) s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = t - 7984#64⌝ ∗
    (memRegion (t - 7984#64) 16 ∗ ((t - 7968#64) ↦₆₄ c) ∗
      memRegion (t - 7960#64) 72 ∗ ((t - 7888#64) ↦₆₄ i) ∗ memRegion (t - 7880#64) 216) ∗
    (memRegion (t - 3328#64) 16 ∗ ((t - 3312#64) ↦₆₄ c) ∗
      memRegion (t - 3304#64) 72 ∗ ((t - 3232#64) ↦₆₄ i) ∗ memRegion (t - 3224#64) 216)

theorem hookMemcpy_pcs_ok : HookOk hookMemcpy memcpyPcsSpec := by
  refine retHook_ok fun ⟨t, c, i⟩ R s0 _ hpre _ => ?_
  simp only [memcpyPcsSpec] at hpre
  rw [← pcs_src, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2⟩, hmem⟩ := hpre
  have h2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (bytes_of_pcs _ c i))) hmem
  rw [sepExists_sepConj_right, sepExists_sepConj_left, satisfies_sepExists] at h2
  obtain ⟨bs, h3⟩ := h2
  rw [sepConj_pure_left_comm, sepConj_assoc, satisfies_pure_sepConj] at h3
  obtain ⟨⟨hlen, b1, b3, b5, h1, h3', h5, rfl⟩, h4⟩ := h3
  have hmem' : s0.mem ⊨ memRegion (t - 7984#64) (b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++
      b5)))).length ∗ (((t - 3328#64) ↦ₛ (b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5))))) ∗ R) := by
    rw [hlen, ← sepConj_assoc]; exact h4
  have hsrc_front : s0.mem ⊨ ((t - 3328#64) ↦ₛ (b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5))))) ∗
      (memRegion (t - 7984#64) 320 ∗ R) := by
    rw [sepConj_comm (memRegion _ 320), sepConj_assoc] at h4; exact h4
  obtain ⟨hlen', hread⟩ := (IsBlock.pointsToBytes _ _).read hsrc_front
  have hx2' : (s0.readReg64 .x2).toNat =
      (b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5)))).length := by
    rw [hx2, hlen]; rfl
  refine ⟨?_, rfl, ‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · dsimp only
    rw [hx0, hx1, hx2', hread]
    exact keepsFrozen_writeBytes_of_memRegion _ hlen' hmem'
  · simp only [memcpyPcsSpec, retHook, State.readReg64_setPC, State.readReg64_setMem,
      hx0, hx1, hx2', hread]
    rw [← pcs_src, ← pcs_dst, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨rfl, trivial⟩, ?_⟩
    have hw := satisfies_writeBytes _ hlen' hmem'
    rw [← sepConj_assoc] at hw
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono (pcs_of_bytes _ c i b1 b3 b5 h1 h3' h5)
      (pcs_of_bytes _ c i b1 b3 b5 h1 h3' h5))) hw

theorem memcpyPcs_of_sessionMemcpyRegion {prog : Program} {entry : BitVec 64}
    (hmc : subroutine_ok prog entry sessionMemcpyRegionSpec) :
    subroutine_ok prog entry memcpyPcsSpec := by
  refine subroutine_ok_outcome_intro fun ⟨t, c, i⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [memcpyPcsSpec] at hpre
  rw [← pcs_src, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2⟩, hmem⟩ := hpre
  have h2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (bytes_of_pcs _ c i))) hmem
  rw [sepExists_sepConj_right, sepExists_sepConj_left, satisfies_sepExists] at h2
  obtain ⟨bs, h3⟩ := h2
  rw [sepConj_pure_left_comm, sepConj_assoc, satisfies_pure_sepConj] at h3
  obtain ⟨⟨hlen, b1, b3, b5, h1, h3', h5, rfl⟩, h4⟩ := h3
  have hpre_mc : s0.mem ⊨ sessionMemcpyRegionSpec.pre (t - 7984#64, t - 3328#64,
      b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5)))) s0 ∗ R := by
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, by rw [hx2, hlen]; rfl⟩, ?_⟩
    rw [hlen]
    exact h4
  refine hmc.mono_outcome (t - 7984#64, t - 3328#64,
    b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5)))) R s0 hpc hrun hpre_mc hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [sessionMemcpyRegionSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨hx0_sf, htr⟩, hpost_mem⟩ := hpost
    dsimp only [memcpyPcsSpec]
    rw [← pcs_src, ← pcs_dst, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hx0_sf⟩, ?_⟩
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono
      (pcs_of_bytes _ c i b1 b3 b5 h1 h3' h5)
      (pcs_of_bytes _ c i b1 b3 b5 h1 h3' h5))) hpost_mem
  · right; left
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · right; right; left
    refine ⟨code, hex, ?_⟩
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1

/-! ## Folding back to the post -/

theorem pcs_entails (a c i : BitVec 64) : pcs a c i ⊢ memRegion a 320 := by
  refine Entails.trans (bytes_of_pcs a c i) (Entails.sepExists_elim fun bs => ?_)
  refine Entails.pure_left fun h => ?_
  have e := pointsToBytes_entails_memRegion a bs
  rw [h.1] at e
  exact e

theorem dst_fold (t c i : BitVec 64) :
    (memRegion (t - 7984#64) 16 ∗ ((t - 7968#64) ↦₆₄ c) ∗
      memRegion (t - 7960#64) 72 ∗ ((t - 7888#64) ↦₆₄ i) ∗ memRegion (t - 7880#64) 216) ⊢
    memRegion (t - 7984#64) 320 := by
  rw [← pcs_dst]; exact pcs_entails _ c i

theorem decode_fold (t w d1 d2 d3 c i : BitVec 64) :
    ((t - 3360#64) ↦₆₄ w) ∗ ((t - 3352#64) ↦₆₄ d1) ∗ ((t - 3344#64) ↦₆₄ d2) ∗
      ((t - 3336#64) ↦₆₄ d3) ∗
      (memRegion (t - 3328#64) 16 ∗ ((t - 3312#64) ↦₆₄ c) ∗
        memRegion (t - 3304#64) 72 ∗ ((t - 3232#64) ↦₆₄ i) ∗ memRegion (t - 3224#64) 216) ⊢
    memRegion (t - 3360#64) 352 := by
  rw [← pcs_src]
  rw [mr_cut' t 3360 3352 8 344 352 rfl rfl (by decide) (by decide) (by decide),
    mr_cut' t 3352 3344 8 336 344 rfl rfl (by decide) (by decide) (by decide),
    mr_cut' t 3344 3336 8 328 336 rfl rfl (by decide) (by decide) (by decide),
    mr_cut' t 3336 3328 8 320 328 rfl rfl (by decide) (by decide) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono
    (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pcs_entails _ c i))))

/-- The `Ok` result the path writes: two empty `Vec`s (`cap = 0`, dangling `ptr = 1`) and the
key `None`. -/
theorem result_fold (A : RustAlloc) (r : BitVec 64) :
    ((r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ 1#64) ∗ ((r + 16#64) ↦₆₄ 0#64) ∗
      ((r + 24#64) ↦₆₄ 0#64) ∗ ((r + 32#64) ↦₆₄ 1#64) ∗ ((r + 40#64) ↦₆₄ 0#64) ∗
      ((r + 48#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ memRegion (r + 56#64) 16) ⊢
    spqrSendResultAt A r (some ([], none, [])) := by
  have hv : ∀ v : BitVec 64,
      ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) ⊢ vecU8 A v [] := by
    intro v
    unfold vecU8
    refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
    refine Entails.trans ?_ (Entails.sepExists_intro 1#64)
    simp only [vecU8At, vecHeader, List.length_nil]
    split
    · rw [sepConj_emp, sepConj_comm _ ⌜_⌝]
      refine Entails.pure_right ?_ (Entails.refl _)
      exact ⟨Nat.zero_le _, by decide, by decide⟩
    · exact absurd rfl ‹_›
  simp only [spqrSendResultAt, spqrSendKeyAt]
  refine Entails.trans (Entails.of_eq (Q := ((r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ 1#64) ∗
      ((r + 16#64) ↦₆₄ 0#64)) ∗ (((r + 24#64) ↦₆₄ 0#64) ∗ ((r + 32#64) ↦₆₄ 1#64) ∗
      ((r + 40#64) ↦₆₄ 0#64)) ∗ ((r + 48#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
      memRegion (r + 56#64) 16) (by simp only [sepConj_assoc])) ?_
  refine Entails.pure_right (by decide) ?_
  have e2 := hv (r + 24#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at e2
  exact sepConj_mono (hv r) (sepConj_mono e2 (Entails.of_eq (by rw [BitVec.add_assoc]; rfl)))

theorem tape_fold (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    tapeAt ctl cur rest ⊢ tapeAfter ctl cur rest 0 := by
  unfold tapeAt tapeAfter
  refine Entails.pure_left fun _ => ?_
  simp only [BitVec.add_zero, Nat.sub_zero]
  exact Entails.refl _

theorem spqrSendEmpty_base_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (img : Obj.Image) (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext) (hE : S.SendEmptyOk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName)
      (spqrSendEmptySpec A ctl S img) := by
  have hfn := (ls_lemma% fnOff "spqr::send::<libsignal_session::HookRng>")
  have hdec := hC.decode_state_empty_ok_at spqrSendName (num% (ls_off% "spqr::decode_state" - ls_off% "spqr::send::<libsignal_session::HookRng>"))
  have hmc := memcpyPcs_of_sessionMemcpyRegion (hC.session_memcpy_region_ok_at spqrSendName (num% (ls_off% "memcpy" - ls_off% "spqr::send::<libsignal_session::HookRng>")))
  spqr_fetches img.base (Rust.withPanics ext) hfn 0 108
  spqr_fetches img.base (Rust.withPanics ext) hfn 136 88
  spqr_fetches img.base (Rust.withPanics ext) hfn 4608 12
  spqr_fetches img.base (Rust.withPanics ext) hfn 4632 36
  simp only [spqrSendEmptySpec, spqrSendSpec, Spec.inImage, stackAt_spqr]
  simp (config := { maxSteps := 1000000 }) only [sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨ret, ⟨v, cap, ptr, bs⟩, cur, rest⟩ := x
  dsimp only at *
  subst bs
  wp_steps
  wp_apply
  wp_simp_pre only [decodeEmpty_split, sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc]
  apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d2
  apply SepWP.exists_elim; intro d1
  wp_steps
  wp_apply
  wp_simp_pre only [ret_split ret, sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro r6
  apply SepWP.exists_elim; intro r5
  apply SepWP.exists_elim; intro r4
  apply SepWP.exists_elim; intro r3
  apply SepWP.exists_elim; intro r2
  apply SepWP.exists_elim; intro r1
  apply SepWP.exists_elim; intro r0
  wp_steps
  refine SepWP.fold (dst_fold s0.sp pqChainNone pqInnerNone) (by sep_focus) ?_
  refine SepWP.fold (decode_fold s0.sp 0xFFFFFFFFFFFFFFFF#64 d1 d2 d3 pqChainNone pqInnerNone)
    (by sep_focus) ?_
  refine SepWP.fold (result_fold A ret) (by sep_focus) ?_
  refine SepWP.fold (tape_fold ctl cur rest) (by sep_focus) ?_
  simp only [hE.send, hE.draws, hE.noPanic]
  wp_done

theorem spqrSendEmpty_base (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image) (hS : TripleRatchetHooks C A S abs) (hE : S.SendEmptyOk) :
    subroutine_ok (rebasedTripleRatchetProg img.base C ctl abs) ((rebasedTripleRatchetProg img.base C ctl abs).fnAddr spqrSendName)
      (spqrSendEmptySpec A ctl S img) :=
  spqrSendEmpty_base_ext C A ctl S (tripleRatchetExterns C ctl abs) img
    (Stage2Contracts.of_tripleRatchetProgAt img.base C A ctl S abs hS) hE

/-- In-image `spqr::send::<HookRng>` satisfies `spqrSendEmptySpec` (`SpqrSendEmptyRunStmt`). -/
theorem spqrSendEmpty_run' (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image) : SpqrSendEmptyRunStmt C A ctl S abs img := by
  intro hS hE himg
  have hP : tripleRatchetProg img C ctl abs = rebasedTripleRatchetProg img.base C ctl abs :=
    libsignalSessionCode_ofImage himg
  have hEntry : entryOf img spqrSendName = (rebasedTripleRatchetProg img.base C ctl abs).fnAddr spqrSendName := by
    unfold entryOf rebasedTripleRatchetProg
    rw [libsignalSessionCode_ofImage himg, Program.fnAddr_rebase, Program.fnAddr_rebase]
  rw [hP, hEntry]
  exact spqrSendEmpty_base C A ctl S abs img hS hE

/-! ## Relocatable per-block contracts (blocks 325 and 124) -/

open Arm64.Obj CryptoVerification

/-- Block `325` (`spqr::decode_state`) on an empty state meets `decodeStateEmptySpec A`
under `[LibsignalPlacement]`. -/
theorem decodeStateEmpty_placed_ok [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_325).rebase (blkPl_325).base H) (blkPl_325).base
      (decodeStateEmptySpec A) := by
  simp only [decodeStateEmptySpec, decodeStateEmptyAt, pqChainNone, pqInnerNone]
  wp_init x s0
  obtain ⟨⟨v, cap, ptr, bs⟩, ret⟩ := x
  dsimp only at *
  subst bs
  rw [InImage.DecodeStateEmpty.vecArg_at_nil A v cap ptr,
      InImage.DecodeStateEmpty.ret_352_split ret,
      InImage.DecodeStateEmpty.stackAt_decodeState_split s0.sp]
  wp_pull_exists
  wp_steps
  wp_done

/-- Relocatable `[LibsignalPlacement]` contract for `spqr::send::<HookRng>` (Block `124`). -/
def spqrSendPlacedSpec [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) : Spec SendCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.st.v⌝ ∗ x.st.at A ∗ memRegion x.ret 72 ∗
      tapeAt ctl x.cur x.rest ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt s.sp spqrSendStack
  post := fun x s0 sf =>
    ⌜S.draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
        ¬ S.sendPanics x.st.bytes x.rest⌝ ∗ x.st.at A ∗
      spqrSendResultAt A x.ret (S.send x.st.bytes x.rest) ∗
      tapeAfter ctl x.cur x.rest (S.draws x.st.bytes x.rest) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt s0.sp spqrSendStack
  onPanic := fun x s0 sf =>
    ⌜(allocFailedIn s0 sf ∨ S.sendPanics x.st.bytes x.rest) ∧ s0.trace <+: sf.trace⌝ ∗
      anyHeap

/-- `spqrSendPlacedSpec` restricted to an empty state (`x.st.bytes = []`). -/
def spqrSendEmptyPlacedSpec [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) : Spec SendCall :=
  { spqrSendPlacedSpec A ctl S with
    pre := fun x s => ⌜x.st.bytes = []⌝ ∗ (spqrSendPlacedSpec A ctl S).pre x s }

/-- Block `124` (`spqr::send::<HookRng>`) on an empty state meets `spqrSendEmptyPlacedSpec`
under `[LibsignalPlacement]`, given `hmc` at `lsmpl.ρ "memcpy"`. -/
theorem spqrSendEmpty_placed_ok_of_memcpy [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State)) (hE : S.SendEmptyOk)
    (hmc : subroutine_ok ((blkPC_124).rebase (blkPl_124).base H)
      (lsmpl.ρ "memcpy") sessionMemcpyRegionSpec) :
    subroutine_ok ((blkPC_124).rebase (blkPl_124).base H) (blkPl_124).base
      (withLsCodeLoaded lsmpl (spqrSendEmptyPlacedSpec A ctl S)) := by
  have hdec0 : subroutine_ok ((blkPC_325).rebase (blkPl_325).base H) (lsmpl.base 325)
      (decodeStateEmptySpec A) := decodeStateEmpty_placed_ok A H
  have hdec := ls_subroutine_ok_of_block (callerProg := (blkPC_124).rebase (blkPl_124).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain hdec0)
  simp only [withLsCodeLoaded] at hdec
  have hmc' := memcpyPcs_of_sessionMemcpyRegion hmc
  simp only [withLsCodeLoaded, spqrSendEmptyPlacedSpec, spqrSendPlacedSpec, stackAt_spqr]
  simp (config := { maxSteps := 1000000 }) only [sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init x s0
  obtain ⟨ret, ⟨v, cap, ptr, bs⟩, cur, rest⟩ := x
  dsimp only at *
  subst bs
  apply sepWP_seq_lscl h (mid := lsmpl.base 325)
  wp_steps
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  intro hcl_call
  wp_apply
  wp_simp_pre only [decodeEmpty_split, sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc]
  apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d2
  apply SepWP.exists_elim; intro d1
  wp_steps
  wp_apply
  wp_simp_pre only [ret_split ret, sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro r6
  apply SepWP.exists_elim; intro r5
  apply SepWP.exists_elim; intro r4
  apply SepWP.exists_elim; intro r3
  apply SepWP.exists_elim; intro r2
  apply SepWP.exists_elim; intro r1
  apply SepWP.exists_elim; intro r0
  wp_steps
  refine SepWP.fold (dst_fold s0.sp pqChainNone pqInnerNone) (by sep_focus) ?_
  refine SepWP.fold (decode_fold s0.sp 0xFFFFFFFFFFFFFFFF#64 d1 d2 d3 pqChainNone pqInnerNone)
    (by sep_focus) ?_
  refine SepWP.fold (result_fold A ret) (by sep_focus) ?_
  refine SepWP.fold (tape_fold ctl cur rest) (by sep_focus) ?_
  simp only [hE.send, hE.draws, hE.noPanic]
  wp_done

/-- Block `124` (`spqr::send::<HookRng>`) on an empty state meets `spqrSendEmptyPlacedSpec`
under `[LibsignalPlacement]`, assuming `HookSat H "memcpy" sessionMemcpyRegionSpec`. -/
theorem spqrSendEmpty_placed_ok [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) {H : String → Option (State → State)} (hE : S.SendEmptyOk)
    (hmc : HookSat H "memcpy" sessionMemcpyRegionSpec) :
    subroutine_ok ((blkPC_124).rebase (blkPl_124).base H) (blkPl_124).base
      (withLsCodeLoaded lsmpl (spqrSendEmptyPlacedSpec A ctl S)) := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem (by decide : "memcpy" ∈ libsignalSessionExterns)
  exact spqrSendEmpty_placed_ok_of_memcpy A ctl S H hE
    (ls_hook_ok (k := k) (by simp [hk, hget]) hmc)

end CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty
