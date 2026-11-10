/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prog
public import LibsignalBinary.Proofs.CodeLayout
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import ProofLib.SepLogic.WP
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalTripleRatchetProofDefs
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeStateEmpty.Proof
import ProofLib.SepLogic.WPp

/-!
# Layouts, Callees, and Frame-Generic Specs for Empty-State `spqr::recv`

Instruction decodes, stack and result-buffer splits, `spqr::decode_state` and `memcpy` callee
lemmas, and frame-generic specifications (`spqrRecvCodeSpec`, `spqrRecvEmptyCodeSpec`) for
`spqr::recv` on an empty state.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.InImage.DecodeStateEmpty
  (mr_cut' vecU8Tail vecArg_at_nil decodeStateEmpty_ok_aux decodeStateEmpty_ok_F)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

gen_decodes libsignalSessionCode_tree spqrRecvBin
  [(ls_off% "spqr::recv") → (ls_off% "spqr::recv" + 352), (ls_off% "spqr::recv" + 384) → (ls_off% "spqr::recv" + 444), (ls_off% "spqr::recv" + 744) → (ls_off% "spqr::recv" + 748),
   (ls_off% "spqr::recv" + 780) → (ls_off% "spqr::recv" + 788), (ls_off% "spqr::recv" + 884) → (ls_off% "spqr::recv" + 888), (ls_off% "spqr::recv" + 912) → (ls_off% "spqr::recv" + 932),
   (ls_off% "spqr::recv" + 952) → (ls_off% "spqr::recv" + 960), (ls_off% "spqr::recv" + 1020) → (ls_off% "spqr::recv" + 1024), (ls_off% "spqr::recv" + 1040) → (ls_off% "spqr::recv" + 1072)]

/-! ## Stack layout (`spqrRecvStack = 131072`, frame `4992 = 0x1380`) -/

/-- The stack of `spqr::recv` on an empty state (`spqrRecvStack = 131072` bytes), split into
`stackAt (sp - 4992#64) extHookStack` for `spqr::decode_state` and the slots touched in
`[sp - 4992, sp)`. -/
theorem stackAt_spqrRecv_split (sp : BitVec 64) :
    stackAt sp spqrRecvStack =
      memRegion (sp - 131072#64) 109696 ∗
      stackAt (sp - 4992#64) extHookStack ∗
      (∃∗ f0 : BitVec 64, (sp - 4992#64) ↦₆₄ f0) ∗
      (∃∗ f8 : BitVec 64, (sp - 4984#64) ↦₆₄ f8) ∗
      (∃∗ f16 : BitVec 64, (sp - 4976#64) ↦₆₄ f16) ∗
      (∃∗ f24 : BitVec 64, (sp - 4968#64) ↦₆₄ f24) ∗
      memRegion (sp - 4960#64) 320 ∗
      memRegion (sp - 4640#64) 448 ∗
      (∃∗ probe : BitVec 64, (sp - 4192#64) ↦₆₄ probe) ∗
      memRegion (sp - 4184#64) 1128 ∗
      memRegion (sp - 3056#64) 352 ∗
      memRegion (sp - 2704#64) 608 ∗
      (∃∗ b50 : BitVec 64, (sp - 2096#64) ↦₆₄ b50) ∗
      (∃∗ b58 : BitVec 64, (sp - 2088#64) ↦₆₄ b58) ∗
      (∃∗ b60 : BitVec 64, (sp - 2080#64) ↦₆₄ b60) ∗
      memRegion (sp - 2072#64) 1976 ∗
      (∃∗ s29 : BitVec 64, (sp - 96#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (sp - 88#64) ↦₆₄ s30) ∗
      (∃∗ s28 : BitVec 64, (sp - 80#64) ↦₆₄ s28) ∗
      (∃∗ s27 : BitVec 64, (sp - 72#64) ↦₆₄ s27) ∗
      (∃∗ s26 : BitVec 64, (sp - 64#64) ↦₆₄ s26) ∗
      (∃∗ s25 : BitVec 64, (sp - 56#64) ↦₆₄ s25) ∗
      (∃∗ s24 : BitVec 64, (sp - 48#64) ↦₆₄ s24) ∗
      (∃∗ s23 : BitVec 64, (sp - 40#64) ↦₆₄ s23) ∗
      (∃∗ s22 : BitVec 64, (sp - 32#64) ↦₆₄ s22) ∗
      (∃∗ s21 : BitVec 64, (sp - 24#64) ↦₆₄ s21) ∗
      (∃∗ s20 : BitVec 64, (sp - 16#64) ↦₆₄ s20) ∗
      (∃∗ s19 : BitVec 64, (sp - 8#64) ↦₆₄ s19) := by
  show memRegion (sp - BitVec.ofNat 64 131072) 131072 = _
  rw [mr_cut' sp 131072 21376 109696 21376 131072 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 21376 4992 16384 4992 21376 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 4992 4984 8 4984 4992 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 4984 4976 8 4976 4984 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 4976 4968 8 4968 4976 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 4968 4960 8 4960 4968 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 4960 4640 320 4640 4960 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 4640 4192 448 4192 4640 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 4192 4184 8 4184 4192 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 4184 3056 1128 3056 4184 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 3056 2704 352 2704 3056 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 2704 2096 608 2096 2704 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 2096 2088 8 2088 2096 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 2088 2080 8 2080 2088 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 2080 2072 8 2072 2080 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 2072 96 1976 96 2072 rfl rfl (by decide) (by decide) (by decide)]
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
  have hstk : memRegion (sp - BitVec.ofNat 64 21376) 16384 = stackAt (sp - 4992#64) extHookStack := by
    simp only [stackAt, extHookStack]; congr 1; bv_omega
  rw [hstk]
  simp only [memRegion_eight]

/-! ## Buffer splits and `memcpy` / `decode_state` callees -/

/-- `decodeStateEmptyAt` at `t - 3056` (`sp_f + 0x790`), cut at the words `spqr::recv` reads
before `memcpy` (`+0`, `+8`, `+16`, `+24`) and the `chain` / `inner` words. -/
theorem decodeEmpty_recv_split (t : BitVec 64) :
    decodeStateEmptyAt (t - 3056#64) =
      ((t - 3056#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
      (∃∗ a1 : BitVec 64, (t - 3048#64) ↦₆₄ a1) ∗
      (∃∗ a2 : BitVec 64, (t - 3040#64) ↦₆₄ a2) ∗
      (∃∗ a3 : BitVec 64, (t - 3032#64) ↦₆₄ a3) ∗
      memRegion (t - 3024#64) 16 ∗
      ((t - 3008#64) ↦₆₄ pqChainNone) ∗
      memRegion (t - 3000#64) 72 ∗
      ((t - 2928#64) ↦₆₄ pqInnerNone) ∗
      memRegion (t - 2920#64) 216 := by
  unfold decodeStateEmptyAt
  simp (disch := decide) only [bv_sub_add_lit, Nat.reduceSub]
  rw [mr_cut' t 3048 3040 8 32 40 rfl rfl (by decide) (by decide) (by decide),
    mr_cut' t 3040 3032 8 24 32 rfl rfl (by decide) (by decide) (by decide),
    mr_cut' t 3032 3024 8 16 24 rfl rfl (by decide) (by decide) (by decide)]
  simp only [memRegion_eight, sepConj_assoc]

/-- The 48-byte `recv` result buffer `ret`, cut at the four 8-byte words touched on the `Ok` and
`Err` paths (`+0`, `+8`, `+16`, `+24`). -/
theorem ret_48_split (r : BitVec 64) :
    memRegion r 48 =
      (∃∗ r0 : BitVec 64, r ↦₆₄ r0) ∗
      (∃∗ r1 : BitVec 64, (r + 8#64) ↦₆₄ r1) ∗
      (∃∗ r2 : BitVec 64, (r + 16#64) ↦₆₄ r2) ∗
      (∃∗ r3 : BitVec 64, (r + 24#64) ↦₆₄ r3) ∗
      memRegion (r + 32#64) 16 := by
  have hs : ∀ (b : BitVec 64) (k : Nat), k ≤ 40 →
      memRegion b (8 + k) = memRegion b 8 ∗ memRegion (b + 8#64) k :=
    fun b k _ => memRegion_split' rfl rfl (by omega)
  rw [hs r 40 (by decide), hs _ 32 (by decide), hs _ 24 (by decide), hs _ 16 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, memRegion_eight]

/-- The 320-byte decode payload at `a` as `spqr::recv` reads it (`chain` at `+16`, `inner` at `+96`). -/
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
    pcs (t - 3024#64) c i = (memRegion (t - 3024#64) 16 ∗ ((t - 3008#64) ↦₆₄ c) ∗
      memRegion (t - 3000#64) 72 ∗ ((t - 2928#64) ↦₆₄ i) ∗ memRegion (t - 2920#64) 216) := by
  unfold pcs
  simp (disch := decide) only [bv_sub_add_lit, Nat.reduceSub]

theorem pcs_dst (t c i : BitVec 64) :
    pcs (t - 4960#64) c i = (memRegion (t - 4960#64) 16 ∗ ((t - 4944#64) ↦₆₄ c) ∗
      memRegion (t - 4936#64) 72 ∗ ((t - 4864#64) ↦₆₄ i) ∗ memRegion (t - 4856#64) 216) := by
  unfold pcs
  simp (disch := decide) only [bv_sub_add_lit, Nat.reduceSub]

/-- `memcpy(t - 4960, t - 3024, 320)` in `spqr::recv` (`+0x194`). -/
def memcpyRecvPcsSpec : Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (t, c, i) s0 =>
    ⌜s0.readReg64 .x0 = t - 4960#64 ∧ s0.readReg64 .x1 = t - 3024#64 ∧
      s0.readReg64 .x2 = 320#64⌝ ∗
    memRegion (t - 4960#64) 320 ∗
    (memRegion (t - 3024#64) 16 ∗ ((t - 3008#64) ↦₆₄ c) ∗
      memRegion (t - 3000#64) 72 ∗ ((t - 2928#64) ↦₆₄ i) ∗ memRegion (t - 2920#64) 216)
  post := fun (t, c, i) s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = t - 4960#64⌝ ∗
    (memRegion (t - 4960#64) 16 ∗ ((t - 4944#64) ↦₆₄ c) ∗
      memRegion (t - 4936#64) 72 ∗ ((t - 4864#64) ↦₆₄ i) ∗ memRegion (t - 4856#64) 216) ∗
    (memRegion (t - 3024#64) 16 ∗ ((t - 3008#64) ↦₆₄ c) ∗
      memRegion (t - 3000#64) 72 ∗ ((t - 2928#64) ↦₆₄ i) ∗ memRegion (t - 2920#64) 216)

theorem hookMemcpy_recv_pcs_ok : HookOk hookMemcpy memcpyRecvPcsSpec := by
  refine retHook_ok fun ⟨t, c, i⟩ R s0 _ hpre _ => ?_
  simp only [memcpyRecvPcsSpec] at hpre
  rw [← pcs_src, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2⟩, hmem⟩ := hpre
  have h2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (bytes_of_pcs _ c i))) hmem
  rw [sepExists_sepConj_right, sepExists_sepConj_left, satisfies_sepExists] at h2
  obtain ⟨bs, h3⟩ := h2
  rw [sepConj_pure_left_comm, sepConj_assoc, satisfies_pure_sepConj] at h3
  obtain ⟨⟨hlen, b1, b3, b5, h1, h3', h5, rfl⟩, h4⟩ := h3
  have hmem' : s0.mem ⊨ memRegion (t - 4960#64) (b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++
      b5)))).length ∗ (((t - 3024#64) ↦ₛ (b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5))))) ∗ R) := by
    rw [hlen, ← sepConj_assoc]; exact h4
  have hsrc_front : s0.mem ⊨ ((t - 3024#64) ↦ₛ (b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5))))) ∗
      (memRegion (t - 4960#64) 320 ∗ R) := by
    rw [sepConj_comm (memRegion _ 320), sepConj_assoc] at h4; exact h4
  obtain ⟨hlen', hread⟩ := (IsBlock.pointsToBytes _ _).read hsrc_front
  have hx2' : (s0.readReg64 .x2).toNat =
      (b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5)))).length := by
    rw [hx2, hlen]; rfl
  refine ⟨?_, rfl, ‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · dsimp only
    rw [hx0, hx1, hx2', hread]
    exact keepsFrozen_writeBytes_of_memRegion _ hlen' hmem'
  · simp only [memcpyRecvPcsSpec, retHook, State.readReg64_setPC, State.readReg64_setMem,
      hx0, hx1, hx2', hread]
    rw [← pcs_src, ← pcs_dst, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨rfl, trivial⟩, ?_⟩
    have hw := satisfies_writeBytes _ hlen' hmem'
    rw [← sepConj_assoc] at hw
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono (pcs_of_bytes _ c i b1 b3 b5 h1 h3' h5)
      (pcs_of_bytes _ c i b1 b3 b5 h1 h3' h5))) hw

theorem memcpy_recv_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr spqrRecvName + bv% (ls_off% "memcpy" - ls_off% "spqr::recv"))
      memcpyRecvPcsSpec := by
  refine hook_ok_at_raw (hname := "memcpy") (stub := libsignalSessionCode.fnOff "memcpy")
    (ls_lemma% fnOff "spqr::recv") (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (fun X => by simp only [arm64_norm]) ?_
  exact ⟨hookMemcpy, rfl, hookMemcpy_recv_pcs_ok⟩

/-- The `bl spqr::decode_state` at `+0x144` (`0x54770`), targeting `fnAddr spqrRecvName - 4496#64`,
on the session code rebased at `b` with an arbitrary hook table `hooks` (`decodeStateEmpty_ok_F`). -/
theorem decode_recv_ok_at_F (b : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) :
    subroutine_ok (libsignalSessionCode.rebase b hooks)
      ((libsignalSessionCode.rebase b hooks).fnAddr spqrRecvName + bv% (2 ^ 64 + (ls_off% "spqr::decode_state") - (ls_off% "spqr::recv")))
      (decodeStateEmptySpec A) := by
  have h : (libsignalSessionCode.rebase b hooks).fnAddr spqrRecvName + bv% (2 ^ 64 + (ls_off% "spqr::decode_state") - (ls_off% "spqr::recv")) =
      (libsignalSessionCode.rebase b hooks).fnAddr decodeStateName := by
    simp only [Program.fnAddr_rebase,
      (ls_lemma% fnOff "spqr::recv"), (ls_lemma% fnOff "spqr::decode_state")]
    bv_omega
  rw [h]
  exact decodeStateEmpty_ok_F b hooks A

theorem decode_recv_ok_at (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr spqrRecvName + bv% (2 ^ 64 + (ls_off% "spqr::decode_state") - (ls_off% "spqr::recv")))
      (decodeStateEmptySpec A) :=
  decode_recv_ok_at_F b (Rust.withPanics (tripleRatchetExterns C ctl abs)) A

/-! ## Frame-generic `spqr::recv` specs, the `memcpy` call-site contract, and the image invariant -/

/-- `spqrRecvCodeSpec` without the `¬ S.recvPanics` conjunct in `post` (the form the code-level
proofs establish; `spqrRecvEmptyCodeSpec_of_0` adds the conjunct on an empty state). -/
def spqrRecvCodeSpec0 (A : RustAlloc) (S : SpqrModel) (img : Obj.Image) (F : SepProp) :
    Spec (VecArg × VecArg × BitVec 64) :=
  Spec.inImage
    { pre := fun (st, msg, ret) s =>
        ⌜s.readReg64 .x0 = st.v ∧ s.readReg64 .x1 = msg.v ∧ s.readReg64 .x8 = ret⌝ ∗
          st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ F ∗ A.pool ∗ stackAt s.sp spqrRecvStack
      post := fun (st, msg, ret) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ st.at A ∗ msg.at A ∗ spqrRecvResultAt A ret (S.recv st.bytes msg.bytes) ∗
          F ∗ A.pool ∗ stackAt s0.sp spqrRecvStack
      onPanic := fun (st, msg, _) s0 sf =>
        ⌜(allocFailedIn s0 sf ∨ S.recvPanics st.bytes msg.bytes) ∧ s0.trace <+: sf.trace⌝ ∗
          anyHeap }
    img

/-- `spqrRecvCodeSpec0` restricted to an empty state (`st.bytes = []`). -/
def spqrRecvEmptyCodeSpec0 (A : RustAlloc) (S : SpqrModel) (img : Obj.Image) (F : SepProp) :
    Spec (VecArg × VecArg × BitVec 64) :=
  { spqrRecvCodeSpec0 A S img F with
    pre := fun x s => ⌜x.1.bytes = []⌝ ∗ (spqrRecvCodeSpec0 A S img F).pre x s }

/-- `spqrRecvSpec A S img` with the logging cell `logOff img` replaced by an arbitrary frame `F`
(in `pre` and `post`); `spqrRecvCodeSpec A S img (logOff img)` unfolds to `spqrRecvSpec A S img`. -/
def spqrRecvCodeSpec (A : RustAlloc) (S : SpqrModel) (img : Obj.Image) (F : SepProp) :
    Spec (VecArg × VecArg × BitVec 64) :=
  Spec.inImage
    { pre := fun (st, msg, ret) s =>
        ⌜s.readReg64 .x0 = st.v ∧ s.readReg64 .x1 = msg.v ∧ s.readReg64 .x8 = ret⌝ ∗
          st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ F ∗ A.pool ∗ stackAt s.sp spqrRecvStack
      post := fun (st, msg, ret) s0 sf =>
        ⌜sf.trace = s0.trace ∧ ¬ S.recvPanics st.bytes msg.bytes⌝ ∗ st.at A ∗ msg.at A ∗
          spqrRecvResultAt A ret (S.recv st.bytes msg.bytes) ∗
          F ∗ A.pool ∗ stackAt s0.sp spqrRecvStack
      onPanic := fun (st, msg, _) s0 sf =>
        ⌜(allocFailedIn s0 sf ∨ S.recvPanics st.bytes msg.bytes) ∧ s0.trace <+: sf.trace⌝ ∗
          anyHeap }
    img

/-- `spqrRecvCodeSpec` restricted to an empty state (`st.bytes = []`), as `spqrRecvEmptySpec`. -/
def spqrRecvEmptyCodeSpec (A : RustAlloc) (S : SpqrModel) (img : Obj.Image) (F : SepProp) :
    Spec (VecArg × VecArg × BitVec 64) :=
  { spqrRecvCodeSpec A S img F with
    pre := fun x s => ⌜x.1.bytes = []⌝ ∗ (spqrRecvCodeSpec A S img F).pre x s }

theorem spqrRecvEmptySpec_eq_code (A : RustAlloc) (S : SpqrModel) (img : Obj.Image) :
    spqrRecvEmptySpec A S img = spqrRecvEmptyCodeSpec A S img (logOff img) := rfl

/-- On an empty state a `SpqrModel.RecvEmptyOk` model never panics (`hE.noPanic`), so
`spqrRecvEmptyCodeSpec0` (no `¬ S.recvPanics` conjunct in `post`) gives `spqrRecvEmptyCodeSpec`;
the two specs have the same `pre` and `onPanic`. -/
theorem spqrRecvEmptyCodeSpec_of_0 {P : Program} {addr : BitVec 64}
    {A : RustAlloc} {S : SpqrModel} {img : Obj.Image} {F : SepProp} (hE : S.RecvEmptyOk)
    (h : subroutine_ok P addr (spqrRecvEmptyCodeSpec0 A S img F)) :
    subroutine_ok P addr (spqrRecvEmptyCodeSpec A S img F) := by
  refine subroutine_ok_outcome_intro fun ⟨st, msg, ret⟩ R s0 hpc hrun hpre hal => ?_
  have hst : st.bytes = [] := by
    have hpre' := hpre
    change s0.mem ⊨ (⌜st.bytes = []⌝ ∗ _) ∗ R at hpre'
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
    exact hpre'.1
  have hnp : ¬ S.recvPanics st.bytes msg.bytes := by
    rw [hst]; exact hE.noPanic msg.bytes
  refine h.mono_outcome (st, msg, ret) R s0 hpc hrun hpre hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗ _) ∗ R at hpost
    change sf.mem ⊨ (⌜sf.trace = s0.trace ∧ ¬ S.recvPanics st.bytes msg.bytes⌝ ∗ _) ∗ R
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1, hnp⟩, hpost.2⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-- `memcpyRecvPcsSpec` augmented with `stackAt sp extHookStack`. -/
def memcpyRecvPcsSpecS : Spec (BitVec 64 × BitVec 64 × BitVec 64) :=
  { memcpyRecvPcsSpec with
    pre := fun x s => memcpyRecvPcsSpec.pre x s ∗ stackAt s.sp extHookStack
    post := fun x s0 sf => memcpyRecvPcsSpec.post x s0 sf ∗ stackAt s0.sp extHookStack }

theorem memcpyRecvPcsSpecS_inImage_of {P : Program} {addr : BitVec 64} (img : Obj.Image)
    (h : subroutine_ok P addr memcpyRecvPcsSpec) :
    subroutine_ok P addr (memcpyRecvPcsSpecS.inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  change s0.mem ⊨ (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
    (memcpyRecvPcsSpec.pre x s0 ∗ stackAt s0.sp extHookStack)) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc] at hpre
  refine h.mono_outcome x (stackAt s0.sp extHookStack ∗ R) s0 hpc hrun hpre.2 hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hst, hpan⟩ | ⟨code, hst, hex⟩ | ⟨hst, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change sf.mem ⊨ (memcpyRecvPcsSpec.post x s0 sf ∗ stackAt s0.sp extHookStack) ∗ R
    rwa [sepConj_assoc]
  · change sf.mem ⊨ ⌜False⌝ ∗ _ at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · change sf.mem ⊨ ⌜False⌝ ∗ _ at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · change sf.mem ⊨ ⌜False⌝ ∗ _ at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem memcpy_recv_ok_at_S (img : Obj.Image) (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr spqrRecvName + bv% (ls_off% "memcpy" - ls_off% "spqr::recv"))
      (memcpyRecvPcsSpecS.inImage img) :=
  memcpyRecvPcsSpecS_inImage_of img (memcpy_recv_ok_at b C ctl abs)

/-- Image call-site invariant `img.FrozenLoaded s ∧ s.symtab = img.symtab`. -/
abbrev RecvImgInv (img : Obj.Image) (s : State) : Prop :=
  img.FrozenLoaded s ∧ s.symtab = img.symtab

theorem RecvImgInv.congr {img : Obj.Image} {s s' : State} (h : RecvImgInv img s)
    (hm : s'.mem = s.mem) (hs : s'.symtab = s.symtab) : RecvImgInv img s' := by
  refine ⟨?_, hs.trans h.2⟩
  have h1 := Obj.Image.frozenLoaded_iff.1 h.1
  rw [← hm] at h1
  exact Obj.Image.frozenLoaded_iff.2 h1

theorem RecvImgInv.of_steps {img : Obj.Image} {prog : Program} {s s' : State}
    (h : RecvImgInv img s) (hs : Steps prog s s') : RecvImgInv img s' :=
  ⟨h.1.of_keepsFrozen hs.keepsFrozen, hs.symtab_eq.trans h.2⟩

/-- `SepWP` sequencing through `mid`, handing the image invariant to the continuation. -/
theorem sepWP_seq_recvImg {prog : Program} {img : Obj.Image} {mid target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hinv : RecvImgInv img s)
    (h : SepWP prog mid s P (fun sm Pm => RecvImgInv img sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post :=
  SepWP.of_sepWP_frozen hinv.1 hinv.2
    (SepWP.mono h fun _ _ _ _ hnext hfl hsym => hnext ⟨hfl, hsym⟩)

/-! ## Postcondition folding helpers -/

theorem pcs_entails (a c i : BitVec 64) : pcs a c i ⊢ memRegion a 320 := by
  refine Entails.trans (bytes_of_pcs a c i) (Entails.sepExists_elim fun bs => ?_)
  refine Entails.pure_left fun h => ?_
  have e := pointsToBytes_entails_memRegion a bs
  rw [h.1] at e
  exact e

theorem dst_recv_fold (t c i : BitVec 64) :
    (memRegion (t - 4960#64) 16 ∗ ((t - 4944#64) ↦₆₄ c) ∗
      memRegion (t - 4936#64) 72 ∗ ((t - 4864#64) ↦₆₄ i) ∗ memRegion (t - 4856#64) 216) ⊢
    memRegion (t - 4960#64) 320 := by
  rw [← pcs_dst]; exact pcs_entails _ c i

theorem decode_recv_fold (t w d1 d2 d3 c i : BitVec 64) :
    ((t - 3056#64) ↦₆₄ w) ∗ ((t - 3048#64) ↦₆₄ d1) ∗ ((t - 3040#64) ↦₆₄ d2) ∗
      ((t - 3032#64) ↦₆₄ d3) ∗
      (memRegion (t - 3024#64) 16 ∗ ((t - 3008#64) ↦₆₄ c) ∗
        memRegion (t - 3000#64) 72 ∗ ((t - 2928#64) ↦₆₄ i) ∗ memRegion (t - 2920#64) 216) ⊢
    memRegion (t - 3056#64) 352 := by
  rw [← pcs_src]
  rw [mr_cut' t 3056 3048 8 344 352 rfl rfl (by decide) (by decide) (by decide),
    mr_cut' t 3048 3040 8 336 344 rfl rfl (by decide) (by decide) (by decide),
    mr_cut' t 3040 3032 8 328 336 rfl rfl (by decide) (by decide) (by decide),
    mr_cut' t 3032 3024 8 320 328 rfl rfl (by decide) (by decide) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono
    (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pcs_entails _ c i))))

/-- The `Ok` result (`([], none)`) written at `ret` on the empty-state path. -/
theorem recv_ok_result_fold (A : RustAlloc) (r : BitVec 64) :
    ((r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ 1#64) ∗ ((r + 16#64) ↦₆₄ 0#64) ∗
      ((r + 24#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (r + 32#64) 16) ⊢
    spqrRecvResultAt A r (.ok ([], none)) := by
  have hv : ((r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ 1#64) ∗ ((r + 16#64) ↦₆₄ 0#64)) ⊢ vecU8 A r [] := by
    unfold vecU8
    refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
    refine Entails.trans ?_ (Entails.sepExists_intro 1#64)
    simp only [vecU8At, vecHeader, List.length_nil]
    split
    · rw [sepConj_emp, sepConj_comm _ ⌜_⌝]
      refine Entails.pure_right ?_ (Entails.refl _)
      exact ⟨Nat.zero_le _, by decide, by decide⟩
    · exact absurd rfl ‹_›
  simp only [spqrRecvResultAt, spqrRecvKeyAt]
  refine Entails.trans (Entails.of_eq (Q := ((r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ 1#64) ∗
      ((r + 16#64) ↦₆₄ 0#64)) ∗ (((r + 24#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
      memRegion (r + 32#64) 16)) (by simp only [sepConj_assoc])) ?_
  refine sepConj_mono hv ?_
  refine Entails.trans ?_ (Entails.sepExists_intro true)
  exact Entails.of_eq (by rw [BitVec.add_assoc]; rfl)

/-- The `Err(MsgDecode)` result (`.error false`: word 0 = `-1`, word 8 = `2`) written at `ret`. -/
theorem recv_err_result_fold (A : RustAlloc) (r r2 r3 : BitVec 64) :
    ((r ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((r + 8#64) ↦₆₄ 2#64) ∗
      ((r + 16#64) ↦₆₄ r2) ∗ ((r + 24#64) ↦₆₄ r3) ∗ memRegion (r + 32#64) 16) ⊢
    spqrRecvResultAt A r (.error false) := by
  simp only [spqrRecvResultAt]
  have h8 : ((r + 8#64) ↦₆₄ 2#64) ⊢ ((r + 8#64) ↦₈ 2#8) ∗ memRegion (r + 9#64) 7 := by
    rw [pointsTo64_eq_pointsToBytes]
    change ((r + 8#64) ↦ₛ (2#8 :: [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8])) ⊢ _
    rw [pointsToBytes_cons, show r + 8#64 + 1#64 = r + 9#64 by bv_arith]
    exact sepConj_mono_right (pointsToBytes_entails_memRegion _ _)
  have htail :
      memRegion (r + 9#64) 7 ∗ ((r + 16#64) ↦₆₄ r2) ∗ ((r + 24#64) ↦₆₄ r3) ∗
        memRegion (r + 32#64) 16 ⊢
      memRegion (r + 9#64) 39 := by
    rw [show (39 : Nat) = 7 + (8 + (8 + 16)) by decide,
        memRegion_split (r + 9#64) 7 32 (by decide),
        show r + 9#64 + 7#64 = r + 16#64 by bv_arith,
        memRegion_split (r + 16#64) 8 24 (by decide),
        show r + 16#64 + 8#64 = r + 24#64 by bv_arith,
        memRegion_split (r + 24#64) 8 16 (by decide),
        show r + 24#64 + 8#64 = r + 32#64 by bv_arith]
    exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))
  refine sepConj_mono_right ?_
  refine Entails.trans (sepConj_mono_left h8) ?_
  rw [sepConj_assoc]
  refine Entails.trans (sepConj_mono_right htail) ?_
  refine sepConj_mono_left ?_
  refine Entails.trans ?_ (Entails.sepExists_intro 2#8)
  exact Entails.pure_right (by decide) (Entails.refl _)

end CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty
