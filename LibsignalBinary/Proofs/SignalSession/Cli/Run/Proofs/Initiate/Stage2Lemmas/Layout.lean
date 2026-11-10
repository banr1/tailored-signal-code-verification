/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.Layout

/-!
# Stage 2 Stack and Key Byte-Split Lemmas

Provides `s0.sp`-relative decompositions of `initSaved`, `initArgsAt`, `initFreshRecAt`, and
`cliBundleAt`, linear `memRegion` split/fold combinators (`mr_split`, `mr_fold`), 32-byte 4-word
splits (`keyWords4`), and unaligned byte-level splits for the 64-byte `(pk, sk)` pair
(`exists_kpSplit`) and optional 32-byte one-time pre-key.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

/-! ## Stack alignment and linear `memRegion` combinators -/

theorem spAligned_of_frame {s0 s : State}
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hal : s0.spAligned = true) :
    s.spAligned = true := by
  dsimp only [State.spAligned] at hal ⊢
  rw [hsp, show BitVec.ofNat 64 cliInitiateFrame = 7408#64 from rfl]
  bv_bits

theorem spAligned_mask_of_frame {s0 s : State}
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hal : s0.spAligned = true) :
    ((s.sp &&& 15#64) == 0#64) = true :=
  spAligned_of_frame hsp hal

theorem spAligned_mask_add_4096 {s : State}
    (hal : ((s.sp &&& 15#64) == 0#64) = true) :
    (((s.sp + 4096#64) &&& 15#64) == 0#64) = true := by
  rw [beq_iff_eq] at hal ⊢
  bv_bits

theorem spAligned_mask_add_7312 {s : State}
    (hal : ((s.sp &&& 15#64) == 0#64) = true) :
    (((s.sp + 7312#64) &&& 15#64) == 0#64) = true := by
  rw [beq_iff_eq] at hal ⊢
  bv_bits

theorem mr_split (b b' : BitVec 64) (n k mn : Nat)
    (hmn : mn = n + k) (hb : b' = b + BitVec.ofNat 64 n)
    (hle : mn ≤ 2 ^ 64 := by decide) :
    memRegion b mn = memRegion b n ∗ memRegion b' k :=
  ProofLib.memRegion_split' (b := b) (n := n) (k := k) (N := mn) (b' := b') hmn hb hle

theorem mr_fold {P Q : SepProp} (b b' : BitVec 64) (n k mn : Nat)
    (hP : P ⊢ memRegion b n) (hQ : Q ⊢ memRegion b' k)
    (hmn : mn = n + k := by rfl) (hb : b' = b + BitVec.ofNat 64 n := by bv_omega)
    (hle : mn ≤ 2 ^ 64 := by decide) :
    P ∗ Q ⊢ memRegion b mn := by
  rw [mr_split b b' n k mn hmn hb hle]
  exact sepConj_mono hP hQ

theorem mr_of_u64 (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) ⊢ memRegion a 8 :=
  IsBlock.entails_memRegion (IsBlock.pointsTo64 a v)

theorem mr_of_u32 (a : BitVec 64) (v : BitVec 32) :
    (a ↦₃₂ v) ⊢ memRegion a 4 :=
  IsBlock.entails_memRegion (IsBlock.pointsTo32 a v)

theorem mr_of_u16 (a : BitVec 64) (v : BitVec 16) :
    (a ↦₁₆ v) ⊢ memRegion a 2 :=
  IsBlock.entails_memRegion (IsBlock.pointsTo16 a v)

theorem mr_of_u8 (a : BitVec 64) (v : BitVec 8) :
    (a ↦₈ v) ⊢ memRegion a 1 :=
  IsBlock.entails_memRegion (IsBlock.pointsTo8 a v)

theorem mr_of_bytes (a : BitVec 64) (bs : List (BitVec 8)) (n : Nat) (hn : bs.length = n) :
    (a ↦ₛ bs) ⊢ memRegion a n :=
  hn ▸ IsBlock.entails_memRegion (IsBlock.pointsToBytes a bs)

theorem memRegion_8_eq_exists (a : BitVec 64) :
    memRegion a 8 = ∃∗ v : BitVec 64, a ↦₆₄ v := by
  rw [show (8 : Nat) = 8 * 1 from rfl, ProofLib.memRegion_cells a 1 (by decide)]
  simp [ProofLib.cells]

theorem memRegion_4_eq_exists (a : BitVec 64) :
    memRegion a 4 = ∃∗ v : BitVec 32, a ↦₃₂ v := by
  apply Entails.antisymm
  · rw [memRegion_eq_exists_bytes a 4 (by decide)]
    refine Entails.sepExists_elim fun bs => ?_
    refine Entails.pure_left fun hlen => ?_
    match bs, hlen with
    | [b0, b1, b2, b3], _ =>
      refine Entails.sepExists_right (b3 ++ b2 ++ b1 ++ b0) ?_
      rw [pointsTo32_eq_pointsToBytes]
      have hu : unpack32 (b3 ++ b2 ++ b1 ++ b0) = [b0, b1, b2, b3] := by
        dsimp only [unpack32]
        exact congrArg₂ List.cons (by bv_bits)
          (congrArg₂ List.cons (by bv_bits)
            (congrArg₂ List.cons (by bv_bits)
              (congrArg₂ List.cons (by bv_bits) rfl)))
      rw [hu]
      exact Entails.refl _
  · exact Entails.sepExists_elim fun v => mr_of_u32 a v

theorem memRegion_1_eq_exists (a : BitVec 64) :
    memRegion a 1 = ∃∗ v : BitVec 8, a ↦₈ v := by
  apply Entails.antisymm
  · rw [memRegion_eq_exists_bytes a 1 (by decide)]
    refine Entails.sepExists_elim fun bs => ?_
    refine Entails.pure_left fun hlen => ?_
    match bs, hlen with
    | [b0], _ =>
      refine Entails.sepExists_right b0 ?_
      rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
      exact Entails.refl _
  · exact Entails.sepExists_elim fun v => mr_of_u8 a v

private theorem u64_addr_eq {a b v : BitVec 64} (h : a = b) : (a ↦₆₄ v) = (b ↦₆₄ v) := h ▸ rfl
private theorem u32_addr_eq {a b : BitVec 64} {v : BitVec 32} (h : a = b) : (a ↦₃₂ v) = (b ↦₃₂ v) := h ▸ rfl
private theorem mr_addr_eq {a b : BitVec 64} {n : Nat} (h : a = b) : memRegion a n = memRegion b n := h ▸ rfl

/-! ## Saved-register spill area, argument table, and stack reassembly -/

theorem initSaved_eq_sp (s0 : State) :
    initSaved s0 =
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .fp) ∗
      ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
      ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
      ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
      ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) := by
  dsimp only [initSaved]
  exact congrArg₂ sepConj (u64_addr_eq (by bv_omega))
    (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
      (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
        (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
          (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
            (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
              (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
                (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
                  (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
                    (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
                      (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
                        (u64_addr_eq (by bv_omega))))))))))))

theorem initSaved_entails_memRegion (s0 : State) :
    initSaved s0 ⊢ memRegion (s0.sp - 96#64) 96 := by
  rw [initSaved_eq_sp s0]
  refine mr_fold (s0.sp - 96#64) (s0.sp - 88#64) 8 88 96 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 88#64) (s0.sp - 80#64) 8 80 88 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 80#64) (s0.sp - 72#64) 8 72 80 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 72#64) (s0.sp - 64#64) 8 64 72 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 64#64) (s0.sp - 56#64) 8 56 64 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 56#64) (s0.sp - 48#64) 8 48 56 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 48#64) (s0.sp - 40#64) 8 40 48 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 40#64) (s0.sp - 32#64) 8 32 40 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 32#64) (s0.sp - 24#64) 8 24 32 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 24#64) (s0.sp - 16#64) 8 16 24 (mr_of_u64 _ _) ?_
  exact mr_fold (s0.sp - 16#64) (s0.sp - 8#64) 8 8 16 (mr_of_u64 _ _) (mr_of_u64 _ _)

theorem err_stack_fold (s0 : State) {stk : Nat}
    (hge : cliInitiateFrame ≤ stk) (hhi : stk ≤ 2 ^ 63) :
    memRegion (s0.sp - BitVec.ofNat 64 cliInitiateFrame) initLocalsSize ∗
      initSaved s0 ∗
      stackAt (s0.sp - BitVec.ofNat 64 cliInitiateFrame) (stk - cliInitiateFrame) ⊢
      stackAt s0.sp stk := by
  have hhi64 : stk ≤ 2 ^ 64 := by omega
  rw [Store.IdTrustPoll.Helpers.stackAt_sub_split s0.sp hge hhi64]
  dsimp only [stackAt]
  have hbot : s0.sp - BitVec.ofNat 64 cliInitiateFrame - BitVec.ofNat 64 (stk - cliInitiateFrame) =
      s0.sp - BitVec.ofNat 64 stk := by
    have heq : BitVec.ofNat 64 stk =
        BitVec.ofNat 64 cliInitiateFrame + BitVec.ofNat 64 (stk - cliInitiateFrame) := by
      rw [← BitVec.ofNat_add, show cliInitiateFrame + (stk - cliInitiateFrame) = stk by omega]
    rw [heq]
    bv_omega
  rw [hbot]
  have htop :
      memRegion (s0.sp - BitVec.ofNat 64 cliInitiateFrame) initLocalsSize ∗ initSaved s0 ⊢
        memRegion (s0.sp - BitVec.ofNat 64 cliInitiateFrame) cliInitiateFrame :=
    mr_fold (s0.sp - BitVec.ofNat 64 cliInitiateFrame) (s0.sp - 96#64)
      initLocalsSize 96 cliInitiateFrame (Entails.refl _) (initSaved_entails_memRegion s0)
      rfl (by dsimp [cliInitiateFrame, initLocalsSize]; bv_omega) (by decide)
  rw [← sepConj_assoc, sepConj_comm]
  exact sepConj_mono_right htop

theorem initArgsAt_eq_sp (img : Obj.Image) (x : InitGhost) (s0 : State) :
    initArgsAt img (s0.sp - BitVec.ofNat 64 cliInitiateFrame) x s0 =
      ((s0.sp - 7200#64) ↦₆₄ x.peerA) ∗
      ((s0.sp - 7192#64) ↦₆₄ x.meA) ∗
      ((s0.sp - 7184#64) ↦₆₄ (x.stores + 0xf0#64)) ∗
      ((s0.sp - 7176#64) ↦₆₄ sessVt img) ∗
      ((s0.sp - 7168#64) ↦₆₄ x.stores) ∗
      ((s0.sp - 7160#64) ↦₆₄ idVt img) ∗
      ((s0.sp - 7152#64) ↦₆₄ x.bundleA) ∗
      ((s0.sp - 7144#64) ↦₆₄ 0#64) ∗
      ((s0.sp - 7136#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 7132#64) 4 ∗
      ((s0.sp - 7128#64) ↦₆₄ (s0.sp - 0x71#64)) ∗
      ((s0.sp - 7120#64) ↦₆₄ (x.bundleA + 0x78#64)) := by
  dsimp only [initArgsAt, cliInitiateFrame]
  exact congrArg₂ sepConj (u64_addr_eq (by bv_omega))
    (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
      (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
        (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
          (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
            (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
              (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
                (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
                  (congrArg₂ sepConj (u32_addr_eq (by bv_omega))
                    (congrArg₂ sepConj (mr_addr_eq (by bv_omega))
                      (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
                        (u64_addr_eq (by bv_omega))))))))))))

theorem initArgsAt_entails_memRegion (img : Obj.Image) (x : InitGhost) (s0 : State) :
    initArgsAt img (s0.sp - BitVec.ofNat 64 cliInitiateFrame) x s0 ⊢
      memRegion (s0.sp - 7200#64) 88 := by
  rw [initArgsAt_eq_sp]
  refine mr_fold (s0.sp - 7200#64) (s0.sp - 7192#64) 8 80 88 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 7192#64) (s0.sp - 7184#64) 8 72 80 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 7184#64) (s0.sp - 7176#64) 8 64 72 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 7176#64) (s0.sp - 7168#64) 8 56 64 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 7168#64) (s0.sp - 7160#64) 8 48 56 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 7160#64) (s0.sp - 7152#64) 8 40 48 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 7152#64) (s0.sp - 7144#64) 8 32 40 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 7144#64) (s0.sp - 7136#64) 8 24 32 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 7136#64) (s0.sp - 7132#64) 4 20 24 (mr_of_u32 _ _) ?_
  refine mr_fold (s0.sp - 7132#64) (s0.sp - 7128#64) 4 16 20 (Entails.refl _) ?_
  exact mr_fold (s0.sp - 7128#64) (s0.sp - 7120#64) 8 8 16 (mr_of_u64 _ _) (mr_of_u64 _ _)

theorem initFreshRecAt_eq_sp (s0 : State) :
    initFreshRecAt (s0.sp - BitVec.ofNat 64 cliInitiateFrame) =
      ((s0.sp - 7112#64) ↦₆₄ 0#64) ∗
      ((s0.sp - 7104#64) ↦₆₄ 8#64) ∗
      ((s0.sp - 7096#64) ↦₆₄ 0#64) ∗
      ((s0.sp - 7088#64) ↦₆₄ (0#64 - 1#64)) := by
  dsimp only [initFreshRecAt, cliInitiateFrame]
  have e0 : s0.sp - 7408#64 + 0x128#64 = s0.sp - 7112#64 := by bv_omega
  have e1 : s0.sp - 7408#64 + 0x130#64 = s0.sp - 7104#64 := by bv_omega
  have e2 : s0.sp - 7408#64 + 0x138#64 = s0.sp - 7096#64 := by bv_omega
  have e3 : s0.sp - 7408#64 + 0x140#64 = s0.sp - 7088#64 := by bv_omega
  rw [e0, e1, e2, e3]; rfl

/-! ## 32-byte 4-word split and 64-byte `(pk, sk)` unaligned split -/

theorem exists_word64_of_len8 {bs : List (BitVec 8)} (h : bs.length = 8) :
    ∃ w : BitVec 64, ∀ a : BitVec 64, (a ↦ₛ bs) = (a ↦₆₄ w) := by
  match bs, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    refine ⟨b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0, fun a => ?_⟩
    rw [pointsTo64_eq_pointsToBytes]
    have hu : unpack64 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) =
        [b0, b1, b2, b3, b4, b5, b6, b7] := by
      dsimp only [unpack64]
      exact congrArg₂ List.cons (by bv_bits)
        (congrArg₂ List.cons (by bv_bits)
          (congrArg₂ List.cons (by bv_bits)
            (congrArg₂ List.cons (by bv_bits)
              (congrArg₂ List.cons (by bv_bits)
                (congrArg₂ List.cons (by bv_bits)
                  (congrArg₂ List.cons (by bv_bits)
                    (congrArg₂ List.cons (by bv_bits) rfl)))))))
    rw [hu]

theorem exists_keyWords4_of_len32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ w0 w1 w2 w3 : BitVec 64,
      ∀ (a a1 a2 a3 : BitVec 64),
        a1 = a + 8#64 → a2 = a + 16#64 → a3 = a + 24#64 →
        (a ↦ₛ bs) = (a ↦₆₄ w0) ∗ (a1 ↦₆₄ w1) ∗ (a2 ↦₆₄ w2) ∗ (a3 ↦₆₄ w3) := by
  have hc0 : (bs.take 8).length = 8 := by simp [h]
  have hc1 : ((bs.drop 8).take 8).length = 8 := by simp [h]
  have hc2 : ((bs.drop 16).take 8).length = 8 := by simp [h]
  have hc3 : (bs.drop 24).length = 8 := by simp [h]
  obtain ⟨w0, hw0⟩ := exists_word64_of_len8 hc0
  obtain ⟨w1, hw1⟩ := exists_word64_of_len8 hc1
  obtain ⟨w2, hw2⟩ := exists_word64_of_len8 hc2
  obtain ⟨w3, hw3⟩ := exists_word64_of_len8 hc3
  have hbs : bs = bs.take 8 ++ ((bs.drop 8).take 8 ++ ((bs.drop 16).take 8 ++ bs.drop 24)) := by
    have s0 : bs = bs.take 8 ++ bs.drop 8 := (List.take_append_drop 8 bs).symm
    have s1 : bs.drop 8 = (bs.drop 8).take 8 ++ bs.drop 16 := by
      simpa [List.drop_drop] using (List.take_append_drop 8 (bs.drop 8)).symm
    have s2 : bs.drop 16 = (bs.drop 16).take 8 ++ bs.drop 24 := by
      simpa [List.drop_drop] using (List.take_append_drop 8 (bs.drop 16)).symm
    exact s0.trans (congrArg (bs.take 8 ++ ·) (s1.trans (congrArg ((bs.drop 8).take 8 ++ ·) s2)))
  refine ⟨w0, w1, w2, w3, fun a a1 a2 a3 e1 e2 e3 => ?_⟩
  subst e1 e2 e3
  conv_lhs => rw [hbs]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      hc0, hc1, hc2, hw0, hw1, hw2, hw3]
  have p2 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  rw [p2]
  have p3 : a + 16#64 + 8#64 = a + 24#64 := by bv_omega
  rw [p3]

/-- Decomposes 64 contiguous bytes `(pk, sk)` at `out + 1` into 7 leading bytes (`b0..b6`), four
64-bit words (`u1..u4`), three 64-bit words (`u5..u7`), and trailing byte `b63` to match the
unaligned `u32` and `ldp` copies in Stage 2. -/
theorem exists_kpSplit {pk sk : List (BitVec 8)} (hpk : pk.length = 32) (hsk : sk.length = 32) :
    ∃ (b0 b1 b2 b3 b4 b5 b6 b63 : BitVec 8) (u1 u2 u3 u4 u5 u6 u7 : BitVec 64),
      (∀ out : BitVec 64,
        ((out + 1#64) ↦ₛ pk) ∗ ((out + 0x21#64) ↦ₛ sk) =
          ((out + 1#64) ↦₈ b0) ∗ ((out + 2#64) ↦₈ b1) ∗ ((out + 3#64) ↦₈ b2) ∗
          ((out + 4#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗
          ((out + 8#64) ↦₆₄ u1) ∗ ((out + 16#64) ↦₆₄ u2) ∗
          ((out + 24#64) ↦₆₄ u3) ∗ ((out + 32#64) ↦₆₄ u4) ∗
          ((out + 40#64) ↦₆₄ u5) ∗ ((out + 48#64) ↦₆₄ u6) ∗
          ((out + 56#64) ↦₆₄ u7) ∗ ((out + 64#64) ↦₈ b63)) ∧
      (∀ a : BitVec 64,
        (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
          ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗
          ((a + 7#64) ↦₆₄ u1) ∗ ((a + 15#64) ↦₆₄ u2) ∗
          ((a + 23#64) ↦₆₄ u3) ∗ ((a + 31#64) ↦₆₄ u4) =
          (a ↦ₛ pk) ∗ ((a + 32#64) ↦ₛ sk.take 7)) ∧
      (∀ s : BitVec 64,
        (s ↦ₛ sk.take 7) ∗
          ((s + 7#64) ↦₆₄ u5) ∗ ((s + 15#64) ↦₆₄ u6) ∗
          ((s + 23#64) ↦₆₄ u7) ∗ ((s + 31#64) ↦₈ b63) =
          (s ↦ₛ sk)) := by
  let hd := pk.take 7
  have hhd : hd.length = 7 := by simp [hd, hpk]
  match h_hd : hd, hhd with
  | [b0, b1, b2, b3, b4, b5, b6], _ =>
    let mid32 := pk.drop 7 ++ sk.take 7
    have hmid32 : mid32.length = 32 := by simp [mid32, hpk, hsk]
    obtain ⟨u1, u2, u3, u4, hu14⟩ := exists_keyWords4_of_len32 hmid32
    let s1 := (sk.drop 7).take 8
    let s2 := (sk.drop 15).take 8
    let s3 := (sk.drop 23).take 8
    let stail := sk.drop 31
    have hs1 : s1.length = 8 := by simp [s1, hsk]
    have hs2 : s2.length = 8 := by simp [s2, hsk]
    have hs3 : s3.length = 8 := by simp [s3, hsk]
    have hst : stail.length = 1 := by simp [stail, hsk]
    obtain ⟨u5, hu5⟩ := exists_word64_of_len8 hs1
    obtain ⟨u6, hu6⟩ := exists_word64_of_len8 hs2
    obtain ⟨u7, hu7⟩ := exists_word64_of_len8 hs3
    match h_st : stail, hst with
    | [b63], _ =>
      have hpk_eq : pk = [b0, b1, b2, b3, b4, b5, b6] ++ pk.drop 7 := by
        simpa [hd, h_hd] using (List.take_append_drop 7 pk).symm
      have hsk_eq : sk = sk.take 7 ++ (s1 ++ (s2 ++ (s3 ++ [b63]))) := by
        have d0 : sk = sk.take 7 ++ sk.drop 7 := (List.take_append_drop 7 sk).symm
        have d1 : sk.drop 7 = s1 ++ sk.drop 15 := by
          simpa [s1, List.drop_drop] using (List.take_append_drop 8 (sk.drop 7)).symm
        have d2 : sk.drop 15 = s2 ++ sk.drop 23 := by
          simpa [s2, List.drop_drop] using (List.take_append_drop 8 (sk.drop 15)).symm
        have d3 : sk.drop 23 = s3 ++ [b63] := by
          simpa [s3, stail, h_st, List.drop_drop] using (List.take_append_drop 8 (sk.drop 23)).symm
        exact d0.trans (congrArg (sk.take 7 ++ ·)
          (d1.trans (congrArg (s1 ++ ·) (d2.trans (congrArg (s2 ++ ·) d3)))))
      refine ⟨b0, b1, b2, b3, b4, b5, b6, b63, u1, u2, u3, u4, u5, u6, u7, ?_, ?_, ?_⟩
      · intro out
        have ho33 : out + 0x21#64 = (out + 1#64) + BitVec.ofNat 64 pk.length := by
          rw [hpk]; bv_omega
        rw [ho33, ← pointsToBytes_append]
        have hall : pk ++ sk =
            [b0, b1, b2] ++ ([b3, b4, b5, b6] ++ (mid32 ++ (s1 ++ (s2 ++ (s3 ++ [b63]))))) := by
          conv_lhs => rw [hpk_eq, hsk_eq]
          simp only [mid32, List.append_assoc, List.cons_append, List.nil_append]
        rw [hall]
        simp only [pointsToBytes_append, List.length_cons, List.length_nil]
        have hw32 : ∀ p : BitVec 64, (p ↦ₛ [b3, b4, b5, b6]) = (p ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) := by
          intro p
          rw [pointsTo32_eq_pointsToBytes]
          have hu : unpack32 (b6 ++ b5 ++ b4 ++ b3) = [b3, b4, b5, b6] := by
            dsimp only [unpack32]
            exact congrArg₂ List.cons (by bv_bits)
              (congrArg₂ List.cons (by bv_bits)
                (congrArg₂ List.cons (by bv_bits)
                  (congrArg₂ List.cons (by bv_bits) rfl)))
          rw [hu]
        have hb1 : ∀ p : BitVec 64, (p ↦ₛ [b0, b1, b2]) =
            (p ↦₈ b0) ∗ ((p + 1#64) ↦₈ b1) ∗ ((p + 2#64) ↦₈ b2) := by
          intro p
          simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
          have q : p + 1#64 + 1#64 = p + 2#64 := by bv_omega
          rw [q]
        have hb63 : ∀ p : BitVec 64, (p ↦ₛ [b63]) = (p ↦₈ b63) := fun p => by
          rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
        rw [hb1, hw32, hmid32, hs1, hs2, hs3,
            hu14 _ (out + 16#64) (out + 24#64) (out + 32#64) (by bv_omega) (by bv_omega) (by bv_omega),
            hu5, hu6, hu7, hb63]
        have q1 : (out + 1#64) + 1#64 = out + 2#64 := by bv_omega
        have q2 : (out + 1#64) + 2#64 = out + 3#64 := by bv_omega
        have q3 : (out + 1#64) + BitVec.ofNat 64 3 = out + 4#64 := by bv_omega
        have q4 : (out + 4#64) + BitVec.ofNat 64 4 = out + 8#64 := by bv_omega
        have q5 : (out + 8#64) + BitVec.ofNat 64 32 = out + 40#64 := by bv_omega
        have q6 : (out + 40#64) + BitVec.ofNat 64 8 = out + 48#64 := by bv_omega
        have q7 : (out + 48#64) + BitVec.ofNat 64 8 = out + 56#64 := by bv_omega
        have q8 : (out + 56#64) + BitVec.ofNat 64 8 = out + 64#64 := by bv_omega
        rw [q1, q2, q3, q4, q5, q6, q7, q8]
        simp only [sepConj_assoc]
      · intro a
        have ha32 : a + 32#64 = a + BitVec.ofNat 64 pk.length := by rw [hpk]
        rw [ha32, ← pointsToBytes_append]
        have hall : pk ++ sk.take 7 = [b0, b1, b2, b3] ++ ([b4, b5, b6] ++ mid32) := by
          conv_lhs => rw [hpk_eq]
          simp only [mid32, List.cons_append, List.nil_append]
        rw [hall]
        simp only [pointsToBytes_append, List.length_cons, List.length_nil]
        have hw32 : (a ↦ₛ [b0, b1, b2, b3]) = (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) := by
          rw [pointsTo32_eq_pointsToBytes]
          have hu : unpack32 (b3 ++ b2 ++ b1 ++ b0) = [b0, b1, b2, b3] := by
            dsimp only [unpack32]
            exact congrArg₂ List.cons (by bv_bits)
              (congrArg₂ List.cons (by bv_bits)
                (congrArg₂ List.cons (by bv_bits)
                  (congrArg₂ List.cons (by bv_bits) rfl)))
          rw [hu]
        have hb3 : ∀ p : BitVec 64, (p ↦ₛ [b4, b5, b6]) =
            (p ↦₈ b4) ∗ ((p + 1#64) ↦₈ b5) ∗ ((p + 2#64) ↦₈ b6) := by
          intro p
          simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
          have q : p + 1#64 + 1#64 = p + 2#64 := by bv_omega
          rw [q]
        rw [hw32, hb3,
            hu14 _ (a + 15#64) (a + 23#64) (a + 31#64) (by bv_omega) (by bv_omega) (by bv_omega)]
        have q1 : a + BitVec.ofNat 64 4 = a + 4#64 := by bv_omega
        have q2 : (a + 4#64) + 1#64 = a + 5#64 := by bv_omega
        have q3 : (a + 4#64) + 2#64 = a + 6#64 := by bv_omega
        have q4 : (a + 4#64) + BitVec.ofNat 64 3 = a + 7#64 := by bv_omega
        rw [q1, q2, q3, q4]
        simp only [sepConj_assoc]
      · intro s
        conv_rhs => rw [hsk_eq]
        have htk : (sk.take 7).length = 7 := by simp [hsk]
        have hb63 : ∀ p : BitVec 64, (p ↦ₛ [b63]) = (p ↦₈ b63) := fun p => by
          rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
        simp only [pointsToBytes_append, htk, hs1, hs2, hs3, hu5, hu6, hu7, hb63]
        have q1 : s + BitVec.ofNat 64 7 = s + 7#64 := rfl
        have q2 : (s + 7#64) + BitVec.ofNat 64 8 = s + 15#64 := by bv_omega
        have q3 : (s + 15#64) + BitVec.ofNat 64 8 = s + 23#64 := by bv_omega
        have q4 : (s + 23#64) + BitVec.ofNat 64 8 = s + 31#64 := by bv_omega
        rw [q1, q2, q3, q4]

/-! ## Optional one-time pre-key 32-byte unaligned copy decomposition -/

theorem memRegion_2_eq_exists (a : BitVec 64) :
    memRegion a 2 = ∃∗ v : BitVec 16, a ↦₁₆ v := by
  apply Entails.antisymm
  · rw [memRegion_eq_exists_bytes a 2 (by decide)]
    refine Entails.sepExists_elim fun bs => ?_
    refine Entails.pure_left fun hlen => ?_
    match bs, hlen with
    | [b0, b1], _ =>
      refine Entails.sepExists_right (b1 ++ b0) ?_
      rw [pointsTo16_eq_pointsToBytes]
      have hu : unpack16 (b1 ++ b0) = [b0, b1] := by
        dsimp only [unpack16]
        exact congrArg₂ List.cons (by bv_bits) (congrArg₂ List.cons (by bv_bits) rfl)
      rw [hu]
      exact Entails.refl _
  · exact Entails.sepExists_elim fun v => mr_of_u16 a v

theorem exists_u16_of_len2 {bs : List (BitVec 8)} (h : bs.length = 2) :
    ∃ w : BitVec 16, ∀ a : BitVec 64, (a ↦ₛ bs) = (a ↦₁₆ w) := by
  match bs, h with
  | [b0, b1], _ =>
    refine ⟨b1 ++ b0, fun a => ?_⟩
    rw [pointsTo16_eq_pointsToBytes]
    have hu : unpack16 (b1 ++ b0) = [b0, b1] := by
      dsimp only [unpack16]
      exact congrArg₂ List.cons (by bv_bits) (congrArg₂ List.cons (by bv_bits) rfl)
    rw [hu]

theorem exists_u32_of_len4 {bs : List (BitVec 8)} (h : bs.length = 4) :
    ∃ w : BitVec 32, ∀ a : BitVec 64, (a ↦ₛ bs) = (a ↦₃₂ w) := by
  match bs, h with
  | [b0, b1, b2, b3], _ =>
    refine ⟨b3 ++ b2 ++ b1 ++ b0, fun a => ?_⟩
    rw [pointsTo32_eq_pointsToBytes]
    have hu : unpack32 (b3 ++ b2 ++ b1 ++ b0) = [b0, b1, b2, b3] := by
      dsimp only [unpack32]
      exact congrArg₂ List.cons (by bv_bits)
        (congrArg₂ List.cons (by bv_bits)
          (congrArg₂ List.cons (by bv_bits)
            (congrArg₂ List.cons (by bv_bits) rfl)))
    rw [hu]

theorem exists_opkSplit32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (v0 : BitVec 32) (v1 : BitVec 16) (v2 : BitVec 8)
      (v3 v4 v5 : BitVec 64) (v6 : BitVec 8),
      ∀ (a a4 a6 a7 a15 a23 a31 : BitVec 64),
        a4 = a + 4#64 → a6 = a + 6#64 → a7 = a + 7#64 →
        a15 = a + 15#64 → a23 = a + 23#64 → a31 = a + 31#64 →
        (a ↦ₛ bs) =
          (a ↦₃₂ v0) ∗ (a4 ↦₁₆ v1) ∗ (a6 ↦₈ v2) ∗
          (a7 ↦₆₄ v3) ∗ (a15 ↦₆₄ v4) ∗ (a23 ↦₆₄ v5) ∗ (a31 ↦₈ v6) := by
  let c0 := bs.take 4
  let c1 := (bs.drop 4).take 2
  let c2 := (bs.drop 6).take 1
  let c3 := (bs.drop 7).take 8
  let c4 := (bs.drop 15).take 8
  let c5 := (bs.drop 23).take 8
  let c6 := bs.drop 31
  have hc0 : c0.length = 4 := by simp [c0, h]
  have hc1 : c1.length = 2 := by simp [c1, h]
  have hc2 : c2.length = 1 := by simp [c2, h]
  have hc3 : c3.length = 8 := by simp [c3, h]
  have hc4 : c4.length = 8 := by simp [c4, h]
  have hc5 : c5.length = 8 := by simp [c5, h]
  have hc6 : c6.length = 1 := by simp [c6, h]
  obtain ⟨v0, hv0⟩ := exists_u32_of_len4 hc0
  obtain ⟨v1, hv1⟩ := exists_u16_of_len2 hc1
  obtain ⟨v3, hv3⟩ := exists_word64_of_len8 hc3
  obtain ⟨v4, hv4⟩ := exists_word64_of_len8 hc4
  obtain ⟨v5, hv5⟩ := exists_word64_of_len8 hc5
  match h_c2 : c2, hc2, h_c6 : c6, hc6 with
  | [v2], _, [v6], _ =>
    have hbs : bs = c0 ++ (c1 ++ ([v2] ++ (c3 ++ (c4 ++ (c5 ++ [v6]))))) := by
      have s0 : bs = c0 ++ bs.drop 4 := (List.take_append_drop 4 bs).symm
      have s1 : bs.drop 4 = c1 ++ bs.drop 6 := by
        simpa [c1, List.drop_drop] using (List.take_append_drop 2 (bs.drop 4)).symm
      have s2 : bs.drop 6 = [v2] ++ bs.drop 7 := by
        simpa [c2, h_c2, List.drop_drop] using (List.take_append_drop 1 (bs.drop 6)).symm
      have s3 : bs.drop 7 = c3 ++ bs.drop 15 := by
        simpa [c3, List.drop_drop] using (List.take_append_drop 8 (bs.drop 7)).symm
      have s4 : bs.drop 15 = c4 ++ bs.drop 23 := by
        simpa [c4, List.drop_drop] using (List.take_append_drop 8 (bs.drop 15)).symm
      have s5 : bs.drop 23 = c5 ++ [v6] := by
        simpa [c5, c6, h_c6, List.drop_drop] using (List.take_append_drop 8 (bs.drop 23)).symm
      exact s0.trans (congrArg (c0 ++ ·)
        (s1.trans (congrArg (c1 ++ ·)
          (s2.trans (congrArg ([v2] ++ ·)
            (s3.trans (congrArg (c3 ++ ·)
              (s4.trans (congrArg (c4 ++ ·) s5)))))))))
    refine ⟨v0, v1, v2, v3, v4, v5, v6, fun a a4 a6 a7 a15 a23 a31 e4 e6 e7 e15 e23 e31 => ?_⟩
    subst e4 e6 e7 e15 e23 e31
    conv_lhs => rw [hbs]
    have hb2 : ∀ p : BitVec 64, (p ↦ₛ [v2]) = (p ↦₈ v2) := fun p => by
      rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
    have hb6 : ∀ p : BitVec 64, (p ↦ₛ [v6]) = (p ↦₈ v6) := fun p => by
      rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
    simp only [pointsToBytes_append, hc0, hc1, hc3, hc4, hc5, List.length_singleton,
      hv0, hv1, hb2, hv3, hv4, hv5, hb6]
    have q1 : a + BitVec.ofNat 64 4 = a + 4#64 := rfl
    have q2 : (a + 4#64) + BitVec.ofNat 64 2 = a + 6#64 := by bv_omega
    have q3 : (a + 6#64) + 1#64 = a + 7#64 := by bv_omega
    have q4 : (a + 7#64) + BitVec.ofNat 64 8 = a + 15#64 := by bv_omega
    have q5 : (a + 15#64) + BitVec.ofNat 64 8 = a + 23#64 := by bv_omega
    have q6 : (a + 23#64) + BitVec.ofNat 64 8 = a + 31#64 := by bv_omega
    rw [q1, q2, q3, q4, q5, q6]

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
