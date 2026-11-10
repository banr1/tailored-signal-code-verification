/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
import all Init.Data.String.Defs

/-!
# Stage 5 Pure Model, `SepWPp`, Stack, and `SpeOwned` Relocation Bridge

`SepWPp` extraction/rodata helpers, store/frame bounds, `RelocWords` 6-word relocation for
`RunDrop.SpeOwned` (`speOwnedAt_words6`), and `initDef` / `slotOut` / `InitPanicPost` agreement
lemmas.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

/-! ## `SepWPp` Extraction and Rodata Injection -/

theorem sat_eq {m : Memory} {P Q : SepProp} (heq : P = Q) (hm : m ⊨ P) : m ⊨ Q :=
  heq ▸ hm

theorem entails_ac {P Q : SepProp} (heq : P = Q) : P ⊢ Q :=
  heq ▸ Entails.refl P

theorem entails_exists_intro {α : Sort _} {P : α → SepProp} (x : α) :
    P x ⊢ ∃∗ y, P y := by
  simpa [sepConj_emp] using Entails.sepExists_intro_frame (R := emp) x
    (entails_ac (sepConj_emp (P x)).symm)

/-- Inject a read-only `.data.rel.ro` assertion `Ro` into the precondition of `SepWPp` whenever
`s.mem ⊨ P' → s.mem ⊨ Ro ∗ P'` holds for arbitrary `P'`. -/
theorem sepWPp_with_rodata {prog : Program} {ret : BitVec 64} {s : State}
    {Ro P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinj : ∀ P', s.mem ⊨ P' → s.mem ⊨ Ro ∗ P')
    (hwp : SepWPp prog ret s (Ro ∗ P) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  fun R hm => hwp R (by rw [sepConj_assoc]; exact hinj _ hm)

/-- Extract any meta-level existential / pure witnesses satisfied on `s.mem ⊨ P ∗ R` before
continuing with `SepWPp`. -/
theorem sepWPp_extract_sat {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ R, s.mem ⊨ P ∗ R →
      ∃ P' : SepProp, (s.mem ⊨ P' ∗ R) ∧ SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  fun R hm hL => let ⟨_, hm', hwp⟩ := h R hm; hwp R hm' hL

/-! ## Store and Frame Arithmetic Helpers -/

/-- Ground preconditions of `idRegIdPollSpec` on `StoresGhost.opened.identity.own`. -/
theorem opened_own_regId_pre :
    StoresGhost.opened.identity.own.path.length < 2 ^ 32 ∧
      cliWrOk (pathOf StoresGhost.opened.identity.own.path (utf8 "registration-id")) :=
  ⟨Nat.le_of_ble_eq_true (by rfl_kernel), cliWrOk_ownFile (by simp [ownFiles])⟩

/-- Ground preconditions of `idSavePollSpec` on `StoresGhost.opened.identity.peers`. -/
theorem opened_peers_bounds :
    StoresGhost.opened.identity.peers.path.length < 2 ^ 32 ∧
      StoresGhost.opened.identity.peers.changed.length < 2 ^ 32 :=
  ⟨Nat.le_of_ble_eq_true (by rfl_kernel), Nat.le_of_ble_eq_true (by rfl_kernel)⟩

/-- Ground precondition of `sessStorePollSpec` on `StoresGhost.opened.sessions`. -/
theorem opened_sessions_changed_lt :
    StoresGhost.opened.sessions.changed.length < 2 ^ 32 :=
  Nat.le_of_ble_eq_true (by rfl_kernel)

/-- Reassemble `stackAt s0.sp stk` from `stackAt fsp (stk - cliInitiateFrame)` and the reclaimed
frame `memRegion fsp cliInitiateFrame` (`fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame`). -/
theorem stackAt_merge_initiateFrame {B : RunBudgets} {stk : Nat}
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) (sp0 : BitVec 64) :
    let fsp := sp0 - BitVec.ofNat 64 cliInitiateFrame
    stackAt fsp (stk - cliInitiateFrame) ∗ memRegion fsp cliInitiateFrame ⊢
      stackAt sp0 stk := by
  intro fsp
  have hge : cliInitiateFrame ≤ stk := stk_ge_frame hstk
  have heq : stk = (stk - cliInitiateFrame) + cliInitiateFrame := by omega
  have hbase : sp0 - BitVec.ofNat 64 stk = fsp - BitVec.ofNat 64 (stk - cliInitiateFrame) := by
    dsimp only [fsp]
    bv_omega
  have hmid : (sp0 - BitVec.ofNat 64 stk) + BitVec.ofNat 64 (stk - cliInitiateFrame) = fsp := by
    dsimp only [fsp]
    bv_omega
  dsimp only [stackAt]
  have hrhs : memRegion (sp0 - BitVec.ofNat 64 stk) stk =
      memRegion (sp0 - BitVec.ofNat 64 stk) ((stk - cliInitiateFrame) + cliInitiateFrame) :=
    congrArg (memRegion (sp0 - BitVec.ofNat 64 stk)) heq
  rw [hrhs, memRegion_split (sp0 - BitVec.ofNat 64 stk) (stk - cliInitiateFrame) cliInitiateFrame
    (by omega), hmid, ← hbase]
  exact Entails.refl _

/-! ## 8-Byte Packing and `RelocWords` Algebra for `SpeOwned` -/

def pack8LE (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  b0.zeroExtend 64 ||| (b1.zeroExtend 64 <<< 8) ||| (b2.zeroExtend 64 <<< 16) |||
    (b3.zeroExtend 64 <<< 24) ||| (b4.zeroExtend 64 <<< 32) ||| (b5.zeroExtend 64 <<< 40) |||
    (b6.zeroExtend 64 <<< 48) ||| (b7.zeroExtend 64 <<< 56)

theorem unpack64_pack8LE (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    unpack64 (pack8LE b0 b1 b2 b3 b4 b5 b6 b7) = [b0, b1, b2, b3, b4, b5, b6, b7] := by
  dsimp only [unpack64, pack8LE]
  refine congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_
    (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_
      (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ rfl))))))) <;>
    (ext i hi; interval_cases i <;> simp)

theorem pointsToBytes_8_exists_64 {bs : List (BitVec 8)} (h : bs.length = 8) :
    ∃ w : BitVec 64, ∀ a : BitVec 64, (a ↦ₛ bs) = (a ↦₆₄ w) := by
  match bs, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    refine ⟨pack8LE b0 b1 b2 b3 b4 b5 b6 b7, fun a => ?_⟩
    rw [pointsTo64_eq_pointsToBytes, unpack64_pack8LE]

/-- `F` owns an `8 * n`-byte inline region at `a` whose words can be read word-by-word at `src`
and reassembled at any `dst` while leaving any heap frame untouched. -/
def RelocWords : Nat → (BitVec 64 → SepProp) → Prop
  | 0, F => ∀ src dst R (m : Memory), m ⊨ F src ∗ R →
      ∃ H : SepProp, (m ⊨ H ∗ R) ∧ (H ⊢ F dst)
  | n + 1, F => ∀ src dst R (m : Memory), m ⊨ F src ∗ R →
      ∃ (w : BitVec 64) (G : BitVec 64 → SepProp),
        RelocWords n G ∧
        (m ⊨ (src ↦₆₄ w) ∗ (G (src + 8#64) ∗ R)) ∧
        (((dst ↦₆₄ w) ∗ G (dst + 8#64)) ⊢ F dst)

theorem relocWords_emp : RelocWords 0 (fun _ => emp) :=
  fun _ _ _ _ hm => ⟨emp, hm, Entails.refl _⟩

theorem relocWords_frame_const (H : SepProp) : RelocWords 0 (fun _ => H) :=
  fun _ _ _ _ hm => ⟨H, hm, Entails.refl _⟩

theorem relocWords_word (w : BitVec 64) : RelocWords 1 (fun a => a ↦₆₄ w) := by
  intro src dst R m hm
  refine ⟨w, fun _ => emp, relocWords_emp, ?_, ?_⟩
  · simpa [sepConj_emp] using hm
  · rw [sepConj_emp]
    exact Entails.refl _

theorem relocWords_exists {α : Type} {n : Nat} {F : α → BitVec 64 → SepProp}
    (h : ∀ x, RelocWords n (F x)) : RelocWords n (fun a => ∃∗ x, F x a) := by
  cases n with
  | zero =>
    intro src dst R m hm
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm
    obtain ⟨x, hm⟩ := hm
    obtain ⟨H, hm', hent⟩ := h x src dst R m hm
    exact ⟨H, hm', Entails.sepExists_right x hent⟩
  | succ k =>
    intro src dst R m hm
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm
    obtain ⟨x, hm⟩ := hm
    obtain ⟨w, G, hG, hm', hent⟩ := h x src dst R m hm
    exact ⟨w, G, hG, hm', Entails.sepExists_right x hent⟩

theorem relocWords_congr_eq {n : Nat} {F G : BitVec 64 → SepProp}
    (heq : ∀ a, F a = G a) (hF : RelocWords n F) : RelocWords n G := by
  have hfun : F = G := funext heq
  exact hfun ▸ hF

private theorem relocWords_prepend_const (HF : SepProp) :
    ∀ {n : Nat} {G0 : BitVec 64 → SepProp},
      RelocWords n G0 → RelocWords n (fun p => HF ∗ G0 p)
  | 0, G0, hG => fun s d R0 m0 hm0 => by
      dsimp only at hm0 ⊢
      have hm0' : m0 ⊨ G0 s ∗ (HF ∗ R0) := sat_eq (by ac_rfl) hm0
      obtain ⟨H2, hm2, hent2⟩ := hG s d (HF ∗ R0) m0 hm0'
      exact ⟨HF ∗ H2, sat_eq (by ac_rfl) hm2, sepConj_mono_right hent2⟩
  | _ + 1, G0, hG => fun s d R0 m0 hm0 => by
      dsimp only at hm0 ⊢
      have hm0' : m0 ⊨ G0 s ∗ (HF ∗ R0) := sat_eq (by ac_rfl) hm0
      obtain ⟨w2, G2, hG2, hm2, hent2⟩ := hG s d (HF ∗ R0) m0 hm0'
      refine ⟨w2, fun p => HF ∗ G2 p, relocWords_prepend_const HF hG2, ?_, ?_⟩
      · dsimp only
        exact sat_eq (by ac_rfl) hm2
      · dsimp only
        exact Entails.trans (entails_ac (by ac_rfl)) (sepConj_mono_right hent2)

theorem relocWords_append {k n : Nat} {F G : BitVec 64 → SepProp}
    (hF : RelocWords k F) (hG : RelocWords n G) :
    RelocWords (k + n) (fun a => F a ∗ G (a + BitVec.ofNat 64 (8 * k))) := by
  induction k generalizing F with
  | zero =>
    simp only [Nat.zero_add, Nat.mul_zero, BitVec.add_zero]
    cases n with
    | zero =>
      intro src dst R m hm
      rw [sepConj_assoc] at hm
      obtain ⟨HF, hmF, hentF⟩ := hF src dst (G src ∗ R) m hm
      have hmG : m ⊨ G src ∗ (HF ∗ R) := sat_eq (by ac_rfl) hmF
      obtain ⟨HG, hmG', hentG⟩ := hG src dst (HF ∗ R) m hmG
      exact ⟨HF ∗ HG, sat_eq (by ac_rfl) hmG', sepConj_mono hentF hentG⟩
    | succ n' =>
      intro src dst R m hm
      rw [sepConj_assoc] at hm
      obtain ⟨HF, hmF, hentF⟩ := hF src dst (G src ∗ R) m hm
      have hmG : m ⊨ G src ∗ (HF ∗ R) := sat_eq (by ac_rfl) hmF
      obtain ⟨w, G', hG', hmG', hentG⟩ := hG src dst (HF ∗ R) m hmG
      refine ⟨w, fun p => HF ∗ G' p, relocWords_prepend_const HF hG',
        by dsimp only; exact sat_eq (by ac_rfl) hmG', ?_⟩
      dsimp only
      exact Entails.trans (entails_ac (by ac_rfl)) (sepConj_mono hentF hentG)
  | succ k' ih =>
    rw [Nat.succ_add]
    intro src dst R m hm
    rw [sepConj_assoc] at hm
    obtain ⟨w, F', hF', hmF, hentF⟩ :=
      hF src dst (G (src + BitVec.ofNat 64 (8 * (k' + 1))) ∗ R) m hm
    refine ⟨w, fun p => F' p ∗ G (p + BitVec.ofNat 64 (8 * k')), ih hF', ?_, ?_⟩
    · dsimp only
      have hs : src + 8#64 + BitVec.ofNat 64 (8 * k') = src + BitVec.ofNat 64 (8 * (k' + 1)) := by
        bv_omega
      rw [hs]
      simpa [sepConj_assoc] using hmF
    · dsimp only
      have hd : dst + 8#64 + BitVec.ofNat 64 (8 * k') = dst + BitVec.ofNat 64 (8 * (k' + 1)) := by
        bv_omega
      rw [hd]
      exact Entails.trans (entails_ac (by ac_rfl)) (sepConj_mono_left hentF)

theorem relocWords_memRegion_1 : RelocWords 1 (fun a => memRegion a 8) :=
  relocWords_congr_eq (fun a => (ProofLib.memRegion_eight a).symm)
    (relocWords_exists relocWords_word)

theorem relocWords_memRegion :
    ∀ n, 8 * n < 2 ^ 64 → RelocWords n (fun a => memRegion a (8 * n))
  | 0, _ => relocWords_congr_eq (fun a => (memRegion_zero a).symm) relocWords_emp
  | n + 1, hn => by
    have hsplit : ∀ a, memRegion a (8 * (n + 1)) = memRegion a 8 ∗ memRegion (a + 8#64) (8 * n) := by
      intro a
      rw [show 8 * (n + 1) = 8 + 8 * n by omega]
      exact memRegion_split a 8 (8 * n) (by omega)
    have h8 : BitVec.ofNat 64 (8 * 1) = 8#64 := rfl
    have raw : RelocWords (n + 1) (fun a => memRegion a 8 ∗ memRegion (a + 8#64) (8 * n)) := by
      simpa [Nat.add_comm 1 n, h8] using
        relocWords_append relocWords_memRegion_1 (relocWords_memRegion n (by omega))
    exact relocWords_congr_eq (fun a => (hsplit a).symm) raw

theorem relocWords_u8_pad7 (b : BitVec 8) :
    RelocWords 1 (fun a => (a ↦₈ b) ∗ memRegion (a + 1#64) 7) := by
  intro src dst R m hm
  dsimp only at hm ⊢
  rw [memRegion_eq_exists_bytes (src + 1#64) 7 (by omega)] at hm
  have hm' :
      m ⊨ (∃∗ bs : List (BitVec 8), ⌜bs.length = 7⌝ ∗ ((src + 1#64) ↦ₛ bs)) ∗ ((src ↦₈ b) ∗ R) :=
    sat_eq (by ac_rfl) hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm'
  obtain ⟨bs, hm'⟩ := hm'
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm'
  obtain ⟨hlen, hm'⟩ := hm'
  have hcons : ∀ a, (a ↦ₛ (b :: bs)) = (a ↦₈ b) ∗ ((a + 1#64) ↦ₛ bs) := fun a => by
    show (a ↦ₛ ([b] ++ bs)) = _
    rw [pointsToBytes_append, show BitVec.ofNat 64 ([b].length) = 1#64 from rfl,
      pointsToBytes_singleton]
  have hm8 : m ⊨ (src ↦ₛ (b :: bs)) ∗ R := by
    rw [hcons src]
    exact sat_eq (by ac_rfl) hm'
  obtain ⟨w, hw⟩ := pointsToBytes_8_exists_64 (bs := b :: bs) (by simp [hlen])
  rw [hw src] at hm8
  refine ⟨w, fun _ => emp, relocWords_emp, by simpa [sepConj_emp] using hm8, ?_⟩
  rw [sepConj_emp, ← hw dst, hcons dst, memRegion_eq_exists_bytes (dst + 1#64) 7 (by omega)]
  refine sepConj_mono_right ?_
  exact Entails.sepExists_right bs (by rw [pure_sepConj_of_true hlen]; exact Entails.refl _)

theorem relocWords_u32_pair (x y : BitVec 32) :
    RelocWords 1 (fun a => (a ↦₃₂ x) ∗ ((a + 4#64) ↦₃₂ y)) := by
  intro src dst R m hm
  have hpair : ∀ a, ((a ↦₃₂ x) ∗ ((a + 4#64) ↦₃₂ y)) = (a ↦ₛ (unpack32 x ++ unpack32 y)) := by
    intro a
    rw [pointsToBytes_append, unpack32_length,
      ← pointsTo32_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]
  obtain ⟨w, hw⟩ := pointsToBytes_8_exists_64 (bs := unpack32 x ++ unpack32 y) (by simp)
  have hm' : m ⊨ ((src ↦₃₂ x) ∗ ((src + 4#64) ↦₃₂ y)) ∗ R := sat_eq (by ac_rfl) hm
  rw [hpair src, hw src] at hm'
  refine ⟨w, fun _ => emp, relocWords_emp, by simpa [sepConj_emp] using hm', ?_⟩
  rw [sepConj_emp, ← hw dst, ← hpair dst]
  exact Entails.refl _

theorem relocWords_vecU8At (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    RelocWords 3 (fun a => vecU8At A a cap ptr bs) := by
  intro src dst R m hm
  let H : SepProp := vecU8Buf A cap ptr bs
  have heq : ∀ a, vecU8At A a cap ptr bs =
      (a ↦₆₄ cap) ∗ (((a + 8#64) ↦₆₄ ptr) ∗ (((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ H)) := by
    intro a
    dsimp only [vecU8At, vecHeader, vecU8Buf, H]
    ac_rfl
  have h1 : RelocWords (1 + 0) (fun p => (p ↦₆₄ BitVec.ofNat 64 bs.length) ∗ H) :=
    by simpa [BitVec.add_zero] using relocWords_append (relocWords_word _) (relocWords_frame_const H)
  have h2 : RelocWords (1 + 1) (fun p =>
      (p ↦₆₄ ptr) ∗ (((p + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ H)) := by
    have h8 : BitVec.ofNat 64 (8 * 1) = 8#64 := rfl
    simpa [h8] using relocWords_append (relocWords_word ptr) h1
  have h3 : RelocWords (1 + 2) (fun a =>
      (a ↦₆₄ cap) ∗ (((a + 8#64) ↦₆₄ ptr) ∗ (((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ H))) := by
    have h8 : BitVec.ofNat 64 (8 * 1) = 8#64 := rfl
    have raw := relocWords_append (relocWords_word cap) h2
    refine relocWords_congr_eq (fun a => ?_) raw
    have ha : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
    rw [h8, ha]
  exact relocWords_congr_eq (fun a => (heq a).symm) h3 src dst R m hm

theorem relocWords_vecU8 (A : RustAlloc) (bs : List (BitVec 8)) :
    RelocWords 3 (fun a => RustHeap.vecU8 A a bs) :=
  relocWords_exists fun cap => relocWords_exists fun ptr => relocWords_vecU8At A cap ptr bs

theorem relocWords_strRef (s : List (BitVec 8)) :
    RelocWords 2 (fun a => strRefAt a s) := by
  refine relocWords_exists fun p => ?_
  have h1 : RelocWords (1 + 0) (fun q => (q ↦₆₄ BitVec.ofNat 64 s.length) ∗ (p ↦ᵣ s)) :=
    by simpa [BitVec.add_zero] using
      relocWords_append (relocWords_word _) (relocWords_frame_const (p ↦ᵣ s))
  exact relocWords_congr_eq (fun a => by dsimp only [strRefAt])
    (relocWords_append (relocWords_word p) h1)

theorem relocWords_addrClone (A : RustAlloc) (v : AddrVal) :
    RelocWords 4 (fun a => addrCloneAt A a v) := by
  have raw := relocWords_append (relocWords_vecU8 A v.name) (relocWords_u8_pad7 v.device)
  refine relocWords_congr_eq (fun a => ?_) raw
  dsimp only [addrCloneAt]
  have h24 : BitVec.ofNat 64 (8 * 3) = 24#64 := rfl
  have ha : a + 24#64 + 1#64 = a + 25#64 := by bv_omega
  rw [h24, ha]

/-- Unpack a `RelocWords 5` payload at `src + 8#64` together with a fixed first word `w0` at `src`
into the concrete 6-word form expected by the epilogue stores. -/
theorem unpack_word0_and_reloc5 {src dst w0 : BitVec 64} {G5 H0 : SepProp}
    {F5 : BitVec 64 → SepProp} {R : SepProp} {m : Memory}
    (hrel5 : RelocWords 5 F5)
    (hm : m ⊨ (src ↦₆₄ w0) ∗ (F5 (src + 8#64) ∗ (H0 ∗ R)))
    (h0 : w0 + 3#64 ≠ 0#64 ∧ w0 + 2#64 ≠ 0#64)
    (hdst : ((dst ↦₆₄ w0) ∗ F5 (dst + 8#64) ∗ H0) ⊢ G5) :
    ∃ (u0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp),
      u0 + 3#64 ≠ 0#64 ∧ u0 + 2#64 ≠ 0#64 ∧
      (m ⊨ (src ↦₆₄ u0) ∗ ((src + 8#64) ↦₆₄ w1) ∗ ((src + 16#64) ↦₆₄ w2) ∗
        ((src + 24#64) ↦₆₄ w3) ∗ ((src + 32#64) ↦₆₄ w4) ∗ ((src + 40#64) ↦₆₄ w5) ∗ (H ∗ R)) ∧
      (((dst ↦₆₄ u0) ∗ ((dst + 8#64) ↦₆₄ w1) ∗ ((dst + 16#64) ↦₆₄ w2) ∗
        ((dst + 24#64) ↦₆₄ w3) ∗ ((dst + 32#64) ↦₆₄ w4) ∗ ((dst + 40#64) ↦₆₄ w5) ∗ H) ⊢ G5) := by
  have hm1 : m ⊨ F5 (src + 8#64) ∗ ((src ↦₆₄ w0) ∗ H0 ∗ R) := sat_eq (by ac_rfl) hm
  obtain ⟨w1, G4, hG4, hm2, hent1⟩ := hrel5 (src + 8#64) (dst + 8#64) _ m hm1
  have hm2' : m ⊨ G4 (src + 8#64 + 8#64) ∗ ((src ↦₆₄ w0) ∗ ((src + 8#64) ↦₆₄ w1) ∗ H0 ∗ R) :=
    sat_eq (by ac_rfl) hm2
  obtain ⟨w2, G3, hG3, hm3, hent2⟩ := hG4 (src + 8#64 + 8#64) (dst + 8#64 + 8#64) _ m hm2'
  have hm3' : m ⊨ G3 (src + 8#64 + 8#64 + 8#64) ∗
      ((src ↦₆₄ w0) ∗ ((src + 8#64) ↦₆₄ w1) ∗ ((src + 8#64 + 8#64) ↦₆₄ w2) ∗ H0 ∗ R) :=
    sat_eq (by ac_rfl) hm3
  obtain ⟨w3, G2, hG2, hm4, hent3⟩ :=
    hG3 (src + 8#64 + 8#64 + 8#64) (dst + 8#64 + 8#64 + 8#64) _ m hm3'
  have hm4' : m ⊨ G2 (src + 8#64 + 8#64 + 8#64 + 8#64) ∗
      ((src ↦₆₄ w0) ∗ ((src + 8#64) ↦₆₄ w1) ∗ ((src + 8#64 + 8#64) ↦₆₄ w2) ∗
       ((src + 8#64 + 8#64 + 8#64) ↦₆₄ w3) ∗ H0 ∗ R) :=
    sat_eq (by ac_rfl) hm4
  obtain ⟨w4, G1, hG1, hm5, hent4⟩ :=
    hG2 (src + 8#64 + 8#64 + 8#64 + 8#64) (dst + 8#64 + 8#64 + 8#64 + 8#64) _ m hm4'
  have hm5' : m ⊨ G1 (src + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) ∗
      ((src ↦₆₄ w0) ∗ ((src + 8#64) ↦₆₄ w1) ∗ ((src + 8#64 + 8#64) ↦₆₄ w2) ∗
       ((src + 8#64 + 8#64 + 8#64) ↦₆₄ w3) ∗
       ((src + 8#64 + 8#64 + 8#64 + 8#64) ↦₆₄ w4) ∗ H0 ∗ R) :=
    sat_eq (by ac_rfl) hm5
  obtain ⟨w5, G0, hG0, hm6, hent5⟩ :=
    hG1 (src + 8#64 + 8#64 + 8#64 + 8#64 + 8#64)
        (dst + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) _ m hm5'
  have hm6' : m ⊨ G0 (src + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) ∗
      ((src ↦₆₄ w0) ∗ ((src + 8#64) ↦₆₄ w1) ∗ ((src + 8#64 + 8#64) ↦₆₄ w2) ∗
       ((src + 8#64 + 8#64 + 8#64) ↦₆₄ w3) ∗
       ((src + 8#64 + 8#64 + 8#64 + 8#64) ↦₆₄ w4) ∗
       ((src + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) ↦₆₄ w5) ∗ H0 ∗ R) :=
    sat_eq (by ac_rfl) hm6
  obtain ⟨Hend, hmEnd, hentEnd⟩ :=
    hG0 (src + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64)
        (dst + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) _ m hm6'
  have hs16 : src + 8#64 + 8#64 = src + 16#64 := by bv_omega
  have hs24 : src + 8#64 + 8#64 + 8#64 = src + 24#64 := by bv_omega
  have hs32 : src + 8#64 + 8#64 + 8#64 + 8#64 = src + 32#64 := by bv_omega
  have hs40 : src + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 = src + 40#64 := by bv_omega
  have hd16 : dst + 8#64 + 8#64 = dst + 16#64 := by bv_omega
  have hd24 : dst + 8#64 + 8#64 + 8#64 = dst + 24#64 := by bv_omega
  have hd32 : dst + 8#64 + 8#64 + 8#64 + 8#64 = dst + 32#64 := by bv_omega
  have hd40 : dst + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 = dst + 40#64 := by bv_omega
  rw [hs40, hs32, hs24, hs16] at hmEnd
  refine ⟨w0, w1, w2, w3, w4, w5, Hend ∗ H0, h0.1, h0.2, sat_eq (by ac_rfl) hmEnd, ?_⟩
  have hchain :
      ((dst + 8#64) ↦₆₄ w1) ∗ (((dst + 16#64) ↦₆₄ w2) ∗ (((dst + 24#64) ↦₆₄ w3) ∗
        (((dst + 32#64) ↦₆₄ w4) ∗ (((dst + 40#64) ↦₆₄ w5) ∗ Hend)))) ⊢ F5 (dst + 8#64) := by
    rw [← hd16, ← hd24, ← hd32, ← hd40]
    exact Entails.trans
      (sepConj_mono_right <| sepConj_mono_right <| sepConj_mono_right <|
        sepConj_mono_right <| sepConj_mono_right hentEnd)
      (Entails.trans
        (sepConj_mono_right <| sepConj_mono_right <| sepConj_mono_right <|
          sepConj_mono_right hent5)
        (Entails.trans
          (sepConj_mono_right <| sepConj_mono_right <| sepConj_mono_right hent4)
          (Entails.trans
            (sepConj_mono_right <| sepConj_mono_right hent3)
            (Entails.trans (sepConj_mono_right hent2) hent1))))
  exact Entails.trans
    (entails_ac (by ac_rfl :
      ((dst ↦₆₄ w0) ∗ ((dst + 8#64) ↦₆₄ w1) ∗ ((dst + 16#64) ↦₆₄ w2) ∗
        ((dst + 24#64) ↦₆₄ w3) ∗ ((dst + 32#64) ↦₆₄ w4) ∗ ((dst + 40#64) ↦₆₄ w5) ∗ (Hend ∗ H0)) =
      (dst ↦₆₄ w0) ∗ (((dst + 8#64) ↦₆₄ w1) ∗ (((dst + 16#64) ↦₆₄ w2) ∗
        (((dst + 24#64) ↦₆₄ w3) ∗ (((dst + 32#64) ↦₆₄ w4) ∗
        (((dst + 40#64) ↦₆₄ w5) ∗ Hend))))) ∗ H0))
    (Entails.trans (sepConj_mono_right (sepConj_mono_left hchain)) hdst)

theorem unpack_word0_and_reloc5_emp {src dst w0 : BitVec 64} {G5 : SepProp}
    {F5 : BitVec 64 → SepProp} {R : SepProp} {m : Memory}
    (hrel5 : RelocWords 5 F5)
    (hm : m ⊨ (src ↦₆₄ w0) ∗ (F5 (src + 8#64) ∗ R))
    (h0 : w0 + 3#64 ≠ 0#64 ∧ w0 + 2#64 ≠ 0#64)
    (hdst : ((dst ↦₆₄ w0) ∗ F5 (dst + 8#64)) ⊢ G5) :
    ∃ (u0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp),
      u0 + 3#64 ≠ 0#64 ∧ u0 + 2#64 ≠ 0#64 ∧
      (m ⊨ (src ↦₆₄ u0) ∗ ((src + 8#64) ↦₆₄ w1) ∗ ((src + 16#64) ↦₆₄ w2) ∗
        ((src + 24#64) ↦₆₄ w3) ∗ ((src + 32#64) ↦₆₄ w4) ∗ ((src + 40#64) ↦₆₄ w5) ∗ (H ∗ R)) ∧
      (((dst ↦₆₄ u0) ∗ ((dst + 8#64) ↦₆₄ w1) ∗ ((dst + 16#64) ↦₆₄ w2) ∗
        ((dst + 24#64) ↦₆₄ w3) ∗ ((dst + 32#64) ↦₆₄ w4) ∗ ((dst + 40#64) ↦₆₄ w5) ∗ H) ⊢ G5) :=
  unpack_word0_and_reloc5 (H0 := emp) hrel5 (by rwa [emp_sepConj]) h0 (by rwa [sepConj_emp])

theorem speWord_ne_poll_tags {i : Nat} (hi : i < 35) :
    speWord i + 3#64 ≠ 0#64 ∧ speWord i + 2#64 ≠ 0#64 := by
  dsimp only [speWord]
  constructor <;> bv_omega

/-- Every `RunDrop.SpeOwned` at `src` exposes 6 contiguous words `w0..w5` with
`w0 + 3#64 ≠ 0#64` (not `Poll::Pending`) and `w0 + 2#64 ≠ 0#64` (not `Poll::Ready(Ok(_))`),
and storing those exact 6 words into `dst` reconstructs `RunDrop.speOwnedAt A dst k`. -/
theorem speOwnedAt_words6 (A : RustAlloc) (src dst : BitVec 64) (k : RunDrop.SpeOwned)
    (R : SepProp) (m : Memory) (hm : m ⊨ RunDrop.speOwnedAt A src k ∗ R) :
    ∃ (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp),
      w0 + 3#64 ≠ 0#64 ∧ w0 + 2#64 ≠ 0#64 ∧
      (m ⊨ (src ↦₆₄ w0) ∗ ((src + 8#64) ↦₆₄ w1) ∗ ((src + 16#64) ↦₆₄ w2) ∗
        ((src + 24#64) ↦₆₄ w3) ∗ ((src + 32#64) ↦₆₄ w4) ∗ ((src + 40#64) ↦₆₄ w5) ∗ (H ∗ R)) ∧
      (((dst ↦₆₄ w0) ∗ ((dst + 8#64) ↦₆₄ w1) ∗ ((dst + 16#64) ↦₆₄ w2) ∗
        ((dst + 24#64) ↦₆₄ w3) ∗ ((dst + 32#64) ↦₆₄ w4) ∗ ((dst + 40#64) ↦₆₄ w5) ∗ H) ⊢
        RunDrop.speOwnedAt A dst k) := by
  cases k with
  | badKemKeyType =>
    dsimp only [RunDrop.speOwnedAt] at hm ⊢
    exact unpack_word0_and_reloc5_emp (F5 := fun p => memRegion p 40)
      (relocWords_memRegion 5 (by decide))
      (sat_eq (by ac_rfl) hm)
      (speWord_ne_poll_tags (by decide))
      (entails_ac (by ac_rfl))
  | badKemKeyLength =>
    dsimp only [RunDrop.speOwnedAt] at hm ⊢
    exact unpack_word0_and_reloc5_emp (F5 := fun p => memRegion p 40)
      (relocWords_memRegion 5 (by decide))
      (sat_eq (by ac_rfl) hm)
      (speWord_ne_poll_tags (by decide))
      (entails_ac (by ac_rfl))
  | plain i hi =>
    have hlt : i < 35 := (by decide : ∀ x ∈ RunDrop.plainSpeTags, x < 35) i hi
    dsimp only [RunDrop.speOwnedAt] at hm ⊢
    exact unpack_word0_and_reloc5_emp (F5 := fun p => memRegion p 40)
      (relocWords_memRegion 5 (by decide))
      (sat_eq (by ac_rfl) hm)
      (speWord_ne_poll_tags hlt)
      (entails_ac (by ac_rfl))
  | withString i hi =>
    have hlt : i < 35 := (by decide : ∀ x ∈ RunDrop.strSpeTags, x < 35) i hi
    dsimp only [RunDrop.speOwnedAt] at hm ⊢
    have h24 : BitVec.ofNat 64 (8 * 3) = 24#64 := rfl
    have hF5 : RelocWords (3 + 2) (fun p =>
        (∃∗ bs : List (BitVec 8), RustHeap.vecU8 A p bs) ∗ memRegion (p + 24#64) 16) := by
      simpa [h24] using
        relocWords_append (relocWords_exists (relocWords_vecU8 A))
          (relocWords_memRegion 2 (by decide))
    have ha : ∀ a : BitVec 64, a + 8#64 + 24#64 = a + 0x20#64 := fun a => by bv_omega
    exact unpack_word0_and_reloc5_emp
      (F5 := fun p =>
        (∃∗ bs : List (BitVec 8), RustHeap.vecU8 A p bs) ∗ memRegion (p + 24#64) 16)
      hF5
      (by rw [ha src]; exact sat_eq (by ac_rfl) hm)
      (speWord_ne_poll_tags hlt)
      (by rw [ha dst]; exact entails_ac (by ac_rfl))
  | untrustedIdentity addr =>
    dsimp only [RunDrop.speOwnedAt, apiErrAt] at hm ⊢
    have h32 : BitVec.ofNat 64 (8 * 4) = 32#64 := rfl
    have hF5 : RelocWords (4 + 1) (fun p => addrCloneAt A p addr ∗ memRegion (p + 32#64) 8) := by
      simpa [h32] using
        relocWords_append (relocWords_addrClone A addr) (relocWords_memRegion 1 (by decide))
    have ha : ∀ a : BitVec 64, a + 8#64 + 32#64 = a + 0x28#64 := fun a => by bv_omega
    exact unpack_word0_and_reloc5_emp
      (F5 := fun p => addrCloneAt A p addr ∗ memRegion (p + 32#64) 8)
      hF5
      (by rw [ha src]; exact sat_eq (by ac_rfl) hm)
      (speWord_ne_poll_tags (by decide))
      (by rw [ha dst]; exact entails_ac (by ac_rfl))
  | sessionNotFound addr op =>
    dsimp only [RunDrop.speOwnedAt, apiErrAt, addrCloneAt, RustHeap.vecU8] at hm
    have hm1 : m ⊨ (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, vecU8At A src cap ptr addr.name) ∗
        (((src + 0x18#64) ↦₈ addr.device) ∗ memRegion (src + 0x19#64) 7 ∗
          strRefAt (src + 0x20#64) (utf8 op) ∗ R) := sat_eq (by ac_rfl) hm
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm1
    obtain ⟨cap, hm1⟩ := hm1
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm1
    obtain ⟨ptr, hm1⟩ := hm1
    dsimp only [vecU8At, vecHeader, vecU8Buf] at hm1
    have hm_buf : m ⊨ vecU8Buf A cap ptr addr.name ∗
        ((src ↦₆₄ cap) ∗ ((src + 8#64) ↦₆₄ ptr) ∗
         ((src + 16#64) ↦₆₄ BitVec.ofNat 64 addr.name.length) ∗
         ((src + 0x18#64) ↦₈ addr.device) ∗ memRegion (src + 0x19#64) 7 ∗
         strRefAt (src + 0x20#64) (utf8 op) ∗ R) := by
      dsimp only [vecU8Buf]
      exact sat_eq (by ac_rfl) hm1
    have hcap_lt : cap.toNat < 2 ^ 63 := by
      dsimp only [vecU8Buf] at hm_buf
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm_buf
      exact hm_buf.1.2.1
    have h0 : cap + 3#64 ≠ 0#64 ∧ cap + 2#64 ≠ 0#64 := by constructor <;> bv_omega
    let F5 : BitVec 64 → SepProp := fun p =>
      (p ↦₆₄ ptr) ∗ ((p + 8#64) ↦₆₄ BitVec.ofNat 64 addr.name.length) ∗
      (((p + 16#64) ↦₈ addr.device) ∗ memRegion (p + 17#64) 7) ∗
      strRefAt (p + 24#64) (utf8 op)
    have hF5 : RelocWords 5 F5 := by
      have h8 : BitVec.ofNat 64 (8 * 1) = 8#64 := rfl
      have r2 : RelocWords (1 + 2) (fun q =>
          (((q) ↦₈ addr.device) ∗ memRegion (q + 1#64) 7) ∗ strRefAt (q + 8#64) (utf8 op)) := by
        simpa [h8] using
          relocWords_append (relocWords_u8_pad7 addr.device) (relocWords_strRef (utf8 op))
      have r3 : RelocWords (1 + 3) (fun q =>
          (q ↦₆₄ BitVec.ofNat 64 addr.name.length) ∗
          ((((q + 8#64) ↦₈ addr.device) ∗ memRegion (q + 8#64 + 1#64) 7) ∗
           strRefAt (q + 8#64 + 8#64) (utf8 op))) := by
        simpa [h8] using relocWords_append (relocWords_word _) r2
      have r4 := relocWords_append (relocWords_word ptr) r3
      refine relocWords_congr_eq (fun p => ?_) r4
      dsimp only [F5]
      have h9 : p + 8#64 + 8#64 = p + 16#64 := by bv_omega
      have h10 : p + 8#64 + 8#64 + 1#64 = p + 17#64 := by bv_omega
      have h11 : p + 8#64 + 8#64 + 8#64 = p + 24#64 := by bv_omega
      rw [h8, h10, h11, h9]
    have hsrc_eq : F5 (src + 8#64) =
        ((src + 8#64) ↦₆₄ ptr) ∗ ((src + 16#64) ↦₆₄ BitVec.ofNat 64 addr.name.length) ∗
        (((src + 0x18#64) ↦₈ addr.device) ∗ memRegion (src + 0x19#64) 7) ∗
        strRefAt (src + 0x20#64) (utf8 op) := by
      dsimp only [F5]
      have a1 : src + 8#64 + 8#64 = src + 16#64 := by bv_omega
      have a2 : src + 8#64 + 16#64 = src + 0x18#64 := by bv_omega
      have a3 : src + 8#64 + 17#64 = src + 0x19#64 := by bv_omega
      have a4 : src + 8#64 + 24#64 = src + 0x20#64 := by bv_omega
      rw [a1, a2, a3, a4]
    refine unpack_word0_and_reloc5 (H0 := vecU8Buf A cap ptr addr.name) (F5 := F5)
      hF5 (by rw [hsrc_eq]; exact sat_eq (by ac_rfl) hm_buf) h0 ?_
    dsimp only [RunDrop.speOwnedAt, apiErrAt, addrCloneAt, F5]
    have d1 : dst + 8#64 + 8#64 = dst + 16#64 := by bv_omega
    have d2 : dst + 8#64 + 16#64 = dst + 0x18#64 := by bv_omega
    have d3 : dst + 8#64 + 17#64 = dst + 0x19#64 := by bv_omega
    have d4 : dst + 8#64 + 24#64 = dst + 0x20#64 := by bv_omega
    rw [d1, d2, d3, d4]
    have hvecIntro : vecU8At A dst cap ptr addr.name ⊢ RustHeap.vecU8 A dst addr.name :=
      Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))
    exact Entails.trans
      (entails_ac (by dsimp only [vecU8At, vecHeader, vecU8Buf]; ac_rfl :
        ((dst ↦₆₄ cap) ∗ (((dst + 8#64) ↦₆₄ ptr) ∗
          ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 addr.name.length) ∗
          (((dst + 0x18#64) ↦₈ addr.device) ∗ memRegion (dst + 0x19#64) 7) ∗
          strRefAt (dst + 0x20#64) (utf8 op)) ∗ vecU8Buf A cap ptr addr.name) =
        vecU8At A dst cap ptr addr.name ∗
          (((dst + 0x18#64) ↦₈ addr.device) ∗ memRegion (dst + 0x19#64) 7 ∗
           strRefAt (dst + 0x20#64) (utf8 op))))
      (Entails.trans (sepConj_mono_left hvecIntro) (entails_ac (by ac_rfl)))
  | proto fnName e =>
    dsimp only [RunDrop.speOwnedAt, speAt] at hm ⊢
    cases e with
    | panic =>
      rw [satisfies_pure_sepConj] at hm
      exact False.elim hm.1
    | invalidProtobufEncoding =>
      exact unpack_word0_and_reloc5_emp (F5 := fun p => memRegion p 40)
        (relocWords_memRegion 5 (by decide))
        (sat_eq (by ac_rfl) hm)
        (speWord_ne_poll_tags (by decide))
        (entails_ac (by ac_rfl))
    | noKeyTypeIdentifier =>
      exact unpack_word0_and_reloc5_emp (F5 := fun p => memRegion p 40)
        (relocWords_memRegion 5 (by decide))
        (sat_eq (by ac_rfl) hm)
        (speWord_ne_poll_tags (by decide))
        (entails_ac (by ac_rfl))
    | invalidKeyAgreement =>
      exact unpack_word0_and_reloc5_emp (F5 := fun p => memRegion p 40)
        (relocWords_memRegion 5 (by decide))
        (sat_eq (by ac_rfl) hm)
        (speWord_ne_poll_tags (by decide))
        (entails_ac (by ac_rfl))
    | invalidState =>
      have h24 : BitVec.ofNat 64 (8 * 3) = 24#64 := rfl
      have hF5 : RelocWords (3 + 2) (fun p =>
          (∃∗ bs : List (BitVec 8), RustHeap.vecU8 A p bs) ∗ strRefAt (p + 24#64) fnName) := by
        simpa [h24] using
          relocWords_append (relocWords_exists (relocWords_vecU8 A)) (relocWords_strRef fnName)
      have ha : ∀ a : BitVec 64, a + 8#64 + 24#64 = a + 32#64 := fun a => by bv_omega
      exact unpack_word0_and_reloc5_emp
        (F5 := fun p =>
          (∃∗ bs : List (BitVec 8), RustHeap.vecU8 A p bs) ∗ strRefAt (p + 24#64) fnName)
        hF5
        (by rw [ha src]; exact sat_eq (by ac_rfl) hm)
        (speWord_ne_poll_tags (by decide))
        (by rw [ha dst]; exact entails_ac (by ac_rfl))
    | ciphertextMessageTooShort n =>
      have h8 : BitVec.ofNat 64 (8 * 1) = 8#64 := rfl
      have hF5 : RelocWords (1 + 4) (fun p =>
          (p ↦₆₄ BitVec.ofNat 64 n) ∗ memRegion (p + 8#64) 32) := by
        simpa [h8] using relocWords_append (relocWords_word _) (relocWords_memRegion 4 (by decide))
      have ha : ∀ a : BitVec 64, a + 8#64 + 8#64 = a + 16#64 := fun a => by bv_omega
      exact unpack_word0_and_reloc5_emp
        (F5 := fun p => (p ↦₆₄ BitVec.ofNat 64 n) ∗ memRegion (p + 8#64) 32)
        hF5
        (by rw [ha src]; exact sat_eq (by ac_rfl) hm)
        (speWord_ne_poll_tags (by decide))
        (by rw [ha dst]; exact entails_ac (by ac_rfl))
    | badKeyLength n =>
      have h8 : BitVec.ofNat 64 (8 * 1) = 8#64 := rfl
      have hF5 : RelocWords (1 + 4) (fun p =>
          (p ↦₆₄ BitVec.ofNat 64 n) ∗ memRegion (p + 8#64) 32) := by
        simpa [h8] using relocWords_append (relocWords_word _) (relocWords_memRegion 4 (by decide))
      have ha : ∀ a : BitVec 64, a + 8#64 + 8#64 = a + 16#64 := fun a => by bv_omega
      exact unpack_word0_and_reloc5_emp
        (F5 := fun p => (p ↦₆₄ BitVec.ofNat 64 n) ∗ memRegion (p + 8#64) 32)
        hF5
        (by rw [ha src]; exact sat_eq (by ac_rfl) hm)
        (speWord_ne_poll_tags (by decide))
        (by rw [ha dst]; exact entails_ac (by ac_rfl))
    | legacyCiphertextVersion v =>
      have h8 : BitVec.ofNat 64 (8 * 1) = 8#64 := rfl
      have hsplit : ∀ a : BitVec 64,
          memRegion (a + 9#64) 39 = memRegion (a + 9#64) 7 ∗ memRegion (a + 16#64) 32 := by
        intro a
        rw [memRegion_split (a + 9#64) 7 32 (by omega),
          show a + 9#64 + 7#64 = a + 16#64 by bv_omega]
      have hF5 : RelocWords (1 + 4) (fun p =>
          ((p ↦₈ v) ∗ memRegion (p + 1#64) 7) ∗ memRegion (p + 8#64) 32) := by
        simpa [h8] using
          relocWords_append (relocWords_u8_pad7 v) (relocWords_memRegion 4 (by decide))
      have ha1 : ∀ a : BitVec 64, a + 8#64 + 1#64 = a + 9#64 := fun a => by bv_omega
      have ha8 : ∀ a : BitVec 64, a + 8#64 + 8#64 = a + 16#64 := fun a => by bv_omega
      exact unpack_word0_and_reloc5_emp
        (F5 := fun p => ((p ↦₈ v) ∗ memRegion (p + 1#64) 7) ∗ memRegion (p + 8#64) 32)
        hF5
        (by rw [ha1 src, ha8 src]; rw [hsplit src] at hm
            exact sat_eq (by ac_rfl) hm)
        (speWord_ne_poll_tags (by decide))
        (by rw [ha1 dst, ha8 dst, hsplit dst]
            exact entails_ac (by ac_rfl))
    | unrecognizedCiphertextVersion v =>
      have h8 : BitVec.ofNat 64 (8 * 1) = 8#64 := rfl
      have hsplit : ∀ a : BitVec 64,
          memRegion (a + 9#64) 39 = memRegion (a + 9#64) 7 ∗ memRegion (a + 16#64) 32 := by
        intro a
        rw [memRegion_split (a + 9#64) 7 32 (by omega),
          show a + 9#64 + 7#64 = a + 16#64 by bv_omega]
      have hF5 : RelocWords (1 + 4) (fun p =>
          ((p ↦₈ v) ∗ memRegion (p + 1#64) 7) ∗ memRegion (p + 8#64) 32) := by
        simpa [h8] using
          relocWords_append (relocWords_u8_pad7 v) (relocWords_memRegion 4 (by decide))
      have ha1 : ∀ a : BitVec 64, a + 8#64 + 1#64 = a + 9#64 := fun a => by bv_omega
      have ha8 : ∀ a : BitVec 64, a + 8#64 + 8#64 = a + 16#64 := fun a => by bv_omega
      exact unpack_word0_and_reloc5_emp
        (F5 := fun p => ((p ↦₈ v) ∗ memRegion (p + 1#64) 7) ∗ memRegion (p + 8#64) 32)
        hF5
        (by rw [ha1 src, ha8 src]; rw [hsplit src] at hm
            exact sat_eq (by ac_rfl) hm)
        (speWord_ne_poll_tags (by decide))
        (by rw [ha1 dst, ha8 dst, hsplit dst]
            exact entails_ac (by ac_rfl))
    | badKeyType v =>
      have h8 : BitVec.ofNat 64 (8 * 1) = 8#64 := rfl
      have hsplit : ∀ a : BitVec 64,
          memRegion (a + 9#64) 39 = memRegion (a + 9#64) 7 ∗ memRegion (a + 16#64) 32 := by
        intro a
        rw [memRegion_split (a + 9#64) 7 32 (by omega),
          show a + 9#64 + 7#64 = a + 16#64 by bv_omega]
      have hF5 : RelocWords (1 + 4) (fun p =>
          ((p ↦₈ v) ∗ memRegion (p + 1#64) 7) ∗ memRegion (p + 8#64) 32) := by
        simpa [h8] using
          relocWords_append (relocWords_u8_pad7 v) (relocWords_memRegion 4 (by decide))
      have ha1 : ∀ a : BitVec 64, a + 8#64 + 1#64 = a + 9#64 := fun a => by bv_omega
      have ha8 : ∀ a : BitVec 64, a + 8#64 + 8#64 = a + 16#64 := fun a => by bv_omega
      exact unpack_word0_and_reloc5_emp
        (F5 := fun p => ((p ↦₈ v) ∗ memRegion (p + 1#64) 7) ∗ memRegion (p + 8#64) 32)
        hF5
        (by rw [ha1 src, ha8 src]; rw [hsplit src] at hm
            exact sat_eq (by ac_rfl) hm)
        (speWord_ne_poll_tags (by decide))
        (by rw [ha1 dst, ha8 dst, hsplit dst]
            exact entails_ac (by ac_rfl))
    | invalidSessionStructure r =>
      have h16 : BitVec.ofNat 64 (8 * 2) = 16#64 := rfl
      have hF5 : RelocWords (2 + 3) (fun p => strRefAt p (invalidSessionStructureStr r) ∗ memRegion (p + 16#64) 24) := by
        simpa [h16] using
          relocWords_append (relocWords_strRef (invalidSessionStructureStr r)) (relocWords_memRegion 3 (by decide))
      have ha : ∀ a : BitVec 64, a + 8#64 + 16#64 = a + 24#64 := fun a => by bv_omega
      exact unpack_word0_and_reloc5_emp
        (F5 := fun p => strRefAt p (invalidSessionStructureStr r) ∗ memRegion (p + 16#64) 24)
        hF5
        (by rw [ha src]; exact sat_eq (by ac_rfl) hm)
        (speWord_ne_poll_tags (by decide))
        (by rw [ha dst]; exact entails_ac (by ac_rfl))
    | duplicatedMessage u c =>
      have h8 : BitVec.ofNat 64 (8 * 1) = 8#64 := rfl
      have hF5 : RelocWords (1 + 4) (fun p =>
          ((p ↦₃₂ u) ∗ ((p + 4#64) ↦₃₂ c)) ∗ memRegion (p + 8#64) 32) := by
        simpa [h8] using
          relocWords_append (relocWords_u32_pair u c) (relocWords_memRegion 4 (by decide))
      have ha4 : ∀ a : BitVec 64, a + 8#64 + 4#64 = a + 12#64 := fun a => by bv_omega
      have ha8 : ∀ a : BitVec 64, a + 8#64 + 8#64 = a + 16#64 := fun a => by bv_omega
      exact unpack_word0_and_reloc5_emp
        (F5 := fun p => ((p ↦₃₂ u) ∗ ((p + 4#64) ↦₃₂ c)) ∗ memRegion (p + 8#64) 32)
        hF5
        (by rw [ha4 src, ha8 src]; exact sat_eq (by ac_rfl) hm)
        (speWord_ne_poll_tags (by decide))
        (by rw [ha4 dst, ha8 dst]; exact entails_ac (by ac_rfl))
    | invalidMessage t r =>
      have h8 : BitVec.ofNat 64 (8 * 1) = 8#64 := rfl
      have h24 : BitVec.ofNat 64 (8 * 3) = 24#64 := rfl
      have htail : RelocWords (1 + 1) (fun q =>
          ((q ↦₈ msgTypeByte t) ∗ memRegion (q + 1#64) 7) ∗ memRegion (q + 8#64) 8) := by
        simpa [h8] using
          relocWords_append (relocWords_u8_pad7 (msgTypeByte t))
            (relocWords_memRegion 1 (by decide))
      have hsplit : ∀ a : BitVec 64,
          memRegion (a + 33#64) 15 = memRegion (a + 33#64) 7 ∗ memRegion (a + 40#64) 8 := by
        intro a
        rw [memRegion_split (a + 33#64) 7 8 (by omega),
          show a + 33#64 + 7#64 = a + 40#64 by bv_omega]
      have ha1 : ∀ a : BitVec 64, a + 8#64 + 24#64 = a + 32#64 := fun a => by bv_omega
      have ha2 : ∀ a : BitVec 64, a + 8#64 + 24#64 + 1#64 = a + 33#64 := fun a => by bv_omega
      have ha3 : ∀ a : BitVec 64, a + 8#64 + 24#64 + 8#64 = a + 40#64 := by bv_omega
      cases r with
      | decryptionFailed =>
        dsimp only [invalidMessageStrAt] at hm
        have hf : m ⊨ ⌜False⌝ ∗ ((src ↦₆₄ speWord 24) ∗
            (((src + 32#64) ↦₈ msgTypeByte t) ∗ memRegion (src + 33#64) 15 ∗ R)) :=
          sat_eq (by ac_rfl) hm
        rw [satisfies_pure_sepConj] at hf
        exact False.elim hf.1
      | tooFarInFuture =>
        have hF5 := relocWords_append (relocWords_vecU8 A tooFarInFutureStr) htail
        exact unpack_word0_and_reloc5_emp hF5
          (by dsimp only [invalidMessageStrAt] at hm ⊢
              rw [hsplit src] at hm
              rw [h24, ha2 src, ha3 src, ha1 src]
              exact sat_eq (by ac_rfl) hm)
          (speWord_ne_poll_tags (by decide))
          (by dsimp only [invalidMessageStrAt]
              rw [h24, ha2 dst, ha3 dst, ha1 dst, hsplit dst]
              exact entails_ac (by ac_rfl))
      | macFailed =>
        have hF5 := relocWords_append (relocWords_vecU8 A macFailedStr) htail
        exact unpack_word0_and_reloc5_emp hF5
          (by dsimp only [invalidMessageStrAt] at hm ⊢
              rw [hsplit src] at hm
              rw [h24, ha2 src, ha3 src, ha1 src]
              exact sat_eq (by ac_rfl) hm)
          (speWord_ne_poll_tags (by decide))
          (by dsimp only [invalidMessageStrAt]
              rw [h24, ha2 dst, ha3 dst, ha1 dst, hsplit dst]
              exact entails_ac (by ac_rfl))
      | pqRatchet =>
        have hF5 := relocWords_append (relocWords_exists (relocWords_vecU8 A)) htail
        exact unpack_word0_and_reloc5_emp hF5
          (by dsimp only [invalidMessageStrAt] at hm ⊢
              rw [hsplit src] at hm
              rw [h24, ha2 src, ha3 src, ha1 src]
              exact sat_eq (by ac_rfl) hm)
          (speWord_ne_poll_tags (by decide))
          (by dsimp only [invalidMessageStrAt]
              rw [h24, ha2 dst, ha3 dst, ha1 dst, hsplit dst]
              exact entails_ac (by ac_rfl))
      | badCiphertext =>
        have hF5 := relocWords_append (relocWords_exists (relocWords_vecU8 A)) htail
        exact unpack_word0_and_reloc5_emp hF5
          (by dsimp only [invalidMessageStrAt] at hm ⊢
              rw [hsplit src] at hm
              rw [h24, ha2 src, ha3 src, ha1 src]
              exact sat_eq (by ac_rfl) hm)
          (speWord_ne_poll_tags (by decide))
          (by dsimp only [invalidMessageStrAt]
              rw [h24, ha2 dst, ha3 dst, ha1 dst, hsplit dst]
              exact entails_ac (by ac_rfl))

/-! ## Model Agreement and Exit/Panic Post Helpers -/

/-- Under `trustedOk`, `save_identity`'s poll cannot take `.error ()`: `idSaveOf p key` is `.ok c`
for some `c : IdentityChange`, and updating `peers` equals `saveUpd`. -/
theorem idSave_ok_of_trusted {F : FsFiles} {peer : AddrVal} {key : IdentityKey}
    {gr : Except Unit (List (BitVec 8))} {p : Except Unit (Option IdentityKey)}
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd F peer key = .ok true)
    (hgr : gr = StoresGhost.opened.identity.peers.get cliIo.rd F peer.name)
    (hp : IdPeerAns gr p) :
    ∃ c : IdentityChange,
      idSaveOf p key = .ok c ∧
      { StoresGhost.opened.identity with
        peers := idSavePeers StoresGhost.opened.identity.peers peer.name key p } =
        StoresGhost.opened.identity.saveUpd cliIo.rd F peer key := by
  have hp' : IdPeerAns (StoresGhost.opened.identity.peers.get cliIo.rd F peer.name) p := hgr ▸ hp
  have ht := IdGhost.trusted_of_peerAns (k := key) hp'
  rw [htrusted] at ht
  obtain ⟨_, hupd⟩ := IdGhost.saveAns_of_peerAns (k := key) hp'
  cases p with
  | error u => simp [idTrustOf] at ht
  | ok opt =>
    cases opt with
    | none => exact ⟨.newOrUnchanged, rfl, hupd.symm⟩
    | some known =>
      exact ⟨if known = key then .newOrUnchanged else .replacedExisting, rfl, hupd.symm⟩

/-- On `get_local_registration_id` returning `.error ()`, `initDef` evaluates to `some none`. -/
theorem initDef_eq_some_none_of_regId_err {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {F : FsFiles} {peer me : AddrVal} {bundle : BundleV} {coins : List (BitVec 8)}
    {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    (hbe : bundleEOf? bundle = some be)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd F peer bundle.idKey = .ok true)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd F = .error ()) :
    initDef X W F peer me bundle coins = some none := by
  simp only [initDef, hbe, htrusted, hkp, hreg]

theorem slotTrace_of_trace_eq {x : InitGhost} {s0 sf : State}
    (htr : sf.trace = s0.trace) (hfs0 : s0.fs.files = x.F) (hfsf : sf.fs.files = x.F) :
    slotTrace s0 sf :=
  ⟨htr ▸ List.prefix_refl _, hfsf.trans hfs0.symm, by rw [htr]⟩

theorem slotOut_err_of_some_none {ans : SlotAns Unit} {s0 sf : State}
    (hans : ans = some none) :
    slotOut ans StoresGhost.opened (.error (.protocol .invalidProtobufEncoding)) s0 sf :=
  ⟨by decide, by decide, hans⟩

theorem slotOut_ok_of_accept {W : PEParams} {ans : SlotAns Unit}
    {F : FsFiles} {peer me : AddrVal} {idKey : IdentityKey} {recBytes : List (BitVec 8)}
    {s0 sf : State}
    (hok : InitOk₀ W F peer me)
    (hans : ans = some (some (initAcceptStoresGhost F peer idKey recBytes, ()))) :
    slotOut ans (initAcceptStoresGhost F peer idKey recBytes) (.ok ()) s0 sf :=
  ⟨by nofun, by nofun, hans, initAcceptStoresGhost_writes_cliWrOk hok idKey recBytes⟩

/-- Any OOM panic (`allocFailedIn s0 sf` with `anyHeap`) entails `InitPanicPost`. -/
theorem initPanicPost_of_oom {A : RustAlloc} {img : Obj.Image} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 sf : State} {Pf : SepProp}
    (hoom : allocFailedIn s0 sf) (hheap : Pf ⊢ anyHeap) :
    InitPanicPost A img S x stk s0 sf Pf := by
  dsimp only [InitPanicPost, initSlotSpec, Spec.inImage]
  rw [pure_sepConj_of_true (Or.inr hoom)]
  exact hheap

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas
