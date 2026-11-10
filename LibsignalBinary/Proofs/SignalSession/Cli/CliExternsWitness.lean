/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryExtProofDefs
public import LibsignalBinary.Proofs.E2E.HooksE.Common
import LibsignalBinary.Proofs.E2E.Pqxdh.SpqrHooksPCommon
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StrlenUtf8A1
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
import LibsignalBinary.Proofs.TripleRatchet.Hooks

@[expose] public section

set_option autoImplicit false

/-!
# Extern Contract Satisfaction for `cliHookTable` (`cliExterns_ok`)

Proves `cliExterns_ok W : CliExternsOk ⟨W.C, W.Q⟩ E2E.HooksE.A0 (cliHookExterns W)`, establishing
that `cliHookTable W` satisfies the abstract extern contract bundle `CliExternsOk` (including PQXDH
rows over `W.Q`, `black_box`, `read_file`, and the `StepFr` frame invariants), and derives the
fixed-table whole-binary correctness statements from their `CliExternsOk`-parameterized counterparts.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack pubFromSecretName dhName staticDropName sharedDropName)

/-- Each row of `cliHookTable W` resolves to its hook in `cliHookExterns W`. -/
theorem cliHookExterns_row (W : CliHooks) {n : String} {h : State → State}
    (hm : (n, h) ∈ cliHookTable W) : cliHookExterns W n = some h :=
  lookup_of_mem_nodup _ n h (by rw [cliHookNames_eq W]; exact cliHookNames_nodup) hm

namespace ExternsWitness

/-! ## Rows and transport -/

theorem hookSat_row {α : Type} {W : CliHooks} {n : String} {h : State → State} {spec : Spec α}
    (hm : (n, h) ∈ cliHookTable W) (hh : HookOk h spec) : HookSat (cliHookExterns W) n spec :=
  ⟨h, cliHookExterns_row W hm, hh⟩

/-- A `HookSat` fact at `cliExterns W` holds at `cliHookExterns W` for a row of the table. -/
theorem hookSat_of_cliExterns {α : Type} {W : CliHooks} {n : String} {h : State → State}
    {spec : Spec α} (hm : (n, h) ∈ cliHookTable W) (hs : HookSat (cliExterns W) n spec) :
    HookSat (cliHookExterns W) n spec := by
  obtain ⟨f, hf, hok⟩ := hs
  rw [cliExterns_row W hm] at hf
  cases hf
  exact hookSat_row hm hok

theorem strlen_row (W : CliHooks) : ("strlen", strlenHook) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 9) rfl)

theorem fromUtf8_row (W : CliHooks) :
    ("core::str::converts::from_utf8", fromUtf8Hook W.utf8Err) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 15) rfl)

theorem blackBox_row (W : CliHooks) :
    ("subtle::black_box::<u8>", LibsignalSession.blackBoxHook) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 20) rfl)

theorem pubFromSecret_row (W : CliHooks) :
    (pubFromSecretName, LibsignalTripleRatchet.pubFromSecretHook W.C.pubKey) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 24) rfl)

theorem dh_row (W : CliHooks) :
    (dhName, LibsignalTripleRatchet.diffieHellmanHook W.C.X) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 25) rfl)

theorem staticDrop_row (W : CliHooks) :
    (staticDropName, LibsignalTripleRatchet.zeroizeSecretHook) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 26) rfl)

theorem sharedDrop_row (W : CliHooks) :
    (sharedDropName, LibsignalTripleRatchet.zeroizeSecretHook) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 27) rfl)

/-- Transport `HookOk f s₁` to `HookOk f s₂` along a ghost map `g : β → α` when every `s₂`-entry
maps to an `s₁`-entry at `g y` and every `s₁`-outcome yields an `s₂`-outcome. -/
theorem hookOk_map {α β : Type} {f : State → State} {s₁ : Spec α} {s₂ : Spec β} (g : β → α)
    (I : State → State → Prop) (hI : ∀ s, I s (f s))
    (hh : HookOk f s₁)
    (hpre : ∀ y R s0, s0.mem ⊨ s₂.pre y s0 ∗ R → s0.mem ⊨ s₁.pre (g y) s0 ∗ R)
    (hpost : ∀ y R s0 sf, I s0 sf → s0.mem ⊨ s₂.pre y s0 ∗ R →
      sf.mem ⊨ s₁.post (g y) s0 sf ∗ R → sf.mem ⊨ s₂.post y s0 sf ∗ R)
    (hpanic : ∀ y R s0 sf, sf.mem ⊨ s₁.onPanic (g y) s0 sf ∗ R → sf.mem ⊨ s₂.onPanic y s0 sf ∗ R)
    (hexit : ∀ y c R s0 sf,
      sf.mem ⊨ s₁.onExit (g y) c s0 sf ∗ R → sf.mem ⊨ s₂.onExit y c s0 sf ∗ R)
    (hoom : ∀ y R s0 sf, sf.mem ⊨ s₁.onOom (g y) s0 sf ∗ R → sf.mem ⊨ s₂.onOom y s0 sf ∗ R) :
    HookOk f s₂ := by
  intro y R s0 hrun hp hsp
  obtain ⟨hkf, hsym, hout⟩ := hh (g y) R s0 hrun (hpre y R s0 hp) hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hr, hc, hq⟩ | ⟨hs, hq⟩ | ⟨c, hs, hq⟩ | ⟨hs, hq⟩
  · exact Or.inl ⟨hr, hc, hpost y R s0 (f s0) (hI s0) hp hq⟩
  · exact Or.inr (Or.inl ⟨hs, hpanic y R s0 (f s0) hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hs, hexit y c R s0 (f s0) hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hs, hoom y R s0 (f s0) hq⟩))

/-- `HookOk h spec` framed by `stk` stack bytes (`CliExt.withStack`), for a spec that cannot
panic, exit or run out of memory. -/
theorem hookOk_cliWithStack {α : Type} {h : State → State} {spec : Spec α} (hh : HookOk h spec)
    (stk : Nat) (hp : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝)
    (he : ∀ x c s0 sf, spec.onExit x c s0 sf = ⌜False⌝)
    (ho : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝) : HookOk h (CliExt.withStack spec stk) :=
  Cli.MainHops.hookOk_withStack hh stk hp he ho

/-! ## The PQXDH rows -/

/-- A pure leaf hook (`compress`, `edNeg`, `scalarMod`, `scalarWide`) meets `CliExt.pureByteFunctionSpec`. -/
theorem leafHook_ok {m n : Nat} (hn : n ≤ 2 ^ 64)
    (f : List.Vector (BitVec 8) m → List.Vector (BitVec 8) n) (byVal : Bool) :
    HookOk
      (fun s => LibsignalAesCbc.returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x8)
        (f (E2E.readVecN s.mem (s.readReg64 .x0) m)).toList)))
      (CliExt.pureByteFunctionSpec f byVal) := by
  change HookOk
    (retHook (fun s => s.setMem (s.mem.writeBytes (s.readReg64 .x8)
      (f (E2E.readVecN s.mem (s.readReg64 .x0) m)).toList)))
    (CliExt.pureByteFunctionSpec f byVal)
  refine retHook_ok fun ⟨inA, v, ret⟩ R s0 hrun hpre _ => ?_
  simp only [CliExt.pureByteFunctionSpec, CliExt.withStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8⟩, hmem⟩
  have hv : E2E.readVecN s0.mem inA m = v := E2E.Pqxdh.readVecN_eq_of_pointsToBytes hmem
  have hlen : (f v).toList.length ≤ 2 ^ 64 := by rw [List.Vector.toList_length]; exact hn
  have hmem_out : s0.mem ⊨ memRegion ret (f v).toList.length ∗
      ((inA ↦ₛ v.toList) ∗ stackAt s0.sp extHookStack ∗ R) := by
    rw [List.Vector.toList_length]
    ac_nf at hmem ⊢
  refine ⟨?_, rfl, hrun, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · simp only [State.setMem, hx0, hx8, hv]
    exact keepsFrozen_writeBytes_of_memRegion _ hlen hmem_out
  · have hw := satisfies_writeBytes _ hlen hmem_out
    simp only [CliExt.pureByteFunctionSpec, CliExt.withStack, retHook, State.trace_setPC, State.setMem, hx0,
      hx8, hv, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨trivial, ?_⟩
    cases byVal
    · simp only [CliExt.inputAfter, Bool.false_eq_true, ↓reduceIte]
      ac_nf at hw ⊢
    · simp only [CliExt.inputAfter, ↓reduceIte]
      have hw' := Satisfies.mono (sepConj_mono_right (sepConj_mono_left
        (List.Vector.toList_length v ▸ pointsToBytes_entails_memRegion inA v.toList))) hw
      ac_nf at hw' ⊢

theorem dsmbHook_ok (Q : E2E.PqxdhPrims) : HookOk (E2E.dsmbHook Q.dsmb) (CliExt.dsmbSpec Q) := by
  change HookOk
    (retHook (fun s => s.setMem (s.mem.writeBytes (s.readReg64 .x8)
      (Q.dsmb (E2E.readVecN s.mem (s.readReg64 .x0) 32) (E2E.readVecN s.mem (s.readReg64 .x1) 160)
        (E2E.readVecN s.mem (s.readReg64 .x2) 32)).toList)))
    (CliExt.dsmbSpec Q)
  refine retHook_ok fun ⟨aA, a, pA, p, bA, b, ret⟩ R s0 hrun hpre _ => ?_
  simp only [CliExt.dsmbSpec, CliExt.withStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx8⟩, hmem⟩
  have ha : E2E.readVecN s0.mem aA 32 = a := E2E.Pqxdh.readVecN_eq_of_pointsToBytes hmem
  have hmemp : s0.mem ⊨ (pA ↦ₛ p.toList) ∗ ((aA ↦ₛ a.toList) ∗ (bA ↦ₛ b.toList) ∗
      memRegion ret 160 ∗ stackAt s0.sp extHookStack ∗ R) := by
    ac_nf at hmem ⊢
  have hp : E2E.readVecN s0.mem pA 160 = p := E2E.Pqxdh.readVecN_eq_of_pointsToBytes hmemp
  have hmemb : s0.mem ⊨ (bA ↦ₛ b.toList) ∗ ((aA ↦ₛ a.toList) ∗ (pA ↦ₛ p.toList) ∗
      memRegion ret 160 ∗ stackAt s0.sp extHookStack ∗ R) := by
    ac_nf at hmem ⊢
  have hb : E2E.readVecN s0.mem bA 32 = b := E2E.Pqxdh.readVecN_eq_of_pointsToBytes hmemb
  have hlen : (Q.dsmb a p b).toList.length ≤ 2 ^ 64 := by
    rw [List.Vector.toList_length]; decide
  have hmem_out : s0.mem ⊨ memRegion ret (Q.dsmb a p b).toList.length ∗
      ((aA ↦ₛ a.toList) ∗ (pA ↦ₛ p.toList) ∗ (bA ↦ₛ b.toList) ∗ stackAt s0.sp extHookStack ∗ R) := by
    rw [List.Vector.toList_length]
    ac_nf at hmem ⊢
  refine ⟨?_, rfl, hrun, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · simp only [State.setMem, hx0, hx1, hx2, hx8, ha, hp, hb]
    exact keepsFrozen_writeBytes_of_memRegion _ hlen hmem_out
  · have hw := satisfies_writeBytes _ hlen hmem_out
    simp only [CliExt.dsmbSpec, CliExt.withStack, retHook, State.trace_setPC, State.setMem, hx0,
      hx1, hx2, hx8, ha, hp, hb, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨trivial, ?_⟩
    ac_nf at hw ⊢

theorem kemDecapsHook_ok (Q : E2E.PqxdhPrims) :
    HookOk (E2E.kemDecapsHook Q.decaps) (CliExt.kemDecapsSpec Q) := by
  change HookOk
    (retHook (fun s => s.setMem (s.mem.writeBytes (s.readReg64 .x8)
      (Q.decaps (E2E.readVecN s.mem (s.readReg64 .x0) 3168)
        (E2E.readVecN s.mem (s.readReg64 .x1) 1568)).toList)))
    (CliExt.kemDecapsSpec Q)
  refine retHook_ok fun ⟨skA, sk, ctA, ct, ret⟩ R s0 hrun hpre _ => ?_
  simp only [CliExt.kemDecapsSpec, CliExt.withStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8⟩, hmem⟩
  have hsk : E2E.readVecN s0.mem skA 3168 = sk := E2E.Pqxdh.readVecN_eq_of_pointsToBytes hmem
  have hmemct : s0.mem ⊨ (ctA ↦ₛ ct.toList) ∗ ((skA ↦ₛ sk.toList) ∗
      memRegion ret 32 ∗ stackAt s0.sp extHookStack ∗ R) := by
    ac_nf at hmem ⊢
  have hct : E2E.readVecN s0.mem ctA 1568 = ct := E2E.Pqxdh.readVecN_eq_of_pointsToBytes hmemct
  have hlen : (Q.decaps sk ct).toList.length ≤ 2 ^ 64 := by
    rw [List.Vector.toList_length]; decide
  have hmem_out : s0.mem ⊨ memRegion ret (Q.decaps sk ct).toList.length ∗
      ((skA ↦ₛ sk.toList) ∗ (ctA ↦ₛ ct.toList) ∗ stackAt s0.sp extHookStack ∗ R) := by
    rw [List.Vector.toList_length]
    ac_nf at hmem ⊢
  refine ⟨?_, rfl, hrun, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · simp only [State.setMem, hx0, hx1, hx8, hsk, hct]
    exact keepsFrozen_writeBytes_of_memRegion _ hlen hmem_out
  · have hw := satisfies_writeBytes _ hlen hmem_out
    simp only [CliExt.kemDecapsSpec, CliExt.withStack, retHook, State.trace_setPC, State.setMem,
      hx0, hx1, hx8, hsk, hct, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨trivial, ?_⟩
    ac_nf at hw ⊢

theorem kemEncapsHook_ok (Q : E2E.PqxdhPrims) :
    HookOk (E2E.kemEncapsHook Q.encaps) (CliExt.kemEncapsSpec Q) := by
  unfold E2E.kemEncapsHook
  refine retHook_ok fun ⟨pkA, pk, rA, rnd, ret⟩ R s0 hrun hpre _ => ?_
  simp only [CliExt.kemEncapsSpec, CliExt.withStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8⟩, hmem⟩
  have hpk : E2E.readVecN s0.mem pkA 1568 = pk := E2E.Pqxdh.readVecN_eq_of_pointsToBytes hmem
  have hmemr : s0.mem ⊨ (rA ↦ₛ rnd.toList) ∗ ((pkA ↦ₛ pk.toList) ∗
      memRegion ret 1600 ∗ stackAt s0.sp extHookStack ∗ R) := by
    ac_nf at hmem ⊢
  have hr : E2E.readVecN s0.mem rA 32 = rnd := E2E.Pqxdh.readVecN_eq_of_pointsToBytes hmemr
  have hsplit : memRegion ret 1600 = memRegion ret 1568 ∗ memRegion (ret + 0x620#64) 32 :=
    ProofLib.memRegion_split' (b := ret) (n := 1568) (k := 32) (b' := ret + 0x620#64) rfl
      (by bv_omega) (by decide)
  rw [hsplit] at hmem
  let o := Q.encaps pk rnd
  have hmem1 : s0.mem ⊨ memRegion ret o.1.toList.length ∗ (memRegion (ret + 0x620#64) 32 ∗
      (pkA ↦ₛ pk.toList) ∗ (rA ↦ₛ rnd.toList) ∗ stackAt s0.sp extHookStack ∗ R) := by
    rw [List.Vector.toList_length]
    ac_nf at hmem ⊢
  have hlen1 : o.1.toList.length ≤ 2 ^ 64 := by rw [List.Vector.toList_length]; decide
  have hkf1 := keepsFrozen_writeBytes_of_memRegion o.1.toList hlen1 hmem1
  have hw1 := satisfies_writeBytes o.1.toList hlen1 hmem1
  have hmem2 : (s0.mem.writeBytes ret o.1.toList) ⊨ memRegion (ret + 0x620#64) o.2.toList.length ∗
      ((ret ↦ₛ o.1.toList) ∗ (pkA ↦ₛ pk.toList) ∗ (rA ↦ₛ rnd.toList) ∗
        stackAt s0.sp extHookStack ∗ R) := by
    rw [List.Vector.toList_length]
    ac_nf at hw1 ⊢
  have hlen2 : o.2.toList.length ≤ 2 ^ 64 := by rw [List.Vector.toList_length]; decide
  have hkf2 := hkf1.trans (keepsFrozen_writeBytes_of_memRegion o.2.toList hlen2 hmem2)
  have hw2 := satisfies_writeBytes o.2.toList hlen2 hmem2
  have hw3 := Satisfies.mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left
      (List.Vector.toList_length rnd ▸ pointsToBytes_entails_memRegion rA rnd.toList))))) hw2
  refine ⟨?_, rfl, hrun, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · simp only [State.setMem, hx0, hx1, hx8, hpk, hr]
    exact hkf2
  · simp only [CliExt.kemEncapsSpec, CliExt.withStack, retHook, State.trace_setPC, State.setMem, hx0, hx1, hx8, hpk, hr, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨trivial, ?_⟩
    ac_nf at hw3 ⊢

theorem toEdwardsHook_ok (Q : E2E.PqxdhPrims) :
    HookOk (E2E.toEdwardsHook Q.montToEd) (CliExt.toEdwardsSpec Q) := by
  change HookOk
    (retHook (fun s =>
      let r := s.readReg64 .x8
      let m :=
        match Q.montToEd (E2E.readVecN s.mem (s.readReg64 .x0) 32) ((s.readReg64 .x1).setWidth 8 &&& 1#8)
        with
        | some p => (s.mem.write64 r 1#64).writeBytes (r + 8#64) p.toList
        | none => s.mem.write64 r 0#64
      s.setMem m))
    (CliExt.toEdwardsSpec Q)
  refine retHook_ok fun ⟨uA, u, sign, ret⟩ R s0 hrun hpre _ => ?_
  simp only [CliExt.toEdwardsSpec, CliExt.withStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8⟩, hmem⟩
  have hu : E2E.readVecN s0.mem uA 32 = u := E2E.Pqxdh.readVecN_eq_of_pointsToBytes hmem
  rw [memRegion_split ret 8 160 (by decide), ProofLib.memRegion_eight ret] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    satisfies_sepExists] at hmem
  rcases hmem with ⟨w0, hmem⟩
  have hmem0 : s0.mem ⊨ (ret ↦₆₄ w0) ∗
      (memRegion (ret + 8#64) 160 ∗ (uA ↦ₛ u.toList) ∗ stackAt s0.sp extHookStack ∗ R) := by
    ac_nf at hmem ⊢
  rcases hres : Q.montToEd u (sign &&& 1#8) with _ | p
  · have hkf1 := E2E.HooksE.HooksOkAux.keepsFrozen_write64_of_pointsTo64 0#64 hmem0
    have hw1 := E2E.HooksE.HooksOkAux.satisfies_write64_of_pointsTo64 0#64 hmem0
    refine ⟨?_, rfl, hrun, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    · dsimp only
      rw [hx0, hx1, hx8, hu, hres]
      exact hkf1
    · dsimp only [CliExt.toEdwardsSpec, CliExt.withStack, retHook, State.setMem]
      rw [hx0, hx1, hx8, hu, hres]
      simp only [CliExt.optionEdwardsPointAt, State.trace_setPC, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨trivial, ?_⟩
      ac_nf at hw1 ⊢
  · have hkf1 := E2E.HooksE.HooksOkAux.keepsFrozen_write64_of_pointsTo64 1#64 hmem0
    have hw1 := E2E.HooksE.HooksOkAux.satisfies_write64_of_pointsTo64 1#64 hmem0
    have hmem1 : (s0.mem.write64 ret 1#64) ⊨ memRegion (ret + 8#64) p.toList.length ∗
        ((ret ↦₆₄ 1#64) ∗ (uA ↦ₛ u.toList) ∗ stackAt s0.sp extHookStack ∗ R) := by
      rw [List.Vector.toList_length]
      ac_nf at hw1 ⊢
    have hlen : p.toList.length ≤ 2 ^ 64 := by rw [List.Vector.toList_length]; decide
    have hkf2 := hkf1.trans (keepsFrozen_writeBytes_of_memRegion p.toList hlen hmem1)
    have hw2 := satisfies_writeBytes p.toList hlen hmem1
    refine ⟨?_, rfl, hrun, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    · dsimp only
      rw [hx0, hx1, hx8, hu, hres]
      exact hkf2
    · dsimp only [CliExt.toEdwardsSpec, CliExt.withStack, retHook, State.setMem]
      rw [hx0, hx1, hx8, hu, hres]
      simp only [CliExt.optionEdwardsPointAt, State.trace_setPC, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨trivial, ?_⟩
      ac_nf at hw2 ⊢

theorem torsionFreeHook_ok (Q : E2E.PqxdhPrims) :
    HookOk (E2E.torsionFreeHook Q.isTorsionFree) (CliExt.torsionFreeSpec Q) := by
  change HookOk
    (retHook (fun s => s.writeReg64 .x0
      (if Q.isTorsionFree (E2E.readVecN s.mem (s.readReg64 .x0) 160) then 1#64 else 0#64)))
    (CliExt.torsionFreeSpec Q)
  refine retHook_ok fun ⟨pA, p⟩ R s0 hrun hpre _ => ?_
  simp only [CliExt.torsionFreeSpec, CliExt.withStack, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hmem⟩
  have hp : E2E.readVecN s0.mem pA 160 = p := E2E.Pqxdh.readVecN_eq_of_pointsToBytes hmem
  refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, hrun,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  simp only [CliExt.torsionFreeSpec, CliExt.withStack, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨rfl, ?_⟩, hmem⟩
  show BitVec.setWidth 32
      (if Q.isTorsionFree (E2E.readVecN s0.mem (s0.readReg64 .x0) 160) then 1#64 else 0#64) = _
  rw [hx0, hp]
  cases Q.isTorsionFree p <;> rfl

/-! ### `compress512`: the state words from their LE bytes -/

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

private theorem sha512State_toList_eq (h : E2E.Sha512State) :
    h.toList = [h.get 0, h.get 1, h.get 2, h.get 3, h.get 4, h.get 5, h.get 6, h.get 7] := by
  rcases h with
    ⟨_ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩, hl⟩
  all_goals (first | rfl | (simp at hl))

private theorem sha512StateBytesLE_length (h : E2E.Sha512State) :
    (E2E.sha512StateBytesLE h).length = 64 := by
  rw [E2E.sha512StateBytesLE, sha512State_toList_eq]
  rfl

private theorem read64_of_readBytes_toLEBytes_8 (m : Memory) (a : BitVec 64) (w : BitVec 64)
    (h : m.readBytes a 8 = LibsignalAesCbc.toLEBytes 8 w) : m.read64 a = w := by
  have h8 : m.readBytes a 8 =
      [m.read8 a, m.read8 (a + 1#64), m.read8 (a + 2#64), m.read8 (a + 3#64),
       m.read8 (a + 4#64), m.read8 (a + 5#64), m.read8 (a + 6#64), m.read8 (a + 7#64)] := by
    simp only [Memory.readBytes, BitVec.add_assoc]; rfl
  have hle : LibsignalAesCbc.toLEBytes 8 w =
      [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8,
       w.extractLsb' 32 8, w.extractLsb' 40 8, w.extractLsb' 48 8, w.extractLsb' 56 8] := rfl
  rw [h8, hle] at h
  simp only [List.cons.injEq, and_true] at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  dsimp only [Memory.read64]
  rw [BitVec.add_zero, h0, h1, h2, h3, h4, h5, h6, h7]
  bv_bits

private theorem readSha512State_of_pointsToBytes {m : Memory} {a : BitVec 64}
    {st : E2E.Sha512State} {R : SepProp} (h : m ⊨ (a ↦ₛ E2E.sha512StateBytesLE st) ∗ R) :
    E2E.readSha512State m a = st := by
  apply List.Vector.ext
  intro i
  simp only [E2E.readSha512State, List.Vector.get_ofFn]
  apply read64_of_readBytes_toLEBytes_8
  rw [readBytes_pointsToBytes_slice (8 * i.val) 8 (by rw [sha512StateBytesLE_length]; omega) h]
  fin_cases i <;> (rw [E2E.sha512StateBytesLE, sha512State_toList_eq]; rfl)

theorem compress512Hook_ok (Q : E2E.PqxdhPrims) :
    HookOk (E2E.compress512Hook Q.F512) (CliExt.compress512Spec Q) := by
  change HookOk
    (retHook (fun s =>
      let st := E2E.readSha512State s.mem (s.readReg64 .x0)
      let bs := s.mem.readBytes (s.readReg64 .x1) (128 * (s.readReg64 .x2).toNat)
      s.setMem (s.mem.writeBytes (s.readReg64 .x0)
        (E2E.sha512StateBytesLE ((E2E.chunks128 bs).foldl Q.F512 st)))))
    (CliExt.compress512Spec Q)
  refine retHook_ok fun ⟨stA, st, blkA, bs, n⟩ R s0 hrun hpre _ => ?_
  simp only [CliExt.compress512Spec, CliExt.withStack, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hbs_len⟩, hmem⟩
  have hst : E2E.readSha512State s0.mem stA = st := readSha512State_of_pointsToBytes hmem
  have hmem_blk : s0.mem ⊨ (blkA ↦ₛ bs) ∗ ((stA ↦ₛ E2E.sha512StateBytesLE st) ∗
      stackAt s0.sp extHookStack ∗ R) := by
    ac_nf at hmem ⊢
  have hbs : s0.mem.readBytes blkA (128 * n) = bs := by
    rw [← hbs_len]
    exact ((IsBlock.pointsToBytes blkA bs).read hmem_blk).2
  let out := E2E.sha512StateBytesLE ((E2E.chunks128 bs).foldl Q.F512 st)
  have hout_len : out.length = (E2E.sha512StateBytesLE st).length := by
    simp only [out, sha512StateBytesLE_length]
  have hmem_reg : s0.mem ⊨ memRegion stA out.length ∗
      ((blkA ↦ₛ bs) ∗ stackAt s0.sp extHookStack ∗ R) := by
    rw [hout_len]
    exact Satisfies.mono (sepConj_mono_left (pointsToBytes_entails_memRegion stA _)) hmem
  have hlen : out.length ≤ 2 ^ 64 := by simp only [out, sha512StateBytesLE_length]; decide
  refine ⟨?_, rfl, hrun, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · simp only [State.setMem, hx0, hx1, hx2, hst, hbs]
    exact keepsFrozen_writeBytes_of_memRegion out hlen hmem_reg
  · simp only [CliExt.compress512Spec, CliExt.withStack, retHook, State.trace_setPC, State.setMem,
      hx0, hx1, hx2, hst, hbs, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨trivial, satisfies_writeBytes out hlen hmem_reg⟩

/-! ## The other rows that need a proof -/

/-- `black_box`: derives the 32-bit postcondition from the 64-bit hook postcondition. -/
theorem blackBoxHook_ok : HookOk LibsignalSession.blackBoxHook CliExt.blackBoxSpec := by
  have h : HookOk LibsignalSession.blackBoxHook
      ({ pre := fun v s => ⌜s.readReg64 .x0 = v⌝
         post := fun v s0 sf =>
           ⌜(sf.readReg64 .x0).setWidth 32 = (v.setWidth 8).zeroExtend 32 ∧
             sf.trace = s0.trace⌝ } : Spec (BitVec 64)) := by
    refine HookOk.mono LibsignalTripleRatchet.blackBoxHook_ok (fun _ _ _ hp => hp)
      (fun v R s0 sf _ hq => ?_) (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq)
    simp only [LibsignalTripleRatchet.blackBoxSpec, satisfies_pure_sepConj] at hq ⊢
    obtain ⟨⟨hx, ht⟩, hR⟩ := hq
    refine ⟨⟨?_, ht⟩, hR⟩
    rw [hx]
    bv_omega
  exact hookOk_cliWithStack h extHookStack (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl)

/-! ## The frame fields -/

/-- The frame of one hook step: `tpidr_el0` kept, no new execute permission, and (when `b`) the
file system kept. -/
def StepFr (b : Bool) (s s' : State) : Prop :=
  s'.tpidrEl0 = s.tpidrEl0 ∧ (∀ a, (s'.mem.perm a).x → (s.mem.perm a).x) ∧
    (b = true → s'.fs = s.fs)

theorem StepFr.trans {b : Bool} {s1 s2 s3 : State} (h12 : StepFr b s1 s2) (h23 : StepFr b s2 s3) :
    StepFr b s1 s3 :=
  ⟨h23.1.trans h12.1, fun a h => h12.2.1 a (h23.2.1 a h),
    fun hb => (h23.2.2 hb).trans (h12.2.2 hb)⟩

theorem StepFr.of_eq {b : Bool} {s s' : State} (ht : s'.tpidrEl0 = s.tpidrEl0)
    (hp : s'.mem.perm = s.mem.perm) (hf : s'.fs = s.fs) : StepFr b s s' :=
  ⟨ht, fun a h => by rwa [hp] at h, fun _ => hf⟩

theorem StepFr.of_eqF {s s' : State} (ht : s'.tpidrEl0 = s.tpidrEl0)
    (hp : s'.mem.perm = s.mem.perm) : StepFr false s s' :=
  ⟨ht, fun a h => by rwa [hp] at h, fun h => absurd h Bool.false_ne_true⟩

theorem StepFr.mapFresh {b : Bool} (s : State) (p : BitVec 64) (n : Nat) :
    StepFr b s (s.setMem (s.mem.mapFresh p n Perm.rw)) := by
  refine ⟨rfl, fun a h => ?_, fun _ => rfl⟩
  change ((s.mem.mapFresh p n Perm.rw).perm a).x = true at h
  rw [Memory.perm_mapFresh] at h
  split at h
  · simp [Perm.rw] at h
  · exact h

theorem StepFr.bumpThen {b : Bool} {size align : Nat} {ok : State → BitVec 64 → State}
    {fail : State → State} {s : State}
    (hok : ∀ p, StepFr b (s.setMem (s.mem.mapFresh p size Perm.rw))
      (ok (s.setMem (s.mem.mapFresh p size Perm.rw)) p))
    (hfail : StepFr b s (fail s)) : StepFr b s (E2E.bumpThen size align ok fail s) := by
  unfold E2E.bumpThen
  split
  · exact (StepFr.mapFresh s _ size).trans (hok _)
  · exact hfail

/-- A hook's steps keep the frame (`b`: also the file system). -/
def HookFr (b : Bool) (f : State → State) : Prop := ∀ s, StepFr b s (f s)

theorem HookFr.weak {f : State → State} (h : HookFr true f) : HookFr false f :=
  fun s => ⟨(h s).1, (h s).2.1, fun hb => absurd hb Bool.false_ne_true⟩

macro "fr_perm" : tactic => `(tactic|
  simp only [retHook, CryptoVerification.LibsignalAesCbc.returnToLinkRegister, Arm64.State.setMem,
    Arm64.State.setPC, Arm64.State.writeReg64, Arm64.State.appendTrace, Arm64.State.setFs,
    Arm64.State.setStatus, CryptoVerification.E2E.writeVecHeader, Arm64.Memory.perm_writeBytes,
    Arm64.Memory.perm_write64, Arm64.Memory.perm_write32, Arm64.Memory.perm_write16,
    Arm64.Memory.perm_write8])

macro "fr_leaf" : tactic => `(tactic| first
  | exact CryptoVerification.SignalSession.ExternsWitness.StepFr.of_eq rfl rfl rfl
  | exact CryptoVerification.SignalSession.ExternsWitness.StepFr.of_eqF rfl rfl
  | (refine CryptoVerification.SignalSession.ExternsWitness.StepFr.of_eq rfl ?_ rfl
     fr_perm
     done)
  | (refine CryptoVerification.SignalSession.ExternsWitness.StepFr.of_eqF rfl ?_
     fr_perm
     done)
  | (refine CryptoVerification.SignalSession.ExternsWitness.StepFr.of_eq rfl ?_ rfl
     fr_perm
     split <;> simp only [Arm64.Memory.perm_writeBytes]))

macro "fr_close" : tactic => `(tactic| (
  try dsimp only
  repeat' split
  all_goals first
    | fr_leaf
    | (refine CryptoVerification.SignalSession.ExternsWitness.StepFr.bumpThen (fun _ => ?_) ?_ <;>
        (try dsimp only) <;> fr_leaf)
    | (refine CryptoVerification.SignalSession.ExternsWitness.StepFr.trans ?_
          (CryptoVerification.SignalSession.ExternsWitness.StepFr.bumpThen (fun _ => ?_) ?_) <;>
        (try dsimp only) <;> fr_leaf)))

section HookFr

variable (W : CliHooks)

theorem compress512Hook_fr : HookFr true (E2E.compress512Hook W.Q.F512) := by
  intro s; unfold E2E.compress512Hook; fr_close
theorem toEdwardsHook_fr : HookFr true (E2E.toEdwardsHook W.Q.montToEd) := by
  intro s; unfold E2E.toEdwardsHook; fr_close
theorem compressHook_fr : HookFr true (E2E.compressHook W.Q.compress) := by
  intro s; unfold E2E.compressHook; fr_close
theorem edNegHook_fr : HookFr true (E2E.edNegHook W.Q.edNeg) := by
  intro s; unfold E2E.edNegHook; fr_close
theorem torsionFreeHook_fr : HookFr true (E2E.torsionFreeHook W.Q.isTorsionFree) := by
  intro s; unfold E2E.torsionFreeHook; fr_close
theorem dsmbHook_fr : HookFr true (E2E.dsmbHook W.Q.dsmb) := by
  intro s; unfold E2E.dsmbHook; fr_close
theorem scalarModHook_fr : HookFr true (E2E.scalarModHook W.Q.scalarMod) := by
  intro s; unfold E2E.scalarModHook; fr_close
theorem scalarWideHook_fr : HookFr true (E2E.scalarWideHook W.Q.scalarWide) := by
  intro s; unfold E2E.scalarWideHook; fr_close
theorem kemEncapsHook_fr : HookFr true (E2E.kemEncapsHook W.Q.encaps) := by
  intro s; unfold E2E.kemEncapsHook; fr_close
theorem kemDecapsHook_fr : HookFr true (E2E.kemDecapsHook W.Q.decaps) := by
  intro s; unfold E2E.kemDecapsHook; fr_close
theorem mlkemFromSeedHook_fr : HookFr true (E2E.mlkemFromSeedHook W.Q.K) := by
  intro s; unfold E2E.mlkemFromSeedHook; fr_close
theorem mlkemPk1Hook_fr : HookFr true E2E.mlkemPk1Hook := by
  intro s; unfold E2E.mlkemPk1Hook; fr_close
theorem mlkemPk2Hook_fr : HookFr true E2E.mlkemPk2Hook := by
  intro s; unfold E2E.mlkemPk2Hook; fr_close
theorem mlkemEncaps1Hook_fr : HookFr true (E2E.mlkemEncaps1Hook W.Q.K) := by
  intro s; unfold E2E.mlkemEncaps1Hook retHook; fr_close
theorem mlkemEncaps2Hook_fr : HookFr true (E2E.mlkemEncaps2Hook W.Q.K) := by
  intro s; unfold E2E.mlkemEncaps2Hook; fr_close
theorem mlkemDecapsHook_fr : HookFr true (E2E.mlkemDecapsHook W.Q.K) := by
  intro s; unfold E2E.mlkemDecapsHook; fr_close
theorem mlkemValidatePkHook_fr : HookFr true (E2E.mlkemValidatePkHook W.Q.K) := by
  intro s; unfold E2E.mlkemValidatePkHook; fr_close
theorem libcruxHmacHook_fr : HookFr true (E2E.libcruxHmacHook W.C.F) := by
  intro s; unfold E2E.libcruxHmacHook; fr_close
theorem hookNoop_fr : HookFr true hookNoop := by
  intro s; unfold hookNoop; fr_close
theorem allocHook0_fr : HookFr true E2E.allocHook0 := by
  intro s; unfold E2E.allocHook0; fr_close
theorem deallocHook_fr : HookFr true E2E.deallocHook := by
  intro s; unfold E2E.deallocHook; fr_close
theorem reallocHook0_fr : HookFr true E2E.reallocHook0 := by
  intro s; unfold E2E.reallocHook0; fr_close
theorem allocZeroedHook0_fr : HookFr true E2E.allocZeroedHook0 := by
  intro s; unfold E2E.allocZeroedHook0; fr_close
theorem hookMemset_fr : HookFr true hookMemset := by
  intro s; unfold hookMemset; fr_close
theorem hookMemcpy_fr : HookFr true hookMemcpy := by
  intro s; unfold hookMemcpy; fr_close
theorem hookMemmove_fr : HookFr true hookMemmove := hookMemcpy_fr
theorem cliBcmpHook_fr : HookFr true (cliBcmpHook W.bcmp) := by
  intro s; unfold cliBcmpHook; fr_close
theorem strlenHook_fr : HookFr true strlenHook := by
  intro s; unfold strlenHook unmodelled; fr_close
theorem readFileHook_fr : HookFr true readFileHook := by
  intro s; unfold readFileHook vecOk vecErr vecEmptyOk unmodelled; fr_close
theorem writeFileHook_fr : HookFr false writeFileHook := by
  intro s; unfold writeFileHook unitResult unmodelled; fr_close
theorem readStdinHook_fr : HookFr false readStdinHook := by
  intro s; unfold readStdinHook vecOk vecErr vecEmptyOk unmodelled; fr_close
theorem writeStdoutHook_fr : HookFr false writeStdoutHook := by
  intro s; unfold writeStdoutHook unitResult unmodelled; fr_close
theorem memrchrHook_fr : HookFr true memrchrHook := by
  intro s; unfold memrchrHook unmodelled; fr_close
theorem fromUtf8Hook_fr : HookFr true (fromUtf8Hook W.utf8Err) := by
  intro s; unfold fromUtf8Hook unmodelled; fr_close
theorem stringCloneHook0_fr : HookFr true E2E.stringCloneHook0 := by
  intro s; unfold E2E.stringCloneHook0 E2E.returnFreshVecU8; fr_close
theorem fmtWriteHook0_fr : HookFr true E2E.fmtWriteHook0 := by
  intro s; unfold E2E.fmtWriteHook0; fr_close
theorem formatInnerHook0_fr : HookFr true E2E.formatInnerHook0 := by
  intro s; unfold E2E.formatInnerHook0; fr_close
theorem durationSinceExactHook_fr : HookFr true durationSinceExactHook := by
  intro s; unfold durationSinceExactHook unmodelled; fr_close
theorem timeAddHook_fr : HookFr true E2E.timeAddHook := by
  intro s; unfold E2E.timeAddHook; fr_close
theorem blackBoxHook_fr : HookFr true LibsignalSession.blackBoxHook := by
  intro s; unfold LibsignalSession.blackBoxHook; fr_close
theorem compress256Hook_fr : HookFr true (LibsignalHmac.compress256Hook W.C.F) := by
  intro s; unfold LibsignalHmac.compress256Hook; fr_close
theorem aesEncHook0_fr : HookFr true (E2E.aesEncHook0 W.C.E) := by
  intro s; unfold E2E.aesEncHook0 E2E.returnFreshVecU8; fr_close
theorem aesDecHook0_fr : HookFr true (E2E.aesDecHook0 W.C.D) := by
  intro s; unfold E2E.aesDecHook0 E2E.returnFreshVecU8; fr_close
theorem pubFromSecretHook_fr :
    HookFr true (LibsignalTripleRatchet.pubFromSecretHook W.C.pubKey) := by
  intro s; unfold LibsignalTripleRatchet.pubFromSecretHook; fr_close
theorem diffieHellmanHook_fr : HookFr true (LibsignalTripleRatchet.diffieHellmanHook W.C.X) := by
  intro s; unfold LibsignalTripleRatchet.diffieHellmanHook; fr_close
theorem zeroizeSecretHook_fr : HookFr true LibsignalTripleRatchet.zeroizeSecretHook := by
  intro s; unfold LibsignalTripleRatchet.zeroizeSecretHook; fr_close

end HookFr

/-! ## `read_file` -/

/-- `read_file` preserves `fs.files`. -/
theorem readFileHook_files (s : State) : (readFileHook s).fs.files = s.fs.files :=
  congrArg FsState.files ((readFileHook_fr s).2.2 rfl)

/-- `read_file` contract across both path representations. -/
theorem readFileHook_ok (img : Obj.Image) :
    HookOk readFileHook (CliExt.readFileSpec E2E.HooksE.A0 img) := by
  intro x R s0 hrun hpre hsp
  rcases x with ⟨pathA, ro, path, ret⟩
  cases ro
  · have hpre' : s0.mem ⊨ (Cli.readFileSpec Cli.MainHops.cliIo.rd Cli.MainHops.cliWrOk
        E2E.HooksE.A0 img extHookStack).pre ⟨pathA, path, ret⟩ s0 ∗ R := by
      simp only [CliExt.readFileSpec, Cli.readFileSpec, Spec.inImage, CliExt.bytesAt,
        Bool.false_eq_true, ↓reduceIte, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      obtain ⟨hi, ⟨hx0, hx1, hx8, hlen, hok⟩, hmem⟩ := hpre
      exact ⟨hi, ⟨hx0, hx1, hx8, hlen, ⟨hok, hlen⟩⟩, hmem⟩
    obtain ⟨hkf, hsym, hout⟩ :=
      Cli.RunSkeleton.cliReadFileHook_ok img extHookStack ⟨pathA, path, ret⟩ R s0 hrun hpre' hsp
    refine ⟨hkf, hsym, ?_⟩
    rcases hout with ⟨hr, hc, hq⟩ | hq | hq | hq
    · refine Or.inl ⟨hr, hc, ?_⟩
      simp only [CliExt.readFileSpec, Cli.readFileSpec, Spec.inImage, CliExt.bytesAt,
        Bool.false_eq_true, ↓reduceIte, sepConj_assoc, sepExists_sepConj_left,
        satisfies_sepExists, satisfies_pure_sepConj] at hq ⊢
      obtain ⟨r, ⟨hr1, hr2⟩, hm⟩ := hq
      exact ⟨r, ⟨readFileHook_files s0, hr1, hr2⟩, hm⟩
    · exact Or.inr (Or.inl hq)
    · exact Or.inr (Or.inr (Or.inl hq))
    · exact Or.inr (Or.inr (Or.inr hq))
  · exact Cli.MainHops.readFileHook_ok img extHookStack ⟨pathA, path, ret⟩ R s0 hrun hpre hsp

theorem readFileName_io : readFileName ∈ CliExt.ioNames := by simp [CliExt.ioNames]
theorem writeFileName_io : writeFileName ∈ CliExt.ioNames := by simp [CliExt.ioNames]
theorem readStdinName_io : readStdinName ∈ CliExt.ioNames := by simp [CliExt.ioNames]
theorem writeStdoutName_io : writeStdoutName ∈ CliExt.ioNames := by simp [CliExt.ioNames]

set_option linter.unusedSimpArgs false in
/-- Every row of `cliHookTable W` preserves `StepFr`, and preserves the file system except on
the four I/O hooks. -/
theorem cliHookTable_fr (W : CliHooks) :
    ∀ p ∈ cliHookTable W, HookFr false p.2 ∧ (p.1 ∈ CliExt.ioNames ∨ HookFr true p.2) := by
  simp only [cliHookTable, E2E.pqxdhHookTable, E2E.spqrHookTable, List.cons_append,
    List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true, or_true, true_or, and_self,
    readFileName_io, writeFileName_io, readStdinName_io, writeStdoutName_io,
    compress512Hook_fr, toEdwardsHook_fr, compressHook_fr, edNegHook_fr, torsionFreeHook_fr,
    dsmbHook_fr, scalarModHook_fr, scalarWideHook_fr, kemEncapsHook_fr, kemDecapsHook_fr,
    mlkemFromSeedHook_fr, mlkemPk1Hook_fr, mlkemPk2Hook_fr, mlkemEncaps1Hook_fr,
    mlkemEncaps2Hook_fr, mlkemDecapsHook_fr, mlkemValidatePkHook_fr, libcruxHmacHook_fr,
    hookNoop_fr, allocHook0_fr, deallocHook_fr,
    reallocHook0_fr, allocZeroedHook0_fr, hookMemset_fr, hookMemmove_fr, hookMemcpy_fr,
    cliBcmpHook_fr, strlenHook_fr, readFileHook_fr, writeFileHook_fr, readStdinHook_fr,
    writeStdoutHook_fr, memrchrHook_fr, fromUtf8Hook_fr, stringCloneHook0_fr, fmtWriteHook0_fr,
    formatInnerHook0_fr, durationSinceExactHook_fr, timeAddHook_fr, blackBoxHook_fr,
    compress256Hook_fr, aesEncHook0_fr, aesDecHook0_fr, pubFromSecretHook_fr,
    diffieHellmanHook_fr, zeroizeSecretHook_fr,
    HookFr.weak (compress512Hook_fr W), HookFr.weak (toEdwardsHook_fr W),
    HookFr.weak (compressHook_fr W), HookFr.weak (edNegHook_fr W),
    HookFr.weak (torsionFreeHook_fr W), HookFr.weak (dsmbHook_fr W),
    HookFr.weak (scalarModHook_fr W), HookFr.weak (scalarWideHook_fr W),
    HookFr.weak (kemEncapsHook_fr W), HookFr.weak (kemDecapsHook_fr W),
    HookFr.weak (mlkemFromSeedHook_fr W), HookFr.weak mlkemPk1Hook_fr,
    HookFr.weak mlkemPk2Hook_fr, HookFr.weak (mlkemEncaps1Hook_fr W),
    HookFr.weak (mlkemEncaps2Hook_fr W), HookFr.weak (mlkemDecapsHook_fr W),
    HookFr.weak (mlkemValidatePkHook_fr W), HookFr.weak (libcruxHmacHook_fr W),
    HookFr.weak hookNoop_fr,
    HookFr.weak allocHook0_fr, HookFr.weak deallocHook_fr, HookFr.weak reallocHook0_fr,
    HookFr.weak allocZeroedHook0_fr, HookFr.weak hookMemset_fr, HookFr.weak hookMemmove_fr,
    HookFr.weak hookMemcpy_fr, HookFr.weak (cliBcmpHook_fr W), HookFr.weak strlenHook_fr,
    HookFr.weak readFileHook_fr, HookFr.weak memrchrHook_fr, HookFr.weak (fromUtf8Hook_fr W),
    HookFr.weak stringCloneHook0_fr, HookFr.weak fmtWriteHook0_fr,
    HookFr.weak formatInnerHook0_fr, HookFr.weak durationSinceExactHook_fr,
    HookFr.weak timeAddHook_fr, HookFr.weak blackBoxHook_fr, HookFr.weak (compress256Hook_fr W),
    HookFr.weak (aesEncHook0_fr W), HookFr.weak (aesDecHook0_fr W),
    HookFr.weak (pubFromSecretHook_fr W), HookFr.weak (diffieHellmanHook_fr W),
    HookFr.weak zeroizeSecretHook_fr]

theorem mem_of_lookup {L : List (String × (State → State))} {n : String} {f : State → State}
    (h : L.lookup n = some f) : (n, f) ∈ L := by
  induction L with
  | nil => cases h
  | cons p L ih =>
    obtain ⟨m, g⟩ := p
    simp only [List.lookup_cons] at h
    split at h
    · rename_i hnm
      cases h
      rw [beq_iff_eq] at hnm
      subst hnm
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem cliHookExterns_fr (W : CliHooks) {n : String} {f : State → State}
    (h : cliHookExterns W n = some f) : HookFr false f ∧ (n ∉ CliExt.ioNames → HookFr true f) := by
  obtain ⟨hw, hs⟩ := cliHookTable_fr W _ (mem_of_lookup h)
  exact ⟨hw, fun hn => hs.resolve_left hn⟩

end ExternsWitness

open ExternsWitness in
/-- `cliHookExterns W` satisfies `CliExternsOk ⟨W.C, W.Q⟩ E2E.HooksE.A0`. -/
theorem cliExterns_ok (W : CliHooks) :
    CliExternsOk ⟨W.C, W.Q⟩ E2E.HooksE.A0 (cliHookExterns W) where
  tpidr n f h s := ((cliHookExterns_fr W h).1 s).1
  noExec n f h s a := ((cliHookExterns_fr W h).1 s).2.1 a
  fsTraced := Cli.RunGlue.fsTHooks_lookup (Cli.RunGlue.cliHookTable_fsT W)
  fsKept n f h hn s := ((cliHookExterns_fr W h).2 hn s).2.2 rfl
  poolEmp := Entails.refl _
  shim := hookSat_row (Cli.MainHops.shim_row W) LibsignalTripleRatchet.sessionShim_hookOk
  alloc :=
    ⟨hookSat_of_cliExterns (Cli.MainHops.alloc_row W) (Cli.Slots.cliExterns_allocHooks W).alloc,
     hookSat_of_cliExterns (Cli.MainHops.dealloc_row W)
       (Cli.Slots.cliExterns_allocHooks W).dealloc,
     hookSat_of_cliExterns (Cli.MainHops.realloc_row W)
       (Cli.Slots.cliExterns_allocHooks W).realloc⟩
  allocZeroed :=
    hookSat_of_cliExterns (Cli.Slots.allocZeroed_row W) (Cli.Slots.cliExterns_allocZeroed W)
  memset := hookSat_row (Cli.MainHops.memset_row W) LibsignalTripleRatchet.hookMemset_trace_ok
  memmove := hookSat_row (Cli.MainHops.memmove_row W) LibsignalTripleRatchet.hookMemmove_trace_ok
  memcpy := hookSat_row (Cli.MainHops.memcpy_row W) LibsignalTripleRatchet.hookMemcpy_trace_ok
  memcpyRO := hookSat_row (Cli.MainHops.memcpy_row W)
    (hookOk_cliWithStack SpqrV1.Alloc.hookMemcpy_region_ro_trace_ok CliExt.memHookStack
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl))
  bcmp := hookSat_row (Cli.RunGlue.bcmp_row W)
    (hookOk_map (s₁ := Cli.cliBcmpSpec) (fun x => ⟨x.a, x.aRo, x.bsA, x.b, x.bRo, x.bsB⟩)
      (fun _ _ => True) (fun _ => trivial) (Cli.RunGlue.cliBcmpHook_ok W)
      (fun _ _ _ hp => hp) (fun _ _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
      (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq))
  strlen := hookSat_row (strlen_row W) (Cli.MainHops.strlenHook_ok extHookStack)
  readFile img := hookSat_row (Cli.MainHops.readFile_row W) (readFileHook_ok img)
  writeFile img := hookSat_row (Cli.MainHops.writeFile_row W)
    (hookOk_map (s₁ := Cli.MainHops.writeFileSpec Cli.MainHops.cliIo img extHookStack)
      (fun x => ⟨x.pathA, x.path, x.buf, x.bs⟩)
      (fun _ _ => True) (fun _ => trivial) (Cli.MainHops.writeFileHook_ok img extHookStack)
      (fun _ _ _ hp => hp) (fun _ _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
      (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq))
  readStdin img := hookSat_row (Cli.MainHops.readStdin_row W)
    (hookOk_map (s₁ := Cli.MainHops.readStdinSpec Cli.MainHops.cliIo E2E.HooksE.A0 img extHookStack)
      (fun x => ⟨x.ret, x.bs⟩)
      (fun _ _ => True) (fun _ => trivial) (Cli.MainHops.readStdinHook_ok img extHookStack)
      (fun _ _ _ hp => hp) (fun _ _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
      (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq))
  writeStdout img := hookSat_row (Cli.MainHops.writeStdout_row W)
    (hookOk_map (s₁ := Cli.MainHops.writeStdoutSpec img extHookStack)
      (fun x => ⟨x.buf, x.bs⟩)
      (fun _ _ => True) (fun _ => trivial) (Cli.MainHops.writeStdoutHook_ok img extHookStack)
      (fun _ _ _ hp => hp) (fun _ _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
      (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq))
  memrchr := hookSat_row (Cli.MainHops.memrchr_row W)
    (hookOk_map (s₁ := Cli.MainHops.memrchrSpec extHookStack) (fun x => ⟨x.c, x.p, x.bs⟩)
      (fun _ _ => True) (fun _ => trivial) (Cli.MainHops.memrchrHook_ok extHookStack)
      (fun _ _ _ hp => hp) (fun _ _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
      (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq))
  fromUtf8 := hookSat_row (fromUtf8_row W) (Cli.MainHops.fromUtf8Hook_ok extHookStack W.utf8Err)
  fmtWrite := hookSat_of_cliExterns (Cli.Slots.fmtWrite_row W) (Cli.Slots.cliExterns_fmtWrite W)
  formatInner :=
    hookSat_of_cliExterns (Cli.Slots.formatInner_row W) (Cli.Slots.cliExterns_formatInner W)
  durationSince :=
    hookSat_row (Cli.Slots.durationSince_row W) Cli.Slots.durationSinceExactHook_epoch_ok
  timeAdd := hookSat_of_cliExterns (Cli.Slots.timeAdd_row W) (Cli.Slots.cliExterns_timeAdd W)
  blackBox := hookSat_row (blackBox_row W) blackBoxHook_ok
  compress256 := hookSat_row (Cli.Slots.compress256_row W)
    (hookOk_cliWithStack (LibsignalTripleRatchet.compress256Hook_ok W.C.F) extHookStack
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl))
  aesEnc := hookSat_of_cliExterns (Cli.Slots.aesEnc_row W) (Cli.Slots.cliExterns_aesEnc W)
  aesDec := hookSat_of_cliExterns (Cli.Slots.aesDec_row W) (Cli.Slots.cliExterns_aesDec W)
  pubFromSecret := hookSat_row (pubFromSecret_row W)
    (hookOk_cliWithStack (LibsignalTripleRatchet.pubFromSecretHook_ok W.C.pubKey) extHookStack
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl))
  dh := hookSat_row (dh_row W)
    (hookOk_cliWithStack (LibsignalTripleRatchet.diffieHellmanHook_ok W.C.X) extHookStack
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl))
  staticDrop := hookSat_row (staticDrop_row W)
    (hookOk_cliWithStack LibsignalTripleRatchet.zeroizeSecretHook_ok extHookStack
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl))
  sharedDrop := hookSat_row (sharedDrop_row W)
    (hookOk_cliWithStack LibsignalTripleRatchet.zeroizeSecretHook_ok extHookStack
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl))
  compress512 := hookSat_row (Cli.Slots.compress512_row W) (compress512Hook_ok W.Q)
  toEdwards := hookSat_row (Cli.Slots.toEdwards_row W) (toEdwardsHook_ok W.Q)
  compress := hookSat_row (Cli.Slots.compress_row W) (leafHook_ok (by decide) W.Q.compress false)
  edNeg := hookSat_row (Cli.Slots.edNeg_row W) (leafHook_ok (by decide) W.Q.edNeg true)
  torsionFree := hookSat_row (Cli.Slots.torsionFree_row W) (torsionFreeHook_ok W.Q)
  dsmb := hookSat_row (Cli.Slots.dsmb_row W) (dsmbHook_ok W.Q)
  scalarMod := hookSat_row (Cli.Slots.scalarMod_row W) (leafHook_ok (by decide) W.Q.scalarMod true)
  scalarWide :=
    hookSat_row (Cli.Slots.scalarWide_row W) (leafHook_ok (by decide) W.Q.scalarWide false)
  kemEncaps := hookSat_row (Cli.Slots.kemEncaps_row W) (kemEncapsHook_ok W.Q)
  kemDecaps := hookSat_row (Cli.Slots.kemDecaps_row W) (kemDecapsHook_ok W.Q)
  spqr :=
    have hS := Cli.Slots.cliExterns_spqrHooks W
    ⟨hookSat_of_cliExterns (Cli.Slots.mlkemFromSeed_row W) hS.fromSeed,
     hookSat_of_cliExterns (Cli.Slots.mlkemPk1_row W) hS.pk1,
     hookSat_of_cliExterns (Cli.Slots.mlkemPk2_row W) hS.pk2,
     hookSat_of_cliExterns (Cli.Slots.mlkemEncaps1_row W) hS.encaps1,
     hookSat_of_cliExterns (Cli.Slots.mlkemEncaps2_row W) hS.encaps2,
     hookSat_of_cliExterns (Cli.Slots.mlkemDecaps_row W) hS.decaps,
     hookSat_of_cliExterns (Cli.Slots.mlkemValidatePk_row W) hS.validatePk,
     hookSat_of_cliExterns (Cli.Slots.libcruxHmac_row W) hS.hmac⟩

/-! ## The old statements from the new ones -/

theorem cliBinaryCorrect_of_ext {elf : ElfImage} (h : CliBinaryCorrectExt elf) :
    CliBinaryCorrect elf :=
  ⟨h.1, fun W hW => h.2 ⟨W.C, W.Q⟩ E2E.HooksE.A0 (cliHookExterns W) (cliExterns_ok W) hW⟩

theorem cliPqBinaryCorrect_of_ext {elf : ElfImage} (h : CliPqBinaryCorrectExt elf) :
    CliPqxdhElfCorrectUnderAllocOk elf :=
  ⟨h.1, fun W hW => h.2 ⟨W.C, W.Q⟩ E2E.HooksE.A0 (cliHookExterns W) (cliExterns_ok W) hW⟩

theorem libsignalCliBinaryCorrect_of_ext {bytes : List (BitVec 8)}
    (h : LibsignalCliBinaryCorrectExt bytes) : LibsignalCliBinaryCorrect bytes :=
  let ⟨elf, hp, he⟩ := h
  ⟨elf, hp, cliBinaryCorrect_of_ext he⟩

theorem libsignalCliPqBinaryCorrect_of_ext {bytes : List (BitVec 8)}
    (h : LibsignalCliPqBinaryCorrectExt bytes) : CliPqxdhBinaryCorrectUnderAllocOk bytes :=
  let ⟨elf, hp, he⟩ := h
  ⟨elf, hp, cliPqBinaryCorrect_of_ext he⟩

end CryptoVerification.SignalSession
