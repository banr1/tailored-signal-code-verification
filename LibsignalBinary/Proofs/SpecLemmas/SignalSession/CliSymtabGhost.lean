/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SymtabGhost
public import LibsignalBinary.Specifications.SignalSession.CliRun
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRunProofDefs

@[expose] public section

set_option autoImplicit false

/-!
# Symbol-Table Ghost Invariance for CLI Externs (`SymtabGhost`)

**Checked by Lean.** Proves that every hook in `cliExterns W` is `SymtabFree` (neither reading nor
writing `State.symtab`), yielding `SymtabGhost` both for `cliProg W` (`symtabGhost_cliProg`) and
for `Program.ofImage img (Rust.withPanics (cliExterns W))` (`symtabGhost_ofImage_cliExterns`).
-/

namespace CryptoVerification.SignalSession

open Arm64 ProofLib

set_option linter.unusedSimpArgs false

/-- Unfolds hook wrappers and closes `SymtabFree` goals via `symtab_free_close`. -/
macro "hook_symtab_free" : tactic => `(tactic| (
  try unfold CryptoVerification.SignalSession.unmodelled
  try unfold CryptoVerification.SignalSession.unitResult
  try unfold CryptoVerification.SignalSession.vecErr
  try unfold CryptoVerification.SignalSession.vecEmptyOk
  try unfold CryptoVerification.E2E.allocFail
  try unfold CryptoVerification.E2E.allocPanicHook
  try unfold CryptoVerification.LibsignalAesCbc.returnToLinkRegister
  try unfold ProofLib.retHook
  first | done | symtab_free_close))

/-! ## Allocation -/

/-- `bumpThen` commutes with `withSymtab` when both continuations do. -/
theorem bumpThen_withSymtab (t : String → String → Option (BitVec 64)) {size align : Nat}
    {ok : State → BitVec 64 → State} {fail : State → State}
    (hok : ∀ s p, ok (s.withSymtab t) p = (ok s p).withSymtab t)
    (hfail : ∀ s, fail (s.withSymtab t) = (fail s).withSymtab t) (s : State) :
    E2E.bumpThen size align ok fail (s.withSymtab t) =
      (E2E.bumpThen size align ok fail s).withSymtab t := by
  unfold E2E.bumpThen
  simp only [State.withSymtab_mem]
  split
  · rw [State.withSymtab_setMem, hok]
  · exact hfail s

/-- Applies `bumpThen_withSymtab` and discharges both continuations via `hook_symtab_free`. -/
macro "bump_symtab_free" : tactic => `(tactic| (
  refine CryptoVerification.SignalSession.bumpThen_withSymtab _ ?_ ?_ _ <;>
    (intros; first | rfl | hook_symtab_free)))

theorem vecOutThen_withSymtab (bs : List (BitVec 8)) (t : String → String → Option (BitVec 64))
    (s : State) : E2E.returnFreshVecU8 bs (s.withSymtab t) = (E2E.returnFreshVecU8 bs s).withSymtab t := by
  unfold E2E.returnFreshVecU8
  bump_symtab_free

theorem vecOk_withSymtab (bs : List (BitVec 8)) (t : String → String → Option (BitVec 64))
    (s : State) : vecOk bs (s.withSymtab t) = (vecOk bs s).withSymtab t := by
  unfold vecOk
  split
  · rfl
  · bump_symtab_free

theorem allocHook0_symtabFree : SymtabFree E2E.allocHook0 := by
  intro t s; unfold E2E.allocHook0; bump_symtab_free

theorem reallocHook0_symtabFree : SymtabFree E2E.reallocHook0 := by
  intro t s; unfold E2E.reallocHook0; dsimp only; bump_symtab_free

theorem allocZeroedHook0_symtabFree : SymtabFree E2E.allocZeroedHook0 := by
  intro t s; unfold E2E.allocZeroedHook0; bump_symtab_free

theorem deallocHook_symtabFree : SymtabFree E2E.deallocHook := hookNoop_symtabFree

theorem stringCloneHook0_symtabFree : SymtabFree E2E.stringCloneHook0 := by
  intro t s; unfold E2E.stringCloneHook0; exact vecOutThen_withSymtab _ t s

/-! ## I/O Hooks -/

theorem readFileHook_symtabFree : SymtabFree readFileHook := by
  intro t s; unfold readFileHook
  have _h := vecOk_withSymtab
  hook_symtab_free

theorem writeFileHook_symtabFree : SymtabFree writeFileHook := by
  intro t s; unfold writeFileHook; hook_symtab_free

theorem readStdinHook_symtabFree : SymtabFree readStdinHook := by
  intro t s; unfold readStdinHook
  have _h := vecOk_withSymtab
  hook_symtab_free

theorem writeStdoutHook_symtabFree : SymtabFree writeStdoutHook := by
  intro t s; unfold writeStdoutHook; hook_symtab_free

/-! ## libc, `core`, `std` -/

theorem strlenHook_symtabFree : SymtabFree strlenHook := by
  intro t s; unfold strlenHook; hook_symtab_free

theorem memrchrHook_symtabFree : SymtabFree memrchrHook := by
  intro t s; unfold memrchrHook; hook_symtab_free

theorem fromUtf8Hook_symtabFree (err : List (BitVec 8) → BitVec 64 × BitVec 16) :
    SymtabFree (fromUtf8Hook err) := by
  intro t s; unfold fromUtf8Hook; hook_symtab_free

theorem durationSinceExactHook_symtabFree : SymtabFree durationSinceExactHook := by
  intro t s; unfold durationSinceExactHook; hook_symtab_free

theorem cliBcmpHook_symtabFree (bcmp : List (BitVec 8) → List (BitVec 8) → BitVec 64) :
    SymtabFree (cliBcmpHook bcmp) := by
  intro t s; unfold cliBcmpHook; hook_symtab_free

theorem fmtWriteHook0_symtabFree : SymtabFree E2E.fmtWriteHook0 := by
  intro t s; unfold E2E.fmtWriteHook0; hook_symtab_free

theorem formatInnerHook0_symtabFree : SymtabFree E2E.formatInnerHook0 := by
  intro t s; unfold E2E.formatInnerHook0; hook_symtab_free

theorem timeAddHook_symtabFree : SymtabFree E2E.timeAddHook := by
  intro t s; unfold E2E.timeAddHook; hook_symtab_free

theorem blackBoxHook_symtabFree : SymtabFree LibsignalSession.blackBoxHook := by
  intro t s; unfold LibsignalSession.blackBoxHook; hook_symtab_free

/-! ## Session Crypto Hooks -/

theorem compress256Hook_symtabFree (F : CryptoGames.HMAC.ShaState → List (BitVec 8) →
    CryptoGames.HMAC.ShaState) : SymtabFree (LibsignalHmac.compress256Hook F) := by
  intro t s; unfold LibsignalHmac.compress256Hook; hook_symtab_free

theorem aesEncHook0_symtabFree (E : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block) :
    SymtabFree (E2E.aesEncHook0 E) := by
  intro t s
  have hout : E2E.aesEncOut E (s.withSymtab t) = E2E.aesEncOut E s := rfl
  unfold E2E.aesEncHook0
  dsimp only [State.withSymtab_readReg64]
  by_cases h1 : (s.readReg64 .x3 != 32#64 || s.readReg64 .x5 != 16#64) = true
  · simp only [h1, ↓reduceIte]; hook_symtab_free
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : 2 ^ 63 ≤ ((s.readReg64 .x1).toNat / 16 + 1) * 16
    · simp only [h2, ↓reduceIte]; exact Rust.panicked_symtabFree t s
    · simp only [h2, ↓reduceIte, hout]; exact vecOutThen_withSymtab _ t s

theorem aesDecHook0_symtabFree (D : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block) :
    SymtabFree (E2E.aesDecHook0 D) := by
  intro t s
  have hout : E2E.aesDecOut D (s.withSymtab t) = E2E.aesDecOut D s := rfl
  unfold E2E.aesDecHook0
  dsimp only [State.withSymtab_readReg64, State.withSymtab_mem]
  by_cases h1 : ((s.readReg64 .x1).toNat == 0 || (s.readReg64 .x1).toNat % 16 != 0) = true
  · simp only [h1, ↓reduceIte]; hook_symtab_free
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (s.readReg64 .x3 != 32#64 || s.readReg64 .x5 != 16#64) = true
    · simp only [h2, ↓reduceIte]; hook_symtab_free
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : 2 ^ 63 ≤ (s.readReg64 .x1).toNat
      · simp only [h3, ↓reduceIte]; exact Rust.panicked_symtabFree t s
      · simp only [h3, ↓reduceIte, hout]
        rcases E2E.aesDecOut D s with _ | pt
        · dsimp only; bump_symtab_free
        · dsimp only
          by_cases h4 : (E2E.bumpAddr? s.mem (s.readReg64 .x1).toNat 1).isNone = true
          · simp only [h4, ↓reduceIte]; hook_symtab_free
          · simp only [h4, Bool.false_eq_true, ↓reduceIte]; exact vecOutThen_withSymtab pt t s

theorem pubFromSecretHook_symtabFree (pubKey : CryptoGames.LibsignalSession.PubKeyFn) :
    SymtabFree (LibsignalTripleRatchet.pubFromSecretHook pubKey) := by
  intro t s; unfold LibsignalTripleRatchet.pubFromSecretHook; hook_symtab_free

theorem diffieHellmanHook_symtabFree (X : CryptoGames.Ratchet.X25519Fn) :
    SymtabFree (LibsignalTripleRatchet.diffieHellmanHook X) := by
  intro t s; unfold LibsignalTripleRatchet.diffieHellmanHook; hook_symtab_free

theorem zeroizeSecretHook_symtabFree : SymtabFree LibsignalTripleRatchet.zeroizeSecretHook := by
  intro t s; unfold LibsignalTripleRatchet.zeroizeSecretHook; hook_symtab_free

/-! ## PQXDH and SPQR Hooks -/

section Pqxdh

theorem compress512Hook_symtabFree (F512 : E2E.Sha512State → List (BitVec 8) → E2E.Sha512State) :
    SymtabFree (E2E.compress512Hook F512) := by
  intro t s; unfold E2E.compress512Hook; hook_symtab_free

theorem toEdwardsHook_symtabFree
    (montToEd : List.Vector (BitVec 8) 32 → BitVec 8 → Option (List.Vector (BitVec 8) 160)) :
    SymtabFree (E2E.toEdwardsHook montToEd) := by
  intro t s; unfold E2E.toEdwardsHook; hook_symtab_free

theorem compressHook_symtabFree
    (compress : List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 32) :
    SymtabFree (E2E.compressHook compress) := by
  intro t s; unfold E2E.compressHook; hook_symtab_free

theorem edNegHook_symtabFree
    (edNeg : List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 160) :
    SymtabFree (E2E.edNegHook edNeg) := by
  intro t s; unfold E2E.edNegHook; hook_symtab_free

theorem torsionFreeHook_symtabFree (isTorsionFree : List.Vector (BitVec 8) 160 → Bool) :
    SymtabFree (E2E.torsionFreeHook isTorsionFree) := by
  intro t s; unfold E2E.torsionFreeHook; hook_symtab_free

theorem dsmbHook_symtabFree (dsmb : List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 160 →
    List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 160) : SymtabFree (E2E.dsmbHook dsmb) := by
  intro t s; unfold E2E.dsmbHook; hook_symtab_free

theorem scalarModHook_symtabFree
    (scalarMod : List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 32) :
    SymtabFree (E2E.scalarModHook scalarMod) := by
  intro t s; unfold E2E.scalarModHook; hook_symtab_free

theorem scalarWideHook_symtabFree
    (scalarWide : List.Vector (BitVec 8) 64 → List.Vector (BitVec 8) 32) :
    SymtabFree (E2E.scalarWideHook scalarWide) := by
  intro t s; unfold E2E.scalarWideHook; hook_symtab_free

theorem kemEncapsHook_symtabFree (encaps : List.Vector (BitVec 8) 1568 →
    List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32) :
    SymtabFree (E2E.kemEncapsHook encaps) := by
  intro t s; unfold E2E.kemEncapsHook; hook_symtab_free

theorem kemDecapsHook_symtabFree (decaps : List.Vector (BitVec 8) 3168 →
    List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32) :
    SymtabFree (E2E.kemDecapsHook decaps) := by
  intro t s; unfold E2E.kemDecapsHook; hook_symtab_free

theorem mlkemFromSeedHook_symtabFree (K : LibsignalSpqrV1.MlKem) :
    SymtabFree (E2E.mlkemFromSeedHook K) := by
  intro t s; unfold E2E.mlkemFromSeedHook; hook_symtab_free

theorem mlkemPk1Hook_symtabFree : SymtabFree E2E.mlkemPk1Hook := by
  intro t s; unfold E2E.mlkemPk1Hook; hook_symtab_free

theorem mlkemPk2Hook_symtabFree : SymtabFree E2E.mlkemPk2Hook := by
  intro t s; unfold E2E.mlkemPk2Hook; hook_symtab_free

theorem mlkemEncaps1Hook_symtabFree (K : LibsignalSpqrV1.MlKem) :
    SymtabFree (E2E.mlkemEncaps1Hook K) := by
  intro t s; unfold E2E.mlkemEncaps1Hook; hook_symtab_free

theorem mlkemEncaps2Hook_symtabFree (K : LibsignalSpqrV1.MlKem) :
    SymtabFree (E2E.mlkemEncaps2Hook K) := by
  intro t s; unfold E2E.mlkemEncaps2Hook; hook_symtab_free

theorem mlkemDecapsHook_symtabFree (K : LibsignalSpqrV1.MlKem) :
    SymtabFree (E2E.mlkemDecapsHook K) := by
  intro t s; unfold E2E.mlkemDecapsHook; hook_symtab_free

theorem mlkemValidatePkHook_symtabFree (K : LibsignalSpqrV1.MlKem) :
    SymtabFree (E2E.mlkemValidatePkHook K) := by
  intro t s; unfold E2E.mlkemValidatePkHook; hook_symtab_free

theorem libcruxHmacHook_symtabFree
    (F : CryptoGames.HMAC.ShaState → List (BitVec 8) → CryptoGames.HMAC.ShaState) :
    SymtabFree (E2E.libcruxHmacHook F) := by
  intro t s
  unfold E2E.libcruxHmacHook
  dsimp only [State.withSymtab_readReg64, State.withSymtab_mem]
  by_cases h1 : ((s.readReg64 .x0).setWidth 32 != 0#32) = true
  · simp only [h1, ↓reduceIte]; rfl
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (s.readReg64 .x2).toNat < 2 ^ 32 ∧ (s.readReg64 .x4).toNat < 2 ^ 32
    · simp only [h2, and_self, ↓reduceIte]; bump_symtab_free
    · simp only [h2, ↓reduceIte]; exact Rust.panicked_symtabFree t s

end Pqxdh

/-! ## Hook Table and Whole Program -/

/-- Every hook in `cliHookTable W` is `SymtabFree`. -/
theorem cliHookTable_symtabFree (W : CliHooks) : ∀ p ∈ cliHookTable W, SymtabFree p.2 := by
  simp only [cliHookTable, E2E.pqxdhHookTable, E2E.spqrHookTable, List.cons_append,
    List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true]
  exact ⟨compress512Hook_symtabFree W.Q.F512, toEdwardsHook_symtabFree W.Q.montToEd,
    compressHook_symtabFree W.Q.compress, edNegHook_symtabFree W.Q.edNeg,
    torsionFreeHook_symtabFree W.Q.isTorsionFree, dsmbHook_symtabFree W.Q.dsmb,
    scalarModHook_symtabFree W.Q.scalarMod, scalarWideHook_symtabFree W.Q.scalarWide,
    kemEncapsHook_symtabFree W.Q.encaps, kemDecapsHook_symtabFree W.Q.decaps,
    mlkemFromSeedHook_symtabFree W.Q.K, mlkemPk1Hook_symtabFree, mlkemPk2Hook_symtabFree,
    mlkemEncaps1Hook_symtabFree W.Q.K, mlkemEncaps2Hook_symtabFree W.Q.K,
    mlkemDecapsHook_symtabFree W.Q.K, mlkemValidatePkHook_symtabFree W.Q.K,
    libcruxHmacHook_symtabFree W.C.F,
    hookNoop_symtabFree, allocHook0_symtabFree, deallocHook_symtabFree,
    reallocHook0_symtabFree, allocZeroedHook0_symtabFree, hookMemset_symtabFree,
    hookMemmove_symtabFree, hookMemcpy_symtabFree, cliBcmpHook_symtabFree W.bcmp,
    strlenHook_symtabFree, readFileHook_symtabFree, writeFileHook_symtabFree,
    readStdinHook_symtabFree, writeStdoutHook_symtabFree, memrchrHook_symtabFree,
    fromUtf8Hook_symtabFree W.utf8Err, fmtWriteHook0_symtabFree,
    formatInnerHook0_symtabFree, durationSinceExactHook_symtabFree, timeAddHook_symtabFree,
    blackBoxHook_symtabFree, compress256Hook_symtabFree W.C.F, aesEncHook0_symtabFree W.C.E,
    aesDecHook0_symtabFree W.C.D, pubFromSecretHook_symtabFree W.C.pubKey,
    diffieHellmanHook_symtabFree W.C.X, zeroizeSecretHook_symtabFree,
    zeroizeSecretHook_symtabFree⟩

theorem symtabFreeHooks_withPanicsE {X : String → Option (State → State)}
    (hX : SymtabFreeHooks X) : SymtabFreeHooks (E2E.withImagePanics X) := by
  intro n f h
  unfold E2E.withImagePanics at h
  split at h
  · cases h
    exact Rust.panicked_symtabFree
  · exact hX n f h

theorem symtabFreeHooks_withCliPanics {X : String → Option (State → State)}
    (hX : SymtabFreeHooks X) : SymtabFreeHooks (withCliPanics X) := by
  intro n f h
  unfold withCliPanics at h
  split at h
  · cases h
    exact Rust.panicked_symtabFree
  · exact hX n f h

/-- Every extern hook in `cliExterns W` is `SymtabFree`. -/
theorem symtabFreeHooks_cliExterns (W : CliHooks) : SymtabFreeHooks (cliExterns W) :=
  symtabFreeHooks_withCliPanics (symtabFreeHooks_lookup (cliHookTable_symtabFree W))

/-- `cliProg W` satisfies `SymtabGhost`. -/
theorem symtabGhost_cliProg (W : CliHooks) : SymtabGhost (cliProg W) := by
  unfold cliProg
  exact symtabGhost_of_hooksSymtabFree
    (Program.hooksSymtabFree_rebase (symtabFreeHooks_cliExterns W) symtabFreeHooks_none)

/-- `Program.ofImage img (Rust.withPanics (cliExterns W))` satisfies `SymtabGhost` for every `img`. -/
theorem symtabGhost_ofImage_cliExterns (img : Obj.Image) (W : CliHooks) :
    SymtabGhost (Program.ofImage img (Rust.withPanics (cliExterns W))) :=
  symtabGhost_of_hooksSymtabFree (Program.hooksSymtabFree_ofImage
    (Rust.symtabFreeHooks_withPanics (symtabFreeHooks_cliExterns W)) symtabFreeHooks_none)

end CryptoVerification.SignalSession
