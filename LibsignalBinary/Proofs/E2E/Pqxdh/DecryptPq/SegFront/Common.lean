/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Defs
import LibsignalBinary.Proofs.FnOffEq
import ProofLib.SepLogic.WPp

/-!
# Shared Framing, Relocation, and Epilogue Helpers for `SegFront`

Instruction-fetch macros, stack recombination and return-epilogue lemmas (`+0x394 .. +0x3b0`),
`RelocBytes` byte/word relocation combinators, and `ErrTailSpec` framing helpers.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.DecryptPq

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

open Lean Elab Tactic in
/-- `code_fetches_from <code> <decPrefix> b H hfn off k0 len` adds `<code>_fetch_fnAddr`
    hypotheses for the instructions `k = k0, k0 + 4, …, k0 + len - 4` of the function at offset
    `off` (`hfn : <code>.fnOff name = off`), using `<decPrefix>_decode_0x<off+k>`. -/
elab "code_fetches_from " codeId:ident decPrefix:ident b:term:max H:term:max hfn:ident
    off:num k0:num len:num : tactic => do
  let off := off.getNat
  let k0 := k0.getNat
  let len := len.getNat
  let codeBase := codeId.getId.eraseMacroScopes
  let decBase := decPrefix.getId.eraseMacroScopes
  let fetchEntry := mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let hex := String.ofList (Nat.toDigits 16 (off + k))
    let dec := mkIdent (decBase.appendAfter s!"_decode_0x{hex}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

/-- Fetch hypotheses for `try_decrypt_with_state::<HookRng>` (`0x6eff8`), from fn-relative offset
`k0`, `len` bytes. -/
macro "dec_fetches " b:term:max H:term:max hfn:ident k0:num len:num : tactic =>
  `(tactic| code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin
      $b (Rust.withPanics $H) $hfn 0x6eff8 $k0 $len)

theorem tryDecryptEntry_eq_fnAddr {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    tryDecryptEntry img = (tripleRatchetProgAt img.base C ctl abs).fnAddr tryDecryptName :=
  entryOf_eq_tripleRatchetProgAt himg tryDecryptName

/-! ## Shared Stack Recombination and Return Epilogue (`+0x394 .. +0x3b0`) -/

/-- Recombine `stackAt (sp0 - 1504#64) tryDecryptSubStack ∗ memRegion (sp0 - 1504#64) 1408 ∗
tryDecryptSavedRegs sp0 s0` into `stackAt sp0 rootStack` (`303104` bytes). -/
theorem tryDecryptStack_recombine (sp0 : BitVec 64) (s0 : State) :
    (stackAt (sp0 - 1504#64) tryDecryptSubStack ∗
      memRegion (sp0 - 1504#64) 1408 ∗
      tryDecryptSavedRegs sp0 s0) ⊢
      stackAt sp0 rootStack := by
  unfold tryDecryptSavedRegs stackAt tryDecryptSubStack tryDecryptFrameSize rootStack
  have h12 :
      (((sp0 - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
       ((sp0 - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
       ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
       ((sp0 - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
       ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
       ((sp0 - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
       ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
       ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
       ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
       ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)) ⊢
      memRegion (sp0 - 96#64) 96 := by
    refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (pointsTo64_entails_memRegion _ _)))))))))))) ?_
    rw [show sp0 - 8#64 = (sp0 - 16#64) + 8#64 by bv_omega,
        ← memRegion_split (sp0 - 16#64) 8 8 (by decide),
        show sp0 - 16#64 = (sp0 - 24#64) + 8#64 by bv_omega,
        ← memRegion_split (sp0 - 24#64) 8 16 (by decide),
        show sp0 - 24#64 = (sp0 - 32#64) + 8#64 by bv_omega,
        ← memRegion_split (sp0 - 32#64) 8 24 (by decide),
        show sp0 - 32#64 = (sp0 - 40#64) + 8#64 by bv_omega,
        ← memRegion_split (sp0 - 40#64) 8 32 (by decide),
        show sp0 - 40#64 = (sp0 - 48#64) + 8#64 by bv_omega,
        ← memRegion_split (sp0 - 48#64) 8 40 (by decide),
        show sp0 - 48#64 = (sp0 - 56#64) + 8#64 by bv_omega,
        ← memRegion_split (sp0 - 56#64) 8 48 (by decide),
        show sp0 - 56#64 = (sp0 - 64#64) + 8#64 by bv_omega,
        ← memRegion_split (sp0 - 64#64) 8 56 (by decide),
        show sp0 - 64#64 = (sp0 - 72#64) + 8#64 by bv_omega,
        ← memRegion_split (sp0 - 72#64) 8 64 (by decide),
        show sp0 - 72#64 = (sp0 - 80#64) + 8#64 by bv_omega,
        ← memRegion_split (sp0 - 80#64) 8 72 (by decide),
        show sp0 - 80#64 = (sp0 - 88#64) + 8#64 by bv_omega,
        ← memRegion_split (sp0 - 88#64) 8 80 (by decide),
        show sp0 - 88#64 = (sp0 - 96#64) + 8#64 by bv_omega,
        ← memRegion_split (sp0 - 96#64) 8 88 (by decide)]
    exact Entails.refl _
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right h12)) ?_
  change memRegion (sp0 - 1504#64 - 260640#64) 260640 ∗
      (memRegion (sp0 - 1504#64) 1408 ∗ memRegion (sp0 - 96#64) 96) ⊢
    memRegion (sp0 - 262144#64) 262144
  rw [show sp0 - 96#64 = (sp0 - 1504#64) + 1408#64 by bv_omega,
      ← memRegion_split (sp0 - 1504#64) 1408 96 (by decide),
      show (sp0 - 1504#64) - 260640#64 = sp0 - 262144#64 by bv_omega,
      show sp0 - 1504#64 = (sp0 - 262144#64) + 260640#64 by bv_omega,
      ← memRegion_split (sp0 - 262144#64) 260640 1504 (by decide)]
  exact Entails.refl _

theorem sepWP_to_reaches_pc {prog : Program} {target_pc : BitVec 64} {s : State}
    {P R : SepProp} {post : State → SepProp → Prop}
    (hwp : SepWP prog target_pc s P post)
    (hm : s.mem ⊨ P ∗ R) :
    reaches_pc prog target_pc s (fun sf => ∃ P_f, sf.mem ⊨ P_f ∗ R ∧ post sf P_f) := by
  intro hL
  obtain ⟨sf, hst, hok | ⟨_, hfalse⟩⟩ := hwp.elim hm hL
  · exact ⟨sf, hst, Or.inl hok⟩
  · exact (not_satisfies_false_sepConj hfalse).elim

theorem decRel_afterTrFrom (G : SessionGhost) : G.AfterTryDecrypt false G.afterTrFrom :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩

/-! ## `RelocBytes`: Byte-Slice and Word-Array Relocation Combinators -/

/-- A separation-logic predicate `P : BitVec 64 → SepProp` is relocatable of byte width `n` if
any `m ⊨ P p ∗ R` decomposes into an `n`-byte slice `p ↦ₛ bs` and a `p`-independent resource `H`
such that `(q ↦ₛ bs) ∗ H ⊢ P q` at any target address `q`. -/
def RelocBytes (n : Nat) (P : BitVec 64 → SepProp) : Prop :=
  ∀ (p : BitVec 64) (R : SepProp) (m : Memory),
    (m ⊨ P p ∗ R) →
    ∃ (bs : List (BitVec 8)) (H : SepProp),
      bs.length = n ∧
      (m ⊨ ((p ↦ₛ bs) ∗ H) ∗ R) ∧
      (∀ q : BitVec 64, (q ↦ₛ bs) ∗ H ⊢ P q)

theorem relocBytes_congr {n : Nat} {P Q : BitVec 64 → SepProp}
    (heq : ∀ a, Q a = P a) (hP : RelocBytes n P) : RelocBytes n Q := by
  intro p R m hm
  have hm' : m ⊨ P p ∗ R := by simpa only [heq p] using hm
  obtain ⟨bs, H, hlen, hm'', hent⟩ := hP p R m hm'
  exact ⟨bs, H, hlen, hm'', fun q => heq q ▸ hent q⟩

theorem relocBytes_pointsToBytes (bs : List (BitVec 8)) {n : Nat} (hn : bs.length = n) :
    RelocBytes n (fun p => p ↦ₛ bs) := by
  intro p R m hm
  exact ⟨bs, emp, hn, by simpa [sepConj_emp] using hm,
    fun q => by simp [sepConj_emp]; exact Entails.refl _⟩

theorem relocBytes_pointsTo8 (b : BitVec 8) : RelocBytes 1 (fun p => p ↦₈ b) :=
  relocBytes_congr (fun a => by rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp])
    (relocBytes_pointsToBytes [b] rfl)

theorem relocBytes_pointsTo32 (w : BitVec 32) : RelocBytes 4 (fun p => p ↦₃₂ w) :=
  relocBytes_congr (fun a => pointsTo32_eq_pointsToBytes a w)
    (relocBytes_pointsToBytes (unpack32 w) (unpack32_length w))

theorem relocBytes_pointsTo64 (w : BitVec 64) : RelocBytes 8 (fun p => p ↦₆₄ w) :=
  relocBytes_congr (fun a => pointsTo64_eq_pointsToBytes a w)
    (relocBytes_pointsToBytes (unpack64 w) (unpack64_length w))

theorem relocBytes_memRegion (n : Nat) (hn : n ≤ 2 ^ 64) :
    RelocBytes n (fun p => memRegion p n) := by
  intro p R m hm
  dsimp only at hm
  rw [memRegion_eq_exists_bytes p n hn, sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨bs, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hlen, hm⟩
  refine ⟨bs, emp, hlen, by simpa [sepConj_emp] using hm, fun q => ?_⟩
  dsimp only
  rw [sepConj_emp, ← hlen]
  exact pointsToBytes_entails_memRegion q bs

theorem relocBytes_const_right {n : Nat} {P : BitVec 64 → SepProp} (H0 : SepProp)
    (hP : RelocBytes n P) :
    RelocBytes n (fun p => P p ∗ H0) := by
  intro p R m hm
  dsimp only at hm
  rw [sepConj_assoc] at hm
  obtain ⟨bs, H, hlen, hm', hent⟩ := hP p (H0 ∗ R) m hm
  refine ⟨bs, H ∗ H0, hlen, by convert hm' using 1; ac_rfl, fun q => ?_⟩
  dsimp only
  rw [← sepConj_assoc]
  exact sepConj_mono_left (hent q)

theorem relocBytes_pure_left {n : Nat} {φ : Prop} {P : BitVec 64 → SepProp}
    (hP : RelocBytes n P) :
    RelocBytes n (fun p => ⌜φ⌝ ∗ P p) := by
  intro p R m hm
  dsimp only at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hφ, hm⟩
  obtain ⟨bs, H, hlen, hm', hent⟩ := hP p R m hm
  exact ⟨bs, H, hlen, hm', fun q => Entails.pure_right hφ (hent q)⟩

theorem relocBytes_exists {α : Type} {n : Nat} {P : α → BitVec 64 → SepProp}
    (hP : ∀ x, RelocBytes n (P x)) :
    RelocBytes n (fun p => ∃∗ x : α, P x p) := by
  intro p R m hm
  dsimp only at hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨x, hm⟩
  obtain ⟨bs, H, hlen, hm', hent⟩ := hP x p R m hm
  exact ⟨bs, H, hlen, hm',
    fun q => Entails.trans (hent q) (Entails.sepExists_intro (P := fun y => P y q) x)⟩

theorem relocBytes_append {n1 n2 n : Nat} {P1 P2 : BitVec 64 → SepProp}
    (h1 : RelocBytes n1 P1) (h2 : RelocBytes n2 P2) (hn : n1 + n2 = n) :
    RelocBytes n (fun p => P1 p ∗ P2 (p + BitVec.ofNat 64 n1)) := by
  intro p R m hm
  dsimp only at hm
  rw [sepConj_assoc] at hm
  obtain ⟨bs1, H1, hlen1, hm1, hent1⟩ := h1 p (P2 (p + BitVec.ofNat 64 n1) ∗ R) m hm
  have hm1_re : m ⊨ P2 (p + BitVec.ofNat 64 n1) ∗ (((p ↦ₛ bs1) ∗ H1) ∗ R) := by
    convert hm1 using 1; ac_rfl
  obtain ⟨bs2, H2, hlen2, hm2, hent2⟩ :=
    h2 (p + BitVec.ofNat 64 n1) (((p ↦ₛ bs1) ∗ H1) ∗ R) m hm1_re
  refine ⟨bs1 ++ bs2, H1 ∗ H2, by simp [hlen1, hlen2, hn], ?_, fun q => ?_⟩
  · rw [pointsToBytes_append, hlen1]
    convert hm2 using 1; ac_rfl
  · dsimp only
    rw [pointsToBytes_append, hlen1]
    have hre :
        (((q ↦ₛ bs1) ∗ ((q + BitVec.ofNat 64 n1) ↦ₛ bs2)) ∗ (H1 ∗ H2)) =
        (((q ↦ₛ bs1) ∗ H1) ∗ (((q + BitVec.ofNat 64 n1) ↦ₛ bs2) ∗ H2)) := by ac_rfl
    rw [hre]
    exact sepConj_mono (hent1 q) (hent2 (q + BitVec.ofNat 64 n1))

theorem relocBytes_vecHeader (cap ptr len : BitVec 64) :
    RelocBytes 24 (fun p => vecHeader p cap ptr len) :=
  relocBytes_congr (fun a => by unfold vecHeader; ac_rfl)
    (relocBytes_append
      (relocBytes_append (relocBytes_pointsTo64 cap) (relocBytes_pointsTo64 ptr) rfl)
      (relocBytes_pointsTo64 len) rfl)

theorem relocBytes_vecU8At (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    RelocBytes 24 (fun p => vecU8At A p cap ptr bs) :=
  relocBytes_const_right _ (relocBytes_vecHeader cap ptr (BitVec.ofNat 64 bs.length))

theorem relocBytes_vecU8 (A : RustAlloc) (bs : List (BitVec 8)) :
    RelocBytes 24 (fun p => vecU8 A p bs) :=
  relocBytes_exists fun cap => relocBytes_exists fun ptr => relocBytes_vecU8At A cap ptr bs

theorem relocBytes_strRefAt (lit : List (BitVec 8)) :
    RelocBytes 16 (fun p => strRefAt p lit) :=
  relocBytes_exists fun ptr =>
    relocBytes_congr (fun a => by ac_rfl)
      (relocBytes_const_right (ptr ↦ᵣ lit)
        (relocBytes_append (relocBytes_pointsTo64 ptr)
          (relocBytes_pointsTo64 (BitVec.ofNat 64 lit.length)) rfl))

theorem relocBytes_invalidMessageStrAt (A : RustAlloc) (r : InvalidMessageReason) :
    RelocBytes 24 (fun p => invalidMessageStrAt A p r) := by
  cases r with
  | tooFarInFuture => exact relocBytes_vecU8 A tooFarInFutureStr
  | macFailed => exact relocBytes_vecU8 A macFailedStr
  | pqRatchet => exact relocBytes_exists fun bs => relocBytes_vecU8 A bs
  | badCiphertext => exact relocBytes_exists fun bs => relocBytes_vecU8 A bs
  | decryptionFailed =>
    intro p R m hm
    exact (not_satisfies_false_sepConj hm).elim

theorem relocBytes_speBodyAt (A : RustAlloc) (fnName : List (BitVec 8))
    (e : SignalProtocolError) (he : e ≠ .panic) :
    RelocBytes 40 (fun p => speBodyAt A fnName p e) := by
  cases e with
  | invalidState =>
    exact relocBytes_append (relocBytes_exists fun bs => relocBytes_vecU8 A bs)
      (relocBytes_strRefAt fnName) rfl
  | ciphertextMessageTooShort n =>
    exact relocBytes_append (relocBytes_pointsTo64 (BitVec.ofNat 64 n))
      (relocBytes_memRegion 32 (by decide)) rfl
  | legacyCiphertextVersion v =>
    exact relocBytes_append (relocBytes_pointsTo8 v) (relocBytes_memRegion 39 (by decide)) rfl
  | unrecognizedCiphertextVersion v =>
    exact relocBytes_append (relocBytes_pointsTo8 v) (relocBytes_memRegion 39 (by decide)) rfl
  | invalidProtobufEncoding =>
    exact relocBytes_memRegion 40 (by decide)
  | noKeyTypeIdentifier =>
    exact relocBytes_memRegion 40 (by decide)
  | badKeyType t =>
    exact relocBytes_append (relocBytes_pointsTo8 t) (relocBytes_memRegion 39 (by decide)) rfl
  | badKeyLength n =>
    exact relocBytes_append (relocBytes_pointsTo64 (BitVec.ofNat 64 n))
      (relocBytes_memRegion 32 (by decide)) rfl
  | invalidKeyAgreement =>
    exact relocBytes_memRegion 40 (by decide)
  | invalidSessionStructure r =>
    exact relocBytes_append (relocBytes_strRefAt (invalidSessionStructureStr r))
      (relocBytes_memRegion 24 (by decide)) rfl
  | duplicatedMessage i c =>
    exact relocBytes_congr (fun a => by unfold speBodyAt; ac_rfl)
      (relocBytes_append
        (relocBytes_append (relocBytes_pointsTo32 i) (relocBytes_pointsTo32 c) rfl)
        (relocBytes_memRegion 32 (by decide)) rfl)
  | invalidMessage t r =>
    exact relocBytes_congr (fun a => by unfold speBodyAt; ac_rfl)
      (relocBytes_append
        (relocBytes_append (relocBytes_invalidMessageStrAt A r)
          (relocBytes_pointsTo8 (msgTypeByte t)) rfl)
        (relocBytes_memRegion 15 (by decide)) rfl)
  | panic => exact (he rfl).elim

/-! ## `speAt` and `speBodyAt` 5-Word Relocation -/

def words5At (a w0 w1 w2 w3 w4 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
  ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4)

theorem words5At_entails_memRegion (a w0 w1 w2 w3 w4 : BitVec 64) :
    words5At a w0 w1 w2 w3 w4 ⊢ memRegion a 40 := by
  unfold words5At
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo64_entails_memRegion _ _))))) ?_
  rw [show a + 32#64 = (a + 24#64) + 8#64 by bv_omega,
      ← memRegion_split (a + 24#64) 8 8 (by decide),
      show a + 24#64 = (a + 16#64) + 8#64 by bv_omega,
      ← memRegion_split (a + 16#64) 8 16 (by decide),
      show a + 16#64 = (a + 8#64) + 8#64 by bv_omega,
      ← memRegion_split (a + 8#64) 8 24 (by decide),
      ← memRegion_split a 8 32 (by decide)]
  exact Entails.refl _

theorem exists_words5_of_length_40 {bs : List (BitVec 8)} (h : bs.length = 40) :
    ∃ w0 w1 w2 w3 w4 : BitVec 64,
      ∀ a : BitVec 64, (a ↦ₛ bs) = words5At a w0 w1 w2 w3 w4 := by
  have h0 : (bs.take 32).length = 32 := by simp [h]
  have h1 : (bs.drop 32).length = 8 := by simp [h]
  obtain ⟨w0, w1, w2, w3, _, hp0⟩ := exists_unpack64_of_length_32 h0
  obtain ⟨w4, hw4⟩ := exists_unpack64_of_length_8 h1
  refine ⟨w0, w1, w2, w3, w4, fun a => ?_⟩
  have hsplit : bs = bs.take 32 ++ bs.drop 32 := (List.take_append_drop 32 bs).symm
  rw [hsplit, pointsToBytes_append, h0, hp0 a, hw4, ← pointsTo64_eq_pointsToBytes]
  unfold words5At
  ac_rfl

theorem speAt_eq_speTag_speBodyAt {A : RustAlloc} {fnName : List (BitVec 8)}
    {a : BitVec 64} {e : SignalProtocolError} (he : e ≠ .panic) :
    speAt A fnName a e = (a ↦₆₄ speTag e) ∗ speBodyAt A fnName (a + 8#64) e := by
  cases e <;> try exact (he rfl).elim
  all_goals
    simp only [speAt, speTag, speBodyAt, BitVec.add_assoc, BitVec.reduceAdd]

theorem exists_words5_of_speBodyAt {A : RustAlloc} {fnName : List (BitVec 8)}
    {p : BitVec 64} {e : SignalProtocolError} {R : SepProp} {m : Memory}
    (he : e ≠ .panic) (hm : m ⊨ speBodyAt A fnName p e ∗ R) :
    ∃ (w0 w1 w2 w3 w4 : BitVec 64) (H : SepProp),
      (m ⊨ (words5At p w0 w1 w2 w3 w4 ∗ H) ∗ R) ∧
      (∀ q : BitVec 64,
        (q ↦₆₄ speTag e) ∗ words5At (q + 8#64) w0 w1 w2 w3 w4 ∗ H ⊢ speAt A fnName q e) := by
  obtain ⟨bs, H, hlen, hm', hent⟩ := relocBytes_speBodyAt A fnName e he p R m hm
  obtain ⟨w0, w1, w2, w3, w4, hwords⟩ := exists_words5_of_length_40 hlen
  refine ⟨w0, w1, w2, w3, w4, H, by rwa [← hwords p], fun q => ?_⟩
  rw [← hwords (q + 8#64), speAt_eq_speTag_speBodyAt he]
  exact sepConj_mono_right (hent (q + 8#64))

theorem exists_words6_of_memRegion_48 {a : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ memRegion a 48 ∗ R) :
    ∃ r0 r1 r2 r3 r4 r5 : BitVec 64,
      m ⊨ ((a ↦₆₄ r0) ∗ words5At (a + 8#64) r1 r2 r3 r4 r5) ∗ R := by
  rw [memRegion_eq_exists_bytes a 48 (by decide), sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨bs, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hlen, hm⟩
  have h0 : (bs.take 8).length = 8 := by simp [hlen]
  have h1 : (bs.drop 8).length = 40 := by simp [hlen]
  obtain ⟨r0, hr0⟩ := exists_unpack64_of_length_8 h0
  obtain ⟨r1, r2, r3, r4, r5, hr5⟩ := exists_words5_of_length_40 h1
  refine ⟨r0, r1, r2, r3, r4, r5, ?_⟩
  have hsplit : bs = bs.take 8 ++ bs.drop 8 := (List.take_append_drop 8 bs).symm
  rw [hsplit, pointsToBytes_append, h0, hr0, ← pointsTo64_eq_pointsToBytes, hr5 (a + 8#64)] at hm
  exact hm

theorem exists_words3_of_memRegion_24 {a : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ memRegion a 24 ∗ R) :
    ∃ t0 t1 t2 : BitVec 64,
      m ⊨ ((a ↦₆₄ t0) ∗ ((a + 8#64) ↦₆₄ t1) ∗ ((a + 16#64) ↦₆₄ t2)) ∗ R := by
  rw [memRegion_eq_exists_bytes a 24 (by decide), sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨bs, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hlen, hm⟩
  have h0 : (bs.take 16).length = 16 := by simp [hlen]
  have h1 : (bs.drop 16).length = 8 := by simp [hlen]
  obtain ⟨t0, t1, _, hp0⟩ := exists_unpack64_of_length_16 h0
  obtain ⟨t2, ht2⟩ := exists_unpack64_of_length_8 h1
  refine ⟨t0, t1, t2, ?_⟩
  have hsplit : bs = bs.take 16 ++ bs.drop 16 := (List.take_append_drop 16 bs).symm
  rw [hsplit, pointsToBytes_append, h0, hp0 a, ht2, ← pointsTo64_eq_pointsToBytes] at hm
  convert hm using 1
  ac_rfl

/-- The state invariant carried inside `SepWP` proofs (`tryDecryptMidMeta` without `img.CallInv`,
which `reaches_pc_callInv` preserves automatically at the `reaches_pc` level). -/
def tryDecryptWPInv (s0 s : State) : Prop :=
  s.status = .Running ∧
  s.sp = s0.sp - 1504#64 ∧
  s0.spAligned = true ∧
  s.spAligned = true ∧
  s.readReg64 .x29 = s0.sp - 96#64 ∧
  (s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)

theorem tryDecryptMidMeta.to_wpInv {img : Obj.Image} {s0 s : State}
    (h : tryDecryptMidMeta img s0 s) : tryDecryptWPInv s0 s := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, _, _, h9⟩
  exact ⟨h1, h2, h3, h4, h5, ⟨h6, h9⟩⟩

theorem reaches_pc_callInv {prog : Program} {img : Obj.Image} {t : BitVec 64} {s : State}
    {Q oom : State → Prop} (hinv : img.FrozenLoaded s ∧ s.symtab = img.symtab)
    (h : reaches_pc prog t s Q oom) :
    reaches_pc prog t s (fun sf => Q sf ∧ img.FrozenLoaded sf ∧ sf.symtab = img.symtab) oom := by
  intro hL
  obtain ⟨sf, hst, ⟨hpc, hrun, hq⟩ | hoom⟩ := h hL
  · exact ⟨sf, hst, Or.inl ⟨hpc, hrun, hq, hinv.1.of_keepsFrozen hst.keepsFrozen, hst.symtab_eq.trans hinv.2⟩⟩
  · exact ⟨sf, hst, Or.inr hoom⟩

theorem sepWP_to_reaches_pc_midMeta {prog : Program} {img : Obj.Image} {target_pc : BitVec 64}
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hmeta : tryDecryptMidMeta img s0 s)
    (hwp : SepWP prog target_pc s P (fun sf P_f => post sf P_f ∧ tryDecryptWPInv s0 sf))
    (hm : s.mem ⊨ P ∗ R) :
    reaches_pc prog target_pc s
      (fun sf => ∃ P_f, sf.mem ⊨ P_f ∗ R ∧ post sf P_f ∧ tryDecryptMidMeta img s0 sf) := by
  have hinv : img.FrozenLoaded s ∧ s.symtab = img.symtab :=
    ⟨hmeta.2.2.2.2.2.2.1, hmeta.2.2.2.2.2.2.2.1⟩
  refine reaches_pc_mono
    (reaches_pc_callInv hinv (sepWP_to_reaches_pc hwp hm)) ?_
  intro sf _ _ ⟨⟨P_f, hm_f, hpost_f, ⟨h1, h2, h3, h4, h5, ⟨h6, h9⟩⟩⟩, h7, h8⟩
  exact ⟨P_f, hm_f, hpost_f, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩⟩

/-! ## `SepWP` Framing and Composition Combinators -/

macro "wp_finish" : tactic =>
  `(tactic| refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_)

theorem SepWP.frame_right {prog : Program} {target_pc : BitVec 64}
    {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (h : SepWP prog target_pc s P Q) :
    SepWP prog target_pc s (P ∗ F) (fun sf Pf => ∃ P', Pf = P' ∗ F ∧ Q sf P') := by
  unfold SepWP at *
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨sf, hst, ⟨hpc, hrun, P', hm', hQ⟩ | ⟨_, hfalse⟩⟩ := h (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hm'
    exact ⟨sf, hst, Or.inl ⟨hpc, hrun, P' ∗ F, hm', P', rfl, hQ⟩⟩
  · exact (not_satisfies_false_sepConj hfalse).elim

theorem SepWP.bind_framed {prog : Program} {mid_pc target_pc : BitVec 64}
    {s : State} {P1 F P : SepProp} {Q1 Q2 : State → SepProp → Prop}
    (h1 : SepWP prog mid_pc s P1 Q1)
    (hP : P = P1 ∗ F)
    (h2 : ∀ s1 P1', Q1 s1 P1' → s1.pc = mid_pc → SepWP prog target_pc s1 (P1' ∗ F) Q2) :
    SepWP prog target_pc s P Q2 := by
  unfold SepWP at *
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨s1, hst1, ⟨hpc1, _, P1', hm1, hQ1⟩ | ⟨_, hfalse⟩⟩ := h1 (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hm1
    obtain ⟨sf, hst2, hout⟩ := h2 s1 P1' hQ1 hpc1 R hm1 (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hout⟩
  · exact (not_satisfies_false_sepConj hfalse).elim

theorem SepWP.mono_pre {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P' : SepProp} {Q : State → SepProp → Prop}
    (hent : P ⊢ P') (h : SepWP prog target_pc s P' Q) :
    SepWP prog target_pc s P Q := by
  exact SepWP.weaken_pre hent h

/-! ## `ErrTailSpec` (`+0x30c → +0x394 → +0x3b0`) -/

theorem optSenderChainBytes_length (o : Option SenderChain) (pad : List (BitVec 8))
    (hpad : pad.length = 100) :
    (optSenderChainBytes o pad).length = 104 := by
  cases o with
  | none =>
    simp [optSenderChainBytes, leBytes, hpad]
  | some sc =>
    simp [optSenderChainBytes, senderChainBytes, chainKeyBytes, keyToBytes32, leBytes,
      List.Vector.toList_length]

open Lean Elab Tactic Meta in
elab "sep_ac_rfl" : tactic =>
  withMainContext do
    evalTactic (← `(tactic|
      try simp only [emp_sepConj, sepConj_emp, BitVec.ofNat_eq_ofNat,
        BitVec.add_assoc, BitVec.reduceAdd]))
    unless (← getGoals).isEmpty do
      withReducible do
        evalTactic (← `(tactic| ac_rfl))

theorem fnAddr_tryDecrypt_add_eq {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff tryDecryptName + k =
      libsignalSessionCode.fnOff name := by fnoff_eq) :
    (tripleRatchetProgAt b C ctl abs).fnAddr tryDecryptName + BitVec.ofNat 64 k =
      (tripleRatchetProgAt b C ctl abs).fnAddr name := by
  simp only [Program.fnAddr_rebase, BitVec.add_assoc, ← BitVec.ofNat_add, hk]

theorem stackAt_sub (sp : BitVec 64) (k n : Nat) (hkn : k ≤ n) (hn : n ≤ 2 ^ 64) :
    stackAt sp n = stackAt sp k ∗ memRegion (sp - BitVec.ofNat 64 n) (n - k) := by
  unfold stackAt
  have hsplit := memRegion_split (sp - BitVec.ofNat 64 n) (n - k) k (by omega)
  have hadd : sp - BitVec.ofNat 64 n + BitVec.ofNat 64 (n - k) = sp - BitVec.ofNat 64 k := by
    bv_omega
  rw [Nat.sub_add_cancel hkn, hadd] at hsplit
  rw [hsplit, sepConj_comm]

theorem stackAt_tryDecryptSubStack_sub (sp0 : BitVec 64) (k : Nat)
    (hkn : k ≤ tryDecryptSubStack) :
    stackAt (sp0 - 1504#64) tryDecryptSubStack =
      stackAt (sp0 - 1504#64) k ∗ memRegion (sp0 - 262144#64) (tryDecryptSubStack - k) := by
  rw [stackAt_sub (sp0 - 1504#64) k tryDecryptSubStack hkn (by decide)]
  have h : sp0 - 1504#64 - BitVec.ofNat 64 tryDecryptSubStack = sp0 - 262144#64 := by
    dsimp only [tryDecryptSubStack, tryDecryptFrameSize, rootStack]; bv_omega
  rw [h]

theorem stackAt_dropChainStack_sub (sp : BitVec 64) :
    stackAt sp dropChainStack =
      stackAt sp allocHookStack ∗
        memRegion (sp - 4144#64) 48 := by
  simpa [dropChainStack, allocHookStack] using
    stackAt_sub sp allocHookStack dropChainStack (by decide) (by decide)

theorem SepWP.rw_pre {prog : Program} {target : BitVec 64} {s : State}
    {P P' : SepProp} {Q : State → SepProp → Prop}
    (hP : P = P') (h : SepWP prog target s P' Q) :
    SepWP prog target s P Q :=
  hP ▸ h

theorem exists_word32_of_length_4 {bs : List (BitVec 8)} (h : bs.length = 4) :
    ∃ w : BitVec 32, ∀ a : BitVec 64, (a ↦ₛ bs) = (a ↦₃₂ w) := by
  refine ⟨pack32 (bs.getD 0 0#8) (bs.getD 1 0#8) (bs.getD 2 0#8) (bs.getD 3 0#8), fun a => ?_⟩
  have htake : (bs.drop 0).take 4 = bs := by
    simp only [List.drop_zero]
    exact List.take_of_length_le (by omega)
  have h1 := pointsToBytes_take4_eq_pointsTo32 a bs 0 (by omega)
  rwa [htake] at h1

theorem exists_words16_of_length_16 {bs : List (BitVec 8)} (h : bs.length = 16) :
    ∃ w0 w1 : BitVec 64,
      ∀ a : BitVec 64, (a ↦ₛ bs) = (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) := by
  obtain ⟨w0, w1, _, hp⟩ := exists_unpack64_of_length_16 h
  exact ⟨w0, w1, hp⟩

theorem reaches_pc_seq_callInv {prog : Program} {img : Obj.Image} {mid t : BitVec 64}
    {s : State} {Q post : State → Prop} (hinv : img.FrozenLoaded s ∧ s.symtab = img.symtab)
    (h1 : reaches_pc prog mid s Q)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → Q sm →
      (img.FrozenLoaded sm ∧ sm.symtab = img.symtab) → reaches_pc prog t sm post) :
    reaches_pc prog t s post :=
  reaches_pc_seq (reaches_pc_callInv hinv h1) fun sm hpc hrun ⟨hq, h1, h2'⟩ =>
    h2 sm hpc hrun hq ⟨h1, h2'⟩

theorem reaches_pc_call_inImage {α : Type} {prog : Program} {img : Obj.Image}
    {callee ret_pc exit_pc : BitVec 64} {spec : Spec α}
    (h_callee : subroutine_ok prog callee (spec.inImage img)) (x : α) (R : SepProp)
    {s_call : State} {post : State → Prop}
    (h_pc : s_call.pc = callee) (h_run : s_call.status = .Running)
    (h_lr : s_call.readReg64 Reg.lr = ret_pc)
    (h_inv : img.FrozenLoaded s_call ∧ s_call.symtab = img.symtab)
    (h_pre : s_call.mem ⊨ spec.pre x s_call ∗ R)
    (h_cont : ∀ s_ret : State,
      s_ret.pc = ret_pc → s_ret.status = .Running → s_ret.sp = s_call.sp →
      CalleeSavedPreserved s_call s_ret →
      (img.FrozenLoaded s_ret ∧ s_ret.symtab = img.symtab) →
      (s_ret.mem ⊨ spec.post x s_call s_ret ∗ R) →
      reaches_pc prog exit_pc s_ret post)
    (h_sp_align : s_call.spAligned = true)
    (h_no_panic : ∀ sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s_call sf ∗ R) := by
      intro _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ code sf, sf.status = .Exited code →
      ¬(sf.mem ⊨ spec.onExit x code s_call sf ∗ R) := by
      intro _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_oom : ∀ sf, sf.status = .OutOfMemory →
      ¬(sf.mem ⊨ spec.onOom x s_call sf ∗ R) := by
      intro _ _ ho; exact not_satisfies_false_sepConj ho) :
    reaches_pc prog exit_pc s_call post := by
  have h_pre_in : s_call.mem ⊨ (spec.inImage img).pre x s_call ∗ R := by
    simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨h_inv, h_pre⟩
  have h_reach := subroutine_ok_apply_full h_callee x R h_pc h_run h_pre_in
    h_sp_align h_no_panic h_no_exit h_no_oom
  rw [h_lr] at h_reach
  refine reaches_pc_seq (reaches_pc_callInv h_inv h_reach) fun s_ret h_ret_pc h_ret_run hq => ?_
  obtain ⟨⟨h_post, h_sp, h_cs⟩, h1, h2⟩ := hq
  exact h_cont s_ret h_ret_pc h_ret_run h_sp h_cs ⟨h1, h2⟩ h_post

theorem exists_word32_of_memRegion_4 {a : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ memRegion a 4 ∗ R) :
    ∃ w : BitVec 32, m ⊨ (a ↦₃₂ w) ∗ R := by
  rw [memRegion_eq_exists_bytes a 4 (by decide), sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨bs, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hlen, hm⟩
  obtain ⟨w, hw⟩ := exists_word32_of_length_4 hlen
  exact ⟨w, by rwa [← hw a]⟩

theorem exists_word64_of_memRegion_8 {a : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ memRegion a 8 ∗ R) :
    ∃ w : BitVec 64, m ⊨ (a ↦₆₄ w) ∗ R := by
  rw [memRegion_eq_exists_bytes a 8 (by decide), sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨bs, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hlen, hm⟩
  obtain ⟨w, hw⟩ := exists_unpack64_of_length_8 hlen
  exact ⟨w, by rwa [pointsTo64_eq_pointsToBytes, ← hw]⟩

theorem tryDecryptWPInv.to_midMeta {img : Obj.Image} {s0 sf : State}
    (hwp : tryDecryptWPInv s0 sf)
    (hinv : img.FrozenLoaded sf ∧ sf.symtab = img.symtab) :
    tryDecryptMidMeta img s0 sf :=
  ⟨hwp.1, hwp.2.1, hwp.2.2.1, hwp.2.2.2.1, hwp.2.2.2.2.1, hwp.2.2.2.2.2.1, hinv.1, hinv.2, hwp.2.2.2.2.2.2⟩

theorem sepWP_to_reaches_pc_with_midMeta {prog : Program} {img : Obj.Image}
    {target : BitVec 64} {s0 s : State} {P R : SepProp}
    {post : State → SepProp → Prop} {Q : State → Prop}
    (hmeta : tryDecryptMidMeta img s0 s)
    (hwp : SepWP prog target s P post)
    (hm : s.mem ⊨ P ∗ R)
    (hcont : ∀ sf P_f, sf.pc = target → post sf P_f →
      (img.FrozenLoaded sf ∧ sf.symtab = img.symtab) →
      (sf.mem ⊨ P_f ∗ R) → Q sf) :
    reaches_pc prog target s Q := by
  have hinv : img.FrozenLoaded s ∧ s.symtab = img.symtab :=
    ⟨hmeta.2.2.2.2.2.2.1, hmeta.2.2.2.2.2.2.2.1⟩
  refine reaches_pc_mono
    (reaches_pc_callInv hinv (sepWP_to_reaches_pc hwp hm)) ?_
  intro sf hpc _ ⟨⟨P_f, hm_f, hpost_f⟩, h7, h8⟩
  exact hcont sf P_f hpc hpost_f ⟨h7, h8⟩ hm_f

def words4At (a w0 w1 w2 w3 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)

def words8At (a w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) : SepProp :=
  words4At a w0 w1 w2 w3 ∗ words4At (a + 32#64) w4 w5 w6 w7

def words16At (a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64) : SepProp :=
  words8At a w0 w1 w2 w3 w4 w5 w6 w7 ∗
  words8At (a + 64#64) w8 w9 w10 w11 w12 w13 w14 w15

def words32At (a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
    w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 : BitVec 64) : SepProp :=
  words16At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 ∗
  words16At (a + 128#64) w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31

theorem exists_words4_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ w0 w1 w2 w3 : BitVec 64,
      ∀ a : BitVec 64, (a ↦ₛ bs) = words4At a w0 w1 w2 w3 := by
  obtain ⟨w0, w1, w2, w3, _, hp⟩ := exists_unpack64_of_length_32 h
  refine ⟨w0, w1, w2, w3, fun a => ?_⟩
  rw [hp a]
  unfold words4At
  ac_rfl

theorem exists_words8_of_length_64 {bs : List (BitVec 8)} (h : bs.length = 64) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64,
      ∀ a : BitVec 64, (a ↦ₛ bs) = words8At a w0 w1 w2 w3 w4 w5 w6 w7 := by
  have h0 : (bs.take 32).length = 32 := by simp [h]
  have h1 : (bs.drop 32).length = 32 := by simp [h]
  obtain ⟨w0, w1, w2, w3, hp0⟩ := exists_words4_of_length_32 h0
  obtain ⟨w4, w5, w6, w7, hp1⟩ := exists_words4_of_length_32 h1
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, fun a => ?_⟩
  have hsplit : bs = bs.take 32 ++ bs.drop 32 := (List.take_append_drop 32 bs).symm
  rw [hsplit, pointsToBytes_append, h0, hp0 a, hp1 (a + 32#64)]
  rfl

theorem exists_words16_of_length_128 {bs : List (BitVec 8)} (h : bs.length = 128) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64,
      ∀ a : BitVec 64, (a ↦ₛ bs) =
        words16At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 := by
  have h0 : (bs.take 64).length = 64 := by simp [h]
  have h1 : (bs.drop 64).length = 64 := by simp [h]
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, hp0⟩ := exists_words8_of_length_64 h0
  obtain ⟨w8, w9, w10, w11, w12, w13, w14, w15, hp1⟩ := exists_words8_of_length_64 h1
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, fun a => ?_⟩
  have hsplit : bs = bs.take 64 ++ bs.drop 64 := (List.take_append_drop 64 bs).symm
  rw [hsplit, pointsToBytes_append, h0, hp0 a, hp1 (a + 64#64)]
  rfl

theorem exists_words32_of_length_256 {bs : List (BitVec 8)} (h : bs.length = 256) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 : BitVec 64,
      ∀ a : BitVec 64, (a ↦ₛ bs) =
        words32At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 := by
  have h0 : (bs.take 128).length = 128 := by simp [h]
  have h1 : (bs.drop 128).length = 128 := by simp [h]
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, hp0⟩ :=
    exists_words16_of_length_128 h0
  obtain ⟨w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, hp1⟩ :=
    exists_words16_of_length_128 h1
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
    w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, fun a => ?_⟩
  have hsplit : bs = bs.take 128 ++ bs.drop 128 := (List.take_append_drop 128 bs).symm
  rw [hsplit, pointsToBytes_append, h0, hp0 a, hp1 (a + 128#64)]
  rfl

theorem exists_word8_of_memRegion_1 {a : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ memRegion a 1 ∗ R) :
    ∃ b : BitVec 8, m ⊨ (a ↦₈ b) ∗ R := by
  rw [memRegion_eq_exists_bytes a 1 (by decide), sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨bs, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hlen, hm⟩
  rcases List.length_eq_one_iff.mp hlen with ⟨b, rfl⟩
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp] at hm
  exact ⟨b, hm⟩

theorem words4At_entails_memRegion (a w0 w1 w2 w3 : BitVec 64) :
    words4At a w0 w1 w2 w3 ⊢ memRegion a 32 := by
  unfold words4At
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion a w0)
      (sepConj_mono (pointsTo64_entails_memRegion (a + 8#64) w1)
        (sepConj_mono (pointsTo64_entails_memRegion (a + 16#64) w2)
          (pointsTo64_entails_memRegion (a + 24#64) w3)))) ?_
  rw [show a + 24#64 = (a + 16#64) + 8#64 by bv_omega,
      ← memRegion_split (a + 16#64) 8 8 (by decide),
      show a + 16#64 = (a + 8#64) + 8#64 by bv_omega,
      ← memRegion_split (a + 8#64) 8 16 (by decide),
      ← memRegion_split a 8 24 (by decide)]
  exact Entails.refl _

theorem words8At_entails_memRegion (a w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    words8At a w0 w1 w2 w3 w4 w5 w6 w7 ⊢ memRegion a 64 := by
  unfold words8At
  refine Entails.trans
    (sepConj_mono (words4At_entails_memRegion a w0 w1 w2 w3)
      (words4At_entails_memRegion (a + 32#64) w4 w5 w6 w7)) ?_
  rw [← memRegion_split a 32 32 (by decide)]
  exact Entails.refl _

theorem words16At_entails_memRegion
    (a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64) :
    words16At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 ⊢ memRegion a 128 := by
  unfold words16At
  refine Entails.trans
    (sepConj_mono (words8At_entails_memRegion a w0 w1 w2 w3 w4 w5 w6 w7)
      (words8At_entails_memRegion (a + 64#64) w8 w9 w10 w11 w12 w13 w14 w15)) ?_
  rw [← memRegion_split a 64 64 (by decide)]
  exact Entails.refl _

theorem words32At_entails_memRegion (a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
    w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 : BitVec 64) :
    words32At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ⊢ memRegion a 256 := by
  unfold words32At
  refine Entails.trans
    (sepConj_mono
      (words16At_entails_memRegion a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15)
      (words16At_entails_memRegion (a + 128#64)
        w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31)) ?_
  rw [← memRegion_split a 128 128 (by decide)]
  exact Entails.refl _

namespace BS9

end BS9

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA
