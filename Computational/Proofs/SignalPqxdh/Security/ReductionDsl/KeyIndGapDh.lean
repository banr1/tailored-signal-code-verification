/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndCore

/-!
# Costed `ReductionDsl` Reduction: `KeyInd` `GapDH`

Expresses the unified 4-leg Fiedler–Günther `GapDH` simulator `fgKeyIndGapDhAdv4` as a
`CostedReduction pqxdhOps pqGapDhIface` program in `ReductionDsl`, in both flat-indexed
(`fgKeyIndGapDhProg`) and tuple-keyed (`fgKeyIndGapDh2Prog`) forms.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyInd

section
set_option allowUnsafeReducibility true
attribute [implicit_reducible] gapDhDdhOracle
end

/-! ## `pqGapDhIface` Query and Lifting Shorthands -/

def ddhQ {Γ : List PT} (x y z : Expr pqxdhOps Γ (B 32)) : Comp pqxdhOps pqGapDhIface Γ .bool :=
  Comp.query (I := pqGapDhIface) (Sum.inr ()) (.pair x (.pair y z))

abbrev gPrim {Γ : List PT} {τ : PT} (c : Comp pqxdhOps pqPrimIface Γ τ) : Comp pqxdhOps pqGapDhIface Γ τ :=
  liftBase (C := gapDhDdhOracle) c

/-! ## Value Types and Accessors for Simulator State -/

def fePos1 {Γ : List PT} (e : Expr pqxdhOps Γ fgPatchEntryTy) : Expr pqxdhOps Γ fgPosTy := .fst e
def fePos2 {Γ : List PT} (e : Expr pqxdhOps Γ fgPatchEntryTy) : Expr pqxdhOps Γ fgPosTy := .fst (.snd e)
def fePos3 {Γ : List PT} (e : Expr pqxdhOps Γ fgPatchEntryTy) : Expr pqxdhOps Γ fgPosTy :=
  .fst (.snd (.snd e))
def fePos4 {Γ : List PT} (e : Expr pqxdhOps Γ fgPatchEntryTy) : Expr pqxdhOps Γ (.opt fgPosTy) :=
  .fst (.snd (.snd (.snd e)))
def feSs {Γ : List PT} (e : Expr pqxdhOps Γ fgPatchEntryTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd (.snd (.snd e))))
def feDk {Γ : List PT} (e : Expr pqxdhOps Γ fgPatchEntryTy) : Expr pqxdhOps Γ drKeyTy :=
  .snd (.snd (.snd (.snd (.snd e))))

def feMk {Γ : List PT} (p1 p2 p3 : Expr pqxdhOps Γ fgPosTy) (p4 : Expr pqxdhOps Γ (.opt fgPosTy))
    (ss : Expr pqxdhOps Γ (B 32)) (dk : Expr pqxdhOps Γ drKeyTy) : Expr pqxdhOps Γ fgPatchEntryTy :=
  .pair p1 (.pair p2 (.pair p3 (.pair p4 (.pair ss dk))))

/-- Fixed per-run parameters `(U, V, Up, prinFlag, prinIdx, dhFlag, ephIdx, spkIdx, opkMode, opkIdx, mode)`
encoding the active DH case (`mode ∈ {0, 1, 2, 3}` for `DH1`, `DH3`, `DH2`, `DH4`) and target indices. -/
abbrev paramsTy : PT :=
  .prod (B 32) (.prod (B 32) (.prod (B 32) (.prod .bool (.prod .nat (.prod .bool
    (.prod .nat (.prod .nat (.prod .bool (.prod .nat .nat)))))))))

def paU {Γ : List PT} (p : Expr pqxdhOps Γ paramsTy) : Expr pqxdhOps Γ (B 32) := .fst p
def paV {Γ : List PT} (p : Expr pqxdhOps Γ paramsTy) : Expr pqxdhOps Γ (B 32) := .fst (.snd p)
def paUp {Γ : List PT} (p : Expr pqxdhOps Γ paramsTy) : Expr pqxdhOps Γ (B 32) := .fst (.snd (.snd p))
def paPrinFlag {Γ : List PT} (p : Expr pqxdhOps Γ paramsTy) : Expr pqxdhOps Γ .bool :=
  .fst (.snd (.snd (.snd p)))
def paPrinIdx {Γ : List PT} (p : Expr pqxdhOps Γ paramsTy) : Expr pqxdhOps Γ .nat :=
  .fst (.snd (.snd (.snd (.snd p))))
def paDhFlag {Γ : List PT} (p : Expr pqxdhOps Γ paramsTy) : Expr pqxdhOps Γ .bool :=
  .fst (.snd (.snd (.snd (.snd (.snd p)))))
def paEphIdx {Γ : List PT} (p : Expr pqxdhOps Γ paramsTy) : Expr pqxdhOps Γ .nat :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd p))))))
def paSpkIdx {Γ : List PT} (p : Expr pqxdhOps Γ paramsTy) : Expr pqxdhOps Γ .nat :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd p)))))))
def paOpkMode {Γ : List PT} (p : Expr pqxdhOps Γ paramsTy) : Expr pqxdhOps Γ .bool :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd p))))))))
def paOpkIdx {Γ : List PT} (p : Expr pqxdhOps Γ paramsTy) : Expr pqxdhOps Γ .nat :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd p)))))))))
def paMode {Γ : List PT} (p : Expr pqxdhOps Γ paramsTy) : Expr pqxdhOps Γ .nat :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd p)))))))))

def paMk {Γ : List PT} (U V Up : Expr pqxdhOps Γ (B 32)) (pf : Expr pqxdhOps Γ .bool)
    (pi : Expr pqxdhOps Γ .nat) (df : Expr pqxdhOps Γ .bool) (ei si : Expr pqxdhOps Γ .nat)
    (om : Expr pqxdhOps Γ .bool) (oi md : Expr pqxdhOps Γ .nat) : Expr pqxdhOps Γ paramsTy :=
  .pair U (.pair V (.pair Up (.pair pf (.pair pi (.pair df (.pair ei (.pair si
    (.pair om (.pair oi md)))))))))

/-- Encoding of `FgKeyIndSimState S`: `(base, fgL, rawRoCache, advRoLog, advKeyPows)`. -/
abbrev simTy : PT :=
  .prod keyIndStateTy
    (.prod (.list fgPatchEntryTy)
      (.prod (.list (.prod (B 192) drKeyTy))
        (.prod (.list (B 192))
          (.list (.prod (B 32) (B 32))))))

def smBase {Γ : List PT} (s : Expr pqxdhOps Γ simTy) : Expr pqxdhOps Γ keyIndStateTy := .fst s
def smFgL {Γ : List PT} (s : Expr pqxdhOps Γ simTy) : Expr pqxdhOps Γ (.list fgPatchEntryTy) :=
  .fst (.snd s)
def smRaw {Γ : List PT} (s : Expr pqxdhOps Γ simTy) :
    Expr pqxdhOps Γ (.list (.prod (B 192) drKeyTy)) := .fst (.snd (.snd s))
def smLog {Γ : List PT} (s : Expr pqxdhOps Γ simTy) : Expr pqxdhOps Γ (.list (B 192)) :=
  .fst (.snd (.snd (.snd s)))
def smPows {Γ : List PT} (s : Expr pqxdhOps Γ simTy) :
    Expr pqxdhOps Γ (.list (.prod (B 32) (B 32))) := .snd (.snd (.snd (.snd s)))

def smMk {Γ : List PT} (base : Expr pqxdhOps Γ keyIndStateTy)
    (fgL : Expr pqxdhOps Γ (.list fgPatchEntryTy))
    (raw : Expr pqxdhOps Γ (.list (.prod (B 192) drKeyTy)))
    (log : Expr pqxdhOps Γ (.list (B 192)))
    (pows : Expr pqxdhOps Γ (.list (.prod (B 32) (B 32)))) : Expr pqxdhOps Γ simTy :=
  .pair base (.pair fgL (.pair raw (.pair log pows)))

def smUpd {Γ : List PT} (s : Expr pqxdhOps Γ simTy)
    (base : Expr pqxdhOps Γ keyIndStateTy := smBase s)
    (fgL : Expr pqxdhOps Γ (.list fgPatchEntryTy) := smFgL s)
    (raw : Expr pqxdhOps Γ (.list (.prod (B 192) drKeyTy)) := smRaw s)
    (log : Expr pqxdhOps Γ (.list (B 192)) := smLog s)
    (pows : Expr pqxdhOps Γ (.list (.prod (B 32) (B 32))) := smPows s) : Expr pqxdhOps Γ simTy :=
  smMk base fgL raw log pows

abbrev gdhStateTy : PT := .prod paramsTy simTy

def simStateToVal {S : Setup} (st : FgKeyIndSimState S) : simTy.denote :=
  (keyIndStateToVal st.base, (st.fgL.map fgPatchEntryToVal,
    (st.rawRoCache.map (Prod.map id drKeyToVal), (st.advRoLog, st.advKeyPows))))

/-! ## DDH-Consistency Table Helpers -/

def mkSecretPosC {Γ : List PT} (z : Expr pqxdhOps Γ (B 32)) : Comp pqxdhOps pqGapDhIface Γ fgPosTy :=
  letV z fun zV =>
  bindV (gPrim (qIsCanonical (v zV))) fun c => .ret (.inl (.pair (v zV) (v c)))

def mkPairPosC {Γ : List PT} (pk1 pk2 : Expr pqxdhOps Γ (B 32)) : Comp pqxdhOps pqGapDhIface Γ fgPosTy :=
  letV (.pair pk1 pk2) fun pp =>
  bindV (gPrim (qPow8 (.fst (v pp)))) fun w1 =>
  bindV (gPrim (qPow8 (.snd (v pp)))) fun w2 =>
  .ret (.inr (.pair (.fst (v pp)) (.pair (.snd (v pp)) (.pair (v w1) (v w2)))))

def computePosC {Γ : List PT} (sk1 sk2 pk1 pk2 : Expr pqxdhOps Γ (B 32)) :
    Comp pqxdhOps pqGapDhIface Γ fgPosTy :=
  .ite (.not (natEq (lenB sk1) (.nat 0)))
    (bindV (gPrim (qX25519 (.pair sk1 pk2))) fun z => mkSecretPosC (v z))
    (.ite (.not (natEq (lenB sk2) (.nat 0)))
      (bindV (gPrim (qX25519 (.pair sk2 pk1))) fun z => mkSecretPosC (v z))
      (mkPairPosC pk1 pk2))

def computeOptPosInitC {Γ : List PT} (sk1 pk1 : Expr pqxdhOps Γ (B 32))
    (opkB? : Expr pqxdhOps Γ (.opt (.prod U32 (B 32)))) :
    Comp pqxdhOps pqGapDhIface Γ (.opt fgPosTy) :=
  letV (.pair (.pair sk1 pk1) opkB?) fun spo =>
  caseOptV (.snd (v spo)) (.ret .none) fun p =>
    bindV (computePosC (.fst (.fst (v spo))) (litB 32 []) (.snd (.fst (v spo))) (.snd (v p)))
      fun pos => .ret (.some (v pos))

def ddhEqC {Γ : List PT} (p1 p2 : Expr pqxdhOps Γ fgPosTy) : Comp pqxdhOps pqGapDhIface Γ .bool :=
  letV (.pair p1 p2) fun pp =>
  caseSumV (.fst (v pp))
    (fun s1 =>
      caseSumV (.snd (v pp))
        (fun s2 => .ret (eqB (.fst (v s1)) (.fst (v s2))))
        (fun q2 =>
          .ite (.snd (v s1))
            (ddhQ (.fst (v q2)) (.fst (.snd (v q2))) (.fst (v s1)))
            (.ret (.bool false))))
    (fun q1 =>
      caseSumV (.snd (v pp))
        (fun s2 =>
          .ite (.snd (v s2))
            (ddhQ (.fst (v q1)) (.fst (.snd (v q1))) (.fst (v s2)))
            (.ret (.bool false)))
        (fun q2 =>
          let w1 := .fst (.snd (.snd (v q1)))
          let w2 := .snd (.snd (.snd (v q1)))
          let w3 := .fst (.snd (.snd (v q2)))
          let w4 := .snd (.snd (.snd (v q2)))
          .ret (orE (.and (eqB w1 w3) (eqB w2 w4)) (.and (eqB w1 w4) (eqB w2 w3)))))

def ddhEqOptC {Γ : List PT} (p1? p2? : Expr pqxdhOps Γ (.opt fgPosTy)) :
    Comp pqxdhOps pqGapDhIface Γ .bool :=
  letV (.pair p1? p2?) fun pp =>
  caseOptV (.fst (v pp))
    (caseOptV (.snd (v pp)) (.ret (.bool true)) fun _ => .ret (.bool false))
    fun p1 =>
      caseOptV (.snd (v pp)) (.ret (.bool false)) fun p2 =>
        ddhEqC (v p1) (v p2)

def entryMatchesC {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32))
    (e : Var Δ fgPatchEntryTy) : Comp pqxdhOps pqGapDhIface Δ .bool :=
  .ite (.not (eqB (v ss) (feSs (v e))))
    (.ret (.bool false))
    (bindV (ddhEqC (v pos1) (fePos1 (v e))) fun b1 =>
     bindV (ddhEqC (v pos2) (fePos2 (v e))) fun b2 =>
     bindV (ddhEqC (v pos3) (fePos3 (v e))) fun b3 =>
     bindV (ddhEqOptC (v pos4?) (fePos4 (v e))) fun b4 =>
     .ret (.and (.and (.and (v b1) (v b2)) (v b3)) (v b4)))

def fgPatchC (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32))
    (fgL : Expr pqxdhOps Δ (.list fgPatchEntryTy)) :
    Comp pqxdhOps pqGapDhIface Δ (.prod drKeyTy (.list fgPatchEntryTy)) :=
  letV fgL fun lV =>
  bindV (findMV K (v lV) fun e => entryMatchesC pos1 pos2 pos3 pos4? ss e) fun found =>
  caseOptV (v found)
    (bindV (gPrim sDrKey96) fun dk =>
     .ret (.pair (v dk) (.cons (feMk (v pos1) (v pos2) (v pos3) (v pos4?) (v ss) (v dk)) (v lV))))
    fun e => .ret (.pair (feDk (v e)) (v lV))

/-! ## KOSK and Partner Helpers -/

def isAdvPowsE (K : Nat) {Γ : List PT} (pows : Expr pqxdhOps Γ (.list (.prod (B 32) (B 32))))
    (wPk : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ .bool :=
  eLet (.pair pows wPk) fun pw => eAny K (.fst (v pw)) fun p => eqB (.snd (v p)) (.snd (v pw))

def koskSenderOkPowsC (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (pows : Expr pqxdhOps Δ (.list (.prod (B 32) (B 32))))
    (ik : Expr pqxdhOps Δ (B 32)) : Comp pqxdhOps pqPrimIface Δ .bool :=
  letV (.pair pows ik) fun pi =>
  bindV (findHonestC S K st (.snd (v pi))) fun hp =>
  bindV (qPow8 (.snd (v pi))) fun wIk =>
  .ret (orE (isSomeE (v hp)) (isAdvPowsE K (.fst (v pi)) (v wIk)))

def koskBundleOkPowsC (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st : Var Γ₁ keyIndStateTy) (pows : Expr pqxdhOps Δ (.list (.prod (B 32) (B 32))))
    (bu : Var Γ₂ preKeyBundleTy) : Comp pqxdhOps pqPrimIface Δ .bool :=
  letV pows fun pV =>
  bindV (findHonestC S K st (buIkB (v bu))) fun hp =>
  bindV (qPow8 (buIkB (v bu))) fun wIk =>
  bindV (isGameSpkC S K st (buSpkB (v bu))) fun gSpk =>
  bindV (qPow8 (buSpkB (v bu))) fun wSpk =>
  bindV (caseOptV (buOpkB (v bu)) (.ret (.bool true)) fun opk =>
    bindV (isGameOpkC S K st (.snd (v opk))) fun gOpk =>
    bindV (qPow8 (.snd (v opk))) fun wOpk =>
    .ret (orE (v gOpk) (isAdvPowsE K (v pV) (v wOpk)))) fun opkOk =>
  .ret (.and
    (.and (orE (isSomeE (v hp)) (isAdvPowsE K (v pV) (v wIk)))
          (orE (v gSpk) (isAdvPowsE K (v pV) (v wSpk))))
    (v opkOk))

def lookupSpkSkC (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (pows : Expr pqxdhOps Δ (.list (.prod (B 32) (B 32))))
    (spkPk : Expr pqxdhOps Δ (B 32)) : Comp pqxdhOps pqPrimIface Δ (B 32) :=
  letV (.pair pows spkPk) fun ps =>
  bindV (qPow8 (.snd (v ps))) fun wSpk =>
  bindV (findMV (min K S.N_dh) (stSpks (v st)) fun sb =>
    bindV (qPow8 (sbSpkPk (.snd (v sb)))) fun p1 =>
    .ret (eqB (v p1) (v wSpk))) fun foundSpk =>
  .ret (eCaseOpt (v foundSpk)
    (eCaseOpt (eFind K (.fst (v ps)) fun p => eqB (.snd (v p)) (v wSpk))
      (litB 32 [])
      fun p => .fst (v p))
    fun sb => sbSpkSk (.snd (v sb)))

def chooseRespRandC (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (r : Var Δ keyIndRespEntryTy) : Comp pqxdhOps pqGapDhIface Δ drKeyTy :=
  bindV (gPrim (findMV (min K S.N_dh) (stSess (v st)) fun s => partnerC s r)) fun f =>
  caseOptV (v f) (gPrim sDrKey96) fun s => .ret (seDrRand (v s))

def chooseInitRandC (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (s : Var Δ keyIndSessionEntryTy) : Comp pqxdhOps pqGapDhIface Δ drKeyTy :=
  bindV (gPrim (findMV (min K S.N_sess_tot) (stResps (v st)) fun r => partnerC s r)) fun f =>
  caseOptV (v f) (gPrim sDrKey96) fun r => .ret (reDrRand (v r))

/-! ## Index Arithmetic and Byte-Slice Helpers -/

def spkFlatIdxE (S : Setup) {Γ : List PT} (u j : Expr pqxdhOps Γ .nat) : Expr pqxdhOps Γ .nat :=
  .add (mulRight u (Nat.min S.N_recv S.N_spk_tot)) j

def opkFlatIdxE (S : Setup) {Γ : List PT} (u j o : Expr pqxdhOps Γ .nat) : Expr pqxdhOps Γ .nat :=
  .add (mulRight (spkFlatIdxE S u j) (Nat.min S.N_opk S.N_opk_tot)) o

def initSlotIdxE (S : Setup) {Γ : List PT} (sid : Expr pqxdhOps Γ sessionIdTy) : Expr pqxdhOps Γ .nat :=
  eCaseSum sid
    (fun ui => .add (mulRight (.fst (v ui)) (Nat.min S.N_send_opk S.N_send_opk_tot)) (.snd (v ui)))
    fun s1 => eCaseSum (v s1)
      (fun ui => .add (.nat S.N_send_opk_tot)
        (.add (mulRight (.fst (v ui)) (Nat.min S.N_send_no_opk S.N_send_no_opk_tot)) (.snd (v ui))))
      fun _ => .nat S.N_send_tot

def respBundleKeyE {Γ : List PT} (sid : Expr pqxdhOps Γ sessionIdTy) :
    Expr pqxdhOps Γ (.prod .nat .nat) :=
  eCaseSum sid
    (fun ui => .pair (.fst (v ui)) (.nat 0))
    fun s1 => eCaseSum (v s1)
      (fun ui => .pair (.fst (v ui)) (.nat 0))
      fun s2 => eCaseSum (v s2)
        (fun kjo => .pair (.fst (v kjo)) (.fst (.snd (v kjo))))
        (fun kjl => .pair (.fst (v kjl)) (.fst (.snd (v kjl))))

def slice32 {Γ : List PT} (off : Nat) (bs : Expr pqxdhOps Γ (B 192)) : Expr pqxdhOps Γ (B 32) :=
  takeKB 192 32 (dropB (.nat off) bs)

/-! ## Random-Oracle Handler -/

def roRawFallbackC (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (sm : Var Γ₁ simTy) (sec : Var Γ₂ (B 192)) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy) :=
  caseOptV (eFind K (smRaw (v sm)) fun p => eqB (.fst (v p)) (v sec))
    (bindV (gPrim sDrKey96) fun dk =>
     .ret (.pair (rDrKey (v dk))
       (smUpd (v sm) (raw := .cons (.pair (v sec) (v dk)) (smRaw (v sm)))
         (log := .cons (v sec) (smLog (v sm))))))
    fun p =>
      .ret (.pair (rDrKey (.snd (v p))) (smUpd (v sm) (log := .cons (v sec) (smLog (v sm)))))

def roParsedC (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (sm : Var Γ₁ simTy) (sec : Var Γ₂ (B 192)) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy) :=
  .ite (.not (eqB (takeKB 192 32 (v sec)) (litB 32 F_X25519)))
    (roRawFallbackC K sm sec)
    (.ite (natEq (lenB (v sec)) (.nat 160))
      (bindV (mkSecretPosC (slice32 32 (v sec))) fun p1 =>
       bindV (mkSecretPosC (slice32 64 (v sec))) fun p2 =>
       bindV (mkSecretPosC (slice32 96 (v sec))) fun p3 =>
       letV (.none (t := fgPosTy)) fun p4 =>
       letV (slice32 128 (v sec)) fun ss =>
       bindV (fgPatchC K p1 p2 p3 p4 ss (smFgL (v sm))) fun res =>
       .ret (.pair (rDrKey (.fst (v res)))
         (smUpd (v sm) (fgL := .snd (v res)) (log := .cons (v sec) (smLog (v sm))))))
      (.ite (natEq (lenB (v sec)) (.nat 192))
        (bindV (mkSecretPosC (slice32 32 (v sec))) fun p1 =>
         bindV (mkSecretPosC (slice32 64 (v sec))) fun p2 =>
         bindV (mkSecretPosC (slice32 96 (v sec))) fun p3 =>
         bindV (mkSecretPosC (slice32 128 (v sec))) fun p4Raw =>
         letV (.some (v p4Raw)) fun p4 =>
         letV (slice32 160 (v sec)) fun ss =>
         bindV (fgPatchC K p1 p2 p3 p4 ss (smFgL (v sm))) fun res =>
         .ret (.pair (rDrKey (.fst (v res)))
           (smUpd (v sm) (fgL := .snd (v res)) (log := .cons (v sec) (smLog (v sm))))))
        (roRawFallbackC K sm sec)))

/-! ## Simulator Query Branches -/

def wrapBase {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy gdhStateTy) :=
  bindV (gPrim c) fun r =>
  .ret (.pair (.fst (v r)) (.pair (v pa) (smUpd (v sm) (base := .snd (v r)))))

def wrapSim {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ paramsTy)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy gdhStateTy) :=
  bindV c fun r => .ret (.pair (.fst (v r)) (.pair (v pa) (.snd (v r))))

def initPrinGdhB (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (u : Var Γ₄ .nat) : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy) :=
  .ite (eAny K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (v u))
    (.ret (.pair rNone (v sm)))
    (letV (.and (paPrinFlag (v pa)) (natEq (v u) (paPrinIdx (v pa)))) fun isT =>
     bindV (gPrim sBytes32) fun sk0 =>
     bindV (gPrim (qX25519Base (v sk0))) fun pk0 =>
     bindV (gPrim sBytes32) fun skS =>
     bindV (gPrim (qSigPkGen (v skS))) fun pkS =>
     letV (.ite (v isT) (litB 32 []) (v sk0)) fun sec0 =>
     letV (.ite (v isT) (paUp (v pa)) (v pk0)) fun ikPk =>
     let e := peMk (v sec0) (v ikPk) (v skS) (v pkS) (.bool false)
     let bSt' := stUpd (v bSt) (prin := .cons (.pair (v u) e) (stPrin (v bSt)))
     .ret (.pair (rInitPrin (v ikPk) (v pkS)) (smUpd (v sm) (base := bSt'))))

def genSpkGdhB (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ (.prod .nat .nat)) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy) :=
  .ite (eAny K (stSpks (v bSt)) fun p => nat2Eq (.fst (v p)) (v x))
    (.ret (.pair rNone (v sm)))
    (caseOptV (eFind K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (.fst (v x)))
      (.ret (.pair rNone (v sm)))
      fun ue =>
        letV (natEq (spkFlatIdxE S (.fst (v x)) (.snd (v x))) (paSpkIdx (v pa))) fun isT =>
        bindV (gPrim sBytes32) fun spkSkRaw =>
        bindV (gPrim (qX25519Base (v spkSkRaw))) fun spkPkRaw =>
        letV (.ite (v isT) (litB 32 []) (v spkSkRaw)) fun spkSk =>
        letV (.ite (v isT) (paV (v pa)) (v spkPkRaw)) fun spkPk =>
        bindV (gPrim sRandom64) fun rSpk =>
        bindV (gPrim (qSigSign 33 (.pair (peSecIKAsign (.snd (v ue)))
          (.pair (encEC (v spkPk)) (v rSpk))))) fun spkSig =>
        bindV (gPrim sRandom64) fun seed =>
        bindV (gPrim (qKemKeyGen (v seed))) fun kp =>
        bindV (gPrim sRandom64) fun rPq =>
        bindV (qSigSign 1569 (.pair (peSecIKAsign (.snd (v ue)))
          (.pair (encKEM (.fst (v kp))) (v rPq))) |> gPrim) fun pqSig =>
        let jId := u32OfNat (.snd (v x))
        let bE := sbMk (v spkSk) (v spkPk) (v spkSig)
          (.snd (v kp)) (.fst (v kp)) (v pqSig) (.bool false)
        let buOut := buMk (peIkAPk (.snd (v ue))) jId (v spkPk) (v spkSig)
          .none jId (.fst (v kp)) (v pqSig)
        let bSt' := stUpd (v bSt) (spks := .cons (.pair (v x) bE) (stSpks (v bSt)))
        .ret (.pair (rBundle buOut) (smUpd (v sm) (base := bSt'))))

def genOpkGdhB (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ (.prod .nat (.prod .nat .nat))) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy) :=
  .ite (eAny K (stOpks (v bSt)) fun p => nat3Eq (.fst (v p)) (v x))
    (.ret (.pair rNone (v sm)))
    (letV (.and (paOpkMode (v pa))
      (natEq (opkFlatIdxE S (.fst (v x)) (.fst (.snd (v x))) (.snd (.snd (v x))))
        (paOpkIdx (v pa)))) fun isT =>
     bindV (gPrim sBytes32) fun opkSkRaw =>
     bindV (gPrim (qX25519Base (v opkSkRaw))) fun opkPkRaw =>
     letV (.ite (v isT) (litB 32 []) (v opkSkRaw)) fun opkSk =>
     letV (.ite (v isT) (paV (v pa)) (v opkPkRaw)) fun opkPk =>
     let oE := oeMk (v opkSk) (v opkPk) (.bool false)
     let bSt' := stUpd (v bSt) (opks := .cons (.pair (v x) oE) (stOpks (v bSt)))
     .ret (.pair (rPk (v opkPk)) (smUpd (v sm) (base := bSt'))))

def initiateGdhB (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (hasOpk : Bool) (x : Var Γ₄ initQTy) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy) :=
  letV (.snd (.snd (v x))) fun bu =>
  let guardOk := if hasOpk then isSomeE (buOpkB (v bu)) else .not (isSomeE (buOpkB (v bu)))
  .ite (.not guardOk) (.ret (.pair rNone (v sm)))
    (letV (initSidE hasOpk (v x)) fun sid =>
     .ite (eAny K (stSess (v bSt)) fun s => sidEq (seSid (v s)) (v sid))
       (.ret (.pair rNone (v sm)))
       (caseOptV (eFind K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (.fst (v x)))
         (.ret (.pair rNone (v sm)))
         fun ue =>
           bindV (gPrim (koskBundleOkPowsC S K bSt (smPows (v sm)) bu)) fun ok =>
           .ite (.not (v ok)) (.ret (.pair rNone (v sm)))
             (letV (.and (.not (paDhFlag (v pa)))
               (natEq (initSlotIdxE S (v sid)) (paEphIdx (v pa)))) fun isTE =>
              bindV (gPrim sBytes32) fun ekSkRaw =>
              bindV (gPrim sBytes32) fun coins =>
              bindV (gPrim (resolveSigPkC S K bSt (buIkB (v bu)))) fun sigPk =>
              bindV (gPrim (qSigVerify 33 (.pair (v sigPk)
                (.pair (encEC (buSpkB (v bu))) (buSpkSig (v bu)))))) fun v1 =>
              bindV (gPrim (qSigVerify 1569 (.pair (v sigPk)
                (.pair (encKEM (buPqspkB (v bu))) (buPqspkSig (v bu)))))) fun v2 =>
              .ite (.not (.and (v v1) (v v2))) (.ret (.pair rNone (v sm)))
                (bindV (gPrim (qKemEncaps (.pair (buPqspkB (v bu)) (v coins)))) fun krOpt =>
                 caseOptV (v krOpt) (.ret (.pair rNone (v sm))) fun kr =>
                   bindV (gPrim (qX25519Base (v ekSkRaw))) fun ekPkRaw =>
                   letV (.ite (v isTE) (litB 32 []) (v ekSkRaw)) fun ekSk =>
                   letV (.ite (v isTE) (paU (v pa)) (v ekPkRaw)) fun ekPk =>
                   bindV (gPrim (lookupSpkSkC S K bSt (smPows (v sm)) (buSpkB (v bu))))
                     fun spkSk =>
                   bindV (computePosC (peSecIKA0 (.snd (v ue))) (v spkSk)
                     (peIkAPk (.snd (v ue))) (buSpkB (v bu))) fun p1 =>
                   bindV (computePosC (v ekSk) (litB 32 []) (v ekPk) (buIkB (v bu))) fun p2 =>
                   bindV (computePosC (v ekSk) (litB 32 []) (v ekPk) (buSpkB (v bu))) fun p3 =>
                   bindV (computeOptPosInitC (v ekSk) (v ekPk) (buOpkB (v bu))) fun p4 =>
                   letV (.fst (v kr)) fun ss =>
                   bindV (fgPatchC K p1 p2 p3 p4 ss (smFgL (v sm))) fun patchR =>
                   letV (.fst (v patchR)) fun dkReal =>
                   letV (.snd (v patchR)) fun fgL' =>
                   letV (hdMk (peIkAPk (.snd (v ue))) (v ekPk) (buSpkId (v bu))
                     (optFst (buOpkB (v bu))) (buPqspkId (v bu)) (.snd (v kr))) fun hdr =>
                   bindV (gPrim (honestPeerC S K bSt (buIkB (v bu)))) fun hp =>
                   bindV (gPrim (checkProvC S K bSt bu)) fun prov =>
                   letV (seMk (v sid) (v hp) (buIkB (v bu)) (buSpkB (v bu))
                     (optSnd (buOpkB (v bu))) (buPqspkB (v bu)) (.fst (v prov))
                     (.fst (.snd (v prov))) (.snd (.snd (v prov))) (v ekSk)
                     (isSomeE (v hp)) (v dkReal) (v dkReal) (v hdr)
                     (.bool false) (.bool false)) fun sInit =>
                   bindV (chooseInitRandC S K bSt sInit) fun dkRand =>
                   let sFinal := seUpd (v sInit) (drRand := v dkRand)
                   let bSt' := stUpd (v bSt) (sess := .cons sFinal (stSess (v bSt)))
                   letV (smUpd (v sm) (base := bSt') (fgL := v fgL')) fun smV =>
                   bindV (gPrim (findHonestC S K bSt (buIkB (v bu)))) fun fh =>
                   .ret (eCaseOpt (v fh)
                     (.pair (rInitUnfresh (v dkReal) (v hdr)) (v smV))
                     fun _ => .pair (rHdr (v hdr)) (v smV))))))

def finishAcceptGdhC (S : Setup) (K : Nat)
    {Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Δ : List PT}
    [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    [Ext Γ₅ Δ] [Ext Γ₆ Δ] [Ext Γ₇ Δ]
    (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (hasOpk : Bool) (x : Var Γ₄ accQTy)
    (ke : Var Γ₅ (.prod .nat principalEntryTy))
    (be : Var Γ₆ (.prod (.prod .nat .nat) spkBundleEntryTy))
    (opkPkOpt : Expr pqxdhOps Δ (.opt (B 32)))
    (opks' : Expr pqxdhOps Δ (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)))
    (usedO' : Expr pqxdhOps Δ (.list (.prod .nat (.prod .nat .nat))))
    (usedN' : Expr pqxdhOps Δ (.list (.prod .nat (.prod .nat .nat))))
    (kyb' : Expr pqxdhOps Δ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (patchR : Var Γ₇ (.prod drKeyTy (.list fgPatchEntryTy))) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy) :=
  letV (.pair opkPkOpt (.pair opks' (.pair usedO' (.pair usedN' kyb')))) fun upd =>
  letV (.fst (v patchR)) fun dk =>
  letV (.snd (v patchR)) fun fgL' =>
  bindV (gPrim (findHonestC S K bSt (hdIkAPk (qHdr (v x))))) fun shOpt =>
  let sidE : Expr pqxdhOps _ sessionIdTy :=
    if hasOpk then .inr (.inr (.inl (qKJO (v x)))) else .inr (.inr (.inr (qKJO (v x))))
  letV (reMk sidE (peIkAPk (.snd (v ke))) (sbSpkPk (.snd (v be))) (.fst (v upd))
    (sbPqspkPk (.snd (v be))) (qHdr (v x)) (isSomeE (v shOpt))
    (v dk) (v dk) (.bool false) (.bool false)) fun rInit =>
  bindV (chooseRespRandC S K bSt rInit) fun dkRand =>
  let rFinal := reUpd (v rInit) (drRand := v dkRand)
  let bSt' := stUpd (v bSt) (opks := .fst (.snd (v upd)))
    (resps := .cons rFinal (stResps (v bSt)))
    (usedO := .fst (.snd (.snd (v upd))))
    (usedN := .fst (.snd (.snd (.snd (v upd)))))
    (kyb := .snd (.snd (.snd (.snd (v upd)))))
  letV (smUpd (v sm) (base := bSt') (fgL := v fgL')) fun smV =>
  .ret (eCaseOpt (v shOpt) (.pair (rDrKey (v dk)) (v smV)) fun _ => .pair rAccFresh (v smV))

def acceptOpkGdhB (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ accQTy) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy) :=
  let hdr := qHdr (v x)
  let guardOk := Expr.and
    (.and (.and (.and (eqU32 (hdSpkId hdr) (u32OfNat (qJ (v x))))
                      (eqU32 (hdPqspkId hdr) (u32OfNat (qJ (v x)))))
                (optU32Eq (hdOpkId hdr) (.some (u32OfNat (qO (v x))))))
          (natEq (lenB (hdIkAPk hdr)) (.nat 32)))
    (natEq (lenB (hdEkAPk hdr)) (.nat 32))
  .ite (.not guardOk) (.ret (.pair rNone (v sm)))
    (.ite (eAny K (stUsedO (v bSt)) fun u => nat3Eq (v u) (qKJO (v x)))
      (.ret (.pair rNone (v sm)))
      (bindV (gPrim (koskSenderOkPowsC S K bSt (smPows (v sm)) (hdIkAPk (qHdr (v x))))) fun sOk =>
       .ite (.not (v sOk)) (.ret (.pair rNone (v sm)))
         (caseOptV (eFind K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (qK (v x)))
           (.ret (.pair rNone (v sm)))
           fun ke =>
             caseOptV (eFind K (stSpks (v bSt)) fun p =>
               nat2Eq (.fst (v p)) (.pair (qK (v x)) (qJ (v x))))
               (.ret (.pair rNone (v sm)))
               fun be =>
                 caseOptV (eFind K (stOpks (v bSt)) fun p => nat3Eq (.fst (v p)) (qKJO (v x)))
                   (.ret (.pair rNone (v sm)))
                   fun oe =>
                     .ite (oeConsumed (.snd (v oe))) (.ret (.pair rNone (v sm)))
                       (letV (kyberCheckE K (stKyb (v bSt)) (.pair (qK (v x))
                         (.pair (hdPqspkId (qHdr (v x)))
                           (.pair (hdSpkId (qHdr (v x))) (hdEkAPk (qHdr (v x))))))) fun kybR =>
                        bindV (gPrim (qIsCanonical (hdEkAPk (qHdr (v x))))) fun canon =>
                        bindV (gPrim (qX25519 (.pair (litB 32 (List.replicate 32 0))
                          (hdIkAPk (qHdr (v x)))))) fun dh1Z =>
                        bindV (gPrim (qX25519 (.pair (litB 32 (List.replicate 32 0))
                          (hdEkAPk (qHdr (v x)))))) fun dh2Z =>
                        .ite (paOpkMode (v pa))
                          (bindV (gPrim (qKemDecaps (.pair (sbPqspkSk (.snd (v be)))
                            (hdKemCt (qHdr (v x)))))) fun ssOpt =>
                           .ite (.not (.and (.and (.and (.fst (v kybR)) (v canon))
                             (nonZero32 (v dh1Z))) (nonZero32 (v dh2Z))))
                             (.ret (.pair rNone (v sm)))
                             (caseOptV (v ssOpt) (.ret (.pair rNone (v sm))) fun ss =>
                               bindV (computePosC (litB 32 []) (sbSpkSk (.snd (v be)))
                                 (hdIkAPk (qHdr (v x))) (sbSpkPk (.snd (v be)))) fun p1 =>
                               bindV (computePosC (litB 32 []) (peSecIKA0 (.snd (v ke)))
                                 (hdEkAPk (qHdr (v x))) (peIkAPk (.snd (v ke)))) fun p2 =>
                               bindV (computePosC (litB 32 []) (sbSpkSk (.snd (v be)))
                                 (hdEkAPk (qHdr (v x))) (sbSpkPk (.snd (v be)))) fun p3 =>
                               bindV (computePosC (litB 32 []) (oeOpkSk (.snd (v oe)))
                                 (hdEkAPk (qHdr (v x))) (oeOpkPk (.snd (v oe)))) fun p4Raw =>
                               letV (.some (v p4Raw)) fun p4 =>
                               bindV (fgPatchC K p1 p2 p3 p4 ss (smFgL (v sm))) fun patchR =>
                               let opks' := eMap K (stOpks (v bSt)) fun p =>
                                 .ite (nat3Eq (.fst (v p)) (qKJO (v x)))
                                   (.pair (.fst (v p))
                                     (oeUpd (.snd (v p)) (consumed := .bool true)))
                                   (v p)
                               finishAcceptGdhC S K sm bSt true x ke be
                                 (.some (oeOpkPk (.snd (v oe)))) opks'
                                 (.cons (qKJO (v x)) (stUsedO (v bSt)))
                                 (stUsedN (v bSt)) (.snd (v kybR)) patchR))
                          (bindV (gPrim (qX25519 (.pair (oeOpkSk (.snd (v oe)))
                            (hdEkAPk (qHdr (v x)))))) fun dh4 =>
                           bindV (gPrim (qKemDecaps (.pair (sbPqspkSk (.snd (v be)))
                             (hdKemCt (qHdr (v x)))))) fun ssOpt =>
                           .ite (.not (.and (.and (.and (.and (.fst (v kybR)) (v canon))
                             (nonZero32 (v dh1Z))) (nonZero32 (v dh2Z))) (nonZero32 (v dh4))))
                             (.ret (.pair rNone (v sm)))
                             (caseOptV (v ssOpt) (.ret (.pair rNone (v sm))) fun ss =>
                               bindV (computePosC (litB 32 []) (sbSpkSk (.snd (v be)))
                                 (hdIkAPk (qHdr (v x))) (sbSpkPk (.snd (v be)))) fun p1 =>
                               bindV (computePosC (litB 32 []) (peSecIKA0 (.snd (v ke)))
                                 (hdEkAPk (qHdr (v x))) (peIkAPk (.snd (v ke)))) fun p2 =>
                               bindV (computePosC (litB 32 []) (sbSpkSk (.snd (v be)))
                                 (hdEkAPk (qHdr (v x))) (sbSpkPk (.snd (v be)))) fun p3 =>
                               bindV (mkSecretPosC (v dh4)) fun p4Raw =>
                               letV (.some (v p4Raw)) fun p4 =>
                               bindV (fgPatchC K p1 p2 p3 p4 ss (smFgL (v sm))) fun patchR =>
                               let opks' := eMap K (stOpks (v bSt)) fun p =>
                                 .ite (nat3Eq (.fst (v p)) (qKJO (v x)))
                                   (.pair (.fst (v p))
                                     (oeUpd (.snd (v p)) (consumed := .bool true)))
                                   (v p)
                               finishAcceptGdhC S K sm bSt true x ke be
                                 (.some (oeOpkPk (.snd (v oe)))) opks'
                                 (.cons (qKJO (v x)) (stUsedO (v bSt)))
                                 (stUsedN (v bSt)) (.snd (v kybR)) patchR))))))

def acceptNoOpkGdhB (S : Setup) (K : Nat) {Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ accQTy) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy) :=
  let hdr := qHdr (v x)
  let guardOk := Expr.and
    (.and (.and (.and (eqU32 (hdSpkId hdr) (u32OfNat (qJ (v x))))
                      (eqU32 (hdPqspkId hdr) (u32OfNat (qJ (v x)))))
                (optU32Eq (hdOpkId hdr) .none))
          (natEq (lenB (hdIkAPk hdr)) (.nat 32)))
    (natEq (lenB (hdEkAPk hdr)) (.nat 32))
  .ite (.not guardOk) (.ret (.pair rNone (v sm)))
    (.ite (eAny K (stUsedN (v bSt)) fun u => nat3Eq (v u) (qKJO (v x)))
      (.ret (.pair rNone (v sm)))
      (bindV (gPrim (koskSenderOkPowsC S K bSt (smPows (v sm)) (hdIkAPk (qHdr (v x))))) fun sOk =>
       .ite (.not (v sOk)) (.ret (.pair rNone (v sm)))
         (caseOptV (eFind K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (qK (v x)))
           (.ret (.pair rNone (v sm)))
           fun ke =>
             caseOptV (eFind K (stSpks (v bSt)) fun p =>
               nat2Eq (.fst (v p)) (.pair (qK (v x)) (qJ (v x))))
               (.ret (.pair rNone (v sm)))
               fun be =>
                 letV (kyberCheckE K (stKyb (v bSt)) (.pair (qK (v x))
                   (.pair (hdPqspkId (qHdr (v x)))
                     (.pair (hdSpkId (qHdr (v x))) (hdEkAPk (qHdr (v x))))))) fun kybR =>
                 bindV (gPrim (qIsCanonical (hdEkAPk (qHdr (v x))))) fun canon =>
                 bindV (gPrim (qX25519 (.pair (litB 32 (List.replicate 32 0))
                   (hdIkAPk (qHdr (v x)))))) fun dh1Z =>
                 bindV (gPrim (qX25519 (.pair (litB 32 (List.replicate 32 0))
                   (hdEkAPk (qHdr (v x)))))) fun dh2Z =>
                 bindV (gPrim (qKemDecaps (.pair (sbPqspkSk (.snd (v be)))
                   (hdKemCt (qHdr (v x)))))) fun ssOpt =>
                 .ite (.not (.and (.and (.and (.fst (v kybR)) (v canon))
                   (nonZero32 (v dh1Z))) (nonZero32 (v dh2Z))))
                   (.ret (.pair rNone (v sm)))
                   (caseOptV (v ssOpt) (.ret (.pair rNone (v sm))) fun ss =>
                     bindV (computePosC (litB 32 []) (sbSpkSk (.snd (v be)))
                       (hdIkAPk (qHdr (v x))) (sbSpkPk (.snd (v be)))) fun p1 =>
                     bindV (computePosC (litB 32 []) (peSecIKA0 (.snd (v ke)))
                       (hdEkAPk (qHdr (v x))) (peIkAPk (.snd (v ke)))) fun p2 =>
                     bindV (computePosC (litB 32 []) (sbSpkSk (.snd (v be)))
                       (hdEkAPk (qHdr (v x))) (sbSpkPk (.snd (v be)))) fun p3 =>
                     letV (.none (t := fgPosTy)) fun p4 =>
                     bindV (fgPatchC K p1 p2 p3 p4 ss (smFgL (v sm))) fun patchR =>
                     finishAcceptGdhC S K sm bSt false x ke be
                       .none (stOpks (v bSt)) (stUsedO (v bSt))
                       (.cons (qKJO (v x)) (stUsedN (v bSt))) (.snd (v kybR)) patchR))))

def registerGdhB {Γ₂ Γ₃ Γ₄ Δ : List PT} [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy) (sk : Var Γ₄ (B 32)) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy) :=
  .ite (.not (natEq (lenB (v sk)) (.nat 32)))
    (.ret (.pair rNone (v sm)))
    (bindV (gPrim (qX25519Base (v sk))) fun pk =>
     bindV (gPrim (qPow8 (v pk))) fun wPk =>
     let bSt' := stUpd (v bSt) (adv := .cons (.pair (v sk) (v pk)) (stAdv (v bSt)))
     let pows' := .cons (.pair (v sk) (v wPk)) (smPows (v sm))
     .ret (.pair (rPk (v pk)) (smUpd (v sm) (base := bSt') (pows := pows'))))

/-! ## Query Dispatcher -/

/-- Full 14-constructor `KeyIndQuery` handler for `fgKeyIndGapDhProg`. -/
def gdhHandle (S : Setup) (K : Nat) :
    Comp pqxdhOps pqGapDhIface [gdhStateTy, keyIndQueryTy] (.prod keyIndRespTy gdhStateTy) :=
  let st : Var [gdhStateTy, keyIndQueryTy] gdhStateTy := .zero
  let q : Var [gdhStateTy, keyIndQueryTy] keyIndQueryTy := .succ .zero
  letV (.fst (v st)) fun pa =>
  letV (.snd (v st)) fun sm =>
  letV (smBase (v sm)) fun bSt =>
  caseSumV (v q) (fun u => wrapSim pa (initPrinGdhB K pa sm bSt u)) fun r1 =>
  caseSumV (v r1) (fun u => wrapBase pa sm (corruptB K bSt u)) fun r2 =>
  caseSumV (v r2) (fun x => wrapSim pa (genSpkGdhB S K pa sm bSt x)) fun r3 =>
  caseSumV (v r3) (fun x => wrapSim pa (genOpkGdhB S K pa sm bSt x)) fun r4 =>
  caseSumV (v r4) (fun x => wrapSim pa (initiateGdhB S K pa sm bSt true x)) fun r5 =>
  caseSumV (v r5) (fun x => wrapSim pa (initiateGdhB S K pa sm bSt false x)) fun r6 =>
  caseSumV (v r6) (fun x => wrapSim pa (acceptOpkGdhB S K pa sm bSt x)) fun r7 =>
  caseSumV (v r7) (fun x => wrapSim pa (acceptNoOpkGdhB S K sm bSt x)) fun r8 =>
  caseSumV (v r8) (fun sid => wrapBase pa sm (testB K bSt sid)) fun r9 =>
  caseSumV (v r9) (fun sec => wrapSim pa (roParsedC K sm sec)) fun r10 =>
  caseSumV (v r10) (fun _ => .ret (.pair rNone (v st))) fun r11 =>
  caseSumV (v r11) (fun sid => wrapBase pa sm (revealB K bSt sid)) fun r12 =>
  caseSumV (v r12) (fun sk => wrapSim pa (registerGdhB sm bSt sk))
                   (fun x => wrapBase pa sm (revealSpkB K bSt x))

/-! ## CDH Extractor -/

/-- Search `advRoLog` at 32-byte slice offset `off` (`32` for DH1, `64` for DH2, `96` for DH3, `128` for DH4)
for a candidate `z` satisfying `DDH(U, V, z)`. -/
def logFindC (K off : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) :
    Comp pqxdhOps pqGapDhIface Δ (B 32) :=
  let cands := eMap K (smLog (v sm)) fun sec => slice32 off (v sec)
  bindV (findMV K cands fun z => ddhQ (paU (v pa)) (paV (v pa)) (v z)) fun found =>
  .ret (eCaseOpt (v found) (litB 32 (List.replicate 32 0)) fun z => v z)

def spkPowsC (S : Setup) (K : Nat) {Γ : List PT} (spks : Expr pqxdhOps Γ
    (.list (.prod (.prod .nat .nat) spkBundleEntryTy))) :
    Comp pqxdhOps pqGapDhIface Γ (.list (.prod (B 32) (B 32))) :=
  mapMV (min K S.N_dh) spks fun sb =>
    bindV (gPrim (qPow8 (sbSpkPk (.snd (v sb))))) fun w =>
    .ret (.pair (sbSpkSk (.snd (v sb))) (v w))

def lookupFromPowsE (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (spkPows : Var Γ₁ (.list (.prod (B 32) (B 32))))
    (advPows : Var Γ₂ (.list (.prod (B 32) (B 32))))
    (wSpk : Var Δ (B 32)) : Expr pqxdhOps Δ (B 32) :=
  eCaseOpt (eFind (min K S.N_dh) (v spkPows) fun p => eqB (.snd (v p)) (v wSpk))
    (eCaseOpt (eFind K (v advPows) fun p => eqB (.snd (v p)) (v wSpk))
      (litB 32 [])
      fun p => .fst (v p))
    fun p => .fst (v p)

def initDh1CandC (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (spkPows : Var Γ₁ (.list (.prod (B 32) (B 32))))
    (advPows : Var Γ₂ (.list (.prod (B 32) (B 32))))
    (s : Var Δ keyIndSessionEntryTy) : Comp pqxdhOps pqGapDhIface Δ (B 32) :=
  bindV (gPrim (qPow8 (sePeerSpk (v s)))) fun wSpk =>
  let spkSk := lookupFromPowsE S K spkPows advPows wSpk
  gPrim (qX25519 (.pair spkSk (hdIkAPk (seHdr (v s)))))

def respDh1CandC (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (spks : Var Γ₁ (.list (.prod (.prod .nat .nat) spkBundleEntryTy)))
    (r : Var Γ₂ keyIndRespEntryTy) : Comp pqxdhOps pqGapDhIface Δ (B 32) :=
  let spkSk := eCaseOpt (eFind (min K S.N_dh) (v spks) fun sb =>
      nat2Eq (.fst (v sb)) (respBundleKeyE (reSid (v r))))
    (litB 32 [])
    fun sb => sbSpkSk (.snd (v sb))
  gPrim (qX25519 (.pair spkSk (hdIkAPk (reHdr (v r)))))

def findMapStepC {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ paramsTy) (acc : Var Γ₂ (.opt (B 32)))
    (cand : Comp pqxdhOps pqGapDhIface Δ (B 32)) : Comp pqxdhOps pqGapDhIface Δ (.opt (B 32)) :=
  caseOptV (v acc)
    (bindV cand fun z =>
     bindV (ddhQ (paU (v pa)) (paV (v pa)) (v z)) fun ok =>
     .ret (.ite (v ok) (.some (v z)) .none))
    fun _ => .ret (v acc)

def extractMode0C (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) : Comp pqxdhOps pqGapDhIface Δ (B 32) :=
  let cands := eMap K (smLog (v sm)) fun sec => slice32 32 (v sec)
  bindV (findMV K cands fun z => ddhQ (paU (v pa)) (paV (v pa)) (v z)) fun f1 =>
  caseOptV (v f1)
    (bindV (spkPowsC S K (stSpks (smBase (v sm)))) fun spkPows =>
     letV (smPows (v sm)) fun advPows =>
     bindV (foldMV (min K S.N_dh) (stSess (smBase (v sm))) .none fun s acc =>
       findMapStepC pa acc (initDh1CandC S K spkPows advPows s)) fun f2 =>
     caseOptV (v f2)
       (letV (stSpks (smBase (v sm))) fun spks =>
        bindV (foldMV (min K S.N_sess_tot) (stResps (smBase (v sm))) .none fun r acc =>
          findMapStepC pa acc (respDh1CandC S K spks r)) fun f3 =>
        .ret (eCaseOpt (v f3) (litB 32 (List.replicate 32 0)) fun z => v z))
       fun z => .ret (v z))
    fun z => .ret (v z)

/-- Full CDH extractor dispatching on `paMode pa ∈ {0, 1, 2, 3}`. -/
def gdhFinish (S : Setup) (K : Nat) :
    Comp pqxdhOps pqGapDhIface [gdhStateTy, .bool] (B 32) :=
  let st : Var [gdhStateTy, .bool] gdhStateTy := .zero
  letV (.fst (v st)) fun pa =>
  letV (.snd (v st)) fun sm =>
  .ite (natEq (paMode (v pa)) (.nat 0)) (extractMode0C S K pa sm)
    (.ite (natEq (paMode (v pa)) (.nat 1))
      (logFindC K 96 pa sm)
      (.ite (natEq (paMode (v pa)) (.nat 2))
        (logFindC K 64 pa sm)
        (logFindC K 128 pa sm)))

/-! ## Initialization and `CostedReduction` Packaging (`fgKeyIndGapDhProg`) -/

def emptySimE {Γ : List PT} (secb : Expr pqxdhOps Γ .bool) : Expr pqxdhOps Γ simTy :=
  smMk (emptyStE secb) .nil .nil .nil .nil

def initParamsDh (S : Setup) {Γ : List PT}
    (useDh1 : Expr pqxdhOps Γ .bool) (tIdx spkIdx : Expr pqxdhOps Γ .nat)
    (U V : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ paramsTy :=
  paMk U V U useDh1 tIdx useDh1 tIdx spkIdx (.bool false) (.nat S.N_opk_tot)
    (.ite useDh1 (.nat 0) (.nat 1))

def initParamsIk (S : Setup) {Γ : List PT}
    (tIdx pIdx : Expr pqxdhOps Γ .nat) (U V : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ paramsTy :=
  paMk U V V (.bool true) pIdx (.bool false) tIdx (.nat S.N_spk_tot)
    (.bool false) (.nat S.N_opk_tot) (.nat 2)

def initParamsOpk (S : Setup) {Γ : List PT}
    (tIdx oIdx : Expr pqxdhOps Γ .nat) (U V : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ paramsTy :=
  paMk U V U (.bool false) (.nat S.N_id) (.bool false) tIdx (.nat S.N_spk_tot)
    (.bool true) oIdx (.nat 3)

def initParamsFlat (S : Setup) {Γ : List PT}
    (U V : Expr pqxdhOps Γ (B 32)) (idx : Expr pqxdhOps Γ .nat) : Expr pqxdhOps Γ paramsTy :=
  let nA := S.N_id * S.N_spk_tot
  let nC := S.N_send_tot * S.N_spk_tot
  let nB := S.N_send_tot * S.N_id
  .ite (.lt idx (.nat nA))
    (initParamsDh S (.bool true)
      (.divK S.N_spk_tot idx) (.modK S.N_spk_tot idx) U V)
    (.ite (.lt idx (.nat (nA + nC)))
      (let r := Expr.sub idx (.nat nA)
       initParamsDh S (.bool false)
         (.divK S.N_spk_tot r) (.modK S.N_spk_tot r) U V)
      (.ite (.lt idx (.nat (nA + nC + nB)))
        (let r := Expr.sub idx (.nat (nA + nC))
         initParamsIk S (.divK S.N_id r) (.modK S.N_id r) U V)
        (let r := Expr.sub idx (.nat (nA + nC + nB))
         initParamsOpk S (.divK S.N_opk_tot r) (.modK S.N_opk_tot r) U V)))

def initAdv4 (S : Setup) {Γ : List PT} (U V : Expr pqxdhOps Γ (B 32)) :
    Comp pqxdhOps pqGapDhIface Γ gdhStateTy :=
  letV (.pair U V) fun uv =>
  bindV (gPrim (sIndex (fgTotalIndexCount S))) fun idx =>
  bindV (gPrim sBool) fun secb =>
  .ret (.pair (initParamsFlat S (.fst (v uv)) (.snd (v uv)) (v idx)) (emptySimE (v secb)))

/-- Flat-indexed `CostedReduction` program for `fgKeyIndGapDhAdv4 S b` with loop bound `K`. -/
def fgKeyIndGapDhProg (S : Setup) (K : Nat) :
    CostedReduction pqxdhOps pqGapDhIface (keyIndSpec S) (keyIndCodec S)
      (.prod (B 32) (B 32)) .unit .bool (B 32) where
  σ      := gdhStateTy
  init   :=
    bindV (initAdv4 S (.fst (.var .zero)) (.snd (.var .zero))) fun s =>
      .ret (.pair .unit (v s))
  handle := gdhHandle S K
  finish := gdhFinish S K

/-! ## Tuple-Keyed `GapDH` Program (`fgKeyIndGapDh2Prog`) -/

abbrev ephTargetTy : PT := .prod .bool (.prod .nat .nat)

abbrev spkTargetTy : PT := .prod .nat .nat

abbrev opkTargetTy : PT := .prod .nat (.prod .nat .nat)

/-- Tuple-keyed per-run parameters `(U, V, Up, prinTarget?, dhFlag, ephTarget?, spkTarget?, opkMode, opkTarget?, mode)`
avoiding `S.N_*` constants in the AST. -/
abbrev params2Ty : PT :=
  .prod (B 32) (.prod (B 32) (.prod (B 32) (.prod (.opt .nat) (.prod .bool
    (.prod (.opt ephTargetTy) (.prod (.opt spkTargetTy)
      (.prod .bool (.prod (.opt opkTargetTy) .nat))))))))

def pa2U {Γ : List PT} (p : Expr pqxdhOps Γ params2Ty) : Expr pqxdhOps Γ (B 32) := .fst p
def pa2V {Γ : List PT} (p : Expr pqxdhOps Γ params2Ty) : Expr pqxdhOps Γ (B 32) := .fst (.snd p)
def pa2Up {Γ : List PT} (p : Expr pqxdhOps Γ params2Ty) : Expr pqxdhOps Γ (B 32) := .fst (.snd (.snd p))
def pa2PrinTarget {Γ : List PT} (p : Expr pqxdhOps Γ params2Ty) : Expr pqxdhOps Γ (.opt .nat) :=
  .fst (.snd (.snd (.snd p)))
def pa2DhFlag {Γ : List PT} (p : Expr pqxdhOps Γ params2Ty) : Expr pqxdhOps Γ .bool :=
  .fst (.snd (.snd (.snd (.snd p))))
def pa2EphTarget {Γ : List PT} (p : Expr pqxdhOps Γ params2Ty) : Expr pqxdhOps Γ (.opt ephTargetTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd p)))))
def pa2SpkTarget {Γ : List PT} (p : Expr pqxdhOps Γ params2Ty) : Expr pqxdhOps Γ (.opt spkTargetTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd p))))))
def pa2OpkMode {Γ : List PT} (p : Expr pqxdhOps Γ params2Ty) : Expr pqxdhOps Γ .bool :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd p)))))))
def pa2OpkTarget {Γ : List PT} (p : Expr pqxdhOps Γ params2Ty) : Expr pqxdhOps Γ (.opt opkTargetTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd p))))))))
def pa2Mode {Γ : List PT} (p : Expr pqxdhOps Γ params2Ty) : Expr pqxdhOps Γ .nat :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd p))))))))

def pa2Mk {Γ : List PT} (U V Up : Expr pqxdhOps Γ (B 32))
    (pt : Expr pqxdhOps Γ (.opt .nat)) (df : Expr pqxdhOps Γ .bool)
    (et : Expr pqxdhOps Γ (.opt ephTargetTy)) (st : Expr pqxdhOps Γ (.opt spkTargetTy))
    (om : Expr pqxdhOps Γ .bool) (ot : Expr pqxdhOps Γ (.opt opkTargetTy))
    (md : Expr pqxdhOps Γ .nat) : Expr pqxdhOps Γ params2Ty :=
  .pair U (.pair V (.pair Up (.pair pt (.pair df (.pair et (.pair st (.pair om (.pair ot md))))))))

abbrev gdhState2Ty : PT := .prod params2Ty simTy

/-- Semantic projection from tuple-keyed `params2Ty.denote` to flat `paramsTy.denote`. -/
def params2ToFlat (S : Setup) (p : params2Ty.denote) : paramsTy.denote :=
  let (U, (V, (Up, (pt, (df, (et, (st, (om, (ot, md))))))))) := p
  let eiRaw := match et with
    | none => S.N_send_tot
    | some (true, (u, i)) => u * Nat.min S.N_send_opk S.N_send_opk_tot + i
    | some (false, (u, i)) => S.N_send_opk_tot + (u * Nat.min S.N_send_no_opk S.N_send_no_opk_tot + i)
  let pf := pt.isSome
  let pi := match pt with
    | some u => u
    | none => if md == 1 then eiRaw else S.N_id
  let ei := if df then pi else eiRaw
  let si := match st with
    | none => S.N_spk_tot
    | some (u, j) => u * Nat.min S.N_recv S.N_spk_tot + j
  let oi := match ot with
    | none => S.N_opk_tot
    | some (u, (j, o)) =>
      (u * Nat.min S.N_recv S.N_spk_tot + j) * Nat.min S.N_opk S.N_opk_tot + o
  (U, (V, (Up, (pf, (pi, (df, (ei, (si, (om, (oi, md))))))))))

def ephSidMatchesE {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (sid : Var Γ₁ sessionIdTy)
    (tgt : Expr pqxdhOps Δ (.opt ephTargetTy)) : Expr pqxdhOps Δ .bool :=
  eCaseOpt tgt (.bool false) fun t =>
    eCaseSum (v sid)
      (fun ui => .and (.fst (v t)) (nat2Eq (v ui) (.snd (v t))))
      fun s1 => eCaseSum (v s1)
        (fun ui => .and (.not (.fst (v t))) (nat2Eq (v ui) (.snd (v t))))
        fun _ => .bool false

def wrapBase2 {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy gdhState2Ty) :=
  bindV (gPrim c) fun r =>
  .ret (.pair (.fst (v r)) (.pair (v pa) (smUpd (v sm) (base := .snd (v r)))))

def wrapSim2 {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy gdhState2Ty) :=
  bindV c fun r => .ret (.pair (.fst (v r)) (.pair (v pa) (.snd (v r))))

def initPrinGdh2B (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (u : Var Γ₄ .nat) : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy) :=
  .ite (eAny K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (v u))
    (.ret (.pair rNone (v sm)))
    (letV (eCaseOpt (pa2PrinTarget (v pa)) (.bool false) fun uT => natEq (v u) (v uT)) fun isT =>
     bindV (gPrim sBytes32) fun sk0 =>
     bindV (gPrim (qX25519Base (v sk0))) fun pk0 =>
     bindV (gPrim sBytes32) fun skS =>
     bindV (gPrim (qSigPkGen (v skS))) fun pkS =>
     letV (.ite (v isT) (litB 32 []) (v sk0)) fun sec0 =>
     letV (.ite (v isT) (pa2Up (v pa)) (v pk0)) fun ikPk =>
     let e := peMk (v sec0) (v ikPk) (v skS) (v pkS) (.bool false)
     let bSt' := stUpd (v bSt) (prin := .cons (.pair (v u) e) (stPrin (v bSt)))
     .ret (.pair (rInitPrin (v ikPk) (v pkS)) (smUpd (v sm) (base := bSt'))))

def genSpkGdh2B (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ (.prod .nat .nat)) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy) :=
  .ite (eAny K (stSpks (v bSt)) fun p => nat2Eq (.fst (v p)) (v x))
    (.ret (.pair rNone (v sm)))
    (caseOptV (eFind K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (.fst (v x)))
      (.ret (.pair rNone (v sm)))
      fun ue =>
        letV (eCaseOpt (pa2SpkTarget (v pa)) (.bool false) fun sp => nat2Eq (v x) (v sp)) fun isT =>
        bindV (gPrim sBytes32) fun spkSkRaw =>
        bindV (gPrim (qX25519Base (v spkSkRaw))) fun spkPkRaw =>
        letV (.ite (v isT) (litB 32 []) (v spkSkRaw)) fun spkSk =>
        letV (.ite (v isT) (pa2V (v pa)) (v spkPkRaw)) fun spkPk =>
        bindV (gPrim sRandom64) fun rSpk =>
        bindV (gPrim (qSigSign 33 (.pair (peSecIKAsign (.snd (v ue)))
          (.pair (encEC (v spkPk)) (v rSpk))))) fun spkSig =>
        bindV (gPrim sRandom64) fun seed =>
        bindV (gPrim (qKemKeyGen (v seed))) fun kp =>
        bindV (gPrim sRandom64) fun rPq =>
        bindV (qSigSign 1569 (.pair (peSecIKAsign (.snd (v ue)))
          (.pair (encKEM (.fst (v kp))) (v rPq))) |> gPrim) fun pqSig =>
        let jId := u32OfNat (.snd (v x))
        let bE := sbMk (v spkSk) (v spkPk) (v spkSig)
          (.snd (v kp)) (.fst (v kp)) (v pqSig) (.bool false)
        let buOut := buMk (peIkAPk (.snd (v ue))) jId (v spkPk) (v spkSig)
          .none jId (.fst (v kp)) (v pqSig)
        let bSt' := stUpd (v bSt) (spks := .cons (.pair (v x) bE) (stSpks (v bSt)))
        .ret (.pair (rBundle buOut) (smUpd (v sm) (base := bSt'))))

def genOpkGdh2B (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ (.prod .nat (.prod .nat .nat))) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy) :=
  .ite (eAny K (stOpks (v bSt)) fun p => nat3Eq (.fst (v p)) (v x))
    (.ret (.pair rNone (v sm)))
    (letV (.and (pa2OpkMode (v pa))
      (eCaseOpt (pa2OpkTarget (v pa)) (.bool false) fun op => nat3Eq (v x) (v op))) fun isT =>
     bindV (gPrim sBytes32) fun opkSkRaw =>
     bindV (gPrim (qX25519Base (v opkSkRaw))) fun opkPkRaw =>
     letV (.ite (v isT) (litB 32 []) (v opkSkRaw)) fun opkSk =>
     letV (.ite (v isT) (pa2V (v pa)) (v opkPkRaw)) fun opkPk =>
     let oE := oeMk (v opkSk) (v opkPk) (.bool false)
     let bSt' := stUpd (v bSt) (opks := .cons (.pair (v x) oE) (stOpks (v bSt)))
     .ret (.pair (rPk (v opkPk)) (smUpd (v sm) (base := bSt'))))

def initiateGdh2B (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (hasOpk : Bool) (x : Var Γ₄ initQTy) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy) :=
  letV (.snd (.snd (v x))) fun bu =>
  let guardOk := if hasOpk then isSomeE (buOpkB (v bu)) else .not (isSomeE (buOpkB (v bu)))
  .ite (.not guardOk) (.ret (.pair rNone (v sm)))
    (letV (initSidE hasOpk (v x)) fun sid =>
     .ite (eAny K (stSess (v bSt)) fun s => sidEq (seSid (v s)) (v sid))
       (.ret (.pair rNone (v sm)))
       (caseOptV (eFind K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (.fst (v x)))
         (.ret (.pair rNone (v sm)))
         fun ue =>
           bindV (gPrim (koskBundleOkPowsC S K bSt (smPows (v sm)) bu)) fun ok =>
           .ite (.not (v ok)) (.ret (.pair rNone (v sm)))
             (letV (.and (.not (pa2DhFlag (v pa)))
               (ephSidMatchesE sid (pa2EphTarget (v pa)))) fun isTE =>
              bindV (gPrim sBytes32) fun ekSkRaw =>
              bindV (gPrim sBytes32) fun coins =>
              bindV (gPrim (resolveSigPkC S K bSt (buIkB (v bu)))) fun sigPk =>
              bindV (gPrim (qSigVerify 33 (.pair (v sigPk)
                (.pair (encEC (buSpkB (v bu))) (buSpkSig (v bu)))))) fun v1 =>
              bindV (gPrim (qSigVerify 1569 (.pair (v sigPk)
                (.pair (encKEM (buPqspkB (v bu))) (buPqspkSig (v bu)))))) fun v2 =>
              .ite (.not (.and (v v1) (v v2))) (.ret (.pair rNone (v sm)))
                (bindV (gPrim (qKemEncaps (.pair (buPqspkB (v bu)) (v coins)))) fun krOpt =>
                 caseOptV (v krOpt) (.ret (.pair rNone (v sm))) fun kr =>
                   bindV (gPrim (qX25519Base (v ekSkRaw))) fun ekPkRaw =>
                   letV (.ite (v isTE) (litB 32 []) (v ekSkRaw)) fun ekSk =>
                   letV (.ite (v isTE) (pa2U (v pa)) (v ekPkRaw)) fun ekPk =>
                   bindV (gPrim (lookupSpkSkC S K bSt (smPows (v sm)) (buSpkB (v bu))))
                     fun spkSk =>
                   bindV (computePosC (peSecIKA0 (.snd (v ue))) (v spkSk)
                     (peIkAPk (.snd (v ue))) (buSpkB (v bu))) fun p1 =>
                   bindV (computePosC (v ekSk) (litB 32 []) (v ekPk) (buIkB (v bu))) fun p2 =>
                   bindV (computePosC (v ekSk) (litB 32 []) (v ekPk) (buSpkB (v bu))) fun p3 =>
                   bindV (computeOptPosInitC (v ekSk) (v ekPk) (buOpkB (v bu))) fun p4 =>
                   letV (.fst (v kr)) fun ss =>
                   bindV (fgPatchC K p1 p2 p3 p4 ss (smFgL (v sm))) fun patchR =>
                   letV (.fst (v patchR)) fun dkReal =>
                   letV (.snd (v patchR)) fun fgL' =>
                   letV (hdMk (peIkAPk (.snd (v ue))) (v ekPk) (buSpkId (v bu))
                     (optFst (buOpkB (v bu))) (buPqspkId (v bu)) (.snd (v kr))) fun hdr =>
                   bindV (gPrim (honestPeerC S K bSt (buIkB (v bu)))) fun hp =>
                   bindV (gPrim (checkProvC S K bSt bu)) fun prov =>
                   letV (seMk (v sid) (v hp) (buIkB (v bu)) (buSpkB (v bu))
                     (optSnd (buOpkB (v bu))) (buPqspkB (v bu)) (.fst (v prov))
                     (.fst (.snd (v prov))) (.snd (.snd (v prov))) (v ekSk)
                     (isSomeE (v hp)) (v dkReal) (v dkReal) (v hdr)
                     (.bool false) (.bool false)) fun sInit =>
                   bindV (chooseInitRandC S K bSt sInit) fun dkRand =>
                   let sFinal := seUpd (v sInit) (drRand := v dkRand)
                   let bSt' := stUpd (v bSt) (sess := .cons sFinal (stSess (v bSt)))
                   letV (smUpd (v sm) (base := bSt') (fgL := v fgL')) fun smV =>
                   bindV (gPrim (findHonestC S K bSt (buIkB (v bu)))) fun fh =>
                   .ret (eCaseOpt (v fh)
                     (.pair (rInitUnfresh (v dkReal) (v hdr)) (v smV))
                     fun _ => .pair (rHdr (v hdr)) (v smV))))))

def acceptOpkGdh2B (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ accQTy) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy) :=
  let hdr := qHdr (v x)
  let guardOk := Expr.and
    (.and (.and (.and (eqU32 (hdSpkId hdr) (u32OfNat (qJ (v x))))
                      (eqU32 (hdPqspkId hdr) (u32OfNat (qJ (v x)))))
                (optU32Eq (hdOpkId hdr) (.some (u32OfNat (qO (v x))))))
          (natEq (lenB (hdIkAPk hdr)) (.nat 32)))
    (natEq (lenB (hdEkAPk hdr)) (.nat 32))
  .ite (.not guardOk) (.ret (.pair rNone (v sm)))
    (.ite (eAny K (stUsedO (v bSt)) fun u => nat3Eq (v u) (qKJO (v x)))
      (.ret (.pair rNone (v sm)))
      (bindV (gPrim (koskSenderOkPowsC S K bSt (smPows (v sm)) (hdIkAPk (qHdr (v x))))) fun sOk =>
       .ite (.not (v sOk)) (.ret (.pair rNone (v sm)))
         (caseOptV (eFind K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (qK (v x)))
           (.ret (.pair rNone (v sm)))
           fun ke =>
             caseOptV (eFind K (stSpks (v bSt)) fun p =>
               nat2Eq (.fst (v p)) (.pair (qK (v x)) (qJ (v x))))
               (.ret (.pair rNone (v sm)))
               fun be =>
                 caseOptV (eFind K (stOpks (v bSt)) fun p => nat3Eq (.fst (v p)) (qKJO (v x)))
                   (.ret (.pair rNone (v sm)))
                   fun oe =>
                     .ite (oeConsumed (.snd (v oe))) (.ret (.pair rNone (v sm)))
                       (letV (kyberCheckE K (stKyb (v bSt)) (.pair (qK (v x))
                         (.pair (hdPqspkId (qHdr (v x)))
                           (.pair (hdSpkId (qHdr (v x))) (hdEkAPk (qHdr (v x))))))) fun kybR =>
                        bindV (gPrim (qIsCanonical (hdEkAPk (qHdr (v x))))) fun canon =>
                        bindV (gPrim (qX25519 (.pair (litB 32 (List.replicate 32 0))
                          (hdIkAPk (qHdr (v x)))))) fun dh1Z =>
                        bindV (gPrim (qX25519 (.pair (litB 32 (List.replicate 32 0))
                          (hdEkAPk (qHdr (v x)))))) fun dh2Z =>
                        .ite (pa2OpkMode (v pa))
                          (bindV (gPrim (qKemDecaps (.pair (sbPqspkSk (.snd (v be)))
                            (hdKemCt (qHdr (v x)))))) fun ssOpt =>
                           .ite (.not (.and (.and (.and (.fst (v kybR)) (v canon))
                             (nonZero32 (v dh1Z))) (nonZero32 (v dh2Z))))
                             (.ret (.pair rNone (v sm)))
                             (caseOptV (v ssOpt) (.ret (.pair rNone (v sm))) fun ss =>
                               bindV (computePosC (litB 32 []) (sbSpkSk (.snd (v be)))
                                 (hdIkAPk (qHdr (v x))) (sbSpkPk (.snd (v be)))) fun p1 =>
                               bindV (computePosC (litB 32 []) (peSecIKA0 (.snd (v ke)))
                                 (hdEkAPk (qHdr (v x))) (peIkAPk (.snd (v ke)))) fun p2 =>
                               bindV (computePosC (litB 32 []) (sbSpkSk (.snd (v be)))
                                 (hdEkAPk (qHdr (v x))) (sbSpkPk (.snd (v be)))) fun p3 =>
                               bindV (computePosC (litB 32 []) (oeOpkSk (.snd (v oe)))
                                 (hdEkAPk (qHdr (v x))) (oeOpkPk (.snd (v oe)))) fun p4Raw =>
                               letV (.some (v p4Raw)) fun p4 =>
                               bindV (fgPatchC K p1 p2 p3 p4 ss (smFgL (v sm))) fun patchR =>
                               let opks' := eMap K (stOpks (v bSt)) fun p =>
                                 .ite (nat3Eq (.fst (v p)) (qKJO (v x)))
                                   (.pair (.fst (v p))
                                     (oeUpd (.snd (v p)) (consumed := .bool true)))
                                   (v p)
                               finishAcceptGdhC S K sm bSt true x ke be
                                 (.some (oeOpkPk (.snd (v oe)))) opks'
                                 (.cons (qKJO (v x)) (stUsedO (v bSt)))
                                 (stUsedN (v bSt)) (.snd (v kybR)) patchR))
                          (bindV (gPrim (qX25519 (.pair (oeOpkSk (.snd (v oe)))
                            (hdEkAPk (qHdr (v x)))))) fun dh4 =>
                           bindV (gPrim (qKemDecaps (.pair (sbPqspkSk (.snd (v be)))
                             (hdKemCt (qHdr (v x)))))) fun ssOpt =>
                           .ite (.not (.and (.and (.and (.and (.fst (v kybR)) (v canon))
                             (nonZero32 (v dh1Z))) (nonZero32 (v dh2Z))) (nonZero32 (v dh4))))
                             (.ret (.pair rNone (v sm)))
                             (caseOptV (v ssOpt) (.ret (.pair rNone (v sm))) fun ss =>
                               bindV (computePosC (litB 32 []) (sbSpkSk (.snd (v be)))
                                 (hdIkAPk (qHdr (v x))) (sbSpkPk (.snd (v be)))) fun p1 =>
                               bindV (computePosC (litB 32 []) (peSecIKA0 (.snd (v ke)))
                                 (hdEkAPk (qHdr (v x))) (peIkAPk (.snd (v ke)))) fun p2 =>
                               bindV (computePosC (litB 32 []) (sbSpkSk (.snd (v be)))
                                 (hdEkAPk (qHdr (v x))) (sbSpkPk (.snd (v be)))) fun p3 =>
                               bindV (mkSecretPosC (v dh4)) fun p4Raw =>
                               letV (.some (v p4Raw)) fun p4 =>
                               bindV (fgPatchC K p1 p2 p3 p4 ss (smFgL (v sm))) fun patchR =>
                               let opks' := eMap K (stOpks (v bSt)) fun p =>
                                 .ite (nat3Eq (.fst (v p)) (qKJO (v x)))
                                   (.pair (.fst (v p))
                                     (oeUpd (.snd (v p)) (consumed := .bool true)))
                                   (v p)
                               finishAcceptGdhC S K sm bSt true x ke be
                                 (.some (oeOpkPk (.snd (v oe)))) opks'
                                 (.cons (qKJO (v x)) (stUsedO (v bSt)))
                                 (stUsedN (v bSt)) (.snd (v kybR)) patchR))))))

/-- Tuple-keyed 14-constructor `KeyIndQuery` handler for `fgKeyIndGapDh2Prog`. -/
def gdhHandle2 (S : Setup) (K : Nat) :
    Comp pqxdhOps pqGapDhIface [gdhState2Ty, keyIndQueryTy] (.prod keyIndRespTy gdhState2Ty) :=
  let st : Var [gdhState2Ty, keyIndQueryTy] gdhState2Ty := .zero
  let q : Var [gdhState2Ty, keyIndQueryTy] keyIndQueryTy := .succ .zero
  letV (.fst (v st)) fun pa =>
  letV (.snd (v st)) fun sm =>
  letV (smBase (v sm)) fun bSt =>
  caseSumV (v q) (fun u => wrapSim2 pa (initPrinGdh2B K pa sm bSt u)) fun r1 =>
  caseSumV (v r1) (fun u => wrapBase2 pa sm (corruptB K bSt u)) fun r2 =>
  caseSumV (v r2) (fun x => wrapSim2 pa (genSpkGdh2B K pa sm bSt x)) fun r3 =>
  caseSumV (v r3) (fun x => wrapSim2 pa (genOpkGdh2B K pa sm bSt x)) fun r4 =>
  caseSumV (v r4) (fun x => wrapSim2 pa (initiateGdh2B S K pa sm bSt true x)) fun r5 =>
  caseSumV (v r5) (fun x => wrapSim2 pa (initiateGdh2B S K pa sm bSt false x)) fun r6 =>
  caseSumV (v r6) (fun x => wrapSim2 pa (acceptOpkGdh2B S K pa sm bSt x)) fun r7 =>
  caseSumV (v r7) (fun x => wrapSim2 pa (acceptNoOpkGdhB S K sm bSt x)) fun r8 =>
  caseSumV (v r8) (fun sid => wrapBase2 pa sm (testB K bSt sid)) fun r9 =>
  caseSumV (v r9) (fun sec => wrapSim2 pa (roParsedC K sm sec)) fun r10 =>
  caseSumV (v r10) (fun _ => .ret (.pair rNone (v st))) fun r11 =>
  caseSumV (v r11) (fun sid => wrapBase2 pa sm (revealB K bSt sid)) fun r12 =>
  caseSumV (v r12) (fun sk => wrapSim2 pa (registerGdhB sm bSt sk))
                   (fun x => wrapBase2 pa sm (revealSpkB K bSt x))

def logFind2C (K off : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) :
    Comp pqxdhOps pqGapDhIface Δ (B 32) :=
  let cands := eMap K (smLog (v sm)) fun sec => slice32 off (v sec)
  bindV (findMV K cands fun z => ddhQ (pa2U (v pa)) (pa2V (v pa)) (v z)) fun found =>
  .ret (eCaseOpt (v found) (litB 32 (List.replicate 32 0)) fun z => v z)

def findMapStep2C {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (acc : Var Γ₂ (.opt (B 32)))
    (cand : Comp pqxdhOps pqGapDhIface Δ (B 32)) : Comp pqxdhOps pqGapDhIface Δ (.opt (B 32)) :=
  caseOptV (v acc)
    (bindV cand fun z =>
     bindV (ddhQ (pa2U (v pa)) (pa2V (v pa)) (v z)) fun ok =>
     .ret (.ite (v ok) (.some (v z)) .none))
    fun _ => .ret (v acc)

def extractMode0_2C (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) : Comp pqxdhOps pqGapDhIface Δ (B 32) :=
  let cands := eMap K (smLog (v sm)) fun sec => slice32 32 (v sec)
  bindV (findMV K cands fun z => ddhQ (pa2U (v pa)) (pa2V (v pa)) (v z)) fun f1 =>
  caseOptV (v f1)
    (bindV (spkPowsC S K (stSpks (smBase (v sm)))) fun spkPows =>
     letV (smPows (v sm)) fun advPows =>
     bindV (foldMV (min K S.N_dh) (stSess (smBase (v sm))) .none fun s acc =>
       findMapStep2C pa acc (initDh1CandC S K spkPows advPows s)) fun f2 =>
     caseOptV (v f2)
       (letV (stSpks (smBase (v sm))) fun spks =>
        bindV (foldMV (min K S.N_sess_tot) (stResps (smBase (v sm))) .none fun r acc =>
          findMapStep2C pa acc (respDh1CandC S K spks r)) fun f3 =>
        .ret (eCaseOpt (v f3) (litB 32 (List.replicate 32 0)) fun z => v z))
       fun z => .ret (v z))
    fun z => .ret (v z)

/-- Tuple-keyed CDH extractor for `fgKeyIndGapDh2Prog`. -/
def gdhFinish2 (S : Setup) (K : Nat) :
    Comp pqxdhOps pqGapDhIface [gdhState2Ty, .bool] (B 32) :=
  let st : Var [gdhState2Ty, .bool] gdhState2Ty := .zero
  letV (.fst (v st)) fun pa =>
  letV (.snd (v st)) fun sm =>
  .ite (natEq (pa2Mode (v pa)) (.nat 0)) (extractMode0_2C S K pa sm)
    (.ite (natEq (pa2Mode (v pa)) (.nat 1))
      (logFind2C K 96 pa sm)
      (.ite (natEq (pa2Mode (v pa)) (.nat 2))
        (logFind2C K 64 pa sm)
        (logFind2C K 128 pa sm)))

/-- Exact `Bernoulli(A / (A + B))` sampler of constant AST size: for `1 ≤ A ≤ B`, draws
`x ← [0, A + B)` and `y₁, y₂ ← [0, A)` and tests `x < y₁ + y₂ + 1`
(since `∑_{y₁, y₂ < A} (y₁ + y₂ + 1) = A³`). -/
def bernoulliRatioGdhC {Δ : List PT} (A B : Nat) : Comp pqxdhOps pqGapDhIface Δ .bool :=
  if A = 0 then
    .ret (.bool false)
  else if B = 0 then
    .ret (.bool true)
  else if A ≤ B then
    bindV (gPrim (sIndex (A + B))) fun x =>
    bindV (gPrim (sIndex A)) fun y1 =>
    bindV (gPrim (sIndex A)) fun y2 =>
    .ret (.lt (v x) (.add (.add (v y1) (v y2)) (.nat 1)))
  else
    bindV (gPrim (sIndex (A + B))) fun x =>
    bindV (gPrim (sIndex B)) fun y1 =>
    bindV (gPrim (sIndex B)) fun y2 =>
    .ret (.not (.lt (v x) (.add (.add (v y1) (v y2)) (.nat 1))))

/-- Weighted binary choice (`w1 : w2`) omitting zero-weight arms at the Lean meta-level. -/
def chooseArm2C {Γ₁ Δ : List PT} {α : PT} [Ext Γ₁ Δ] (w1 w2 : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' α) :
    Comp pqxdhOps pqGapDhIface Δ α :=
  if w1 = 0 then c2
  else if w2 = 0 then c1
  else
    bindV (bernoulliRatioGdhC w1 w2) fun b =>
    .ite (v b) c1 c2

def samplePrin2C (S : Setup) {Δ : List PT} : Comp pqxdhOps pqGapDhIface Δ (.opt .nat) :=
  if S.N_id = 0 then
    .ret .none
  else
    bindV (gPrim (sIndex S.N_id)) fun u =>
    .ret (.some (v u))

def sampleSpkPair2C (S : Setup) {Δ : List PT} : Comp pqxdhOps pqGapDhIface Δ (.opt spkTargetTy) :=
  if S.N_spk_tot = 0 then
    .ret .none
  else
    bindV (gPrim (sIndex S.N_id)) fun u =>
    bindV (gPrim (sIndex S.N_recv)) fun j =>
    .ret (.some (.pair (v u) (v j)))

def sampleOpkTriple2C (S : Setup) {Δ : List PT} : Comp pqxdhOps pqGapDhIface Δ (.opt opkTargetTy) :=
  if S.N_opk_tot = 0 then
    .ret .none
  else
    bindV (gPrim (sIndex S.N_id)) fun u =>
    bindV (gPrim (sIndex S.N_recv)) fun j =>
    bindV (gPrim (sIndex S.N_opk)) fun o =>
    .ret (.some (.pair (v u) (.pair (v j) (v o))))

def sampleSendOpkTarget2C (S : Setup) {Δ : List PT} : Comp pqxdhOps pqGapDhIface Δ (.opt ephTargetTy) :=
  if S.N_send_opk_tot = 0 then
    .ret .none
  else
    bindV (gPrim (sIndex S.N_id)) fun u =>
    bindV (gPrim (sIndex S.N_send_opk)) fun i =>
    .ret (.some (.pair (.bool true) (.pair (v u) (v i))))

def sampleSendNoOpkTarget2C (S : Setup) {Δ : List PT} : Comp pqxdhOps pqGapDhIface Δ (.opt ephTargetTy) :=
  if S.N_send_no_opk_tot = 0 then
    .ret .none
  else
    bindV (gPrim (sIndex S.N_id)) fun u =>
    bindV (gPrim (sIndex S.N_send_no_opk)) fun i =>
    .ret (.some (.pair (.bool false) (.pair (v u) (v i))))

def sampleSendTarget2C (S : Setup) {Δ : List PT} : Comp pqxdhOps pqGapDhIface Δ (.opt ephTargetTy) :=
  if S.N_send_tot = 0 then
    .ret .none
  else
    chooseArm2C (Γ₁ := Δ) S.N_send_opk_tot S.N_send_no_opk_tot
      (fun {_} [_] => sampleSendOpkTarget2C S)
      (fun {_} [_] => sampleSendNoOpkTarget2C S)

def sampleDhParams2C (S : Setup) {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (uv : Var Γ₁ (.prod (B 32) (B 32))) : Comp pqxdhOps pqGapDhIface Δ params2Ty :=
  let nA := S.N_id * S.N_spk_tot
  let nC := S.N_send_tot * S.N_spk_tot
  if nA + nC = 0 then
    let U := .fst (v uv)
    let V := .snd (v uv)
    .ret (pa2Mk U V U (.some (.nat 0)) (.bool true) .none
      (.some (.pair (.nat 0) (.nat 0))) (.bool false) .none (.nat 0))
  else
    chooseArm2C (Γ₁ := Γ₁) nA nC
      (fun {_} [_] =>
        bindV (samplePrin2C S) fun pt =>
        bindV (sampleSpkPair2C S) fun st =>
        let U := .fst (v uv)
        let V := .snd (v uv)
        .ret (pa2Mk U V U (v pt) (.bool true) .none (v st) (.bool false) .none (.nat 0)))
      (fun {_} [_] =>
        bindV (sampleSendTarget2C S) fun et =>
        bindV (sampleSpkPair2C S) fun st =>
        let U := .fst (v uv)
        let V := .snd (v uv)
        .ret (pa2Mk U V U .none (.bool false) (v et) (v st) (.bool false) .none (.nat 1)))

/-- Tuple-keyed 4-mode parameter sampler matching `initParamsFlat S U V <$> sampleIndex (fgTotalIndexCount S)`
under `params2ToFlat S`. -/
def initParams2C (S : Setup) {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (uv : Var Γ₁ (.prod (B 32) (B 32))) : Comp pqxdhOps pqGapDhIface Δ params2Ty :=
  if fgTotalIndexCount S = 0 then
    let U := .fst (v uv)
    let V := .snd (v uv)
    .ret (pa2Mk U V U .none (.bool false)
      (.some (.pair (.bool true) (.pair (.nat 0) (.nat 0))))
      .none (.bool true)
      (.some (.pair (.nat 0) (.pair (.nat 0) (.nat 0))))
      (.nat 3))
  else
    let nA := S.N_id * S.N_spk_tot
    let nC := S.N_send_tot * S.N_spk_tot
    let nB := S.N_send_tot * S.N_id
    let nD := S.N_send_opk_tot * S.N_opk_tot
    chooseArm2C (Γ₁ := Γ₁) (nA + nC) (nB + nD)
      (fun {_} [_] =>
        chooseArm2C (Γ₁ := Γ₁) nA nC
          (fun {_} [_] =>
            bindV (samplePrin2C S) fun pt =>
            bindV (sampleSpkPair2C S) fun st =>
            let U := .fst (v uv)
            let V := .snd (v uv)
            .ret (pa2Mk U V U (v pt) (.bool true) .none (v st) (.bool false) .none (.nat 0)))
          (fun {_} [_] =>
            bindV (sampleSendTarget2C S) fun et =>
            bindV (sampleSpkPair2C S) fun st =>
            let U := .fst (v uv)
            let V := .snd (v uv)
            .ret (pa2Mk U V U .none (.bool false) (v et) (v st) (.bool false) .none (.nat 1))))
      (fun {_} [_] =>
        chooseArm2C (Γ₁ := Γ₁) nB nD
          (fun {_} [_] =>
            bindV (sampleSendTarget2C S) fun et =>
            bindV (samplePrin2C S) fun pt =>
            let U := .fst (v uv)
            let V := .snd (v uv)
            .ret (pa2Mk U V V (v pt) (.bool false) (v et) .none (.bool false) .none (.nat 2)))
          (fun {_} [_] =>
            bindV (sampleSendOpkTarget2C S) fun et =>
            bindV (sampleOpkTriple2C S) fun ot =>
            let U := .fst (v uv)
            let V := .snd (v uv)
            .ret (pa2Mk U V U .none (.bool false) (v et) .none (.bool true) (v ot) (.nat 3))))

def initAdv4_2 (S : Setup) {Γ : List PT} (U V : Expr pqxdhOps Γ (B 32)) :
    Comp pqxdhOps pqGapDhIface Γ gdhState2Ty :=
  letV (.pair U V) fun uv =>
  bindV (initParams2C S uv) fun pa =>
  bindV (gPrim sBool) fun secb =>
  .ret (.pair (v pa) (emptySimE (v secb)))

/-- Tuple-keyed `CostedReduction` program for `fgKeyIndGapDhAdv4 S b` with loop bound `K`,
whose AST size is independent of `S.N_*`. -/
def fgKeyIndGapDh2Prog (S : Setup) (K : Nat) :
    CostedReduction pqxdhOps pqGapDhIface (keyIndSpec S) (keyIndCodec S)
      (.prod (B 32) (B 32)) .unit .bool (B 32) where
  σ      := gdhState2Ty
  init   :=
    bindV (initAdv4_2 S (.fst (.var .zero)) (.snd (.var .zero))) fun s =>
      .ret (.pair .unit (v s))
  handle := gdhHandle2 S K
  finish := gdhFinish2 S K

end SignalPqxdh.Security.ReductionDsl.KeyInd
