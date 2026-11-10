/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.NonVacuity.CliSatisfiable
public import Symbolic.Proofs.Tests.Refinement.Cli.Cheval26.Fixture

/-!
# Non-Vacuity Witness Payloads, Wire Parses, and `CoinSplit`

Extracts the payloads of `Fixture.trace` via single-pass
list slices, establishes `ExternContractsHoldCli chevalInterp` and `ProtocolSetupWF chevalRecords`,
verifies the wire-format parses, and proves `CoinSplit chevalCliTrace cwTrace` and
`CallsMatchSchedules chevalCalls cwWho cwOk`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Refinement.Cli.Cheval26

open DY
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.X25519 (isLowOrderKey lowOrderUs uCoord leValue p25519)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Refinement (x25519PublicKeySymbol x25519AgreementSymbol
  x25519TorsionSymbol torsionShift aesCbcEncryptSymbol aesCbcDecryptSymbol ExternCryptoLawsHold)
open DY.Libsignal.PQXDH.Refinement (X25519TorsionShiftsRejected)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open CryptoVerification.SignalSession (PublicBundle)
open Symbolic.BugInjection

/-! ## Witness Payloads, `chevalInterp`, and `chevalRecords` -/

abbrev cwSetup : PQXDHSpqrSetup := Fixture.setup
abbrev cwTrace : List MachineEvent := Fixture.trace
abbrev cwWho : List Participant := Fixture.who
abbrev cwOk : Nat → Bool := Fixture.ok

def evBytes : MachineEvent → HwBytes
  | .recv b | .send b | .pt b | .accept b | .rng b | .leak b => b

def traceAt : List MachineEvent → Nat → HwBytes
  | e :: _, 0 => evBytes e
  | _ :: tl, n + 1 => traceAt tl n
  | [], _ => []

def traceEv (i : Nat) : HwBytes := traceAt cwTrace i

def blob0 : HwBytes := traceEv 0
def rngPieces0 : List HwBytes := ((cwTrace.drop 1).take 34).map evBytes
def coins0 : HwBytes := rngPieces0.flatten
def pt1 : HwBytes := traceEv 35
def coins1 : HwBytes := traceEv 36
def c1Out : HwBytes := traceEv 37
def coins2 : HwBytes := traceEv 39
def pt3 : HwBytes := traceEv 41
def coins3 : HwBytes := List.replicate 64 0#8
def c3Out : HwBytes := traceEv 42
def rngPieces4 : List HwBytes := ((cwTrace.drop 44).take 34).map evBytes
def coins4 : HwBytes := rngPieces4.flatten
def pt5 : HwBytes := traceEv 78
def coins5 : HwBytes := traceEv 79
def c5Out : HwBytes := traceEv 80
def c6In : HwBytes := traceEv 81
def coins6 : HwBytes := traceEv 82
def pt6Out : HwBytes := traceEv 83

section FastHex
open Lean Meta Elab Command

private theorem traceAt_zero (e : MachineEvent) (tl : List MachineEvent) :
    traceAt (e :: tl) 0 = evBytes e := rfl
private theorem traceAt_succ (e : MachineEvent) (tl : List MachineEvent) (n : Nat) :
    traceAt (e :: tl) (n + 1) = traceAt tl n := rfl
private theorem evBytes_recv (b : HwBytes) : evBytes (.recv b) = b := rfl
private theorem evBytes_send (b : HwBytes) : evBytes (.send b) = b := rfl
private theorem evBytes_pt (b : HwBytes) : evBytes (.pt b) = b := rfl
private theorem evBytes_accept (b : HwBytes) : evBytes (.accept b) = b := rfl
private theorem evBytes_rng (b : HwBytes) : evBytes (.rng b) = b := rfl
private def dropEv (n : Nat) (l : List MachineEvent) : List MachineEvent := l.drop n
private def takeMapEv (n : Nat) (l : List MachineEvent) : List HwBytes := (l.take n).map evBytes
private theorem dropEv_zero (l : List MachineEvent) : dropEv 0 l = l := rfl
private theorem dropEv_succ (e : MachineEvent) (tl : List MachineEvent) (n : Nat) :
    dropEv (n + 1) (e :: tl) = dropEv n tl := rfl
private theorem takeMapEv_zero (l : List MachineEvent) : takeMapEv 0 l = [] := rfl
private theorem takeMapEv_succ (b : HwBytes) (tl : List MachineEvent) (n : Nat) :
    takeMapEv (n + 1) (.rng b :: tl) = b :: takeMapEv n tl := rfl

private def hexBytesChars (cs : List Char) : HwBytes :=
  Symbolic.BugInjection.hexBytes.go
    (fun c => if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10) cs
private theorem hexBytes_eq_hexBytesChars (s : String) :
    hexBytes s = hexBytesChars s.toList := rfl
private meta def hexDigitVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
private meta def parseHexStr (s : String) : List UInt8 :=
  let rec go : List Char → List UInt8
    | a :: b :: rest => UInt8.ofNat (16 * hexDigitVal a + hexDigitVal b) :: go rest
    | _ => []
  go s.toList

private meta partial def zetaAll (e : Expr) : Expr :=
  match e with
  | .letE _ _ v b _ => zetaAll (b.instantiate1 v)
  | .mdata _ b => zetaAll b
  | _ => e

private meta partial def unpackListElems (e : Expr) (acc : Array (Expr × Expr)) :
    MetaM (Array (Expr × Expr)) := do
  match e with
  | .letE _ _ v b _ => unpackListElems (b.instantiate1 v) acc
  | .mdata _ b => unpackListElems b acc
  | _ =>
    match e.getAppFnArgs with
    | (``List.cons, #[_, hd, tl]) => unpackListElems tl (acc.push (hd, tl))
    | (``List.nil, _) => pure acc
    | (fn, args) => throwError "unexpected list constructor {fn} ({args.size})"

private meta def mkRawEvProof (lhsExpr : Expr) (i : Nat) : MetaM (Expr × Expr × String) := do
  let some ci := (← getEnv).find? ``Fixture.trace
    | throwError "trace not found"
  let traceBody := zetaAll ci.value!
  let elems ← unpackListElems traceBody #[]
  let some (evExpr, tlAtI) := elems[i]? | throwError "trace[{i}] out of range"
  let (evCtor, #[hexApp]) := evExpr.getAppFnArgs | throwError "unexpected event {evExpr}"
  let (_, #[.lit (.strVal s)]) := hexApp.getAppFnArgs | throwError "unexpected hexApp"
  let evThm := match evCtor with
    | ``MachineEvent.recv => ``evBytes_recv
    | ``MachineEvent.send => ``evBytes_send
    | ``MachineEvent.pt => ``evBytes_pt
    | ``MachineEvent.accept => ``evBytes_accept
    | ``MachineEvent.rng => ``evBytes_rng
    | _ => panic! "unexpected event constructor"
  let listBv8Ty := mkApp (mkConst ``List [0]) (mkApp (mkConst ``BitVec) (mkNatLit 8))
  let mut curTerm := mkApp2 (mkConst ``traceAt) traceBody (mkNatLit i)
  let mut curPrf := mkApp2 (mkConst ``Eq.refl [1]) listBv8Ty lhsExpr
  for k in [0:i] do
    let (hd, tl) := elems[k]!
    let rem := i - 1 - k
    let nextTerm := mkApp2 (mkConst ``traceAt) tl (mkNatLit rem)
    let stepPrf := mkApp3 (mkConst ``traceAt_succ) hd tl (mkNatLit rem)
    curPrf := mkAppN (mkConst ``Eq.trans [1]) #[listBv8Ty, lhsExpr, curTerm, nextTerm, curPrf, stepPrf]
    curTerm := nextTerm
  let evBytesTerm := mkApp (mkConst ``evBytes) evExpr
  let stepZero := mkApp2 (mkConst ``traceAt_zero) evExpr tlAtI
  curPrf := mkAppN (mkConst ``Eq.trans [1]) #[listBv8Ty, lhsExpr, curTerm, evBytesTerm, curPrf, stepZero]
  let stepEv := mkApp (mkConst evThm) hexApp
  let eqEv := mkAppN (mkConst ``Eq.trans [1]) #[listBv8Ty, lhsExpr, evBytesTerm, hexApp, curPrf, stepEv]
  pure (eqEv, hexApp, s)

elab "def_raw_trace_ev " thmId:ident " : " lhsId:ident " := " idx:num : command => do
  liftTermElabM do
    let lhsExpr := mkConst (← realizeGlobalConstNoOverloadWithInfo lhsId)
    let (eqEv, hexApp, _) ← mkRawEvProof lhsExpr idx.getNat
    let listBv8Ty := mkApp (mkConst ``List [0]) (mkApp (mkConst ``BitVec) (mkNatLit 8))
    let fullTy := mkApp3 (mkConst ``Eq [1]) listBv8Ty lhsExpr hexApp
    addDecl <| .thmDecl {
      name := (← getCurrNamespace) ++ thmId.getId, levelParams := [], type := fullTy, value := eqEv }

elab "def_fast_trace_ev " thmId:ident " : " lhsId:ident " := " idx:num : command => do
  liftTermElabM do
    let lhsExpr := mkConst (← realizeGlobalConstNoOverloadWithInfo lhsId)
    let (eqEv, hexApp, s) ← mkRawEvProof lhsExpr idx.getNat
    let strExpr := mkStrLit s
    let charTy := mkConst ``Char
    let listCharTy := mkApp (mkConst ``List [0]) charTy
    let mut csExpr := mkApp (mkConst ``List.nil [0]) charTy
    for c in s.toList.reverse do
      csExpr := mkApp3 (mkConst ``List.cons [0]) charTy (toExpr c) csExpr
    let bv8Ty := mkApp (mkConst ``BitVec) (mkNatLit 8)
    let listBv8Ty := mkApp (mkConst ``List [0]) bv8Ty
    let mut bsExpr := mkApp (mkConst ``List.nil [0]) bv8Ty
    for b in (parseHexStr s).reverse do
      let bvExpr := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 8) (mkNatLit b.toNat)
      bsExpr := mkApp3 (mkConst ``List.cons [0]) bv8Ty bvExpr bsExpr
    let strTy := mkConst ``String
    let ofListCs := mkApp (mkConst ``String.ofList) csExpr
    let strEq := mkApp2 (mkConst ``Eq.refl [1]) strTy strExpr
    let toListFn := mkConst ``String.toList
    let toListEq1 := mkAppN (mkConst ``congrArg [1, 1])
      #[strTy, listCharTy, strExpr, ofListCs, toListFn, strEq]
    let toListEq2 := mkApp (mkConst ``String.toList_ofList) csExpr
    let toListEq := mkAppN (mkConst ``Eq.trans [1])
      #[listCharTy, mkApp toListFn strExpr, mkApp toListFn ofListCs, csExpr, toListEq1, toListEq2]
    let hbcFn := mkConst ``hexBytesChars
    let hbcCs := mkApp hbcFn csExpr
    let eq1 := mkApp (mkConst ``hexBytes_eq_hexBytesChars) strExpr
    let eq2 := mkAppN (mkConst ``congrArg [1, 1])
      #[listCharTy, listBv8Ty, mkApp toListFn strExpr, csExpr, hbcFn, toListEq]
    let eqHex1 := mkAppN (mkConst ``Eq.trans [1])
      #[listBv8Ty, hexApp, mkApp hbcFn (mkApp toListFn strExpr), hbcCs, eq1, eq2]
    let eqGo := mkApp2 (mkConst ``Eq.refl [1]) listBv8Ty bsExpr
    let eqHexGo := mkAppN (mkConst ``Eq.trans [1])
      #[listBv8Ty, hexApp, hbcCs, bsExpr, eqHex1, eqGo]
    let fullPrf := mkAppN (mkConst ``Eq.trans [1])
      #[listBv8Ty, lhsExpr, hexApp, bsExpr, eqEv, eqHexGo]
    let fullTy := mkApp3 (mkConst ``Eq [1]) listBv8Ty lhsExpr bsExpr
    addDecl <| .thmDecl {
      name := (← getCurrNamespace) ++ thmId.getId, levelParams := [], type := fullTy, value := fullPrf }

elab "def_raw_rng_slice " thmId:ident " : " lhsId:ident " := " offStx:num lenStx:num : command => do
  liftTermElabM do
    let off := offStx.getNat
    let len := lenStx.getNat
    let lhsExpr := mkConst (← realizeGlobalConstNoOverloadWithInfo lhsId)
    let some ci := (← getEnv).find? ``Fixture.trace
      | throwError "trace not found"
    let traceBody := zetaAll ci.value!
    let elems ← unpackListElems traceBody #[]
    let meTy := mkConst ``MachineEvent
    let listMeTy := mkApp (mkConst ``List [0]) meTy
    let listBv8Ty := mkApp (mkConst ``List [0]) (mkApp (mkConst ``BitVec) (mkNatLit 8))
    let listHwTy := mkApp (mkConst ``List [0]) listBv8Ty
    let startDrop := mkApp2 (mkConst ``dropEv) (mkNatLit off) traceBody
    let mut curDrop := startDrop
    let mut dropPrf := mkApp2 (mkConst ``Eq.refl [1]) listMeTy startDrop
    for k in [0:off] do
      let (hd, tl) := elems[k]!
      let rem := off - 1 - k
      let nextDrop := mkApp2 (mkConst ``dropEv) (mkNatLit rem) tl
      let step := mkApp3 (mkConst ``dropEv_succ) hd tl (mkNatLit rem)
      dropPrf := mkAppN (mkConst ``Eq.trans [1]) #[listMeTy, startDrop, curDrop, nextDrop, dropPrf, step]
      curDrop := nextDrop
    let tlAtOff := if off == 0 then traceBody else elems[off - 1]!.2
    let stepZero := mkApp (mkConst ``dropEv_zero) tlAtOff
    dropPrf := mkAppN (mkConst ``Eq.trans [1]) #[listMeTy, startDrop, curDrop, tlAtOff, dropPrf, stepZero]
    let tmFn := mkApp (mkConst ``takeMapEv) (mkNatLit len)
    let eq0 := mkApp2 (mkConst ``Eq.refl [1]) listHwTy lhsExpr
    let eq1 := mkAppN (mkConst ``congrArg [1, 1]) #[listMeTy, listHwTy, startDrop, tlAtOff, tmFn, dropPrf]
    let eq01 := mkAppN (mkConst ``Eq.trans [1])
      #[listHwTy, lhsExpr, mkApp tmFn startDrop, mkApp tmFn tlAtOff, eq0, eq1]
    let tlAtEnd := elems[off + len - 1]!.2
    let mut accTerm := mkApp (mkConst ``List.nil [0]) listBv8Ty
    let mut accLhs := mkApp2 (mkConst ``takeMapEv) (mkNatLit 0) tlAtEnd
    let mut accPrf := mkApp (mkConst ``takeMapEv_zero) tlAtEnd
    for j in (List.range len).reverse do
      let idx := off + j
      let (evExpr, tlAfter) := elems[idx]!
      let (_, #[hexApp]) := evExpr.getAppFnArgs | throwError "bad rng event"
      let rem := len - 1 - j
      let newLhs := mkApp2 (mkConst ``takeMapEv) (mkNatLit (rem + 1))
        (mkApp3 (mkConst ``List.cons [0]) meTy evExpr tlAfter)
      let midTerm := mkApp3 (mkConst ``List.cons [0]) listBv8Ty hexApp accLhs
      let newTerm := mkApp3 (mkConst ``List.cons [0]) listBv8Ty hexApp accTerm
      let step1 := mkApp3 (mkConst ``takeMapEv_succ) hexApp tlAfter (mkNatLit rem)
      let step2 := mkAppN (mkConst ``congrArg [1, 1])
        #[listHwTy, listHwTy, accLhs, accTerm, mkApp2 (mkConst ``List.cons [0]) listBv8Ty hexApp, accPrf]
      accPrf := mkAppN (mkConst ``Eq.trans [1]) #[listHwTy, newLhs, midTerm, newTerm, step1, step2]
      accLhs := newLhs
      accTerm := newTerm
    let fullPrf := mkAppN (mkConst ``Eq.trans [1])
      #[listHwTy, lhsExpr, mkApp tmFn tlAtOff, accTerm, eq01, accPrf]
    let fullTy := mkApp3 (mkConst ``Eq [1]) listHwTy lhsExpr accTerm
    addDecl <| .thmDecl {
      name := (← getCurrNamespace) ++ thmId.getId, levelParams := [], type := fullTy, value := fullPrf }

end FastHex

def_raw_trace_ev blob0_raw : blob0 := 0
def_raw_rng_slice rngPieces0_raw : rngPieces0 := 1 34
def_raw_trace_ev pt1_raw : pt1 := 35
def_raw_trace_ev coins1_raw : coins1 := 36
def_raw_trace_ev c1Out_raw : c1Out := 37
def_raw_trace_ev coins2_raw : coins2 := 39
def_raw_trace_ev pt3_raw : pt3 := 41
def_raw_trace_ev c3Out_raw : c3Out := 42
def_raw_rng_slice rngPieces4_raw : rngPieces4 := 44 34
def_raw_trace_ev pt5_raw : pt5 := 78
def_raw_trace_ev coins5_raw : coins5 := 79
def_raw_trace_ev c5Out_raw : c5Out := 80
def_raw_trace_ev c6In_raw : c6In := 81
def_raw_trace_ev coins6_raw : coins6 := 82
def_raw_trace_ev pt6Out_raw : pt6Out := 83

def_fast_trace_ev blob0_val : blob0 := 0
def_fast_trace_ev c1Out_val : c1Out := 37
def_fast_trace_ev c3Out_val : c3Out := 42
def_fast_trace_ev c5Out_val : c5Out := 80
def_fast_trace_ev c6In_val : c6In := 81

def s1 : HwBytes := slice c1Out 75 143
def s3 : HwBytes := slice c3Out 75 143
def s5 : HwBytes := slice c5Out 75 143
def pkSpk : HwBytes := slice blob0 47 32
def pkBob : HwBytes := slice blob0 1781 32
def c6BaseKey : HwBytes := slice c6In 4 33

def chevalPubKey (s : HwBytes) : HwBytes :=
  if s = clamp cwSetup.spk then pkSpk
  else if s = clamp cwSetup.bobId then pkBob
  else toyPubKey

def chevalInterp : ExternInterpretation := fun symbol arguments =>
  if symbol = x25519PublicKeySymbol then
    match arguments with | [s] => some (chevalPubKey s) | _ => none
  else if symbol = x25519AgreementSymbol then
    match arguments with | [_, point] => some (toyAgreement point) | _ => none
  else if symbol = aesCbcEncryptSymbol ∨ symbol = aesCbcDecryptSymbol then
    match arguments with | [text, _, _] => some text | _ => none
  else none

def chevalRecords : ProtocolSetup := cwSetup.compRecords

private theorem length_slice_of_le {l : HwBytes} {off len : Nat} (h : off + len ≤ l.length) :
    (slice l off len).length = len := by
  simp only [slice, List.length_take, List.length_drop]; omega

private theorem blob0_length : blob0.length = 1813 := by rw [blob0_val]; decide +kernel
theorem c1Out_length : c1Out.length = 1797 := by rw [c1Out_val]; decide +kernel
private theorem c3Out_length : c3Out.length = 1797 := by rw [c3Out_val]; decide +kernel
theorem c6In_length : c6In.length = 1797 := by rw [c6In_val]; decide +kernel

theorem s1_length : s1.length = 143 := length_slice_of_le (by have := c1Out_length; omega)
theorem s3_length : s3.length = 143 := length_slice_of_le (by have := c3Out_length; omega)

theorem coins0_length : coins0.length = 192 := by unfold coins0; rw [rngPieces0_raw]; decide +kernel
theorem coins1_length : coins1.length = 64 := by rw [coins1_raw]; decide +kernel
theorem coins2_length : coins2.length = 32 := by rw [coins2_raw]; decide +kernel
theorem coins4_length : coins4.length = 192 := by unfold coins4; rw [rngPieces4_raw]; decide +kernel
theorem coins5_length : coins5.length = 64 := by rw [coins5_raw]; decide +kernel
theorem coins6_length : coins6.length = 32 := by rw [coins6_raw]; decide +kernel
theorem pt1_length : pt1.length = 5 := by rw [pt1_raw]; decide +kernel
theorem pt3_length : pt3.length = 6 := by rw [pt3_raw]; decide +kernel
theorem pt5_length : pt5.length = 5 := by rw [pt5_raw]; decide +kernel

private theorem pkSpk_length : pkSpk.length = 32 := length_slice_of_le (by have := blob0_length; omega)
private theorem pkBob_length : pkBob.length = 32 := length_slice_of_le (by have := blob0_length; omega)
private theorem pkSpk_lt_p25519 : leValue (pkSpk.map BitVec.toNat) < p25519 := by unfold pkSpk; rw [blob0_val]; decide +kernel
private theorem pkBob_lt_p25519 : leValue (pkBob.map BitVec.toNat) < p25519 := by unfold pkBob; rw [blob0_val]; decide +kernel
private theorem pkSpk_not_lowOrder : isLowOrderKey (pkSpk.map BitVec.toNat) = false := by unfold pkSpk; rw [blob0_val]; decide +kernel
private theorem pkBob_not_lowOrder : isLowOrderKey (pkBob.map BitVec.toNat) = false := by unfold pkBob; rw [blob0_val]; decide +kernel

private theorem chevalPubKey_length (s : HwBytes) : (chevalPubKey s).length = 32 := by
  unfold chevalPubKey; split; { exact pkSpk_length }; split; { exact pkBob_length }; exact toyPubKey_length

private theorem chevalPubKey_lt_p25519 (s : HwBytes) :
    leValue ((chevalPubKey s).map BitVec.toNat) < p25519 := by
  unfold chevalPubKey; split; { exact pkSpk_lt_p25519 }; split; { exact pkBob_lt_p25519 }; exact toyPubKey_lt_p25519

private theorem chevalPubKey_not_lowOrder (s : HwBytes) :
    isLowOrderKey ((chevalPubKey s).map BitVec.toNat) = false := by
  unfold chevalPubKey; split; { exact pkSpk_not_lowOrder }; split; { exact pkBob_not_lowOrder }; exact toyPubKey_not_lowOrder

theorem chevalInterp_publicKey (s : HwBytes) :
    chevalInterp x25519PublicKeySymbol [s] = some (chevalPubKey s) := by simp [chevalInterp]

private theorem chevalInterp_agreement (s p : HwBytes) :
    chevalInterp x25519AgreementSymbol [s, p] = some (toyAgreement p) := by
  simp [chevalInterp, x25519PublicKeySymbol, x25519AgreementSymbol]

theorem chevalInterp_cryptoEquationsHold : ExternCryptoLawsHold chevalInterp where
  x25519_agreement_commutes a b := by
    simp only [chevalInterp_publicKey, Option.getD_some, chevalInterp_agreement,
      toyAgreement, chevalPubKey_not_lowOrder, Bool.false_eq_true, ↓reduceIte]
  x25519_agreement_length a p := by simp [chevalInterp_agreement, length_toyAgreement]
  x25519_public_key_length a := by simp [chevalInterp_publicKey, chevalPubKey_length]
  x25519_agreement_reads_u_coordinate a b b' hb hb' hu := by
    simp only [chevalInterp_agreement]
    have hl : isLowOrderKey (b.map BitVec.toNat) = isLowOrderKey (b'.map BitVec.toNat) := by
      simp only [isLowOrderKey, List.length_map, hb, hb']
      exact congrArg (fun u => (32 == 32 && lowOrderUs.contains u)) hu
    simp only [toyAgreement, hl]
  x25519_agreement_torsion_invariant secret point t := by
    simp only [chevalInterp_agreement]; congr 1; unfold torsionShift
    split
    · rfl
    · have h1 : x25519TorsionSymbol ≠ x25519PublicKeySymbol := by decide
      have h2 : x25519TorsionSymbol ≠ x25519AgreementSymbol := by decide
      have h3 : x25519TorsionSymbol ≠ aesCbcEncryptSymbol := by decide
      have h4 : x25519TorsionSymbol ≠ aesCbcDecryptSymbol := by decide
      simp [chevalInterp, h1, h2, h3, h4]
  x25519_agreement_zero_iff_low_order a b _ _ := by
    rw [chevalInterp_agreement, Option.getD_some]; unfold toyAgreement
    cases h : isLowOrderKey (b.map BitVec.toNat)
    · simp only [Bool.false_eq_true, ↓reduceIte, iff_false]; exact toyNonzeroAgreement_ne_zero
    · simp only [↓reduceIte]
  x25519_public_key_not_low_order a _ := by simp [chevalInterp_publicKey, chevalPubKey_not_lowOrder]
  aes_cbc_decrypt_inverts_encrypt plaintext key iv := by
    simp [chevalInterp, x25519PublicKeySymbol, x25519AgreementSymbol,
      aesCbcEncryptSymbol, aesCbcDecryptSymbol]
  aes_cbc_encrypt_of_decrypt c k iv p _ _ h := by
    simp [chevalInterp, x25519PublicKeySymbol, x25519AgreementSymbol,
      aesCbcEncryptSymbol, aesCbcDecryptSymbol] at h ⊢
    exact h.symm
  hmac_tag_length k d t h := by
    simp [chevalInterp, DY.Libsignal.PQXDH.Refinement.libcruxHmacSymbol,
      x25519PublicKeySymbol, x25519AgreementSymbol,
      aesCbcEncryptSymbol, aesCbcDecryptSymbol] at h

theorem chevalInterp_pubCanonical : X25519PubCanonical chevalInterp := fun s => by
  simp [chevalInterp_publicKey, chevalPubKey_lt_p25519]

theorem chevalInterp_torsionShiftsRejected : X25519TorsionShiftsRejected chevalInterp := by
  intro _ _ _ _ _ _ ⟨_, _, hto, _⟩
  have h1 : DY.Libsignal.PQXDH.Refinement.toEdwardsSymbol ≠ x25519PublicKeySymbol := by decide
  have h2 : DY.Libsignal.PQXDH.Refinement.toEdwardsSymbol ≠ x25519AgreementSymbol := by decide
  have h3 : DY.Libsignal.PQXDH.Refinement.toEdwardsSymbol ≠ aesCbcEncryptSymbol := by decide
  have h4 : DY.Libsignal.PQXDH.Refinement.toEdwardsSymbol ≠ aesCbcDecryptSymbol := by decide
  simp [chevalInterp, h1, h2, h3, h4] at hto

theorem chevalInterp_contractsHold : ExternContractsHoldCli chevalInterp :=
  ⟨chevalInterp_cryptoEquationsHold, chevalInterp_pubCanonical, chevalInterp_torsionShiftsRejected⟩

private theorem cwSetup_small :
    cwSetup.aliceId.length = 32 ∧ cwSetup.bobId.length = 32 ∧ cwSetup.spk.length = 32 ∧
    [cwSetup.aliceId, cwSetup.bobId, cwSetup.spk, fillFresh 11 64, fillFresh 16 64,
      fillFresh 17 64].Nodup := by decide +kernel

theorem chevalRecords_opaque :
    chevalRecords.opaqueBytes (setupPublic chevalRecords 5) = cwSetup.spkSig ∧
    chevalRecords.opaqueBytes (setupPublic chevalRecords 6) = cwSetup.kyberPk ∧
    chevalRecords.opaqueBytes (setupPublic chevalRecords 7) = cwSetup.kyberPkSig := by
  obtain ⟨h5, h6, h7⟩ := compRecords_public cwSetup
  refine ⟨?_, ?_, ?_⟩
  · rw [chevalRecords, h5]; dsimp only [PQXDHSpqrSetup.compRecords]
    rw [comp_gamma_sign, comp_gamma_randTerm_pos cwSetup 11 64 (by decide)]
    simp [PQXDHSpqrSetup.compSem, PQXDHSpqrSetup.compGhost, PQXDHSpqrSetup.fresh]
  · rw [chevalRecords, h6]; dsimp only [PQXDHSpqrSetup.compRecords]; rw [comp_gamma_kemPk]; rfl
  · rw [chevalRecords, h7]; dsimp only [PQXDHSpqrSetup.compRecords]
    rw [comp_gamma_sign, comp_gamma_randTerm_pos cwSetup 17 64 (by decide)]
    simp [PQXDHSpqrSetup.compSem, PQXDHSpqrSetup.compGhost, PQXDHSpqrSetup.fresh, fillFresh_ne_11_17]

theorem chevalRecords_secrets :
    secretBytes chevalRecords 1 = cwSetup.bobId ∧
    secretBytes chevalRecords 2 = cwSetup.spk := by
  have hR := compRecords_randomsAt cwSetup
  constructor <;>
    (rw [chevalRecords, secretBytes, hR]; simp [PQXDHSpqrSetup.compRecords, PQXDHSpqrSetup.fresh])

theorem chevalRecords_wf : ProtocolSetupWF chevalRecords := by
  obtain ⟨_, r, ⟨⟨_, _, _, hss, hk, hks, hsec, hslice⟩, _, _, _, _, _, _, _, _, ho5, ho6, ho7, hksB, _⟩, _⟩ :=
    Fixture.nonvacuous
  obtain ⟨ha, hb, hs, hnd⟩ := cwSetup_small
  obtain ⟨o5, o6, o7⟩ := chevalRecords_opaque
  have hR := compRecords_randomsAt cwSetup
  refine ⟨compRecords_ne cwSetup, ?_, ?_,
    by dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSigTerm] at hss ⊢; rw [o5, ← ho5]; exact hss,
    by dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm] at hk ⊢; rw [o6, ← ho6]; exact hk,
    by dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkSigTerm] at hks ⊢; rw [o7, ← ho7]; exact hks,
    by show cwSetup.kyberSec.length = 3169; rw [← hksB]; exact hsec,
    by show slice cwSetup.kyberSec 1537 1568 = _; dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm] at hslice ⊢; rw [o6, ← hksB, ← ho6]; exact hslice⟩
  · rw [chevalRecords, hR]; intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [PQXDHSpqrSetup.compRecords, PQXDHSpqrSetup.fresh, fillFresh, ha, hb, hs]
  · rw [chevalRecords, hR]; simpa [PQXDHSpqrSetup.compRecords, PQXDHSpqrSetup.fresh] using hnd

/-! ## Bundle Blob, Canonical Pre-Key Messages, and Wire Parses -/

def cwBundle : PublicBundle where
  registrationId := cwSetup.regIdB
  identityKey := ecKey pkBob
  signedId := cwSetup.spkId
  signedKey := ecKey pkSpk
  signedSig := cwSetup.spkSig
  kyberId := cwSetup.kpkId
  kyberKey := kyberKey cwSetup.kyberPk
  kyberSig := cwSetup.kyberPkSig
  oneTime := none

theorem clamp_bobId_ne_spk : clamp cwSetup.bobId ≠ clamp cwSetup.spk := by decide +kernel

theorem bundleBlob_cwBundle : bundleBlob cwBundle = blob0 := by
  unfold cwBundle pkBob pkSpk; rw [blob0_val]; apply eq_of_beq; decide +kernel

theorem parse_c1Out_msg : (parsePreKeyWire c1Out).map (·.message) = some s1 := by
  unfold s1; rw [c1Out_val]; apply eq_of_beq; decide +kernel

theorem parse_c3Out_msg : (parsePreKeyWire c3Out).map (·.message) = some s3 := by
  unfold s3; rw [c3Out_val]; apply eq_of_beq; decide +kernel

theorem parse_c5Out_msg : (parsePreKeyWire c5Out).map (·.message) = some s5 := by
  unfold s5; rw [c5Out_val]; apply eq_of_beq; decide +kernel

theorem parse_c6In_fields :
    (parsePreKeyWire c6In).map (fun q => (q.message, q.baseKey.take 33)) =
      some (s3, c6BaseKey) := by
  unfold s3 c6BaseKey; rw [c6In_val, c3Out_val]; apply eq_of_beq; decide +kernel

private theorem sentBody_of_preKey {bs msg : HwBytes}
    (hh : bs.head? = some 3#8) (hp : (parsePreKeyWire bs).map (·.message) = some msg) :
    (sentBody bs).toList = [msg] := by
  cases hc : bs with
  | nil => simp [hc] at hh
  | cons b tl =>
    simp only [hc, List.head?_cons, Option.some.injEq] at hh; subst hh
    have hw : (3#8 : BitVec 8) ≠ DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag := by decide
    simp only [sentBody, ← hc, hw, ↓reduceIte, hp, Option.toList]

theorem sentBody_c1Out : (sentBody c1Out).toList = [s1] :=
  sentBody_of_preKey (bs := c1Out) (by rw [c1Out_val]; decide +kernel) parse_c1Out_msg
theorem sentBody_c3Out : (sentBody c3Out).toList = [s3] :=
  sentBody_of_preKey (bs := c3Out) (by rw [c3Out_val]; decide +kernel) parse_c3Out_msg
theorem sentBody_c5Out : (sentBody c5Out).toList = [s5] :=
  sentBody_of_preKey (bs := c5Out) (by rw [c5Out_val]; decide +kernel) parse_c5Out_msg

theorem canonicalPreKey_c1Out : CanonicalPreKey c1Out :=
  ⟨none, 7, 9, 1111, slice c1Out 40 32, slice c1Out 5 32, slice c1Out 229 1568, s1,
    length_slice_of_le (by have := c1Out_length; omega),
    length_slice_of_le (by have := c1Out_length; omega),
    length_slice_of_le (by have := c1Out_length; omega),
    by unfold s1; rw [c1Out_val]; apply eq_of_beq; decide +kernel⟩

theorem canonicalPreKey_c6In : CanonicalPreKey c6In :=
  ⟨none, 7, 9, 1111, slice c6In 40 32, slice c6In 5 32, slice c6In 229 1568, s3,
    length_slice_of_le (by have := c6In_length; omega),
    length_slice_of_le (by have := c6In_length; omega),
    length_slice_of_le (by have := c6In_length; omega),
    by unfold s3; rw [c6In_val, c3Out_val]; apply eq_of_beq; decide +kernel⟩

theorem c6BaseKey_take2 : c6BaseKey.take 2 = [0x05#8, 0x50#8] := by
  unfold c6BaseKey; rw [c6In_val]; decide +kernel

theorem pt3_ne_pt1 : pt3 ≠ pt1 := by
  intro h; have := congrArg List.length h; rw [pt3_length, pt1_length] at this; cases this

theorem pt5_ne_pt1 : pt5 ≠ pt1 := by rw [pt5_raw, pt1_raw]; decide +kernel

theorem pt5_ne_pt3 : pt5 ≠ pt3 := by
  intro h; have := congrArg List.length h; rw [pt5_length, pt3_length] at this; cases this

theorem c6In_ne_c1Out : c6In ≠ c1Out := by
  intro h; have h8 : c6In.take 8 = c1Out.take 8 := congrArg (List.take 8) h
  rw [c6In_val, c1Out_val] at h8; exact absurd h8 (by decide +kernel)

/-! ## CLI Trace Schedule, `CoinSplit`, and `CallsMatchSchedules` -/

/-- The 19-event CLI-granularity trace of the 7 calls (each run emits a single `.rng` of its
`coins` file). -/
def chevalCliTrace : List MachineEvent :=
  [.recv blob0, .rng coins0,
   .pt pt1, .rng coins1, .send c1Out,
   .recv c1Out, .rng coins2, .accept pt1,
   .pt pt3, .rng coins3, .send c3Out,
   .recv blob0, .rng coins4,
   .pt pt5, .rng coins5, .send c5Out,
   .recv c6In, .rng coins6, .accept pt6Out]

def chevalCalls : List (Participant × Bool) :=
  [("alice", true), ("alice", true), ("bob", true), ("alice", true),
   ("alice", true), ("alice", true), ("bob", true)]

section AssembledTrace
attribute [local irreducible] Symbolic.BugInjection.hexBytes

private theorem assembledHwTrace_eq :
    [.recv blob0] ++ rngPieces0.map .rng ++
      [.pt pt1, .rng coins1, .send c1Out,
       .recv c1Out, .rng coins2, .accept pt1,
       .pt pt3, .send c3Out,
       .recv blob0] ++ rngPieces4.map .rng ++
      [.pt pt5, .rng coins5, .send c5Out,
       .recv c6In, .rng coins6, .accept pt6Out] = cwTrace := by
  rw [blob0_raw, rngPieces0_raw, pt1_raw, coins1_raw, c1Out_raw, coins2_raw,
      pt3_raw, c3Out_raw, rngPieces4_raw, pt5_raw, coins5_raw, c5Out_raw,
      c6In_raw, coins6_raw, pt6Out_raw]
  rfl

end AssembledTrace

private theorem all_nonEmpty_imp {ps : List HwBytes} (h : (ps.all (fun p => !p.isEmpty)) = true) :
    ∀ p ∈ ps, p ≠ [] := by
  intro p hp heq; subst heq; have := List.all_eq_true.mp h [] hp; simp at this

theorem chevalCliTrace_coinSplit : CoinSplit chevalCliTrace cwTrace := by
  rw [← assembledHwTrace_eq]
  simp only [chevalCliTrace, List.append_assoc, List.cons_append, List.nil_append]
  have hp0 : ∀ p ∈ rngPieces0, p ≠ [] := by rw [rngPieces0_raw]; exact all_nonEmpty_imp (by decide +kernel)
  have hp4 : ∀ p ∈ rngPieces4, p ≠ [] := by rw [rngPieces4_raw]; exact all_nonEmpty_imp (by decide +kernel)
  have hc1 : ∀ p ∈ [coins1], p ≠ [] := by rw [coins1_raw]; exact all_nonEmpty_imp (by decide +kernel)
  have hc2 : ∀ p ∈ [coins2], p ≠ [] := by rw [coins2_raw]; exact all_nonEmpty_imp (by decide +kernel)
  have hc5 : ∀ p ∈ [coins5], p ≠ [] := by rw [coins5_raw]; exact all_nonEmpty_imp (by decide +kernel)
  have hc6 : ∀ p ∈ [coins6], p ≠ [] := by rw [coins6_raw]; exact all_nonEmpty_imp (by decide +kernel)
  exact CoinSplit.keep (fun _ h => nomatch h) <|
    CoinSplit.split (pieces := rngPieces0) hp0 (List.prefix_refl _) <|
    CoinSplit.keep (fun _ h => nomatch h) <| CoinSplit.split (pieces := [coins1]) hc1 (by simp) <|
    CoinSplit.keep (fun _ h => nomatch h) <| CoinSplit.keep (fun _ h => nomatch h) <|
    CoinSplit.split (pieces := [coins2]) hc2 (by simp) <|
    CoinSplit.keep (fun _ h => nomatch h) <| CoinSplit.keep (fun _ h => nomatch h) <|
    CoinSplit.split (pieces := []) (fun _ h => nomatch h) List.nil_prefix <|
    CoinSplit.keep (fun _ h => nomatch h) <| CoinSplit.keep (fun _ h => nomatch h) <|
    CoinSplit.split (pieces := rngPieces4) hp4 (List.prefix_refl _) <|
    CoinSplit.keep (fun _ h => nomatch h) <| CoinSplit.split (pieces := [coins5]) hc5 (by simp) <|
    CoinSplit.keep (fun _ h => nomatch h) <| CoinSplit.keep (fun _ h => nomatch h) <|
    CoinSplit.split (pieces := [coins6]) hc6 (by simp) <|
    CoinSplit.keep (fun _ h => nomatch h) CoinSplit.nil

theorem chevalCalls_fit : CallsMatchSchedules chevalCalls cwWho cwOk := by
  refine ⟨by decide, fun k p b hk hget => ?_⟩
  have hk6 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by simp [chevalCalls] at hk; omega
  rcases hk6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp [chevalCalls] at hget; obtain ⟨_, rfl⟩ := hget; rfl)
end Symbolic.Proofs.Tests.Refinement.Cli.Cheval26
