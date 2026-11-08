import Mathlib
import A306559
import Spec_A306559

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # Check_Spec_A306559 : clotures (Option B)

Verifie que la spec figee `Spec_A306559.lean` EST la cible
implementee dans `A306559.lean` : chaque corps verbatim
`SpecA306559.*` est egal a sa racine. Methode : `rfl` pour
les corps NON recursifs (delta+iota suffit) ; `funext` +
`induction` + `rw` des ponts deja prouves pour les corps
recursifs - deux constantes recursives DISTINCTES ne sont
jamais `rfl`-egales, l'egalite se prouve point par point.
Chaque enonce `SpecProp*` est `Iff` avec son pendant via
les egalites de fonctions. La proposition (EX, UN) reste
FORMULEE - et elle est PROUVEE dans `A306559.lean`
(`theorem A306559`), transportee ici par `proven_A306559`. -/

/-- L'alphabet spec EST l'alphabet racine (alias). -/
theorem spec_eq_letter306559 :
    SpecA306559.letterSpec = A306559.Letter306559 := rfl

/-- Corps verbatim : `isVowelSpec` est `isVowel306559`. -/
theorem spec_eq_isVowel306559 :
    SpecA306559.isVowelSpec = A306559.isVowel306559 := rfl

/-- Corps verbatim : `nameSpec` est `name306559`. -/
theorem spec_eq_name306559 :
    SpecA306559.nameSpec = A306559.name306559 := rfl

/-- Corps verbatim : `iterSpec` est `iter306559`
    (recursif : `funext` + induction). -/
theorem spec_eq_iter306559 :
    @SpecA306559.iterSpec = @A306559.iter306559 := by
  funext α f n x
  induction n with
  | zero => rfl
  | succ n ih =>
      show f (SpecA306559.iterSpec f n x) =
        f (A306559.iter306559 f n x)
      rw [ih]

/-- Corps verbatim : `stepSpec` est `step306559`. -/
theorem spec_eq_step306559 :
    SpecA306559.stepSpec = A306559.step306559 := rfl

/-- Corps verbatim : `wordOfSpec` est `wordOf306559`. -/
theorem spec_eq_wordOf306559 :
    SpecA306559.wordOfSpec = A306559.wordOf306559 := by
  funext a i
  show (SpecA306559.nameSpec (a (SpecA306559.iterSpec
        (SpecA306559.stepSpec a) i (0, 0)).1)).getD
      (SpecA306559.iterSpec (SpecA306559.stepSpec a) i (0, 0)).2
      A306559.Letter306559.O =
    (A306559.name306559 (a (A306559.iter306559
        (A306559.step306559 a) i (0, 0)).1)).getD
      (A306559.iter306559 (A306559.step306559 a) i (0, 0)).2
      A306559.Letter306559.O
  rw [spec_eq_iter306559, spec_eq_step306559, spec_eq_name306559]

/-- Corps verbatim : `cumSpec` est `cum306559` (recursif). -/
theorem spec_eq_cum306559 :
    SpecA306559.cumSpec = A306559.cum306559 := by
  funext a j
  induction j with
  | zero => rfl
  | succ j ih =>
      show SpecA306559.cumSpec a j +
          (SpecA306559.nameSpec (a j)).length =
        A306559.cum306559 a j + (A306559.name306559 (a j)).length
      rw [ih, spec_eq_name306559]

/-- Corps verbatim : `nextVowelSpec` est `nextVowel306559`
    (recursif sur le carburant). -/
theorem spec_eq_nextVowel306559 :
    SpecA306559.nextVowelSpec = A306559.nextVowel306559 := by
  funext a p f
  induction f generalizing p with
  | zero => rfl
  | succ f ih =>
      show (if SpecA306559.isVowelSpec (SpecA306559.wordOfSpec a p)
            then p else SpecA306559.nextVowelSpec a (p + 1) f) =
        (if A306559.isVowel306559 (A306559.wordOf306559 a p)
            then p else A306559.nextVowel306559 a (p + 1) f)
      rw [spec_eq_isVowel306559, spec_eq_wordOf306559, ih]

/-- Corps verbatim : `vposSpec` est `vpos306559` (recursif). -/
theorem spec_eq_vpos306559 :
    SpecA306559.vposSpec = A306559.vpos306559 := by
  funext a k
  induction k with
  | zero =>
      show SpecA306559.nextVowelSpec a 0 5 =
        A306559.nextVowel306559 a 0 5
      rw [spec_eq_nextVowel306559]
  | succ k ih =>
      show SpecA306559.nextVowelSpec a
          (SpecA306559.vposSpec a k + 1) 5 =
        A306559.nextVowel306559 a
          (A306559.vpos306559 a k + 1) 5
      rw [ih, spec_eq_nextVowel306559]

/-- Corps verbatim : `runSpec` est `run306559`. -/
theorem spec_eq_run306559 :
    SpecA306559.runSpec = A306559.run306559 := by
  funext a k
  show SpecA306559.vposSpec a (k + 1) - SpecA306559.vposSpec a k - 1 =
    A306559.vpos306559 a (k + 1) - A306559.vpos306559 a k - 1
  rw [spec_eq_vpos306559]

/-- Corps verbatim : `WSpec` est `W306559`. -/
theorem spec_eq_W306559 :
    SpecA306559.WSpec = A306559.W306559 := rfl

/-- Corps verbatim : `MstepSpec` est `Mstep306559`. -/
theorem spec_eq_Mstep306559 :
    SpecA306559.MstepSpec = A306559.Mstep306559 := rfl

/-- Corps verbatim : `bitsAuxSpec` est `bitsAux306559`
    (recursif sur le carburant). -/
theorem spec_eq_bitsAux306559 :
    SpecA306559.bitsAuxSpec = A306559.bitsAux306559 := by
  funext f n
  induction f generalizing n with
  | zero => rfl
  | succ f ih =>
      show (if n = 0 then [] else
          (n % 2) :: SpecA306559.bitsAuxSpec f (n / 2)) =
        (if n = 0 then [] else
          (n % 2) :: A306559.bitsAux306559 f (n / 2))
      rw [ih]

/-- Corps verbatim : `bitsSpec` est `bits306559`. -/
theorem spec_eq_bits306559 :
    SpecA306559.bitsSpec = A306559.bits306559 := by
  funext n
  show SpecA306559.bitsAuxSpec (n + 1) n =
    A306559.bitsAux306559 (n + 1) n
  rw [spec_eq_bitsAux306559]

/-- Corps verbatim : `MfoldSpec` est `Mfold306559`. -/
theorem spec_eq_Mfold306559 :
    SpecA306559.MfoldSpec = A306559.Mfold306559 := by
  funext n
  show ((SpecA306559.bitsSpec n).dropLast.reverse).foldl
      SpecA306559.MstepSpec 0 =
    ((A306559.bits306559 n).dropLast.reverse).foldl
      A306559.Mstep306559 0
  rw [spec_eq_bits306559, spec_eq_Mstep306559]

/-- Corps verbatim : `MSpec` est `M306559`. -/
theorem spec_eq_M306559 :
    SpecA306559.MSpec = A306559.M306559 := by
  funext n
  show SpecA306559.MfoldSpec (n + 1) = A306559.Mfold306559 (n + 1)
  rw [spec_eq_Mfold306559]

/-- Corps verbatim : `aStarSpec` est `aStar306559`
    (match non recursif : cas litteraux). -/
theorem spec_eq_aStar306559 :
    SpecA306559.aStarSpec = A306559.aStar306559 := by
  funext k
  cases k with
  | zero => rfl
  | succ k =>
      cases k with
      | zero => rfl
      | succ k =>
          cases k with
          | zero => rfl
          | succ k =>
              show (SpecA306559.MSpec k).castLE (by decide) =
                (A306559.M306559 k).castLE (by decide)
              rw [spec_eq_M306559]

/-- (EX) : la spec d'existence est `conjectureEX306559`. -/
theorem spec_prop_EX306559 :
    SpecPropEXA306559 ↔ A306559.conjectureEX306559 := by
  show (∀ k : ℕ, SpecA306559.runSpec SpecA306559.aStarSpec k =
        (SpecA306559.aStarSpec k).val) ↔
      (∀ k : ℕ, A306559.run306559 A306559.aStar306559 k =
        (A306559.aStar306559 k).val)
  rw [spec_eq_run306559, spec_eq_aStar306559]

/-- (UN) : la spec d'unicite est `conjectureUN306559`. -/
theorem spec_prop_UN306559 :
    SpecPropUNA306559 ↔ A306559.conjectureUN306559 := by
  show (∀ a : ℕ → Fin 4,
        a 0 = 1 → a 1 = 2 → a 2 = 3 →
        (∀ k : ℕ, SpecA306559.runSpec a k = (a k).val) →
          a = SpecA306559.aStarSpec) ↔
      (∀ a : ℕ → Fin 4,
        a 0 = 1 → a 1 = 2 → a 2 = 3 →
        (∀ k : ℕ, A306559.run306559 a k = (a k).val) →
          a = A306559.aStar306559)
  rw [spec_eq_run306559, spec_eq_aStar306559]

/-- La spec complete est le capstone `A306559`. -/
theorem spec_prop_full306559 :
    SpecPropA306559 ↔ A306559.conjectureEX306559 ∧
      A306559.conjectureUN306559 := by
  show ((∀ k : ℕ, SpecA306559.runSpec SpecA306559.aStarSpec k =
          (SpecA306559.aStarSpec k).val) ∧
        (∀ a : ℕ → Fin 4,
          a 0 = 1 → a 1 = 2 → a 2 = 3 →
          (∀ k : ℕ, SpecA306559.runSpec a k = (a k).val) →
            a = SpecA306559.aStarSpec)) ↔
      ((∀ k : ℕ, A306559.run306559 A306559.aStar306559 k =
          (A306559.aStar306559 k).val) ∧
        (∀ a : ℕ → Fin 4,
          a 0 = 1 → a 1 = 2 → a 2 = 3 →
          (∀ k : ℕ, A306559.run306559 a k = (a k).val) →
            a = A306559.aStar306559))
  rw [spec_eq_run306559, spec_eq_aStar306559]

/-- L'implementation prouve la spec. -/
theorem proven_A306559 : SpecPropA306559 :=
  spec_prop_full306559.mpr A306559
