import Mathlib
import A306559
import Spec_A306559

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # Check_AntiVacuite_A306559 : non-vacuite et ancres

La conjecture Neder n'est pas vide de sens :
- la conjonction COMPLETE des hypotheses de `UN` (graine +
  equation auto-descriptive) est satisfaite par
  `aStar306559` - c'est exactement `EX` deja prouve ;
- le morphisme `M306559` est non constant (0 ET 1 sont
  atteints) et son prefixe certifie coincide avec la
  suite `r43-check.txt` : `0,1,1,0,1,0,1,1,1` ;
- les runs initiaux `[1,2,3,0,1]` sont certifies par
  `decide` - `run 3 = 0` montre que la valeur `0` est
  atteinte (la suite n'est pas `>= 1` partout) ;
- `decide` est legitime ici : toutes les definitions sont
  structurellement recursives (iterateur, carburant 5 pour
  `nextVowel`, carburant `n+1` pour `bitsAux`), sans
  `WellFounded.fix` - `Nat.digits` n'est PAS utilise pour
  cette raison (voir `A306559.lean`).

ABLATION (chargee) : `aBad306559` coincide avec `aStar`
sauf au bloc 3 (`ONE` au lieu de `ZERO`) : l'equation
auto-descriptive CASSE deja a `k = 4` - la valeur de
`M(1)` n'est donc pas gratuite, l'equation contraint
reellement la queue morphique. -/

open A306559

/-- (a) Satisfiabilite : TOUTES les hypotheses de `UN` sont
    realisees simultanement par `aStar306559` (graine +
    equation complete, grace a `aStar306559_selfdesc`). -/
theorem antiVac_sat306559 : ∃ a : ℕ → Fin 4,
    a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 3 ∧
      (∀ k : ℕ, run306559 a k = (a k).val) :=
  ⟨aStar306559, rfl, rfl, rfl, aStar306559_selfdesc⟩

/-- (b) Ancres morphiques : prefixe `M(0..8) =
    0,1,1,0,1,0,1,1,1` (fichier `r43-check.txt`). -/
theorem antiVac_M_prefix306559 :
    M306559 0 = 0 ∧ M306559 1 = 1 ∧ M306559 2 = 1 ∧
    M306559 3 = 0 ∧ M306559 4 = 1 ∧ M306559 5 = 0 ∧
    M306559 6 = 1 ∧ M306559 7 = 1 ∧ M306559 8 = 1 := by
  decide

/-- `aStar` sur la graine et le debut de la queue :
    `1,2,3,0,1,1,0,1,0,1,1`. -/
theorem antiVac_aStar_prefix306559 :
    aStar306559 0 = 1 ∧ aStar306559 1 = 2 ∧
    aStar306559 2 = 3 ∧ aStar306559 3 = 0 ∧
    aStar306559 4 = 1 ∧ aStar306559 5 = 1 ∧
    aStar306559 6 = 0 ∧ aStar306559 7 = 1 ∧
    aStar306559 8 = 0 ∧ aStar306559 9 = 1 ∧
    aStar306559 10 = 1 := by
  decide

/-- Ancres de positions de voyelles : `0,2,5,9,10,12,14`
    (ONE|TWO|THREE|ZERO|ONE|ONE...). -/
theorem antiVac_vpos_prefix306559 :
    vpos306559 aStar306559 0 = 0 ∧ vpos306559 aStar306559 1 = 2 ∧
    vpos306559 aStar306559 2 = 5 ∧ vpos306559 aStar306559 3 = 9 ∧
    vpos306559 aStar306559 4 = 10 ∧ vpos306559 aStar306559 5 = 12 ∧
    vpos306559 aStar306559 6 = 14 := by
  decide

/-- Ancres de runs : les 7 premiers runs sont
    `1,2,3,0,1,1,0` - autodescription sur le prefixe. -/
theorem antiVac_run_prefix306559 :
    run306559 aStar306559 0 = 1 ∧ run306559 aStar306559 1 = 2 ∧
    run306559 aStar306559 2 = 3 ∧ run306559 aStar306559 3 = 0 ∧
    run306559 aStar306559 4 = 1 ∧ run306559 aStar306559 5 = 1 ∧
    run306559 aStar306559 6 = 0 := by
  decide

/-- Le morphisme n'est pas constant : `0` et `1` sont tous
    deux atteints (sinon `W` decrirait un mot constant). -/
theorem antiVac_M_nonconstant306559 :
    (∃ k, M306559 k = 0) ∧ (∃ k, M306559 k = 1) :=
  ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩

/-- Suite ablation : identique a `aStar` sauf au bloc 3,
    ou `ZERO` est remplace par `ONE`. -/
def aBad306559 : ℕ → Fin 4 := fun j => if j = 3 then 1 else aStar306559 j

/-- (c) Ablation : sans la bonne valeur `M(0)` au bloc 3,
    l'equation auto-descriptive casse des `k = 4` :
    `run = 0` contre `aBad 4 = aStar 4 = 1`. L'equation
    discrimine donc reellement la queue morphique. -/
theorem antiVac_ablation306559 :
    ¬ (∀ k : ℕ, run306559 aBad306559 k = (aBad306559 k).val) := by
  intro h
  have h4 : run306559 aBad306559 4 = 0 := by decide
  have hv : (aBad306559 4).val = 1 := by decide
  have h' := h 4
  rw [h4, hv] at h'
  exact absurd h' (by decide)

#print axioms A306559
