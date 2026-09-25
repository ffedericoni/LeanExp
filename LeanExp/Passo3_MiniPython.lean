/-!
# Passo 3 — "Deep embedding": un mini-Python dentro Lean

Nei passi 1–2 abbiamo tradotto *a mano* ogni funzione: se sbagliamo la
traduzione, il teorema non dice nulla sul programma vero. Qui invece
definiamo in Lean la **sintassi** e la **semantica** di un piccolo
frammento di Python (interi, assegnamenti, `if`, `while`) e dimostriamo
proprietà del programma *come albero sintattico*.

È la stessa architettura dei verificatori seri: una volta fidati della
semantica (scritta una volta sola), ogni programma si può verificare
senza traduzioni ad hoc; la traduzione Python → AST può essere
automatizzata (ad es. con il modulo `ast` di Python).
-/

namespace MiniPy

/-- Lo stato del programma: il valore di ogni variabile. -/
abbrev Stato := String → Int

def Stato.set (s : Stato) (x : String) (v : Int) : Stato :=
  fun y => if y = x then v else s y

/-- Espressioni intere. -/
inductive Expr where
  | cost : Int → Expr
  | var  : String → Expr
  | add  : Expr → Expr → Expr
  | sub  : Expr → Expr → Expr
  | mul  : Expr → Expr → Expr

/-- Condizioni booleane. -/
inductive Cond where
  | lt  : Expr → Expr → Cond
  | eq  : Expr → Expr → Cond
  | not : Cond → Cond

/-- Istruzioni. -/
inductive Stmt where
  | pass   : Stmt
  | assign : String → Expr → Stmt
  | seq    : Stmt → Stmt → Stmt
  | ite    : Cond → Stmt → Stmt → Stmt
  | while  : Cond → Stmt → Stmt

def Expr.eval (s : Stato) : Expr → Int
  | cost n  => n
  | var x   => s x
  | add a b => a.eval s + b.eval s
  | sub a b => a.eval s - b.eval s
  | mul a b => a.eval s * b.eval s

def Cond.eval (s : Stato) : Cond → Bool
  | lt a b => decide (a.eval s < b.eval s)
  | eq a b => decide (a.eval s = b.eval s)
  | not c  => !c.eval s

/-- **Semantica big-step**: `Exec p s s'` significa "eseguendo `p` nello
stato `s` il programma termina nello stato `s'`". È una relazione, non una
funzione: così non dobbiamo preoccuparci della terminazione nella definizione
(un ciclo infinito semplicemente non ha nessuno stato finale). -/
inductive Exec : Stmt → Stato → Stato → Prop where
  | pass (s) : Exec .pass s s
  | assign (s x e) : Exec (.assign x e) s (s.set x (e.eval s))
  | seq {p q s s₁ s₂} : Exec p s s₁ → Exec q s₁ s₂ → Exec (.seq p q) s s₂
  | ifTrue {c p q s s'} : c.eval s = true → Exec p s s' → Exec (.ite c p q) s s'
  | ifFalse {c p q s s'} : c.eval s = false → Exec q s s' → Exec (.ite c p q) s s'
  | whileTrue {c b s s₁ s₂} :
      c.eval s = true → Exec b s s₁ → Exec (.while c b) s₁ s₂ → Exec (.while c b) s s₂
  | whileFalse {c b s} : c.eval s = false → Exec (.while c b) s s

/-! ## Il programma

```python
i = 0
tot = 0
while i < n:
    i += 1
    tot += i
```
-/

/-- L'AST del programma (è ciò che produrrebbe un traduttore automatico
a partire da `ast.parse` di Python). -/
def sommaFinoA : Stmt :=
  .seq (.assign "i" (.cost 0)) <|
  .seq (.assign "tot" (.cost 0)) <|
  .while (.lt (.var "i") (.var "n"))
    (.seq (.assign "i"   (.add (.var "i") (.cost 1)))
          (.assign "tot" (.add (.var "tot") (.var "i"))))

/-! ## Regola di Hoare per il `while`

Il teorema generale che rende utilizzabile la semantica: se un invariante
`I` è preservato dal corpo quando la condizione è vera, allora vale anche
all'uscita del ciclo, insieme alla negazione della condizione. Si dimostra
**una volta sola** e vale per ogni programma. -/
theorem regola_while {c : Cond} {b : Stmt} {I : Stato → Prop}
    (hcorpo : ∀ s s', I s → c.eval s = true → Exec b s s' → I s')
    {s s' : Stato} (hexec : Exec (.while c b) s s') (hI : I s) :
    I s' ∧ c.eval s' = false := by
  generalize hw : Stmt.while c b = w at hexec
  induction hexec with
  | whileTrue hc hb _ _ ih₂ =>
    cases hw; exact ih₂ (hcorpo _ _ hI hc hb) rfl
  | whileFalse hc => cases hw; exact ⟨hI, hc⟩
  | pass | assign | seq | ifTrue | ifFalse => cases hw

/-! ## Correttezza del programma -/

/-- Per ogni esecuzione che termina, partendo da `n ≥ 0`, alla fine
`2 * tot = n * (n + 1)`. -/
theorem sommaFinoA_corretta (s s' : Stato) (hn : 0 ≤ s "n")
    (h : Exec sommaFinoA s s') :
    2 * s' "tot" = s "n" * (s "n" + 1) := by
  -- Scomponiamo l'esecuzione nelle sue parti: i due assegnamenti e il ciclo.
  unfold sommaFinoA at h
  cases h with | seq ha hresto =>
  cases hresto with | seq hb hloop =>
  cases ha; cases hb
  -- L'invariante del ciclo, espresso sullo stato.
  let I : Stato → Prop := fun t =>
    t "n" = s "n" ∧ 0 ≤ t "i" ∧ t "i" ≤ s "n" ∧ 2 * t "tot" = t "i" * (t "i" + 1)
  have hfine := regola_while (I := I) ?corpo hloop ?inizio
  case inizio =>
    simp [I, Stato.set, Expr.eval, hn]
  case corpo =>
    intro t t' ⟨htn, h0, hle, hinv⟩ hc hb
    cases hb with | seq hi htot =>
    cases hi; cases htot
    simp only [Cond.eval, Expr.eval] at hc
    have hc := of_decide_eq_true hc     -- hc : t "i" < t "n"
    simp only [I, Stato.set, Expr.eval]
    simp
    refine ⟨htn, by omega, by omega, by grind⟩
  -- All'uscita: invariante ∧ ¬(i < n) ⇒ i = n.
  obtain ⟨⟨htn, _, hle, hinv⟩, hc⟩ := hfine
  simp only [Cond.eval, Expr.eval] at hc
  have hc := of_decide_eq_false hc      -- hc : ¬ (i < n)
  have : s' "i" = s "n" := by omega
  rw [hinv, this]

/-! ## Un interprete eseguibile

`Exec` è una relazione: ottima per le dimostrazioni, ma non si può eseguire.
Scriviamo quindi anche un interprete con "carburante" (`fuel`: numero
massimo di passi, così Lean accetta che termini) e dimostriamo che è
**corretto rispetto alla semantica**. In questo modo possiamo anche *testare*
il modello confrontandolo con l'esecuzione reale di Python. -/

def run : Nat → Stmt → Stato → Option Stato
  | 0, _, _ => none
  | _ + 1, .pass, s => some s
  | _ + 1, .assign x e, s => some (s.set x (e.eval s))
  | f + 1, .seq p q, s => (run f p s).bind (run f q)
  | f + 1, .ite c p q, s => if c.eval s then run f p s else run f q s
  | f + 1, .while c b, s =>
      if c.eval s then (run f b s).bind (run f (.while c b)) else some s

/-- Correttezza dell'interprete: se `run` restituisce uno stato, quello è
davvero uno stato finale secondo la semantica `Exec`. -/
theorem run_corretto : ∀ (f : Nat) (p : Stmt) (s s' : Stato),
    run f p s = some s' → Exec p s s' := by
  intro f
  induction f with
  | zero => intro p s s' h; simp [run] at h
  | succ f ih =>
    intro p s s' h
    cases p with
    | pass => simp [run] at h; subst h; exact .pass s
    | assign x e => simp [run] at h; subst h; exact .assign s x e
    | seq p q =>
      simp only [run, Option.bind_eq_some_iff] at h
      obtain ⟨s₁, h₁, h₂⟩ := h
      exact .seq (ih _ _ _ h₁) (ih _ _ _ h₂)
    | ite c p q =>
      simp only [run] at h
      cases hc : c.eval s <;> simp [hc] at h
      · exact .ifFalse hc (ih _ _ _ h)
      · exact .ifTrue hc (ih _ _ _ h)
    | «while» c b =>
      cases hc : c.eval s
      · simp [run, hc] at h; subst h; exact .whileFalse hc
      · simp only [run, hc, ite_true, Option.bind_eq_some_iff] at h
        obtain ⟨s₁, h₁, h₂⟩ := h
        exact .whileTrue hc (ih _ _ _ h₁) (ih _ _ _ h₂)

/-- Stato iniziale con `n = 10` e tutte le altre variabili a 0. -/
def stato0 : Stato := fun x => if x = "n" then 10 else 0

#eval (run 100 sommaFinoA stato0).map (· "tot")   -- some 55

/-- Esempio: il programma, con `n = 10`, termina davvero (non solo "se
termina, allora...") e il risultato è 55. -/
example : ∃ s', Exec sommaFinoA stato0 s' ∧ s' "tot" = 55 := by
  obtain ⟨s', h⟩ : ∃ s', run 100 sommaFinoA stato0 = some s' := ⟨_, rfl⟩
  refine ⟨s', run_corretto _ _ _ _ h, ?_⟩
  have := sommaFinoA_corretta stato0 s' (by decide) (run_corretto _ _ _ _ h)
  simp [stato0] at this
  omega

end MiniPy
