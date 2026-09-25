import LeanExp.Passo3_MiniPython
import LeanExp.Generato.Esempi

/-!
# Passo 4 — Dimostrare teoremi sul codice tradotto automaticamente

`tools/py2lean.py` legge `python/esempi.py` con il modulo `ast` di Python e
genera `LeanExp/Generato/Esempi.lean`, che contiene l'AST MiniPy di ogni
funzione del frammento supportato. Qui dimostriamo teoremi **su quei
termini generati**: nessuna traduzione a mano.

La catena di fiducia diventa:

  `esempi.py` ──(py2lean, ~250 righe di Python)──▶ AST MiniPy
                                        ──(semantica `Exec`)──▶ teoremi

Per rigenerare dopo aver modificato il Python:
```
python3 tools/py2lean.py python/esempi.py -o LeanExp/Generato/Esempi.lean
```
Se il Python cambia in modo sbagliato, **le dimostrazioni qui sotto smettono
di compilare**.
-/

namespace Passo4
open MiniPy Generato.Esempi

/-! ## `somma_fino_a`: il traduttore produce esattamente l'AST scritto a mano

Quindi il teorema del Passo 3 vale per il codice generato. -/

theorem somma_fino_a_come_passo3 : somma_fino_a = MiniPy.sommaFinoA := rfl

theorem somma_fino_a_corretta (s s' : Stato) (hn : 0 ≤ s "n")
    (h : Exec somma_fino_a s s') :
    2 * s' "tot" = s "n" * (s "n" + 1) :=
  MiniPy.sommaFinoA_corretta s s' hn h

/-! ## `prodotto`

```python
def prodotto(a: int, b: int) -> int:
    tot = 0
    i = 0
    while i < b:
        tot += a
        i += 1
    return tot
```
-/

/-- Se `b ≥ 0` e l'esecuzione termina, il risultato è `a * b`. -/
theorem prodotto_corretto (s s' : Stato) (hb : 0 ≤ s "b")
    (h : Exec prodotto s s') :
    s' "tot" = s "a" * s "b" := by
  unfold prodotto at h
  cases h with | seq ha hresto =>
  cases hresto with | seq hb' hloop =>
  cases ha; cases hb'
  -- Invariante: a e b non cambiano, 0 ≤ i ≤ b e tot = a * i.
  let I : Stato → Prop := fun t =>
    t "a" = s "a" ∧ t "b" = s "b" ∧ 0 ≤ t "i" ∧ t "i" ≤ s "b" ∧ t "tot" = s "a" * t "i"
  have hfine := regola_while (I := I) ?corpo hloop ?inizio
  case inizio =>
    simp [I, Stato.set, Expr.eval, hb]
  case corpo =>
    intro t t' ⟨hta, htb, h0, hle, hinv⟩ hc hcorpo
    cases hcorpo with | seq htot hi =>
    cases htot; cases hi
    simp only [Cond.eval, Expr.eval] at hc
    have hc := of_decide_eq_true hc
    simp only [I, Stato.set, Expr.eval]
    simp
    refine ⟨hta, htb, by omega, by omega, by rw [hinv, hta]; grind⟩
  obtain ⟨⟨_, htb, _, hle, hinv⟩, hc⟩ := hfine
  simp only [Cond.eval, Expr.eval] at hc
  have hc := of_decide_eq_false hc
  have : s' "i" = s "b" := by omega
  rw [hinv, this]

/-! ## `valore_assoluto`

```python
def valore_assoluto(x: int) -> int:
    if x < 0:
        r = -x
    else:
        r = x
    return r
```
-/

theorem valore_assoluto_corretto (s s' : Stato)
    (h : Exec valore_assoluto s s') :
    0 ≤ s' "r" ∧ (s' "r" = s "x" ∨ s' "r" = - s "x") := by
  unfold valore_assoluto at h
  cases h with
  | ifTrue hc hassign =>
    cases hassign
    simp only [Cond.eval, Expr.eval] at hc
    have hc := of_decide_eq_true hc
    simp [Stato.set, Expr.eval]; omega
  | ifFalse hc hassign =>
    cases hassign
    simp only [Cond.eval, Expr.eval] at hc
    have hc := of_decide_eq_false hc
    simp [Stato.set, Expr.eval]; omega

/-! ## Il modello si può anche eseguire (test rapido) -/

def conParametri (xs : List (String × Int)) : Stato :=
  fun v => (xs.lookup v).getD 0

#eval (run 1000 prodotto (conParametri [("a", 6), ("b", 7)])).map (· "tot")         -- some 42
#eval (run 1000 valore_assoluto (conParametri [("x", -5)])).map (· "r")              -- some 5

end Passo4
