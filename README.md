# LeanExp — Dimostrare la correttezza di programmi Python con Lean 4

Percorso a passi incrementali. Ogni file Lean corrisponde a funzioni di
[`python/esempi.py`](python/esempi.py).

| Passo | File | Idea | Cosa si impara |
|---|---|---|---|
| 1 | [`Passo1_Shallow.lean`](LeanExp/Passo1_Shallow.lean) | *Shallow embedding*: si traduce a mano la funzione Python in una funzione Lean pura | `for` → `foldl`, invarianti come lemmi generalizzati, induzione su liste, precondizioni nei tipi |
| 2 | [`Passo2_Cicli.lean`](LeanExp/Passo2_Cicli.lean) | Cicli `while` come ricorsione | terminazione (`termination_by`), induzione funzionale, invarianti, attenzione a `int` vs `Nat` |
| 3 | [`Passo3_MiniPython.lean`](LeanExp/Passo3_MiniPython.lean) | *Deep embedding*: sintassi + semantica di un mini-Python in Lean | semantica big-step, regola di Hoare per il `while` dimostrata una volta sola, interprete eseguibile dimostrato corretto |
| 4 | [`Passo4_Traduttore.lean`](LeanExp/Passo4_Traduttore.lean) | Traduzione **automatica** Python → MiniPy con [`tools/py2lean.py`](tools/py2lean.py) | dimostrazioni sul codice generato; se il Python cambia in modo sbagliato, le dimostrazioni non compilano più |

## Il traduttore `py2lean`

```bash
python3 tools/py2lean.py python/esempi.py -o LeanExp/Generato/Esempi.lean          # rigenera
python3 tools/py2lean.py python/esempi.py -o LeanExp/Generato/Esempi.lean --check  # è aggiornato?
python3 -m unittest discover tools                                                 # test
```

Usa il modulo `ast` di Python e accetta solo un frammento in cui ogni
costrutto ha in MiniPy *esattamente* il significato che ha in Python:
interi, `+ - *`, confronti, `and/or/not`, assegnamenti (anche `+=` ecc.),
`if/elif/else`, `while`, `pass`, e `return <variabile>` finale.
Tutto il resto viene **rifiutato** con la riga e il motivo (es. `//` e `%`,
che in Python arrotondano diversamente da Lean; `while x:` che usa la
"truthiness"; `break`; `return` anticipati). Rifiuta anche le variabili che
potrebbero non essere definite (in Python sarebbero un `NameError`, in
MiniPy avrebbero silenziosamente un valore). Le funzioni non traducibili
restano nel file generato come commento con il motivo.

## Come compilare

```bash
# installa Lean (una volta sola)
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
lake build          # verifica tutte le dimostrazioni
python3 python/esempi.py
python3 -m unittest discover tools
```

Se `lake build` termina senza errori, **tutti i teoremi sono dimostrati**
(non ci sono `sorry`). Si consiglia VS Code con l'estensione *Lean 4* per
vedere lo stato della dimostrazione passo passo.

## Il punto critico: il divario Python ↔ Lean

Lean dimostra teoremi sul **modello**, non sul file `.py`. Le fonti di errore
sono nella traduzione:

* `int` di Python è illimitato → usare `Int`, non `Nat` né `Int64`
  (vedi Passo 2: con `Nat` `somma_fino_a(-3)` sparirebbe dal teorema);
* aliasing e mutabilità delle liste, eccezioni (`IndexError`), `None`,
  tipizzazione dinamica: nei passi 1–2 vengono semplicemente ignorati;
* nel passo 3 il divario si riduce a *una* cosa di cui fidarsi, la
  semantica di `MiniPy`, invece che a ogni traduzione manuale.

## Possibili prossimi passi

1. ~~Traduttore automatico Python → `MiniPy.Stmt`~~ (fatto, Passo 4).
2. **Test differenziali**: eseguire `MiniPy.run` e Python sugli stessi input
   (anche con Hypothesis) per acquisire fiducia nella semantica.
3. Estendere `MiniPy` con liste, funzioni, `return`, eccezioni.
4. Un *verification condition generator*: calcolare automaticamente le
   obbligazioni di prova dalle annotazioni (`assert`, invarianti) come fanno
   Dafny o Nagini (il verificatore per Python basato su Viper).
