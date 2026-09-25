import LeanExp.Passo3_MiniPython

/-! File GENERATO da tools/py2lean.py — non modificare a mano.
Sorgente: `python/esempi.py` -/

namespace Generato.Esempi
open MiniPy

-- `somma` non tradotta: riga 9: il parametro `xs` deve essere annotato `int`

-- `massimo` non tradotta: riga 16: il parametro `xs` deve essere annotato `int`

-- `contiene` non tradotta: riga 25: il parametro `xs` deve essere annotato `int`

/-- `somma_fino_a` (python/esempi.py, riga 34).
Parametri: n; risultato nella variabile `tot`. -/
def somma_fino_a : Stmt :=
  (.seq
    (.assign "i" (.cost 0))
    (.seq
      (.assign "tot" (.cost 0))
      (.while (.lt (.var "i") (.var "n"))
        (.seq
          (.assign "i" (.add (.var "i") (.cost 1)))
          (.assign "tot" (.add (.var "tot") (.var "i")))))))

def somma_fino_a.parametri : List String := ["n"]
def somma_fino_a.risultato : String := "tot"

/-- `prodotto` (python/esempi.py, riga 45).
Parametri: a, b; risultato nella variabile `tot`. -/
def prodotto : Stmt :=
  (.seq
    (.assign "tot" (.cost 0))
    (.seq
      (.assign "i" (.cost 0))
      (.while (.lt (.var "i") (.var "b"))
        (.seq
          (.assign "tot" (.add (.var "tot") (.var "a")))
          (.assign "i" (.add (.var "i") (.cost 1)))))))

def prodotto.parametri : List String := ["a", "b"]
def prodotto.risultato : String := "tot"

/-- `valore_assoluto` (python/esempi.py, riga 55).
Parametri: x; risultato nella variabile `r`. -/
def valore_assoluto : Stmt :=
  (.ite (.lt (.var "x") (.cost 0))
    (.assign "r" (.sub (.cost 0) (.var "x")))
    (.assign "r" (.var "x")))

def valore_assoluto.parametri : List String := ["x"]
def valore_assoluto.risultato : String := "r"

end Generato.Esempi
