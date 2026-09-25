"""Test del traduttore: python3 -m unittest discover tools"""

import ast
import textwrap
import unittest

from py2lean import NonSupportato, cond, espr, genera, traduci_funzione


def funz(src: str) -> ast.FunctionDef:
    return ast.parse(textwrap.dedent(src)).body[0]


def e(src: str) -> ast.expr:
    return ast.parse(src, mode="eval").body


class TestEspressioni(unittest.TestCase):
    def test_aritmetica(self):
        self.assertEqual(espr(e("a + 2 * b")),
                         '(.add (.var "a") (.mul (.cost 2) (.var "b")))')

    def test_meno_unario(self):
        self.assertEqual(espr(e("-x")), '(.sub (.cost 0) (.var "x"))')

    def test_rifiuta_divisione(self):
        for op in ["a // b", "a % b", "a / b", "a ** b"]:
            with self.assertRaises(NonSupportato, msg=op):
                espr(e(op))

    def test_rifiuta_bool_e_float(self):
        for src in ["True", "1.5", "f(x)", "xs[0]"]:
            with self.assertRaises(NonSupportato, msg=src):
                espr(e(src))


class TestCondizioni(unittest.TestCase):
    def test_confronti(self):
        self.assertEqual(cond(e("a > b")), '(.lt (.var "b") (.var "a"))')
        self.assertEqual(cond(e("a <= b")), '(.not (.lt (.var "b") (.var "a")))')
        self.assertEqual(cond(e("a != b")), '(.not (.eq (.var "a") (.var "b")))')

    def test_and_or(self):
        self.assertEqual(cond(e("a < b and b < c or a == c")),
                         '(.or (.and (.lt (.var "a") (.var "b")) (.lt (.var "b") (.var "c")))'
                         ' (.eq (.var "a") (.var "c")))')

    def test_rifiuta_truthiness_e_concatenati(self):
        for src in ["x", "a < b < c", "x is None"]:
            with self.assertRaises(NonSupportato, msg=src):
                cond(e(src))


class TestFunzioni(unittest.TestCase):
    def test_ok(self):
        t = traduci_funzione(funz("""
            def f(n: int) -> int:
                r = 0
                while n > 0:
                    r += n
                    n -= 1
                return r
        """))
        self.assertEqual((t.parametri, t.risultato), (["n"], "r"))

    def rifiuta(self, src: str, frammento: str):
        with self.assertRaises(NonSupportato) as ctx:
            traduci_funzione(funz(src))
        self.assertIn(frammento, str(ctx.exception))

    def test_rifiuta_return_anticipato(self):
        self.rifiuta("""
            def f(n: int) -> int:
                r = 0
                if n < 0:
                    return r
                r = n
                return r
        """, "return")

    def test_rifiuta_break(self):
        self.rifiuta("""
            def f(n: int) -> int:
                while n > 0:
                    break
                return n
        """, "Break")

    def test_rifiuta_variabile_non_definita(self):
        self.rifiuta("""
            def f(n: int) -> int:
                r = n + y
                return r
        """, "`y`")

    def test_rifiuta_variabile_definita_solo_in_un_ramo(self):
        self.rifiuta("""
            def f(n: int) -> int:
                if n > 0:
                    r = 1
                return r
        """, "`r`")

    def test_accetta_variabile_definita_in_entrambi_i_rami(self):
        traduci_funzione(funz("""
            def f(n: int) -> int:
                if n > 0:
                    r = 1
                else:
                    r = 2
                return r
        """))

    def test_rifiuta_parametro_non_int(self):
        self.rifiuta("""
            def f(xs: list[int]) -> int:
                r = 0
                return r
        """, "`xs`")

    def test_genera_salta_non_supportate(self):
        testo = genera("def g(x: int):\n    return x * 2\n", "x.py", "X")
        self.assertIn("`g` non tradotta", testo)


if __name__ == "__main__":
    unittest.main()
