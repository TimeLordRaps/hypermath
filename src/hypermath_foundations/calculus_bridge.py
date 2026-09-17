# Copyright 2026 Tyler Roost / TimeLordRaps
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Metamath & Formal Calculus Bridge.

Provides verifiable translation mapping from Hypermath expressions to Metamath
and opens formal pathways to the five essential calculi:
  1. Language Calculus (operational semantics, grammar production lattices)
  2. Meta-Calculus (symbolic dynamics of symbolic representational calculi)
  3. Hyper-Calculus (group-theoretical / Lie-algebraic approach to forms of calculus)
  4. Ordinal Calculus (transfinite difference and limit derivatives on ordinals)
  5. Normal Math Calculus (standard differential and integral calculus via Ordinatics localization)
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import Callable, Sequence

from .abstraction import FormTerm

# ============================================================================
# §1  The Metamath Bridge
# ============================================================================

@dataclass
class MetamathDatabase:
    """A verified, self-contained Metamath database generator and checker.

    Emits conforming Metamath syntax (.mm) and validates proof assertions in RPN.
    """

    constants: set[str] = field(default_factory=set)
    variables: set[str] = field(default_factory=set)
    floating_hypotheses: dict[str, tuple[str, str]] = field(default_factory=dict)  # label -> (type, var)
    essential_hypotheses: dict[str, list[str]] = field(default_factory=dict)       # label -> tokens
    disjoint_restrictions: set[tuple[str, str]] = field(default_factory=set)
    axioms: dict[str, list[str]] = field(default_factory=dict)                     # label -> tokens
    theorems: dict[str, tuple[list[str], list[str]]] = field(default_factory=dict) # label -> (tokens, proof)

    def add_constant(self, c: str) -> None:
        self.constants.add(c)

    def add_variable(self, v: str) -> None:
        self.variables.add(v)

    def add_floating(self, label: str, type_code: str, var: str) -> None:
        self.floating_hypotheses[label] = (type_code, var)

    def add_essential(self, label: str, tokens: Sequence[str]) -> None:
        self.essential_hypotheses[label] = list(tokens)

    def add_disjoint(self, var1: str, var2: str) -> None:
        pair = (min(var1, var2), max(var1, var2))
        self.disjoint_restrictions.add(pair)

    def add_axiom(self, label: str, tokens: Sequence[str]) -> None:
        self.axioms[label] = list(tokens)

    def add_theorem(self, label: str, tokens: Sequence[str], proof: Sequence[str]) -> None:
        self.theorems[label] = (list(tokens), list(proof))

    def emit(self) -> str:
        """Render database as standard Metamath source code."""
        lines: list[str] = []
        if self.constants:
            lines.append(f"$c {' '.join(sorted(self.constants))} $.")
        if self.variables:
            lines.append(f"$v {' '.join(sorted(self.variables))} $.")
        for pair in sorted(self.disjoint_restrictions):
            lines.append(f"$d {pair[0]} {pair[1]} $.")
        for label, (type_code, var) in sorted(self.floating_hypotheses.items()):
            lines.append(f"{label} $f {type_code} {var} $.")
        for label, tokens in sorted(self.essential_hypotheses.items()):
            lines.append(f"{label} $e {' '.join(tokens)} $.")
        for label, tokens in sorted(self.axioms.items()):
            lines.append(f"{label} $a {' '.join(tokens)} $.")
        for label, (tokens, proof) in sorted(self.theorems.items()):
            lines.append(f"{label} $p {' '.join(tokens)} $= {' '.join(proof)} $.")
        return "\n".join(lines) + "\n"

    @staticmethod
    def _parse_implication(tokens: list[str]) -> tuple[list[str], list[str]] | None:
        if not tokens:
            return None
        toks = tokens[1:] if tokens[0] == "|-" else tokens
        if len(toks) >= 2 and toks[0] == "(" and toks[-1] == ")":
            toks = toks[1:-1]
        depth = 0
        for i, tok in enumerate(toks):
            if tok == "(":
                depth += 1
            elif tok == ")":
                depth -= 1
            elif tok == "->" and depth == 0:
                ante = toks[:i]
                cons = toks[i + 1 :]
                return (ante, cons)
        return None

    def verify_proof(self, label: str) -> bool:
        """RPN verification of a Metamath theorem proof."""
        if label not in self.theorems:
            return False
        expected_statement, proof_tokens = self.theorems[label]
        if not proof_tokens:
            return False
        stack: list[list[str]] = []

        for step in proof_tokens:
            if step in self.floating_hypotheses:
                tc, v = self.floating_hypotheses[step]
                stack.append([tc, v])
            elif step in self.essential_hypotheses:
                stack.append(list(self.essential_hypotheses[step]))
            elif step in self.axioms or (step in self.theorems and step != label):
                target_stmt = (
                    self.axioms[step] if step in self.axioms else self.theorems[step][0]
                )
                vars_in_target: list[str] = []
                for tok in target_stmt:
                    if tok in self.variables and tok not in vars_in_target:
                        vars_in_target.append(tok)

                if vars_in_target:
                    if len(stack) < len(vars_in_target):
                        return False
                    subst: dict[str, list[str]] = {}
                    for var in reversed(vars_in_target):
                        popped = stack.pop()
                        if len(popped) >= 2 and popped[0] in self.constants:
                            subst[var] = popped[1:]
                        else:
                            subst[var] = popped
                    instantiated: list[str] = []
                    for tok in target_stmt:
                        if tok in subst:
                            instantiated.extend(subst[tok])
                        else:
                            instantiated.append(tok)
                    stack.append(instantiated)
                else:
                    stack.append(list(target_stmt))
            elif step == "mp":
                # Modus Ponens deduction step: [..., minor, major] -> [..., consequent]
                if len(stack) < 2:
                    return False
                major = stack.pop()
                minor = stack.pop()
                parsed = self._parse_implication(major)
                if parsed is None:
                    return False
                ante, cons = parsed
                minor_payload = minor[1:] if minor and minor[0] == "|-" else minor
                ante_payload = ante[1:] if ante and ante[0] == "|-" else ante
                if minor_payload != ante_payload:
                    return False
                res_stmt = ["|-"] + cons if ((minor and minor[0] == "|-") or (major and major[0] == "|-")) else cons
                stack.append(res_stmt)
            else:
                return False

        if len(stack) != 1:
            return False
        return stack[0] == expected_statement


def form_to_metamath(term: FormTerm, db: MetamathDatabase) -> list[str]:
    """Functorial mapping: translate a Hypermath FormTerm into Metamath tokens."""
    db.add_constant("term")
    db.add_constant("(")
    db.add_constant(")")
    if not term.args:
        db.add_constant(term.symbol)
        return [term.symbol]
    db.add_constant(term.symbol)
    tokens = [term.symbol, "("]
    for i, arg in enumerate(term.args):
        if i > 0:
            db.add_constant(",")
            tokens.append(",")
        tokens.extend(form_to_metamath(arg, db))
    tokens.append(")")
    return tokens


# ============================================================================
# §2  Calculus Pathway 1: Language Calculus
# ============================================================================

@dataclass(frozen=True)
class GrammarProduction:
    """Production rule for formal language syntax: Head -> Body."""

    head: str
    body: tuple[str, ...]

    def matches(self, sequence: Sequence[str], position: int) -> bool:
        if position + len(self.body) > len(sequence):
            return False
        return tuple(sequence[position : position + len(self.body)]) == self.body


@dataclass
class LanguageCalculus:
    """Language Calculus: operational semantics and grammar rewriting lattice.

    Formalizes transitions (e, sigma) -> (e', sigma') and syntax evaluation.
    """

    productions: list[GrammarProduction] = field(default_factory=list)

    def add_production(self, head: str, body: Sequence[str]) -> None:
        self.productions.append(GrammarProduction(head=head, body=tuple(body)))

    def parse_step(self, tokens: Sequence[str]) -> list[str]:
        """Perform one reduction step under the production rules."""
        toks = list(tokens)
        for prod in self.productions:
            for i in range(len(toks) - len(prod.body) + 1):
                if prod.matches(toks, i):
                    return toks[:i] + [prod.head] + toks[i + len(prod.body) :]
        return toks

    def reduce(self, tokens: Sequence[str], max_steps: int = 100) -> list[str]:
        current = list(tokens)
        for _ in range(max_steps):
            next_step = self.parse_step(current)
            if next_step == current:
                break
            current = next_step
        return current


# ============================================================================
# §3  Calculus Pathway 2: Meta-Calculus (Symbolic Dynamics)
# ============================================================================

@dataclass
class MetaCalculus:
    """Meta-Calculus: symbolic dynamics of symbolic representational calculi.

    Analyzes orbits, attractors, cycles, and fixed points of rewrite systems.
    """

    rules: dict[str, Callable[[FormTerm], FormTerm]] = field(default_factory=dict)

    def add_rewrite_rule(self, name: str, rule: Callable[[FormTerm], FormTerm]) -> None:
        self.rules[name] = rule

    def rewrite_step(self, term: FormTerm) -> FormTerm:
        """Apply active rewrite rules to a term."""
        for rule in self.rules.values():
            new_term = rule(term)
            if new_term != term:
                return new_term
        return term

    def compute_orbit(self, initial: FormTerm, max_steps: int = 32) -> list[FormTerm]:
        """Compute the symbolic trajectory orbit: [t0, t1, t2, ...]."""
        orbit = [initial]
        current = initial
        for _ in range(max_steps):
            next_t = self.rewrite_step(current)
            if next_t == current:
                break
            orbit.append(next_t)
            current = next_t
        return orbit

    def detect_cycle(self, orbit: Sequence[FormTerm]) -> tuple[bool, int, int]:
        """Floyd cycle-detection on a symbolic orbit. Returns (has_cycle, start, period)."""
        seen: dict[str, int] = {}
        for idx, term in enumerate(orbit):
            h = term.digest()
            if h in seen:
                start = seen[h]
                period = idx - start
                return (True, start, period)
            seen[h] = idx
        return (False, -1, 0)


# ============================================================================
# §4  Calculus Pathway 3: Hyper-Calculus (Group-Theoretic / Lie Derivations)
# ============================================================================

class HyperCalculus:
    """Hyper-Calculus: group-theoretical and Lie-algebraic approach to calculus.

    Derivations act as Lie algebra generators satisfying the Leibniz product rule:
    D(f * g) = D(f) * g + f * D(g)
    and the Lie Bracket: [D1, D2] = D1 o D2 - D2 o D1.
    """

    @staticmethod
    def leibniz_product(
        d: Callable[[float], float] | None,
        f: Callable[[float], float],
        g: Callable[[float], float],
        x: float,
        df_x: float | None = None,
        dg_x: float | None = None,
    ) -> float:
        """Compute D(f * g)(x) using the Leibniz rule: D(f)*g + f*D(g)."""
        if df_x is None:
            if d is None:
                raise ValueError("Either df_x or derivation d must be provided")
            df_x = d(x)
        if dg_x is None:
            raise ValueError("dg_x must be provided")
        return df_x * g(x) + f(x) * dg_x

    @staticmethod
    def lie_bracket(
        d1: Callable[[Callable[[float], float]], Callable[[float], float]],
        d2: Callable[[Callable[[float], float]], Callable[[float], float]],
        f: Callable[[float], float],
    ) -> Callable[[float], float]:
        """Lie bracket of two derivation operators: [D1, D2](f) = D1(D2(f)) - D2(D1(f))."""
        d1_d2_f = d1(d2(f))
        d2_d1_f = d2(d1(f))
        return lambda x: d1_d2_f(x) - d2_d1_f(x)

    @staticmethod
    def translation_group_action(f: Callable[[float], float], a: float) -> Callable[[float], float]:
        """Translation operator T_a(f)(x) = f(x + a)."""
        return lambda x: f(x + a)

    @staticmethod
    def dilation_group_action(f: Callable[[float], float], scale: float) -> Callable[[float], float]:
        """Dilation operator S_lambda(f)(x) = f(scale * x)."""
        return lambda x: f(scale * x)


# ============================================================================
# §5  Calculus Pathway 4: Ordinal Calculus
# ============================================================================

class OrdinalCalculus:
    """Ordinal Calculus: transfinite differences, limit derivatives, and ordinal sums."""

    @staticmethod
    def transfinite_difference(
        f: Callable[[int], int],
        omega_idx: int,
    ) -> int:
        """Transfinite forward difference: Delta_w f(w) = f(w + 1) - f(w)."""
        return f(omega_idx + 1) - f(omega_idx)

    @staticmethod
    def limit_derivative(
        coefficients: Sequence[int],
    ) -> tuple[int, ...]:
        """Formal derivative of an ordinal polynomial alpha(w) = sum a_i * w^i.

        d/dw sum a_i * w^i = sum i * a_i * w^{i-1}.
        """
        if len(coefficients) <= 1:
            return (0,)
        result = [i * coeff for i, coeff in enumerate(coefficients)][1:]
        while len(result) > 1 and result[-1] == 0:
            result.pop()
        return tuple(result) if result else (0,)


# ============================================================================
# §6  Calculus Pathway 5: Normal Math Calculus (Standard Analysis)
# ============================================================================

class MathCalculus:
    """Normal Math Calculus: standard continuous differential and integral analysis.

    Reachable via Ordinatics localization K = Q(X) and partial specialization W(X) = -1/2.
    """

    @staticmethod
    def derivative(f: Callable[[float], float], x: float, h: float = 1e-6) -> float:
        """Numerical derivative via symmetric difference quotient."""
        if h <= 0:
            raise ValueError("Step size h must be strictly positive")
        return (f(x + h) - f(x - h)) / (2.0 * h)

    @staticmethod
    def definite_integral(
        f: Callable[[float], float], a: float, b: float, subdivisions: int = 1000
    ) -> float:
        """Definite Riemann integral via trapezoidal rule."""
        if subdivisions <= 0:
            raise ValueError("Subdivisions must be strictly positive")
        if a == b:
            return 0.0
        h = (b - a) / subdivisions
        total = 0.5 * (f(a) + f(b))
        for i in range(1, subdivisions):
            total += f(a + i * h)
        return total * h

    @classmethod
    def verify_leibniz_rule(
        cls,
        f: Callable[[float], float],
        g: Callable[[float], float],
        x: float,
        tol: float = 1e-4,
    ) -> bool:
        """Verify (f * g)'(x) == f'(x)*g(x) + f(x)*g'(x)."""
        def fg(t: float) -> float:
            return f(t) * g(t)
        lhs = cls.derivative(fg, x)
        rhs = cls.derivative(f, x) * g(x) + f(x) * cls.derivative(g, x)
        return math.isclose(lhs, rhs, abs_tol=tol)

    @classmethod
    def verify_fundamental_theorem(
        cls,
        f: Callable[[float], float],
        f_prime: Callable[[float], float],
        a: float,
        b: float,
        tol: float = 1e-3,
    ) -> bool:
        """Verify Fundamental Theorem of Calculus: integral_a^b f'(t) dt == f(b) - f(a)."""
        integral_val = cls.definite_integral(f_prime, a, b)
        analytic_diff = f(b) - f(a)
        return math.isclose(integral_val, analytic_diff, abs_tol=tol)
