"""Lean 4 export of checked first-order proof terms."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import cast

from .. import peano as _peano
from .. import presburger as _presburger
from .. import robinson as _robinson
from .. import squaring as _squaring
from ..checker import Theory, check
from ..emitter import Emitter, Visit, case
from ..proof import (
    CANONICAL_PROOF_TYPES,
    MP,
    RAA,
    Assume,
    Axiom,
    Cong,
    ExFalso,
    ExistsElim,
    ExistsIntro,
    ForallElim,
    ForallIntro,
    ImpIntro,
    Induct,
    Inst,
    Pf,
    Refl,
    Sym,
    Trans,
)
from ..sequent import Sequent
from ..syntax import (
    Exists,
    Formula,
    Fun,
    Not,
    Var,
    children,
    instantiate,
)
from .models import LeanModel
from .syntax import (
    _ABSTRACT,
    _L_ATOM,
    CARRIER,
    LeanError,
    _free_names,
    _Names,
    _render,
    _render_statement,
    _Style,
    closure_names,
    lean_name,
    render_formula,
    render_statement,
    substitute,
)

# ---------------------------------------------------------------------------
# Proof export: one conditional theorem per checked proof
# ---------------------------------------------------------------------------

# Readable names for the axioms of the theories we export. Anything unrecognised
# gets `ax<n>` from a deterministic ordering, so the export never depends on a
# theory's `frozenset` iteration order.
AXIOM_LABELS: dict = {
    _presburger.ADD_ZERO_F: "ax_add_zero",
    _presburger.ADD_SUCC_F: "ax_add_succ",
    _presburger.SUCC_NEQ_ZERO: "ax_succ_ne_zero",
    _presburger.SUCC_INJ: "ax_succ_inj",
    _peano.MUL_ZERO_F: "ax_mul_zero",
    _peano.MUL_SUCC_F: "ax_mul_succ",
    _robinson.SUCC_NEQ_ONE: "ax_succ_ne_one",
    _robinson.SUCC_INJ: "ax_succ_inj",
    _robinson.ADD_ONE: "ax_add_one",
    _robinson.ADD_SUCC: "ax_add_succ",
    _robinson.MUL_ONE: "ax_mul_one",
    _robinson.MUL_SUCC: "ax_mul_succ",
    _squaring.SQUARE_ZERO_F: "ax_square_zero",
    _squaring.SQUARE_SUCC_F: "ax_square_succ",
}


def export_theorem(name: str, pf: object, theory: Theory) -> str:
    """Render a checked proof as a self-contained Lean 4 `theorem`.

    The proof is re-checked here (`check`), so an unproved recipe never reaches
    the file. What comes out is CONDITIONAL: the theory's function symbols and
    axioms -- and the induction principle, if the proof uses `Induct` -- are
    hypotheses of the theorem, over an abstract carrier `M`. No `axiom`, no
    `sorry`: Lean is asked to verify the entailment, not to believe us."""
    return _Export(pf, theory).theorem(name)


def uses_induction(pf: object) -> bool:
    """Whether the proof cites the `Induct` rule (so needs the `ind` hypothesis)."""
    return any(type(n) is Induct for n in _tree(pf))


def _tree(node: object):
    """Every dataclass node under `node` -- proof terms and the syntax they embed --
    iteratively (a proof term is a dataclass, so `children` walks it too)."""
    stack: list = [node]
    while stack:
        n = stack.pop()
        yield n
        stack.extend(children(n))


def _symbols(nodes) -> dict:
    """`name -> arity` for every function symbol occurring in `nodes`."""
    arities: dict = {}
    for root in nodes:
        for n in _tree(root):
            if type(n) is Fun:
                arity = len(n.args)
                if arities.setdefault(n.name, arity) != arity:
                    raise LeanError(f"symbol {n.name!r} used at two arities")
    return arities


def _var_names(nodes) -> set:
    return {n.name for root in nodes for n in _tree(root) if type(n) is Var}


def _fun_type(arity: int) -> str:
    return " → ".join([CARRIER] * (arity + 1))


@dataclass(frozen=True, slots=True)
class _ProofContext:
    sigma: dict
    env: dict


@dataclass(slots=True)
class _Export(
    Emitter[Pf, _ProofContext],
    covers=CANONICAL_PROOF_TYPES,
):
    """One theorem's worth of export state: the naming decisions, then the
    emitters that consume them.

    The proof is rendered under a substitution environment `sigma` (object
    variable name -> the term it now stands for) threaded downward, which is what
    makes `Inst` free: instantiating a variable is not an operation in the Lean
    proof at all, it is a change to the environment the *same* sub-proof renders
    under. An axiom is then rendered as its hypothesis applied to the images of
    its own free variables, in `closure_names` order -- the one place where the
    lexicographic closure order is load-bearing."""

    pf: object
    theory: Theory
    seq: Sequent = field(init=False)
    supply: _Names = field(init=False)
    axiom_names: dict = field(init=False)
    open_names: dict = field(init=False)
    symbols: dict = field(init=False)
    sigma0: dict = field(init=False)
    concls: dict = field(init=False, default_factory=dict)

    def __post_init__(self) -> None:
        self.seq = check(self.pf, self.theory)
        roots = [self.pf, self.seq.concl, *self.seq.hyps, *self.theory.axioms]
        if self.theory.zero is not None:
            roots.append(self.theory.zero)
        self.symbols = _symbols(roots)
        self.supply = _Names({_ABSTRACT.symbol(s) for s in self.symbols})
        self.axiom_names = {}
        for i, ax in enumerate(sorted(self.theory.axioms, key=render_statement)):
            self.axiom_names[ax] = self.supply.fresh(AXIOM_LABELS.get(ax, f"ax{i + 1}"))
        if uses_induction(self.pf):
            self.supply.fresh("ind")
        # Object variables are renamed only when their name is not usable in Lean
        # (or is already a parameter); everything else keeps the name it had.
        self.sigma0 = {}
        for v in sorted(_var_names(roots)):
            # `_Names` returns Lean identifiers. A French-quoted rendering is
            # not an object-language variable name that may safely be stored in
            # `Var` and rendered again: doing so would double-quote names such
            # as the interpretation layer's canonical `x!1`. Rename any name
            # that needs escaping to an ordinary fresh identifier instead.
            target = self.fresh_binder(v)
            if target != v:
                self.sigma0[v] = Var(target)
        self.open_names = {}
        for hyp in sorted(self.seq.hyps, key=render_statement):
            self.open_names[self.subst(hyp)] = self.supply.fresh("h")

    # --- naming and substitution -------------------------------------------

    def fresh_binder(self, object_name: str) -> str:
        """A fresh ordinary Lean binder safe to store back in ``Var``.

        French-quoted identifiers are a final rendering form, not canonical
        object-language names. Internal substitution environments therefore
        receive a plain fallback whenever the source name needs escaping.
        """
        return self.supply.fresh(object_name if lean_name(object_name) == object_name else "x")

    def subst(self, node):
        return substitute(node, self.sigma0)

    def conclusion(self, pf: object) -> Formula:
        """A sub-proof's derived conclusion (cached). Only the rules that cannot
        read their own conclusion off their fields -- `ExistsElim` -- need it."""
        hit = self.concls.get(id(pf))
        if hit is None:
            hit = cast(Pf, pf).derive(self.theory).concl
            self.concls[id(pf)] = hit
        return hit

    # --- the theorem --------------------------------------------------------

    def symbol_order(self) -> list:
        """The theory's function symbols as the theorem takes them: constants
        first, then by name -- so an arithmetic signature reads zero, succ, add,
        mul. Deterministic, and shared by the theorem and its `Nat` instance."""
        return sorted(self.symbols, key=lambda s: (self.symbols[s], _ABSTRACT.symbol(s)))

    def theorem(self, name: str) -> str:
        concl = self.subst(self.seq.concl)
        hyps = [self.subst(h) for h in sorted(self.seq.hyps, key=render_statement)]
        hyp_vars = sorted({v for h in hyps for v in h.free_vars()})
        concl_vars = [v for v in closure_names(concl) if v not in hyp_vars]

        params = [f"{{{CARRIER} : Type}}"]
        params += [
            f"({_ABSTRACT.symbol(s)} : {_fun_type(self.symbols[s])})" for s in self.symbol_order()
        ]
        params += [f"({lean_name(v)} : {CARRIER})" for v in hyp_vars]
        params += [f"({self.open_names[h]} : {render_formula(h)})" for h in hyps]
        params += [
            f"({self.axiom_names[ax]} : {render_statement(ax)})"
            for ax in sorted(self.theory.axioms, key=lambda a: self.axiom_names[a])
        ]
        if uses_induction(self.pf):
            params.append(f"(ind : {self.induction_type()})")

        statement = "".join(f"∀ {lean_name(v)} : {CARRIER}, " for v in concl_vars)
        statement += render_formula(concl)
        body = "".join(f"fun {lean_name(v)} : {CARRIER} => " for v in concl_vars)
        body += self.proof_text(self.pf, self.sigma0, {})

        head = f"theorem {name} " + " ".join(params[:4])
        rest = "".join(f"\n    {p}" for p in params[4:])
        return f"{head}{rest}\n    : {statement} :=\n  {body}\n"

    def model_example(self, name: str, model: LeanModel) -> str:
        """Instantiate the theorem in a completely registered semantic model.

        Arguments are passed by name, so neither axiom nor symbol ordering can
        change the meaning. Registrations are tied to an exact theory object;
        an unregistered or merely equal theory remains conditional.
        """
        if model.theory is not self.theory:
            raise LeanError(f"model {model.name!r} is not registered for this theory")
        if self.seq.hyps:
            raise LeanError("cannot instantiate a theorem with open hypotheses in a model")
        symbol_map = model.symbol_map()
        if set(symbol_map) != set(self.symbols):
            raise LeanError(
                f"model {model.name!r} symbols do not match the exported theorem: "
                f"expected {sorted(self.symbols)!r}, got {sorted(symbol_map)!r}"
            )
        style = _Style(model.carrier, symbol_map)
        statement = _render_statement(self.subst(self.seq.concl), style)
        args = [f"({CARRIER} := {model.carrier})"]
        args += [
            f"({_ABSTRACT.symbol(s)} := {symbol_map[s]})" for s in self.symbol_order()
        ]
        axiom_proofs = model.axiom_map()
        for ax in sorted(self.theory.axioms, key=lambda a: self.axiom_names[a]):
            label = self.axiom_names[ax]
            proof = axiom_proofs.get(ax)
            if proof is None:
                raise LeanError(f"model {model.name!r} has no proof for {label}")
            args.append(f"({label} := {proof})")
        if uses_induction(self.pf):
            if model.induction_proof is None:
                raise LeanError(f"model {model.name!r} has no induction proof")
            args.append(f"(ind := {model.induction_proof})")
        applied = "\n    ".join([f"  {name} {args[0]}", *args[1:]])
        return f"example : {statement} :=\n{applied}\n"

    def induction_type(self) -> str:
        """The induction principle as a hypothesis: exactly the schema our
        `Induct` rule implements, with the theory's own base term."""
        zero = self.term_text(self.theory.zero, _L_ATOM)
        succ = _ABSTRACT.symbol(self.theory.succ or "S")
        return (
            f"∀ P : {CARRIER} → Prop, P {zero} → "
            f"(∀ n : {CARRIER}, P n → P ({succ} n)) → ∀ n : {CARRIER}, P n"
        )

    def term_text(self, term, prec: int = _L_ATOM) -> str:
        return _render(term, _Names(_free_names(term)), prec)

    # --- the proof term -----------------------------------------------------

    def proof_text(self, pf: object, sigma: dict, env: dict) -> str:
        """Render a proof iteratively with environments carried on each visit."""
        return self.render(cast(Pf, pf), _ProofContext(sigma, env))

    def unsupported(self, value: object, context: object) -> tuple[object, ...]:
        raise LeanError(f"cannot export the rule {type(value).__name__}")

    @case(Axiom)
    def _axiom(self, pf: Axiom, context: _ProofContext) -> tuple[object, ...]:
        name = self.axiom_names.get(pf.formula)
        if name is None:
            raise LeanError(f"not an axiom of the exported theory: {pf.formula!r}")
        args = [
            self.term_text(substitute(Var(v), context.sigma), _L_ATOM)
            for v in closure_names(pf.formula)
        ]
        return (f"({name} {' '.join(args)})" if args else name,)

    @case(Assume)
    def _assume(self, pf: Assume, context: _ProofContext) -> tuple[object, ...]:
        key = substitute(pf.formula, context.sigma)
        name = context.env.get(key) or self.open_names.get(key)
        if name is None:
            raise LeanError(f"no hypothesis in scope for {key!r}")
        return (name,)

    @case(Refl)
    def _refl(self, pf: Refl, context: _ProofContext) -> tuple[object, ...]:
        return (f"(Eq.refl {self.term_text(substitute(pf.term, context.sigma))})",)

    @case(Sym)
    def _sym(self, pf: Sym, context: _ProofContext) -> tuple[object, ...]:
        return ("(Eq.symm ", Visit(pf.sub, context), ")")

    @case(Trans)
    def _trans(self, pf: Trans, context: _ProofContext) -> tuple[object, ...]:
        return (
            "(Eq.trans ",
            Visit(pf.left, context),
            " ",
            Visit(pf.right, context),
            ")",
        )

    @case(Cong)
    def _cong(self, pf: Cong, context: _ProofContext) -> tuple[object, ...]:
        """`congrArg f h₁` gives `f a₁ = f b₁` (partially applied for an n-ary f);
        each further argument is folded on with `congr : f = g → a = b → f a = g b`."""
        name = _ABSTRACT.symbol(pf.fun)
        if not pf.args:
            return (f"(Eq.refl {name})",)
        pieces: list[object] = ["(congr " * (len(pf.args) - 1)]
        pieces += [f"(congrArg {name} ", Visit(pf.args[0], context), ")"]
        for sub in pf.args[1:]:
            pieces += [" ", Visit(sub, context), ")"]
        return tuple(pieces)

    @case(MP)
    def _mp(self, pf: MP, context: _ProofContext) -> tuple[object, ...]:
        return ("(", Visit(pf.imp, context), " ", Visit(pf.ant, context), ")")

    @case(ImpIntro)
    def _imp_intro(self, pf: ImpIntro, context: _ProofContext) -> tuple[object, ...]:
        hyp = substitute(pf.hyp, context.sigma)
        name = self.supply.fresh("h")
        return (
            f"(fun {name} : {render_formula(hyp)} => ",
            Visit(pf.body, _ProofContext(context.sigma, {**context.env, hyp: name})),
            ")",
        )

    @case(Inst)
    def _inst(self, pf: Inst, context: _ProofContext) -> tuple[object, ...]:
        """Instantiation emits nothing: it re-renders the sub-proof under an
        extended environment, so the variable is already gone by the time any
        axiom or hypothesis is printed."""
        sigma = {**context.sigma, pf.var: substitute(pf.term, context.sigma)}
        return (Visit(pf.sub, _ProofContext(sigma, context.env)),)

    @case(Induct)
    def _induct(self, pf: Induct, context: _ProofContext) -> tuple[object, ...]:
        """`ind (fun n => P n) <base at zero> (fun n => <step at n>) <the variable>`.
        Our `Induct` proves `pred` with `var` still free -- read as universally
        quantified -- so the Lean term applies the principle back to `var`'s
        current image, and base/step render under `var := zero` / `var := n`."""
        base_var = self.fresh_binder(pf.var)
        step_var = self.fresh_binder(pf.var)
        motive = render_formula(substitute(pf.pred, {**context.sigma, pf.var: Var(base_var)}))
        arg = self.term_text(substitute(Var(pf.var), context.sigma))
        return (
            f"(ind (fun {base_var} : {CARRIER} => {motive}) ",
            Visit(
                pf.base,
                _ProofContext({**context.sigma, pf.var: self.theory.zero}, context.env),
            ),
            f" (fun {step_var} : {CARRIER} => ",
            Visit(
                pf.step,
                _ProofContext({**context.sigma, pf.var: Var(step_var)}, context.env),
            ),
            f") {arg})",
        )

    @case(ExFalso)
    def _ex_falso(self, pf: ExFalso, context: _ProofContext) -> tuple[object, ...]:
        concl = render_formula(substitute(pf.concl, context.sigma))
        return ("(False.elim ", Visit(pf.sub, context), f" : {concl})")

    @case(RAA)
    def _raa(self, pf: RAA, context: _ProofContext) -> tuple[object, ...]:
        goal = substitute(pf.goal, context.sigma)
        negated = Not(goal)
        name = self.supply.fresh("h")
        return (
            f"(Classical.byContradiction (fun {name} : {render_formula(negated)} => ",
            Visit(pf.sub, _ProofContext(context.sigma, {**context.env, negated: name})),
            f") : {render_formula(goal)})",
        )

    @case(ForallElim)
    def _forall_elim(self, pf: ForallElim, context: _ProofContext) -> tuple[object, ...]:
        arg = self.term_text(substitute(pf.term, context.sigma))
        return ("(", Visit(pf.sub, context), f" {arg})")

    @case(ForallIntro)
    def _forall_intro(self, pf: ForallIntro, context: _ProofContext) -> tuple[object, ...]:
        if pf.sort:
            raise LeanError(f"sorted generalization :{pf.sort} is out of scope")
        name = self.fresh_binder(pf.var)
        return (
            f"(fun {name} : {CARRIER} => ",
            Visit(
                pf.sub,
                _ProofContext({**context.sigma, pf.var: Var(name)}, context.env),
            ),
            ")",
        )

    @case(ExistsIntro)
    def _exists_intro(self, pf: ExistsIntro, context: _ProofContext) -> tuple[object, ...]:
        claim = render_formula(substitute(pf.claim, context.sigma))
        witness = self.term_text(substitute(pf.witness, context.sigma))
        return (f"(Exists.intro {witness} ", Visit(pf.sub, context), f" : {claim})")

    @case(ExistsElim)
    def _exists_elim(self, pf: ExistsElim, context: _ProofContext) -> tuple[object, ...]:
        ex = self.conclusion(pf.sub_ex)
        if type(ex) is not Exists:
            raise LeanError(f"exists-elim needs an existential, got {ex!r}")
        name = self.fresh_binder(pf.eigenvar)
        inner = {**context.sigma, pf.eigenvar: Var(name)}
        instance = substitute(instantiate(ex, Var(pf.eigenvar)), inner)
        hyp = self.supply.fresh("h")
        phi = render_formula(substitute(self.conclusion(pf.sub_use), inner))
        return (
            "(Exists.elim ",
            Visit(pf.sub_ex, context),
            f" (fun {name} : {CARRIER} => fun {hyp} : {render_formula(instance)} => ",
            Visit(pf.sub_use, _ProofContext(inner, {**context.env, instance: hyp})),
            f") : {phi})",
        )


__all__ = ["AXIOM_LABELS", "export_theorem", "uses_induction"]
