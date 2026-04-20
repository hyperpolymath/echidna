#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
#
# Generate high-quality synthetic proofs for provers with tiny communities
# where downloadable corpora are unavailable or extremely limited.
#
# Covers: Nuprl, Minlog, Twelf, Imandra
#
# Each prover gets 100+ synthetic proofs based on:
# - Known theorems from their documentation and papers
# - Standard mathematical facts adapted to each prover's syntax
# - Realistic tactic/proof term sequences for that specific prover
#
# Output: training_data/proof_states_{prover}.jsonl
# ID ranges:
#   Nuprl:  88000+
#   Minlog: 88500+
#   Twelf:  89000+
#   Imandra: 89500+

using JSON3

const REPO_ROOT = dirname(dirname(abspath(@__FILE__)))
const OUTPUT_DIR = joinpath(REPO_ROOT, "training_data")

# ---------------------------------------------------------------------------
# Nuprl (Cornell)
# ---------------------------------------------------------------------------
# Nuprl uses a constructive type theory (Martin-Loef style) with a rich
# tactic language. Proofs are extracted as programs.

"""
    generate_nuprl() -> Vector{Dict{String,Any}}

Generate Nuprl synthetic proofs.
"""
function generate_nuprl()::Vector{Dict{String,Any}}
    arithmetic = [
        ("add_comm", "all x,y:Int. (x + y) = (y + x)", "Auto"),
        ("add_assoc", "all x,y,z:Int. ((x + y) + z) = (x + (y + z))", "Auto"),
        ("mul_comm", "all x,y:Int. (x * y) = (y * x)", "Auto"),
        ("mul_assoc", "all x,y,z:Int. ((x * y) * z) = (x * (y * z))", "Auto"),
        ("distrib_left", "all x,y,z:Int. (x * (y + z)) = ((x * y) + (x * z))", "Auto"),
        ("add_zero", "all x:Int. (x + 0) = x", "Auto"),
        ("mul_one", "all x:Int. (x * 1) = x", "Auto"),
        ("add_inverse", "all x:Int. (x + (-x)) = 0", "Auto"),
        ("nat_induction", "all P:(Nat -> Prop). P(0) => (all n:Nat. P(n) => P(n+1)) => all n:Nat. P(n)", "Intro; Intro; NatInd; Auto"),
        ("div_mod", "all a:Int, b:PosInt. a = (b * (a / b)) + (a mod b)", "Auto"),
        ("abs_nonneg", "all x:Int. 0 <= |x|", "CaseAnalysis `x >= 0`; Auto"),
        ("triangle_ineq", "all x,y:Int. |x + y| <= |x| + |y|", "CaseAnalysis `x >= 0`; CaseAnalysis `y >= 0`; Auto"),
        ("even_or_odd", "all n:Nat. (exists k:Nat. n = 2*k) or (exists k:Nat. n = 2*k + 1)", "NatInd; Auto; OrElim; Auto"),
        ("gcd_divides", "all a,b:PosInt. divides(gcd(a,b), a) & divides(gcd(a,b), b)", "Unfold `gcd`; NatInd; Auto"),
        ("prime_factorization", "all n:Nat. n >= 2 => exists ps:List(PosInt). all p in ps. prime(p) & product(ps) = n", "StrongInduction; Auto"),
    ]

    types = [
        ("pair_eta", "all A,B:Type, p:A*B. p = <fst(p), snd(p)>", "Intro; PairElim; Auto"),
        ("sum_elim", "all A,B:Type, C:Type. (A -> C) -> (B -> C) -> (A + B) -> C", "Intro; Intro; Intro; DecideElim; Auto"),
        ("void_elim", "all A:Type. Void -> A", "Intro; VoidElim; Auto"),
        ("unit_unique", "all x,y:Unit. x = y", "Intro; Intro; UnitElim; Auto"),
        ("func_ext", "all A,B:Type, f,g:A->B. (all x:A. f(x) = g(x)) => f = g", "Intro; FunExt; Auto"),
        ("curry_uncurry", "all A,B,C:Type, f:A*B->C. uncurry(curry(f)) = f", "Intro; FunExt; Intro; PairElim; Auto"),
        ("dep_pair_eta", "all A:Type, B:A->Type, p:(x:A * B(x)). p = <fst(p), snd(p)>", "Intro; DPairElim; Auto"),
        ("iso_nat_list_unit", "all n:Nat. exists l:List(Unit). length(l) = n", "NatInd; Auto; Witness `cons(tt, l)`; Auto"),
        ("type_product_comm", "all A,B:Type. A*B ~ B*A", "Intro; Iso; Lambda x. <snd(x), fst(x)>; Lambda y. <snd(y), fst(y)>; Auto"),
        ("type_sum_comm", "all A,B:Type. A+B ~ B+A", "Intro; Iso; DecideElim; Auto"),
    ]

    lists = [
        ("append_nil", "all A:Type, l:List(A). append(l, nil) = l", "ListInd; Auto"),
        ("append_assoc", "all A:Type, l1,l2,l3:List(A). append(append(l1,l2),l3) = append(l1,append(l2,l3))", "ListInd `l1`; Auto"),
        ("length_append", "all A:Type, l1,l2:List(A). length(append(l1,l2)) = length(l1) + length(l2)", "ListInd `l1`; Auto"),
        ("map_id", "all A:Type, l:List(A). map(id, l) = l", "ListInd; Auto"),
        ("map_compose", "all A,B,C:Type, f:B->C, g:A->B, l:List(A). map(f, map(g, l)) = map(compose(f,g), l)", "ListInd; Auto"),
        ("reverse_reverse", "all A:Type, l:List(A). reverse(reverse(l)) = l", "ListInd; Auto; Unfold `reverse`; Auto"),
        ("length_reverse", "all A:Type, l:List(A). length(reverse(l)) = length(l)", "ListInd; Auto"),
        ("member_append", "all A:Type, x:A, l1,l2:List(A). member(x, append(l1,l2)) <=> member(x,l1) or member(x,l2)", "ListInd `l1`; Auto; OrElim; Auto"),
        ("filter_length", "all A:Type, p:A->Bool, l:List(A). length(filter(p, l)) <= length(l)", "ListInd; Auto; CaseAnalysis `p(hd)`; Auto"),
        ("foldr_append", "all A,B:Type, f:A->B->B, z:B, l1,l2:List(A). foldr(f, z, append(l1,l2)) = foldr(f, foldr(f,z,l2), l1)", "ListInd `l1`; Auto"),
    ]

    logic = [
        ("modus_ponens", "all P,Q:Prop. P => (P => Q) => Q", "Intro; Intro; Apply; Auto"),
        ("and_comm", "all P,Q:Prop. P & Q => Q & P", "Intro; AndElim; Split; Auto"),
        ("or_comm", "all P,Q:Prop. P or Q => Q or P", "Intro; OrElim; [Right; Auto | Left; Auto]"),
        ("double_neg_elim", "all P:Prop. ~~P => P", "Intro; ByContradiction; Auto"),
        ("de_morgan_and", "all P,Q:Prop. ~(P & Q) <=> (~P or ~Q)", "Split; Intro; ByContradiction; Auto; Intro; OrElim; Auto"),
        ("de_morgan_or", "all P,Q:Prop. ~(P or Q) <=> (~P & ~Q)", "Split; Intro; Split; Intro; Apply; Left; Auto; Intro; Apply; Right; Auto; Intro; AndElim; OrElim; Auto"),
        ("contrapositive", "all P,Q:Prop. (P => Q) => (~Q => ~P)", "Intro; Intro; Intro; Apply; Auto"),
        ("forall_implies_exists", "all A:Type, P:A->Prop, a:A. (all x:A. P(x)) => exists x:A. P(x)", "Intro; Intro; Witness `a`; Apply; Auto"),
        ("exists_not_forall_not", "all A:Type, P:A->Prop. (exists x:A. P(x)) => ~(all x:A. ~P(x))", "Intro; ExistsElim; Intro; Apply; Auto"),
        ("peirce", "all P,Q:Prop. ((P => Q) => P) => P", "Intro; ByContradiction; Apply; Intro; Absurd; Auto"),
    ]

    constructive = [
        ("nat_decidable_eq", "all m,n:Nat. (m = n) or ~(m = n)", "NatInd `m`; NatInd `n`; Auto; CaseAnalysis; Auto"),
        ("markov_nat", "all f:Nat->Bool. ~~(exists n:Nat. f(n) = true) => exists n:Nat. f(n) = true", "Intro; BoundedSearch; Auto"),
        ("choice_nat", "all R:Nat->Nat->Prop. (all n:Nat. exists m:Nat. R(n,m)) => exists f:Nat->Nat. all n:Nat. R(n, f(n))", "Intro; CountableChoice; Auto"),
        ("well_ordering_nat", "all P:Nat->Prop. (exists n:Nat. P(n)) => exists m:Nat. P(m) & (all k:Nat. k < m => ~P(k))", "StrongInduction; Auto"),
        ("brouwer_continuity", "all f:(Nat->Nat)->Nat. exists n:Nat. all a,b:Nat->Nat. (all i:Nat. i < n => a(i) = b(i)) => f(a) = f(b)", "Continuity; Auto"),
        ("church_rosser", "all M,N,P:Term. reduces(M, N) => reduces(M, P) => exists Q:Term. reduces(N, Q) & reduces(P, Q)", "Induction; Diamond; Auto"),
        ("fan_theorem", "all T:Tree. (all b:Branch. bar(T, b)) => exists n:Nat. uniform_bar(T, n)", "BarInduction; Auto"),
        ("kripke_schema", "all A:Prop. (A \\/ ~A) => decidable(A)", "Intro; OrElim; Auto"),
    ]

    sets = [
        ("set_ext", "all A:Type, s1,s2:Set(A). (all x:A. x in s1 <=> x in s2) => s1 = s2", "Intro; SetExt; Auto"),
        ("union_comm", "all A:Type, s1,s2:Set(A). union(s1, s2) = union(s2, s1)", "SetExt; Auto"),
        ("union_assoc", "all A:Type, s1,s2,s3:Set(A). union(union(s1,s2),s3) = union(s1,union(s2,s3))", "SetExt; Auto"),
        ("inter_comm", "all A:Type, s1,s2:Set(A). intersect(s1, s2) = intersect(s2, s1)", "SetExt; Auto"),
        ("distrib_union_inter", "all A:Type, s1,s2,s3:Set(A). union(s1, intersect(s2, s3)) = intersect(union(s1,s2), union(s1,s3))", "SetExt; Auto"),
        ("empty_subset", "all A:Type, s:Set(A). subset(empty, s)", "Intro; ElimEmpty; Auto"),
        ("union_superset", "all A:Type, s1,s2:Set(A). subset(s1, union(s1, s2))", "Intro; UnionElim; Auto"),
        ("power_set_monotone", "all A:Type, s1,s2:Set(A). subset(s1, s2) => subset(pow(s1), pow(s2))", "Intro; Intro; Apply; Auto"),
        ("finite_union", "all A:Type, s1,s2:FiniteSet(A). finite(union(s1, s2))", "Intro; FiniteUnion; Auto"),
        ("cardinal_union", "all A:Type, s1,s2:FiniteSet(A). card(union(s1,s2)) = card(s1) + card(s2) - card(intersect(s1,s2))", "InclusionExclusion; Auto"),
    ]

    relations = [
        ("refl_closure", "all A:Type, R:A->A->Prop, x:A. refl_trans_closure(R)(x, x)", "Intro; RTC_Refl; Auto"),
        ("trans_composition", "all A:Type, R:A->A->Prop, x,y,z:A. trans_closure(R)(x,y) => trans_closure(R)(y,z) => trans_closure(R)(x,z)", "Intro; Induction; Auto"),
        ("equiv_sym", "all A:Type, R:A->A->Prop, x,y:A. equivalence(R) => R(x, y) => R(y, x)", "Intro; Intro; ApplySym; Auto"),
        ("well_founded_induction", "all A:Type, R:A->A->Prop. well_founded(R) => all P:A->Prop. (all x:A. (all y:A. R(y,x) => P(y)) => P(x)) => all x:A. P(x)", "Intro; WFInduction; Auto"),
        ("partial_order_antisym", "all A:Type, R:A->A->Prop, x,y:A. partial_order(R) => R(x,y) => R(y,x) => x = y", "Intro; ApplyAntisym; Auto"),
        ("total_order_trichotomy", "all A:Type, R:A->A->Prop, x,y:A. total_order(R) => R(x,y) \\/ x = y \\/ R(y,x)", "Intro; Trichotomy; Auto"),
        ("graph_path_compose", "all V:Type, E:V->V->Prop, x,y,z:V. path(E)(x,y) => path(E)(y,z) => path(E)(x,z)", "Induction; Auto"),
        ("converse_relation", "all A,B:Type, R:A->B->Prop, x:A, y:B. R(x,y) <=> converse(R)(y,x)", "Intro; Split; Auto"),
    ]

    number_theory = [
        ("euclid_lemma", "all p:Prime, a,b:Nat. divides(p, a*b) => divides(p, a) or divides(p, b)", "Intro; CaseGCD; Auto"),
        ("fundamental_arith", "all n:Nat. n >= 2 => exists! ps:List(Prime). product(ps) = n", "StrongInduction; Auto"),
        ("bezout", "all a,b:Nat. a > 0 \\/ b > 0 => exists x,y:Int. a*x + b*y = gcd(a,b)", "Intro; ExtendedEuclid; Auto"),
        ("infinitude_primes", "all n:Nat. exists p:Prime. p > n", "Intro; Witness `factorial(n)+1`; Auto"),
        ("wilson_theorem", "all p:Prime. (factorial(p-1) + 1) mod p = 0", "Intro; ModArith; Auto"),
        ("fermat_little", "all p:Prime, a:Nat. coprime(a, p) => (a^(p-1)) mod p = 1", "Intro; GroupOrder; Auto"),
        ("chinese_remainder", "all m,n:Nat. coprime(m,n) => all a,b:Int. exists x:Int. (x mod m = a) & (x mod n = b)", "Intro; Intro; CRT; Auto"),
        ("sum_of_squares", "all n:Nat. (exists a,b:Nat. n = a*a + b*b) <=> all p:Prime. p `divides` n & p mod 4 = 3 => even(mult(p, n))", "Classify; Auto"),
        ("pigeon_hole", "all n,m:Nat, f:Fin(n)->Fin(m). n > m => exists i,j:Fin(n). i <> j & f(i) = f(j)", "Intro; PHP; Auto"),
    ]

    real_analysis = [
        ("lim_sum", "all f,g:Nat->Real, a,b:Real. lim(f) = a => lim(g) = b => lim(fun n. f(n)+g(n)) = a+b", "Intro; LimitArith; Auto"),
        ("lim_prod", "all f,g:Nat->Real, a,b:Real. lim(f) = a => lim(g) = b => lim(fun n. f(n)*g(n)) = a*b", "Intro; LimitArith; Auto"),
        ("squeeze", "all f,g,h:Nat->Real. (all n:Nat. f(n) <= g(n) <= h(n)) => lim(f) = lim(h) => lim(g) = lim(f)", "Intro; Squeeze; Auto"),
        ("continuous_compose", "all f,g:Real->Real. continuous(f) => continuous(g) => continuous(compose(f, g))", "Intro; EpsilonDelta; Auto"),
        ("ivt", "all f:Real->Real, a,b:Real, y:Real. continuous(f) => f(a) <= y <= f(b) => exists c:Real. a <= c <= b & f(c) = y", "Intro; Bisection; Auto"),
        ("mvt", "all f:Real->Real, a,b:Real. differentiable(f) => a < b => exists c:Real. a < c < b & derivative(f)(c) = (f(b)-f(a))/(b-a)", "Intro; Rolle; Auto"),
        ("cauchy_complete", "all s:Nat->Real. cauchy(s) => exists L:Real. lim(s) = L", "Intro; CompletenessAxiom; Auto"),
        ("compact_attains", "all f:Real->Real, K:Set(Real). compact(K) => continuous(f) => exists m,M:Real. m in f(K) & M in f(K) & all y in f(K). m <= y <= M", "Intro; Intro; ExtremeValue; Auto"),
    ]

    computability = [
        ("halting_undecidable", "~exists H:(Prog->Input->Bool). all p:Prog, x:Input. H(p, x) = true <=> halts(p, x)", "Diagonalization; Auto"),
        ("rice_theorem", "all P:(Prog->Prop). nontrivial(P) => ~decidable(P)", "Intro; Reduction; Auto"),
        ("recursion_theorem", "all f:Prog->Prog. exists e:Prog. equal_programs(e, f(e))", "KleeneRecursion; Auto"),
        ("smn_theorem", "all n,m:Nat, f:Prog. exists s:Prog. all x,y:Input. run(f, pair(x,y)) = run(run(s, x), y)", "Intro; Intro; SMN; Auto"),
        ("kleene_normal", "all f:PartialFn. exists e,U:Prog. all x:Input. f(x) = run(U, pair(e, x))", "Intro; NormalForm; Auto"),
        ("church_turing_lambda", "all f:ComputableFn. exists t:Term. reduces_to_numeral(t(numeral(x)), numeral(f(x)))", "Intro; Encode; Auto"),
    ]

    category_theory = [
        ("cat_comp_assoc", "all C:Cat, f:Hom(a,b), g:Hom(b,c), h:Hom(c,d). comp(comp(h,g),f) = comp(h,comp(g,f))", "Intro; CatAssoc; Auto"),
        ("cat_id_left", "all C:Cat, f:Hom(a,b). comp(id(b), f) = f", "Intro; CatIdLeft; Auto"),
        ("cat_id_right", "all C:Cat, f:Hom(a,b). comp(f, id(a)) = f", "Intro; CatIdRight; Auto"),
        ("functor_comp", "all F:Functor, f:Hom(a,b), g:Hom(b,c). Fmap(comp(g,f)) = comp(Fmap(g), Fmap(f))", "Intro; FunctorLaw; Auto"),
        ("functor_id", "all F:Functor, a:Obj. Fmap(id(a)) = id(Fobj(a))", "Intro; FunctorIdLaw; Auto"),
        ("natural_trans", "all F,G:Functor, eta:NatTrans(F,G), f:Hom(a,b). comp(eta(b), Fmap_F(f)) = comp(Fmap_G(f), eta(a))", "Intro; Naturality; Auto"),
        ("iso_compose", "all C:Cat, f:Hom(a,b), g:Hom(b,a). comp(g, f) = id(a) => comp(f, g) = id(b) => isomorphism(f)", "Intro; Isomorphism; Auto"),
        ("product_universal", "all C:Cat, p:Obj, f:Hom(p,a), g:Hom(p,b). exists! h:Hom(p, prod(a,b)). comp(pi1, h) = f & comp(pi2, h) = g", "Intro; Universal; Auto"),
    ]

    topology = [
        ("open_union", "all X:TopSpace, U,V:Open(X). open(union(U, V))", "Intro; OpenAxiom; Auto"),
        ("open_finite_inter", "all X:TopSpace, U,V:Open(X). open(intersect(U, V))", "Intro; OpenAxiom; Auto"),
        ("continuous_compose", "all X,Y,Z:TopSpace, f:X->Y, g:Y->Z. continuous(f) => continuous(g) => continuous(compose(g, f))", "Intro; Continuous; Auto"),
        ("compact_closed", "all X:TopSpace, K:Subspace(X). compact(K) => hausdorff(X) => closed(K)", "Intro; Compact; Auto"),
        ("connected_image", "all X,Y:TopSpace, f:X->Y. continuous(f) => connected(X) => connected(image(f))", "Intro; Connected; Auto"),
        ("hausdorff_limit", "all X:TopSpace, s:Nat->X, L1,L2:X. hausdorff(X) => lim(s) = L1 => lim(s) = L2 => L1 = L2", "Intro; Hausdorff; Auto"),
        ("homeomorphism", "all X,Y:TopSpace, f:X->Y. continuous(f) => continuous(inverse(f)) => homeomorphism(f)", "Intro; Homeomorphism; Auto"),
    ]

    algebra = [
        ("group_inv_unique", "all G:Group, a,b,c:G. op(a,b) = e => op(a,c) = e => b = c", "Intro; Cancel; Auto"),
        ("subgroup_closed", "all G:Group, H:Subgroup(G), a,b:H. op(a, b) in H", "Intro; SubgroupAxiom; Auto"),
        ("lagrange", "all G:FinGroup, H:Subgroup(G). divides(order(H), order(G))", "Intro; Lagrange; Auto"),
        ("homomorphism_kernel", "all G,H:Group, f:Homomorphism(G, H). subgroup(kernel(f), G)", "Intro; KernelAxiom; Auto"),
        ("ring_add_group", "all R:Ring. group(R, +)", "Intro; RingAxiom; Auto"),
        ("ideal_closed", "all R:Ring, I:Ideal(R), a:R, b:I. op(a, b) in I", "Intro; IdealAxiom; Auto"),
        ("field_no_zero_div", "all F:Field, a,b:F. a*b = 0 => a = 0 or b = 0", "Intro; FieldAxiom; Auto"),
        ("vector_space_sum", "all V:VectorSpace, v,w:V. v + w = w + v", "Intro; VectorAxiom; Auto"),
    ]

    probability = [
        ("prob_nonneg", "all P:ProbMeasure, A:Event. P(A) >= 0", "Intro; ProbAxiom; Auto"),
        ("prob_total", "all P:ProbMeasure. P(universe) = 1", "Intro; ProbAxiom; Auto"),
        ("prob_additivity", "all P:ProbMeasure, A,B:Event. disjoint(A, B) => P(union(A, B)) = P(A) + P(B)", "Intro; Additivity; Auto"),
        ("bayes_rule", "all P:ProbMeasure, A,B:Event. P(B) > 0 => P(A | B) = P(A & B) / P(B)", "Intro; BayesDef; Auto"),
        ("conditional_indep", "all P:ProbMeasure, A,B,C:Event. indep(A, B | C) <=> P(A & B | C) = P(A | C) * P(B | C)", "Intro; Split; Auto"),
        ("markov_ineq", "all X:RandomVar, a:PosReal. P(X >= a) <= E(X) / a", "Intro; Markov; Auto"),
        ("expectation_linear", "all X,Y:RandomVar, a,b:Real. E(a*X + b*Y) = a*E(X) + b*E(Y)", "Intro; Linearity; Auto"),
        ("variance_nonneg", "all X:RandomVar. var(X) >= 0", "Intro; Variance; Auto"),
    ]

    bishop_analysis = [
        ("bishop_real_approx", "all x:Real, n:PosInt. exists q:Rational. abs(x - q) < 1/n", "Intro; ConstructReal; Auto"),
        ("bishop_seq_modulus", "all s:Nat->Real, eps:PosReal. cauchy(s) => exists M:Nat. all m,n:Nat. m >= M => n >= M => abs(s(m) - s(n)) < eps", "Intro; Intro; ModulusCauchy; Auto"),
        ("bishop_cont_uniform", "all f:Real->Real, K:CompactInterval. continuous(f) => uniformly_continuous_on(f, K)", "Intro; Intro; HeineCantor; Auto"),
        ("bishop_rational_dense", "all a,b:Real. a < b => exists q:Rational. a < q < b", "Intro; RationalDensity; Auto"),
        ("bishop_sqrt_exists", "all x:NonNegReal. exists y:NonNegReal. y*y = x", "Intro; Newton; Auto"),
    ]

    proof_theory = [
        ("cut_elim_nuprl", "all A,B. |- A -> (A |- B) -> |- B", "Intros; CutAdmissible; Auto"),
        ("proof_identity", "all A:Prop. |- A -> A", "Intro; Axiom; Auto"),
        ("proof_weakening", "all A,B:Prop. |- B => (A |- B)", "Intros; Weakening; Auto"),
        ("subtype_refl", "all T:Type. T subtype T", "Intro; SubtypeRefl; Auto"),
        ("subtype_trans", "all T1,T2,T3:Type. T1 subtype T2 => T2 subtype T3 => T1 subtype T3", "Intros; SubtypeTrans; Auto"),
        ("equality_symmetry", "all A:Type, x,y:A. x = y => y = x", "Intros; EqSym; Auto"),
        ("equality_trans", "all A:Type, x,y,z:A. x = y => y = z => x = z", "Intros; EqTrans; Auto"),
    ]

    information = [
        ("entropy_nonneg", "all P:ProbDist. entropy(P) >= 0", "Intro; EntropyDef; Auto"),
        ("entropy_uniform_max", "all n:PosNat, P:ProbDist(Fin(n)). entropy(P) <= log(n)", "Intro; Intro; MaxEntropy; Auto"),
        ("mutual_info_nonneg", "all X,Y:RandomVar. I(X; Y) >= 0", "Intro; MIDef; Auto"),
        ("chain_rule_entropy", "all X,Y:RandomVar. H(X, Y) = H(X) + H(Y | X)", "Intro; ChainRule; Auto"),
        ("kraft_inequality", "all C:PrefixCode. sum(c in C, 2^(-length(c))) <= 1", "Intro; Kraft; Auto"),
        ("source_coding", "all X:RandomVar, eps:PosReal. exists n:PosNat, C:Code. expected_length(C(X^n)) / n <= H(X) + eps", "Intro; ShannonSource; Auto"),
    ]

    quotient_types = [
        ("quotient_class", "all A:Type, R:Equiv(A), x,y:A. R(x,y) => [x]_R = [y]_R", "Intros; QuotientEq; Auto"),
        ("quotient_lift", "all A,B:Type, R:Equiv(A), f:A->B. (all x,y:A. R(x,y) => f(x) = f(y)) => A/R -> B", "Intros; QuotientLift; Auto"),
        ("nat_quot_modp", "all p:PosNat. Nat/cong(p) ~ Fin(p)", "Intro; Bijection; Auto"),
        ("partition_quotient", "all A:Type, R:Equiv(A). partition(A, R) <=> A/R", "Intro; Partition; Auto"),
        ("setoid_morphism", "all A,B:Setoid, f:A->B. morphism(f) <=> (all x,y:A. eq_A(x,y) => eq_B(f(x), f(y)))", "Intro; Morphism; Auto"),
    ]

    w_types = [
        ("w_type", "all A:Type, B:A->Type. W(A, B) : Type", "Intros; WType; Auto"),
        ("w_induction", "all A:Type, B:A->Type, P:W(A,B)->Prop. (all a:A, f:B(a)->W(A,B). (all b:B(a). P(f(b))) => P(sup(a, f))) => all w:W(A,B). P(w)", "Intros; WInduction; Auto"),
        ("w_nat_iso", "Nat ~ W(Bool, lambda b. if b then Unit else Empty)", "Intro; Bijection; Auto"),
        ("w_list_iso", "all A:Type. List(A) ~ W(1 + A, lambda s. match s with inl _ => Empty | inr _ => Unit)", "Intro; Bijection; Auto"),
    ]

    all_categories = [
        ("arithmetic", arithmetic),
        ("types", types),
        ("lists", lists),
        ("logic", logic),
        ("constructive", constructive),
        ("sets", sets),
        ("relations", relations),
        ("number_theory", number_theory),
        ("real_analysis", real_analysis),
        ("computability", computability),
        ("category_theory", category_theory),
        ("topology", topology),
        ("algebra", algebra),
        ("probability", probability),
        ("bishop_analysis", bishop_analysis),
        ("proof_theory", proof_theory),
        ("information", information),
        ("quotient_types", quotient_types),
        ("w_types", w_types),
    ]

    proofs = Dict{String,Any}[]
    for (category, entries) in all_categories
        for (name, goal, tactic) in entries
            tactic_names = [strip(t) for t in split(tactic, r"[;\[\]|]") if !isempty(strip(t)) && isuppercase(first(strip(t)))]
            seen = Set{String}(); unique_t = String[]
            for t in tactic_names
                t ∉ seen && (push!(seen, t); push!(unique_t, t))
                length(unique_t) >= 20 && break
            end
            push!(proofs, Dict{String,Any}(
                "id" => 0,
                "prover" => "Nuprl",
                "theorem" => name,
                "goal" => goal,
                "context" => unique_t,
                "tactic_proof" => tactic,
                "source" => "nuprl_synthetic/$(category)",
            ))
        end
    end
    return proofs
end

# ---------------------------------------------------------------------------
# Minlog (Munich)
# ---------------------------------------------------------------------------
# Minlog is a proof assistant based on minimal logic, focused on program
# extraction from proofs. Uses natural deduction with normalization.

"""
    generate_minlog() -> Vector{Dict{String,Any}}

Generate Minlog synthetic proofs.
"""
function generate_minlog()::Vector{Dict{String,Any}}
    natural_deduction = [
        ("imp_refl", "A -> A", "assume A; exact A"),
        ("imp_trans", "(A -> B) -> (B -> C) -> A -> C", "assume f; assume g; assume a; exact (g (f a))"),
        ("and_intro", "A -> B -> A /\\ B", "assume a; assume b; split; [exact a | exact b]"),
        ("and_elim_l", "A /\\ B -> A", "assume h; elim h; assume a; assume b; exact a"),
        ("and_elim_r", "A /\\ B -> B", "assume h; elim h; assume a; assume b; exact b"),
        ("or_intro_l", "A -> A \\/ B", "assume a; left; exact a"),
        ("or_intro_r", "B -> A \\/ B", "assume b; right; exact b"),
        ("or_elim", "(A -> C) -> (B -> C) -> A \\/ B -> C", "assume f; assume g; assume h; elim h; [assume a; exact (f a) | assume b; exact (g b)]"),
        ("false_elim", "F -> A", "assume h; elim h"),
        ("not_intro", "(A -> F) -> ~A", "assume f; intro; exact f"),
        ("double_neg_intro", "A -> ~~A", "assume a; assume h; exact (h a)"),
        ("contrapositive", "(A -> B) -> ~B -> ~A", "assume f; assume nb; assume a; exact (nb (f a))"),
        ("and_comm", "A /\\ B -> B /\\ A", "assume h; elim h; assume a; assume b; split; [exact b | exact a]"),
        ("or_comm", "A \\/ B -> B \\/ A", "assume h; elim h; [assume a; right; exact a | assume b; left; exact b]"),
        ("curry", "(A /\\ B -> C) -> A -> B -> C", "assume f; assume a; assume b; exact (f (a, b))"),
    ]

    arithmetic_extraction = [
        ("add_zero", "all n. n + 0 = n", "ind on n; [refl | assume IH; simp; exact IH]"),
        ("add_succ", "all m n. m + S(n) = S(m + n)", "ind on m; [refl | assume IH; simp; use IH]"),
        ("add_comm", "all m n. m + n = n + m", "ind on m; [use add_zero | assume IH; simp; use add_succ; use IH]"),
        ("add_assoc", "all m n k. (m + n) + k = m + (n + k)", "ind on m; [refl | assume IH; simp; use IH]"),
        ("mul_zero", "all n. n * 0 = 0", "ind on n; [refl | assume IH; simp; use IH]"),
        ("mul_succ", "all m n. m * S(n) = m + m * n", "ind on m; [refl | assume IH; simp; use IH; use add_assoc; use add_comm]"),
        ("mul_comm", "all m n. m * n = n * m", "ind on m; [use mul_zero | assume IH; simp; use mul_succ; use IH]"),
        ("sub_self", "all n. n - n = 0", "ind on n; [refl | assume IH; simp; use IH]"),
        ("max_comm", "all m n. max(m, n) = max(n, m)", "cases; auto"),
        ("min_comm", "all m n. min(m, n) = min(n, m)", "cases; auto"),
        ("max_assoc", "all l m n. max(l, max(m, n)) = max(max(l, m), n)", "cases; auto"),
        ("le_refl", "all n. n <= n", "intro; refl"),
        ("le_trans", "all l m n. l <= m -> m <= n -> l <= n", "assume h1; assume h2; elim h1; elim h2; auto"),
        ("le_antisym", "all m n. m <= n -> n <= m -> m = n", "assume h1; assume h2; elim h1; elim h2; auto"),
        ("lt_succ", "all n. n < S(n)", "intro; auto"),
    ]

    program_extraction = [
        ("sqrt_extraction", "all n. ex m. m * m <= n /\\ n < (m+1) * (m+1)", "ind on n; [ex 0; auto | assume IH; elim IH; assume m; cases; [ex m; auto | ex (S m); auto]]"),
        ("gcd_extraction", "all a b. b > 0 -> ex d. divides(d, a) /\\ divides(d, b) /\\ all c. divides(c, a) -> divides(c, b) -> divides(c, d)", "strong_ind on b; cases; auto"),
        ("div_extraction", "all a b. b > 0 -> ex q r. a = b * q + r /\\ r < b", "strong_ind on a; cases; auto"),
        ("prime_test", "all n. n >= 2 -> prime(n) \\/ ex d. 1 < d /\\ d < n /\\ divides(d, n)", "bounded_search; auto"),
        ("list_sort", "all l:list(nat). ex l'. sorted(l') /\\ perm(l, l')", "ind on l; [ex nil; auto | assume IH; elim IH; assume l'; insert; auto]"),
        ("binary_search_extract", "all a:array(nat) v. sorted(a) -> (ex i. a[i] = v) \\/ (all i. a[i] <> v)", "log_search; auto"),
        ("min_element", "all l:list(nat). l <> nil -> ex m. mem(m, l) /\\ all x. mem(x, l) -> m <= x", "ind on l; auto"),
        ("majority_element", "all l:list(nat). length(l) > 0 -> ex m. count(m, l) > length(l) / 2 \\/ all x. count(x, l) <= length(l) / 2", "boyer_moore; auto"),
    ]

    realizability = [
        ("realizer_identity", "[r : A -> A] = lambda x. x", "normalize; refl"),
        ("realizer_compose", "[r : (A -> B) -> (B -> C) -> A -> C] = lambda f g x. g (f x)", "normalize; refl"),
        ("realizer_pair", "[r : A -> B -> A /\\ B] = lambda a b. (a, b)", "normalize; refl"),
        ("realizer_fst", "[r : A /\\ B -> A] = lambda p. fst(p)", "normalize; refl"),
        ("realizer_snd", "[r : A /\\ B -> B] = lambda p. snd(p)", "normalize; refl"),
        ("realizer_inl", "[r : A -> A \\/ B] = lambda a. inl(a)", "normalize; refl"),
        ("realizer_inr", "[r : B -> A \\/ B] = lambda b. inr(b)", "normalize; refl"),
        ("realizer_case", "[r : (A -> C) -> (B -> C) -> A \\/ B -> C] = lambda f g s. case s of inl(a) => f a | inr(b) => g b", "normalize; refl"),
        ("realizer_forall", "[r : (all x:N. A(x))] = lambda x. r_x", "normalize; refl"),
        ("realizer_exists", "[r : (ex x:N. A(x))] = (n, proof_of_A(n))", "normalize; refl"),
        ("realizer_induction", "[r : nat_rec] = lambda base step n. (rec base step n)", "normalize; refl"),
    ]

    lists_minlog = [
        ("list_nil_append", "all l:list. nil ++ l = l", "intro; refl"),
        ("list_append_nil", "all l:list. l ++ nil = l", "ind on l; [refl | assume IH; simp; use IH]"),
        ("list_append_assoc", "all l1 l2 l3. (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)", "ind on l1; [refl | assume IH; simp; use IH]"),
        ("list_length_append", "all l1 l2. length(l1 ++ l2) = length(l1) + length(l2)", "ind on l1; [refl | assume IH; simp; use IH]"),
        ("list_rev_involutive", "all l. rev(rev(l)) = l", "ind on l; [refl | assume IH; simp; use rev_append; use IH]"),
        ("list_rev_append", "all l1 l2. rev(l1 ++ l2) = rev(l2) ++ rev(l1)", "ind on l1; [simp; use list_append_nil | assume IH; simp; use IH; use list_append_assoc]"),
        ("list_map_id", "all l. map(lambda x. x, l) = l", "ind on l; [refl | assume IH; simp; use IH]"),
        ("list_map_compose", "all f g l. map(f, map(g, l)) = map(lambda x. f (g x), l)", "ind on l; [refl | assume IH; simp; use IH]"),
        ("list_filter_length", "all p l. length(filter(p, l)) <= length(l)", "ind on l; [auto | assume IH; cases p; auto]"),
        ("list_foldr_append", "all f z l1 l2. foldr(f, z, l1 ++ l2) = foldr(f, foldr(f, z, l2), l1)", "ind on l1; [refl | assume IH; simp; use IH]"),
        ("list_all_forall", "all p l. (all x. mem(x, l) -> p(x)) -> list_all(p, l)", "ind on l; [auto | assume IH; cases; auto]"),
    ]

    trees = [
        ("tree_height_nonneg", "all t. height(t) >= 0", "ind on t; auto"),
        ("tree_size_nonneg", "all t. size(t) >= 1", "ind on t; auto"),
        ("tree_leaves_ge_1", "all t. leaves(t) >= 1", "ind on t; auto"),
        ("tree_mirror_involutive", "all t. mirror(mirror(t)) = t", "ind on t; [refl | assume IH1 IH2; simp; use IH1; use IH2]"),
        ("tree_size_height", "all t. size(t) <= 2^(height(t)+1) - 1", "ind on t; [auto | assume IH1 IH2; simp; use IH1; use IH2]"),
        ("bst_inorder_sorted", "all t. is_bst(t) -> sorted(inorder(t))", "ind on t; [auto | assume IH; split; auto]"),
        ("tree_flatten_append", "all t1 t2. flatten(Node(t1, x, t2)) = flatten(t1) ++ [x] ++ flatten(t2)", "intro; refl"),
        ("tree_count_sum", "all x t. count(x, flatten(t)) = count_tree(x, t)", "ind on t; auto"),
    ]

    classical_logic = [
        ("tnd", "all A. A \\/ ~A", "use classical; auto"),
        ("dne", "all A. ~~A -> A", "assume h; classical; auto"),
        ("peirce_law", "all A B. ((A -> B) -> A) -> A", "assume h; classical; auto"),
        ("contrapos_classical", "all A B. (~B -> ~A) -> (A -> B)", "assume h; classical; auto"),
        ("or_impl", "all A B. (A \\/ B) -> (~A -> B)", "assume h nA; elim h; [assume a; absurd | assume b; exact b]"),
        ("impl_or", "all A B. (A -> B) -> (~A \\/ B)", "assume h; classical; auto"),
        ("and_not_or", "all A B. ~A /\\ ~B -> ~(A \\/ B)", "assume h; elim h; assume nA nB; intro; elim; auto"),
        ("demorgan_classical_1", "all A B. ~(A /\\ B) -> (~A \\/ ~B)", "assume h; classical; auto"),
        ("demorgan_classical_2", "all A B. ~(A \\/ B) <-> (~A /\\ ~B)", "split; intros; split; intros; auto"),
        ("classical_exists", "all P. ~(all x. ~P(x)) -> ex x. P(x)", "assume h; classical; auto"),
    ]

    sequent_calculus = [
        ("cut_elim", "all A B C. (Gamma |- A) -> (A, Gamma |- B) -> (Gamma |- B)", "intros; cut_admissible; auto"),
        ("structural_weaken", "all A B. (Gamma |- B) -> (A, Gamma |- B)", "intros; weakening; auto"),
        ("structural_contract", "all A B. (A, A, Gamma |- B) -> (A, Gamma |- B)", "intros; contraction; auto"),
        ("structural_exchange", "all A B C. (A, B, Gamma |- C) -> (B, A, Gamma |- C)", "intros; exchange; auto"),
        ("identity_axiom", "all A. (A |- A)", "intro; axiom"),
        ("and_right", "all A B. (Gamma |- A) -> (Gamma |- B) -> (Gamma |- A /\\ B)", "intros; andR; auto"),
        ("and_left_1", "all A B C. (A, Gamma |- C) -> (A /\\ B, Gamma |- C)", "intros; andL1; auto"),
        ("impl_right", "all A B. (A, Gamma |- B) -> (Gamma |- A -> B)", "intros; implR; auto"),
        ("impl_left", "all A B C. (Gamma |- A) -> (B, Gamma |- C) -> (A -> B, Gamma |- C)", "intros; implL; auto"),
    ]

    induction_advanced = [
        ("strong_ind", "all P. (all n. (all m. m < n -> P(m)) -> P(n)) -> all n. P(n)", "assume h; strong_ind; auto"),
        ("course_of_values", "all P. P(0) -> (all n. P(n) -> P(n+1)) -> all n. P(n)", "assume p0 step; nat_rec; auto"),
        ("well_founded_acc", "all R. well_founded(R) -> all P. (all x. (all y. R(y,x) -> P(y)) -> P(x)) -> all x. P(x)", "assume wf ih; wf_rec; auto"),
        ("mutual_ind_evenodd", "(all n. even(n) -> P(n)) /\\ (all n. odd(n) -> Q(n))", "mutual_ind; auto"),
        ("struct_ind_list", "all P. P(nil) -> (all x xs. P(xs) -> P(cons x xs)) -> all l. P(l)", "assume p_nil p_cons; list_rec; auto"),
        ("struct_ind_tree", "all P. P(leaf) -> (all t1 x t2. P(t1) -> P(t2) -> P(Node t1 x t2)) -> all t. P(t)", "assume p_leaf p_node; tree_rec; auto"),
        ("transfinite_ind", "all P. (all beta. beta < alpha -> P(beta)) -> P(alpha)", "assume ih; transfinite; auto"),
    ]

    higher_order = [
        ("higher_order_app", "all f x. (lambda y. f y) x = f x", "beta_reduce; refl"),
        ("fun_ext_ho", "all f g. (all x. f x = g x) -> f = g", "assume h; fun_ext; auto"),
        ("curry_uncurry", "all f x y. curry (uncurry f) x y = f x y", "intros; beta_reduce; refl"),
        ("uncurry_curry", "all f p. uncurry (curry f) p = f p", "intro; cases p; beta_reduce; refl"),
        ("compose_assoc", "all f g h. compose (compose f g) h = compose f (compose g h)", "fun_ext; beta_reduce; refl"),
        ("id_left", "all f. compose id f = f", "fun_ext; beta_reduce; refl"),
        ("id_right", "all f. compose f id = f", "fun_ext; beta_reduce; refl"),
        ("ho_induction_schema", "all P. (all x. x = 0 \\/ (ex y. x = y+1 /\\ P(y))) -> P(0) -> all x. P(x)", "assume h p0; induct; auto"),
    ]

    program_verification = [
        ("factorial_correct", "all n. factorial(n) >= 1", "ind on n; [simp; auto | assume IH; simp; use IH]"),
        ("fibonacci_monotone", "all m n. m <= n -> fib(m) <= fib(n)", "assume h; ind on n; auto"),
        ("sum_range_formula", "all n. sum(0..n, lambda i. i) = n * (n+1) / 2", "ind on n; auto"),
        ("sort_preserves_elements", "all l. mset(sort l) = mset(l)", "ind on l; auto"),
        ("reverse_length", "all l. length(reverse l) = length l", "ind on l; [refl | assume IH; simp; use length_append; use IH]"),
        ("gcd_correct", "all a b. b > 0 -> divides(gcd(a,b), a) /\\ divides(gcd(a,b), b)", "strong_ind on b; cases; auto"),
        ("is_sorted_cons", "all x xs. is_sorted(cons x xs) -> is_sorted xs", "intros; cases; auto"),
        ("search_correct", "all x l. linear_search(x, l) = true <-> mem(x, l)", "ind on l; split; auto"),
    ]

    modal_logic = [
        ("modal_k", "all A B. box(A -> B) -> box(A) -> box(B)", "intros; box_elim; auto"),
        ("modal_t", "all A. box(A) -> A", "intro; reflexive_frame; auto"),
        ("modal_4", "all A. box(A) -> box(box(A))", "intro; transitive_frame; auto"),
        ("modal_5", "all A. dia(A) -> box(dia(A))", "intro; euclidean_frame; auto"),
        ("modal_dual", "all A. dia(A) <-> ~box(~A)", "split; intros; auto"),
        ("necessitation", "all A. |- A -> |- box(A)", "intro; necessitate; auto"),
        ("distribution", "all A B. box(A /\\ B) <-> box(A) /\\ box(B)", "split; intros; split; box_elim; auto"),
    ]

    intuitionistic = [
        ("disjunction_property", "all A B. (|- A \\/ B) -> (|- A) \\/ (|- B)", "assume h; intuit; auto"),
        ("existence_property", "all P. (|- ex x. P(x)) -> ex witness. |- P(witness)", "assume h; intuit; auto"),
        ("double_neg_shift", "all A. ~~(A \\/ ~A)", "intro; assume h; apply h; right; intro; apply h; left; auto"),
        ("glivenko", "all A. (|- ~~A classically) -> (|- ~~A intuitionistically)", "assume h; glivenko; auto"),
        ("kripke_model", "all w:World, A. forces(w, A) <-> satisfies(w, A)", "intro; split; kripke; auto"),
        ("negation_translation", "all A. (~~A)_neg = ~~A_neg", "intro; neg_translation; auto"),
        ("godel_neg", "all A. valid(A) <-> valid(~~A_neg)", "intro; split; godel_negative; auto"),
    ]

    games = [
        ("game_det", "all G:Game. open(G) -> determined(G)", "assume h; gale_stewart; auto"),
        ("strategy_winning", "all G:Game, sigma:Strategy. winning(sigma, G) -> all play. consistent(play, sigma) -> G_wins(play)", "assume w; intro con; auto"),
        ("zermelo", "all G:FiniteGame. determined(G)", "intro; backward_induction; auto"),
        ("minimax", "all G:ZeroSum, v:Value. v = max(min(payoff))", "intro; minimax_theorem; auto"),
        ("nash_existence", "all G:FiniteGame. ex sigma. nash_equilibrium(sigma, G)", "intro; brouwer; auto"),
    ]

    realizers_advanced = [
        ("realizer_nat_rec", "[r : nat_rec] = lambda base step n. (fix F lambda k. if k=0 then base else step k (F (k-1))) n", "normalize; refl"),
        ("realizer_list_rec", "[r : list_rec] = lambda nil_case cons_case l. (fix F lambda xs. match xs with nil => nil_case | x::xs' => cons_case x (F xs')) l", "normalize; refl"),
        ("realizer_bounded_search", "[r : bounded_search_lemma] = lambda p bound. search_loop p 0 bound", "normalize; refl"),
        ("realizer_minimization", "[r : minimization] = lambda f. mu (lambda n. f n = 0)", "normalize; refl"),
        ("realizer_fixpoint", "[r : fix_point_thm] = lambda f. fix f", "normalize; refl"),
        ("realizer_choice", "[r : countable_choice] = lambda R. lambda n. choose (R n)", "normalize; refl"),
    ]

    bounded_arithmetic = [
        ("bit_length", "all n. n > 0 -> bit_length(n) = floor(log2(n)) + 1", "strong_ind on n; auto"),
        ("parity", "all n. parity(n) = n mod 2", "ind on n; auto"),
        ("binary_rep", "all n. binary_decode(binary_encode(n)) = n", "ind on n; auto"),
        ("pow_two_le", "all n. 2^n > n", "ind on n; auto"),
        ("pigeon_bounded", "all f:fin(n)->fin(m). n > m -> ex i j. i <> j /\\ f(i) = f(j)", "assume; pigeonhole; auto"),
        ("bounded_search", "all p:nat->bool. (ex n. n <= N /\\ p n = true) -> ex k. k <= N /\\ p k = true /\\ (all j. j < k -> p j = false)", "assume; bounded_search; auto"),
        ("pspace_pspace", "pspace = pspace", "refl"),
    ]

    finite_logic = [
        ("fin_sat_decidable", "all phi:Formula. decidable(sat(phi))", "intro; propositional_sat; auto"),
        ("resolution_sound", "all phi. res_derives(empty, phi) -> unsat(phi)", "assume h; resolution_soundness; auto"),
        ("resolution_complete", "all phi. unsat(phi) -> res_derives(empty, phi)", "assume h; resolution_completeness; auto"),
        ("dpll_terminates", "all phi. terminates(dpll(phi))", "intro; wf_induct; auto"),
        ("cnf_equivalent", "all phi. equivalent(phi, to_cnf(phi))", "intro; tseitin; auto"),
        ("horn_sat_poly", "all phi:HornFormula. poly_time_decidable(sat(phi))", "intro; unit_propagation; auto"),
    ]

    all_categories = [
        ("natural_deduction", natural_deduction),
        ("arithmetic", arithmetic_extraction),
        ("extraction", program_extraction),
        ("realizability", realizability),
        ("lists", lists_minlog),
        ("trees", trees),
        ("classical_logic", classical_logic),
        ("sequent_calculus", sequent_calculus),
        ("induction_advanced", induction_advanced),
        ("higher_order", higher_order),
        ("program_verification", program_verification),
        ("modal_logic", modal_logic),
        ("intuitionistic", intuitionistic),
        ("games", games),
        ("realizers_advanced", realizers_advanced),
        ("bounded_arithmetic", bounded_arithmetic),
        ("finite_logic", finite_logic),
    ]

    proofs = Dict{String,Any}[]
    for (category, entries) in all_categories
        for (name, goal, tactic) in entries
            tactic_names = [strip(t) for t in split(tactic, r"[;\[\]|]") if !isempty(strip(t)) && length(strip(t)) > 1]
            seen = Set{String}(); unique_t = String[]
            for t in tactic_names
                t ∉ seen && (push!(seen, t); push!(unique_t, t))
                length(unique_t) >= 20 && break
            end
            push!(proofs, Dict{String,Any}(
                "id" => 0,
                "prover" => "Minlog",
                "theorem" => name,
                "goal" => goal,
                "context" => unique_t,
                "tactic_proof" => tactic,
                "source" => "minlog_synthetic/$(category)",
            ))
        end
    end
    return proofs
end

# ---------------------------------------------------------------------------
# Twelf (CMU)
# ---------------------------------------------------------------------------
# Twelf is a logic programming language for defining and reasoning about
# deductive systems using the logical framework LF (Edinburgh LF).

"""
    generate_twelf() -> Vector{Dict{String,Any}}

Generate Twelf synthetic proofs using LF encoding style.
"""
function generate_twelf()::Vector{Dict{String,Any}}
    natural_numbers = [
        ("nat", "nat : type.", "z : nat.\ns : nat -> nat."),
        ("plus", "plus : nat -> nat -> nat -> type.", "plus-z : plus z N N.\nplus-s : plus (s M) N (s P) <- plus M N P."),
        ("plus_comm", "plus-comm : plus M N P -> plus N M P -> type.", "plus-comm-z : plus-comm plus-z D <- plus-zero-right D.\nplus-comm-s : plus-comm (plus-s D1) D2 <- plus-comm D1 D3 <- plus-succ-right D3 D2."),
        ("plus_assoc", "plus-assoc : plus A B AB -> plus AB C ABC -> plus B C BC -> plus A BC ABC -> type.", "%mode plus-assoc +D1 +D2 -D3 -D4."),
        ("times", "times : nat -> nat -> nat -> type.", "times-z : times z N z.\ntimes-s : times (s M) N P <- times M N Q <- plus N Q P."),
        ("leq", "leq : nat -> nat -> type.", "leq-z : leq z N.\nleq-s : leq (s M) (s N) <- leq M N."),
        ("leq_refl", "leq-refl : {N:nat} leq N N -> type.", "leq-refl-z : leq-refl z leq-z.\nleq-refl-s : leq-refl (s N) (leq-s D) <- leq-refl N D."),
        ("leq_trans", "leq-trans : leq A B -> leq B C -> leq A C -> type.", "%mode leq-trans +D1 +D2 -D3."),
        ("max", "max : nat -> nat -> nat -> type.", "max-zl : max z N N.\nmax-zr : max N z N.\nmax-ss : max (s M) (s N) (s P) <- max M N P."),
        ("even_odd", "even : nat -> type.\nodd : nat -> type.", "even-z : even z.\neven-s : even (s N) <- odd N.\nodd-s : odd (s N) <- even N."),
    ]

    lambda_calculus = [
        ("tp", "tp : type.", "arr : tp -> tp -> tp.\nunit : tp."),
        ("tm", "tm : type.", "app : tm -> tm -> tm.\nlam : tp -> (tm -> tm) -> tm.\nempty : tm."),
        ("of", "of : tm -> tp -> type.", "of-app : of (app E1 E2) T <- of E1 (arr T2 T) <- of E2 T2.\nof-lam : of (lam T1 E) (arr T1 T2) <- ({x:tm} of x T1 -> of (E x) T2).\nof-empty : of empty unit."),
        ("value", "value : tm -> type.", "value-lam : value (lam T E).\nvalue-empty : value empty."),
        ("step", "step : tm -> tm -> type.", "step-app1 : step (app E1 E2) (app E1' E2) <- step E1 E1'.\nstep-app2 : step (app V E2) (app V E2') <- value V <- step E2 E2'.\nstep-beta : step (app (lam T E) V) (E V) <- value V."),
        ("preservation", "preservation : of E T -> step E E' -> of E' T -> type.", "%mode preservation +Dof +Dstep -Dof'.\npreservation-app1 : preservation (of-app D1 D2) (step-app1 S) (of-app D1' D2) <- preservation D1 S D1'.\npreservation-beta : preservation (of-app (of-lam D1) D2) (step-beta V) (D1 _ D2)."),
        ("progress", "progress : of E T -> (value E + step E E') -> type.", "%mode progress +Dof -Dresult."),
        ("subst", "subst : (tm -> tm) -> tm -> tm -> type.", "subst-var : subst ([x] x) V V.\nsubst-const : subst ([x] C) V C.\nsubst-app : subst ([x] app (E1 x) (E2 x)) V (app E1' E2') <- subst E1 V E1' <- subst E2 V E2'.\nsubst-lam : subst ([x] lam T ([y] E x y)) V (lam T E') <- ({y:tm} subst ([x] E x y) V (E' y))."),
    ]

    lists = [
        ("list", "list : type.", "nil : list.\ncons : nat -> list -> list."),
        ("append", "append : list -> list -> list -> type.", "append-nil : append nil L L.\nappend-cons : append (cons H T) L (cons H R) <- append T L R."),
        ("append_assoc", "append-assoc : append L1 L2 L12 -> append L12 L3 L123 -> append L2 L3 L23 -> append L1 L23 L123 -> type.", "%mode append-assoc +D1 +D2 -D3 -D4."),
        ("reverse", "reverse : list -> list -> type.", "reverse-nil : reverse nil nil.\nreverse-cons : reverse (cons H T) R <- reverse T T' <- append T' (cons H nil) R."),
        ("length", "length : list -> nat -> type.", "length-nil : length nil z.\nlength-cons : length (cons H T) (s N) <- length T N."),
        ("member", "member : nat -> list -> type.", "member-head : member X (cons X L).\nmember-tail : member X (cons Y L) <- member X L."),
        ("sorted", "sorted : list -> type.", "sorted-nil : sorted nil.\nsorted-one : sorted (cons X nil).\nsorted-cons : sorted (cons X (cons Y L)) <- leq X Y <- sorted (cons Y L)."),
        ("insert_sorted", "insert : nat -> list -> list -> type.", "insert-nil : insert X nil (cons X nil).\ninsert-leq : insert X (cons Y L) (cons X (cons Y L)) <- leq X Y.\ninsert-gt : insert X (cons Y L) (cons Y L') <- insert X L L'."),
    ]

    logic_framework = [
        ("prop", "o : type.", "imp : o -> o -> o.\nand : o -> o -> o.\nor : o -> o -> o.\nnot : o -> o.\nforall : (i -> o) -> o.\nexists : (i -> o) -> o."),
        ("pf", "pf : o -> type.", "imp-i : ({x:pf A} pf B) -> pf (imp A B).\nimp-e : pf (imp A B) -> pf A -> pf B.\nand-i : pf A -> pf B -> pf (and A B).\nand-e1 : pf (and A B) -> pf A.\nand-e2 : pf (and A B) -> pf B.\nor-i1 : pf A -> pf (or A B).\nor-i2 : pf B -> pf (or A B).\nor-e : pf (or A B) -> ({x:pf A} pf C) -> ({x:pf B} pf C) -> pf C.\nnot-i : ({x:pf A} pf false) -> pf (not A).\nnot-e : pf (not A) -> pf A -> pf false.\nforall-i : ({x:i} pf (A x)) -> pf (forall A).\nforall-e : pf (forall A) -> {T:i} pf (A T).\nexists-i : {T:i} pf (A T) -> pf (exists A).\nexists-e : pf (exists A) -> ({x:i} {y:pf (A x)} pf C) -> pf C."),
        ("and_comm_pf", "and-comm : pf (imp (and A B) (and B A)).", "and-comm = imp-i ([h:pf (and A B)] and-i (and-e2 h) (and-e1 h))."),
        ("or_comm_pf", "or-comm : pf (imp (or A B) (or B A)).", "or-comm = imp-i ([h:pf (or A B)] or-e h ([a] or-i2 a) ([b] or-i1 b))."),
        ("modus_ponens_pf", "mp : pf A -> pf (imp A B) -> pf B.", "mp = [a:pf A] [f:pf (imp A B)] imp-e f a."),
        ("double_neg_intro_pf", "dn-intro : pf (imp A (not (not A))).", "dn-intro = imp-i ([a:pf A] not-i ([h:pf (not A)] not-e h a))."),
        ("contra_pf", "contra : pf (imp (imp A B) (imp (not B) (not A))).", "contra = imp-i ([f:pf (imp A B)] imp-i ([nb:pf (not B)] not-i ([a:pf A] not-e nb (imp-e f a))))."),
    ]

    binary_trees = [
        ("tree", "tree : type.", "empty : tree.\nnode : nat -> tree -> tree -> tree."),
        ("insert_bst", "insert : nat -> tree -> tree -> type.", "insert-empty : insert X empty (node X empty empty).\ninsert-lt : insert X (node Y L R) (node Y L' R) <- leq X Y <- insert X L L'.\ninsert-gt : insert X (node Y L R) (node Y L R') <- leq Y X <- insert X R R'."),
        ("tree_size", "tree-size : tree -> nat -> type.", "tree-size-empty : tree-size empty z.\ntree-size-node : tree-size (node X L R) (s N) <- tree-size L NL <- tree-size R NR <- plus NL NR N."),
        ("tree_height", "tree-height : tree -> nat -> type.", "tree-height-empty : tree-height empty z.\ntree-height-node : tree-height (node X L R) (s H) <- tree-height L HL <- tree-height R HR <- max HL HR H."),
        ("tree_member", "tree-member : nat -> tree -> type.", "tree-member-node : tree-member X (node X L R).\ntree-member-left : tree-member X (node Y L R) <- tree-member X L.\ntree-member-right : tree-member X (node Y L R) <- tree-member X R."),
        ("tree_mirror", "mirror : tree -> tree -> type.", "mirror-empty : mirror empty empty.\nmirror-node : mirror (node X L R) (node X R' L') <- mirror L L' <- mirror R R'."),
        ("mirror_involutive", "mirror-involutive : mirror T T' -> mirror T' T -> type.", "%mode mirror-involutive +D1 -D2."),
        ("inorder_flatten", "inorder : tree -> list -> type.", "inorder-empty : inorder empty nil.\ninorder-node : inorder (node X L R) M <- inorder L ML <- inorder R MR <- append ML (cons X MR) M."),
    ]

    substitution = [
        ("substitution", "subst' : (tm -> tm) -> tm -> tm -> type.", "subst'-id : subst' ([x] x) V V.\nsubst'-const : subst' ([x] C) V C."),
        ("capture_avoid", "fresh : tm -> (tm -> tm) -> type.", "fresh-const : fresh V ([x] C).\nfresh-app : fresh V ([x] app (E1 x) (E2 x)) <- fresh V E1 <- fresh V E2."),
        ("alpha_eq", "alpha-eq : tm -> tm -> type.", "alpha-eq-refl : alpha-eq E E.\nalpha-eq-lam : alpha-eq (lam T ([x] E x)) (lam T ([y] E y)) <- ({x} alpha-eq (E x) (E x))."),
        ("beta_red", "beta-red : tm -> tm -> type.", "beta-red-step : beta-red (app (lam T E) V) (E V) <- value V."),
        ("eta_red", "eta-red : tm -> tm -> type.", "eta-red-step : eta-red (lam T ([x] app E x)) E."),
        ("subst_lemma", "subst-lemma : subst' E1 V1 E1' -> subst' E2 V2 E2' -> subst' ([x] E1 x) V1 E1'' -> type.", "%mode subst-lemma +D1 +D2 +D3."),
    ]

    session_types = [
        ("channel", "chan : type.", "new-chan : chan."),
        ("msg_type", "msg : type.", "unit-msg : msg.\nsum-msg : msg -> msg -> msg."),
        ("protocol", "proto : type.", "send-proto : msg -> proto -> proto.\nrecv-proto : msg -> proto -> proto.\nend-proto : proto."),
        ("duality", "dual : proto -> proto -> type.", "dual-end : dual end-proto end-proto.\ndual-send : dual (send-proto M P) (recv-proto M Q) <- dual P Q.\ndual-recv : dual (recv-proto M P) (send-proto M Q) <- dual P Q."),
        ("session_safe", "session-safe : chan -> proto -> type.", "%mode session-safe +C +P."),
        ("linear_use", "linear : chan -> type.", "linear-new : linear C <- new-chan."),
    ]

    linear_lf = [
        ("linear_type", "ltp : type.", "lolli : ltp -> ltp -> ltp.\ntensor : ltp -> ltp -> ltp.\nwith-type : ltp -> ltp -> ltp.\none-type : ltp."),
        ("linear_tm", "ltm : type.", "lapp : ltm -> ltm -> ltm.\nllam : ltp -> (ltm -> ltm) -> ltm.\npair-ltm : ltm -> ltm -> ltm.\nunit-ltm : ltm."),
        ("linear_of", "lof : ltm -> ltp -> type.", "lof-lam : lof (llam T1 E) (lolli T1 T2) <- ({x:ltm} lof x T1 -> lof (E x) T2).\nlof-pair : lof (pair-ltm E1 E2) (tensor T1 T2) <- lof E1 T1 <- lof E2 T2.\nlof-unit : lof unit-ltm one-type."),
        ("linear_safety", "linear-safety : lof E T -> step E E' -> lof E' T -> type.", "%mode linear-safety +D1 +D2 -D3."),
        ("linear_single", "linear-single : ltm -> type.", "linear-single-var : linear-single (var X).\nlinear-single-app : linear-single (lapp E1 E2) <- linear-single E1 <- linear-single E2."),
    ]

    metatheory = [
        ("weakening", "weakening : of E T -> of E T -> type.", "%mode weakening +Dof -Dof'."),
        ("type_unique", "type-unique : of E T1 -> of E T2 -> eq T1 T2 -> type.", "%mode type-unique +D1 +D2 -D3."),
        ("canonical_forms", "canonical : value V -> of V T -> type.", "%mode canonical +Dv +Dof."),
        ("progress_lemma", "progress-lemma : of E T -> (value E + step E E') -> type.", "%mode progress-lemma +Dof -Dresult."),
        ("preservation_lemma", "preservation-lemma : of E T -> step E E' -> of E' T -> type.", "%mode preservation-lemma +Dof +Dstep -Dof'."),
        ("normalization", "strong-norm : of E T -> type.", "%mode strong-norm +Dof."),
        ("confluence", "confluence : reduces E E1 -> reduces E E2 -> (reduces E1 E' /\\ reduces E2 E') -> type.", "%mode confluence +D1 +D2 -D3."),
    ]

    polymorphism = [
        ("forall_type", "forall-tp : (tp -> tp) -> tp.", "forall-intro : of E (forall-tp A) <- ({X:tp} of E (A X)).\nforall-elim : of (tapp E T) (A T) <- of E (forall-tp A)."),
        ("exists_type", "exists-tp : (tp -> tp) -> tp.", "pack : of (pack T E) (exists-tp A) <- of E (A T).\nunpack : of (open E1 [X] [x] E2) C <- of E1 (exists-tp A) <- ({X:tp} {x:tm} of x (A X) -> of (E2 X x) C)."),
        ("type_abstraction", "tabs : tp -> (tp -> tm) -> tm.", "of-tabs : of (tabs K E) (forall-tp A) <- ({X:tp} of (E X) (A X))."),
        ("param_poly", "parametricity : of E (forall-tp A) -> type.", "%mode parametricity +D."),
        ("subtype", "sub : tp -> tp -> type.", "sub-refl : sub T T.\nsub-trans : sub T1 T3 <- sub T1 T2 <- sub T2 T3.\nsub-arrow : sub (arr S1 T1) (arr S2 T2) <- sub S2 S1 <- sub T1 T2."),
    ]

    modules = [
        ("module_signature", "module-sig : type.", "mk-sig : list -> module-sig."),
        ("module_impl", "module-impl : module-sig -> type.", "mk-impl : list -> module-impl Sig."),
        ("functor", "functor : module-sig -> module-sig -> type.", "apply-functor : functor S1 S2 -> module-impl S1 -> module-impl S2 -> type."),
        ("abstract_type", "abs-tp : type.", "pack-abs : tp -> (tp -> tp) -> abs-tp.\nopen-abs : abs-tp -> (tp -> tp -> tp) -> tp -> type."),
        ("structure_eq", "struct-eq : module-impl S -> module-impl S -> type.", "%mode struct-eq +M1 +M2."),
        ("include_module", "include : module-impl S1 -> module-impl S2 -> module-impl S3 -> type.", "%mode include +M1 +M2 -M3."),
    ]

    records_twelf = [
        ("record", "record : type.", "empty-rec : record.\ncons-rec : label -> tm -> record -> record."),
        ("label", "label : type.", "lab-a : label.\nlab-b : label.\nlab-c : label."),
        ("rec_lookup", "lookup : label -> record -> tm -> type.", "lookup-head : lookup L (cons-rec L V R) V.\nlookup-tail : lookup L (cons-rec L' V R) V' <- lookup L R V'."),
        ("rec_update", "update : label -> tm -> record -> record -> type.", "update-head : update L V (cons-rec L V' R) (cons-rec L V R).\nupdate-tail : update L V (cons-rec L' V' R) (cons-rec L' V' R') <- update L V R R'."),
        ("rec_concat", "rec-concat : record -> record -> record -> type.", "rec-concat-nil : rec-concat empty-rec R R.\nrec-concat-cons : rec-concat (cons-rec L V R1) R2 (cons-rec L V R3) <- rec-concat R1 R2 R3."),
    ]

    traces = [
        ("trace", "trace : type.", "empty-trace : trace.\nstep-trace : tm -> tm -> trace -> trace."),
        ("trace_step", "trace-step : trace -> tm -> tm -> type.", "%mode trace-step +T +E -E'."),
        ("trace_append", "trace-append : trace -> trace -> trace -> type.", "trace-app-nil : trace-append empty-trace T T.\ntrace-app-cons : trace-append (step-trace E1 E2 T1) T2 (step-trace E1 E2 T3) <- trace-append T1 T2 T3."),
        ("evaluates", "evaluates : tm -> tm -> type.", "eval-refl : evaluates E E.\neval-step : evaluates E E'' <- step E E' <- evaluates E' E''."),
        ("multistep", "multistep : tm -> tm -> trace -> type.", "multistep-refl : multistep E E empty-trace.\nmultistep-step : multistep E E'' (step-trace E E' T) <- step E E' <- multistep E' E'' T."),
    ]

    bigstep = [
        ("bigstep", "bigstep : tm -> tm -> type.", "bigstep-val : bigstep V V <- value V.\nbigstep-app : bigstep (app E1 E2) V <- bigstep E1 (lam T E) <- bigstep E2 V2 <- bigstep (E V2) V."),
        ("bigstep_det", "bigstep-det : bigstep E V1 -> bigstep E V2 -> eq V1 V2 -> type.", "%mode bigstep-det +D1 +D2 -D3."),
        ("bigstep_value", "bigstep-value : bigstep E V -> value V -> type.", "%mode bigstep-value +D -Dv."),
        ("bigstep_of", "bigstep-of : bigstep E V -> of E T -> of V T -> type.", "%mode bigstep-of +D1 +D2 -D3."),
        ("bigstep_smallstep", "bigstep-smallstep : bigstep E V -> multistep E V _ -> type.", "%mode bigstep-smallstep +D1 -D2."),
    ]

    hoas = [
        ("hoas_abs", "habs : (tm -> tm) -> tm.", "habs-intro : of (habs E) (arr T1 T2) <- ({x:tm} of x T1 -> of (E x) T2)."),
        ("hoas_app", "happ : tm -> tm -> tm.", "happ-intro : of (happ E1 E2) T2 <- of E1 (arr T1 T2) <- of E2 T1."),
        ("hoas_beta", "hstep : tm -> tm -> type.", "hstep-beta : hstep (happ (habs E) V) (E V) <- value V."),
        ("hoas_subst", "hsubst : (tm -> tm) -> tm -> tm -> type.", "%mode hsubst +E +V -E'."),
        ("parametric_hoas", "phabs : (tm -> tm) -> tm.", "%block phabs-block : block {x:tm}."),
    ]

    parsing = [
        ("token", "token : type.", "tok-ident : string -> token.\ntok-num : nat -> token.\ntok-lparen : token.\ntok-rparen : token.\ntok-plus : token.\ntok-times : token."),
        ("parse_expr", "parse : list -> tm -> list -> type.", "%mode parse +Input -Result -Rest."),
        ("lex", "lex : string -> list -> type.", "%mode lex +Input -Tokens."),
        ("ast", "ast : type.", "ast-num : nat -> ast.\nast-var : string -> ast.\nast-bin : op -> ast -> ast -> ast."),
        ("op", "op : type.", "op-add : op.\nop-sub : op.\nop-mul : op.\nop-div : op."),
        ("grammar", "grammar-rule : type.", "gr-term : symbol -> grammar-rule.\ngr-alt : grammar-rule -> grammar-rule -> grammar-rule.\ngr-seq : grammar-rule -> grammar-rule -> grammar-rule."),
    ]

    automata = [
        ("dfa_state", "state : type.", "init-state : state.\ntrans-state : state -> char -> state."),
        ("dfa_accept", "accepts : dfa -> string -> type.", "%mode accepts +D +S."),
        ("nfa_run", "nfa-run : nfa -> list -> state -> type.", "%mode nfa-run +N +S -Q."),
        ("regex", "regex : type.", "re-char : char -> regex.\nre-concat : regex -> regex -> regex.\nre-alt : regex -> regex -> regex.\nre-star : regex -> regex.\nre-epsilon : regex."),
        ("regex_match", "re-match : regex -> string -> type.", "%mode re-match +R +S."),
        ("pda", "pda-state : type.", "pda-init : pda-state.\npda-push : pda-state -> char -> stack -> pda-state."),
    ]

    effects = [
        ("io_monad", "io : type -> type.", "io-return : A -> io A.\nio-bind : io A -> (A -> io B) -> io B."),
        ("state_monad", "state-m : type -> type.", "state-return : A -> state-m A.\nstate-bind : state-m A -> (A -> state-m B) -> state-m B.\nstate-get : state-m state.\nstate-put : state -> state-m unit."),
        ("exception", "exc : type -> type.", "exc-pure : A -> exc A.\nexc-raise : string -> exc A.\nexc-catch : exc A -> (string -> exc A) -> exc A."),
        ("continuation", "cont : type -> type -> type.", "cont-pure : A -> cont A R.\ncont-callcc : ((A -> cont B R) -> cont A R) -> cont A R."),
        ("free_monad", "free : type -> type.", "free-pure : A -> free A.\nfree-op : op-sig -> (result -> free A) -> free A."),
    ]

    numerics_twelf = [
        ("add_zero_left", "add-zero-left : {N:nat} plus z N N -> type.", "%mode add-zero-left +N -D.\nadd-zero-left-z : add-zero-left z plus-z.\nadd-zero-left-s : add-zero-left (s N) plus-z <- add-zero-left N _."),
        ("add_zero_right", "add-zero-right : {N:nat} plus N z N -> type.", "%mode add-zero-right +N -D.\nadd-zero-right-z : add-zero-right z plus-z.\nadd-zero-right-s : add-zero-right (s N) (plus-s D) <- add-zero-right N D."),
        ("times_zero_right", "times-zero-right : {N:nat} times N z z -> type.", "%mode times-zero-right +N -D."),
        ("div_algorithm", "div-mod : nat -> nat -> nat -> nat -> type.", "div-mod-base : div-mod M N z M <- lt M N.\ndiv-mod-rec : div-mod M N (s Q) R <- leq N M <- sub M N M' <- div-mod M' N Q R."),
        ("gcd", "gcd : nat -> nat -> nat -> type.", "gcd-zero : gcd M z M.\ngcd-rec : gcd M N G <- modulo M N R <- gcd N R G."),
    ]

    all_categories = [
        ("natural_numbers", natural_numbers),
        ("lambda_calculus", lambda_calculus),
        ("lists", lists),
        ("logic_framework", logic_framework),
        ("binary_trees", binary_trees),
        ("substitution", substitution),
        ("session_types", session_types),
        ("linear_lf", linear_lf),
        ("metatheory", metatheory),
        ("polymorphism", polymorphism),
        ("modules", modules),
        ("records", records_twelf),
        ("traces", traces),
        ("bigstep", bigstep),
        ("hoas", hoas),
        ("parsing", parsing),
        ("automata", automata),
        ("effects", effects),
        ("numerics", numerics_twelf),
    ]

    proofs = Dict{String,Any}[]
    for (category, entries) in all_categories
        for (name, sig, impl) in entries
            context = [m.captures[1] for m in eachmatch(r"\b(\w+-\w+|\w+)\s*:", sig)]
            push!(proofs, Dict{String,Any}(
                "id" => 0,
                "prover" => "Twelf",
                "theorem" => name,
                "goal" => sig,
                "context" => context[1:min(10, length(context))],
                "tactic_proof" => impl,
                "source" => "twelf_synthetic/$(category)",
            ))
        end
    end
    return proofs
end

# ---------------------------------------------------------------------------
# Imandra (Aesthetic Integration)
# ---------------------------------------------------------------------------
# Imandra is an automated reasoning system for OCaml programs, combining
# automated theorem proving with counterexample generation.

"""
    generate_imandra() -> Vector{Dict{String,Any}}

Generate Imandra synthetic proofs using OCaml-like syntax.
"""
function generate_imandra()::Vector{Dict{String,Any}}
    arithmetic = [
        ("add_comm", "theorem add_comm x y = x + y = y + x", "[@@auto]"),
        ("add_assoc", "theorem add_assoc x y z = (x + y) + z = x + (y + z)", "[@@auto]"),
        ("mul_comm", "theorem mul_comm x y = x * y = y * x", "[@@auto]"),
        ("mul_assoc", "theorem mul_assoc x y z = (x * y) * z = x * (y * z)", "[@@auto]"),
        ("distrib", "theorem distrib x y z = x * (y + z) = x * y + x * z", "[@@auto]"),
        ("add_zero", "theorem add_zero x = x + 0 = x", "[@@auto]"),
        ("mul_one", "theorem mul_one x = x * 1 = x", "[@@auto]"),
        ("mul_zero", "theorem mul_zero x = x * 0 = 0", "[@@auto]"),
        ("abs_nonneg", "theorem abs_nonneg x = abs x >= 0", "[@@auto]"),
        ("abs_triangle", "theorem abs_triangle x y = abs (x + y) <= abs x + abs y", "[@@auto]"),
        ("max_comm", "theorem max_comm x y = max x y = max y x", "[@@auto]"),
        ("min_comm", "theorem min_comm x y = min x y = min y x", "[@@auto]"),
        ("max_assoc", "theorem max_assoc x y z = max x (max y z) = max (max x y) z", "[@@auto]"),
        ("min_max_absorb", "theorem min_max_absorb x y = min x (max x y) = x", "[@@auto]"),
        ("div_mod_id", "theorem div_mod_id a b = b > 0 ==> a = b * (a / b) + (a mod b)", "[@@auto]"),
    ]

    lists = [
        ("append_nil", "theorem append_nil l = l @ [] = l", "[@@induct l]"),
        ("append_assoc", "theorem append_assoc l1 l2 l3 = (l1 @ l2) @ l3 = l1 @ (l2 @ l3)", "[@@induct l1]"),
        ("length_append", "theorem length_append l1 l2 = List.length (l1 @ l2) = List.length l1 + List.length l2", "[@@induct l1]"),
        ("rev_rev", "theorem rev_rev l = List.rev (List.rev l) = l", "[@@induct l] [@@auto]"),
        ("map_id", "theorem map_id l = List.map (fun x -> x) l = l", "[@@induct l]"),
        ("map_compose", "theorem map_compose f g l = List.map f (List.map g l) = List.map (fun x -> f (g x)) l", "[@@induct l]"),
        ("length_map", "theorem length_map f l = List.length (List.map f l) = List.length l", "[@@induct l]"),
        ("length_rev", "theorem length_rev l = List.length (List.rev l) = List.length l", "[@@induct l] [@@auto]"),
        ("mem_append", "theorem mem_append x l1 l2 = List.mem x (l1 @ l2) = (List.mem x l1 || List.mem x l2)", "[@@induct l1]"),
        ("filter_append", "theorem filter_append p l1 l2 = List.filter p (l1 @ l2) = List.filter p l1 @ List.filter p l2", "[@@induct l1]"),
        ("flat_map_assoc", "theorem flat_map_assoc f g l = List.concat_map g (List.concat_map f l) = List.concat_map (fun x -> List.concat_map g (f x)) l", "[@@induct l]"),
        ("nth_map", "theorem nth_map f l i = i < List.length l ==> List.nth (List.map f l) i = f (List.nth l i)", "[@@induct l] [@@auto]"),
        ("for_all_append", "theorem for_all_append p l1 l2 = List.for_all p (l1 @ l2) = (List.for_all p l1 && List.for_all p l2)", "[@@induct l1]"),
    ]

    verification = [
        ("sorted_insert", "theorem sorted_insert x l = sorted l ==> sorted (insert x l)", "[@@induct l] [@@auto]"),
        ("sorted_sort", "theorem sorted_sort l = sorted (sort l)", "[@@induct l] [@@auto]"),
        ("perm_sort", "theorem perm_sort l = is_perm l (sort l)", "[@@induct l] [@@auto]"),
        ("bsearch_correct", "theorem bsearch_correct a v = sorted a ==> (match bsearch a v with Some i -> a.(i) = v | None -> not (Array.exists (fun x -> x = v) a))", "[@@auto]"),
        ("stack_push_pop", "theorem stack_push_pop x s = pop (push x s) = (x, s)", "[@@auto]"),
        ("queue_fifo", "theorem queue_fifo x q = not (is_empty q) ==> fst (dequeue (enqueue x q)) = front q", "[@@auto]"),
        ("rbt_invariant", "theorem rbt_invariant x t = is_rbt t ==> is_rbt (rbt_insert x t)", "[@@induct t] [@@auto]"),
        ("bst_invariant", "theorem bst_invariant x t = is_bst t ==> is_bst (bst_insert x t)", "[@@induct t] [@@auto]"),
        ("heap_insert_min", "theorem heap_insert_min x h = is_heap h ==> find_min (heap_insert x h) <= x", "[@@induct h] [@@auto]"),
    ]

    finance = [
        ("margin_nonneg", "theorem margin_nonneg acct = valid_account acct ==> margin_requirement acct >= 0.0", "[@@auto]"),
        ("order_fill_balance", "theorem order_fill_balance order book = valid_order order ==> balance_after (fill order book) >= 0.0", "[@@auto]"),
        ("matching_symmetric", "theorem matching_symmetric buy sell = can_match buy sell ==> can_match sell buy", "[@@auto]"),
        ("settlement_complete", "theorem settlement_complete trades = all_valid trades ==> is_settled (settle trades)", "[@@auto]"),
        ("risk_monotone", "theorem risk_monotone p1 p2 = portfolio_subset p1 p2 ==> risk p1 <= risk p2", "[@@auto]"),
    ]

    counterexamples = [
        ("cx_list_rev_sorted", "verify (fun l -> sorted l ==> sorted (List.rev l))", "CX: l = [1; 3; 2] -- List.rev [1;3;2] = [2;3;1] which is not sorted"),
        ("cx_append_comm", "verify (fun l1 l2 -> l1 @ l2 = l2 @ l1)", "CX: l1 = [1], l2 = [2] -- [1;2] <> [2;1]"),
        ("cx_map_injective", "verify (fun f l1 l2 -> List.map f l1 = List.map f l2 ==> l1 = l2)", "CX: f = (fun _ -> 0), l1 = [1], l2 = [2]"),
        ("cx_sort_idempotent", "verify (fun l -> sort (sort l) = sort l)", "Verified: true (sort is idempotent)"),
        ("cx_filter_length", "verify (fun p l -> List.length (List.filter p l) <= List.length l)", "Verified: true"),
        ("cx_subset_reflexive", "verify (fun s -> subset s s)", "Verified: true"),
        ("cx_division_positive", "verify (fun x y -> x > 0 && y > 0 ==> x / y >= 0)", "Verified: true"),
        ("cx_int_overflow", "verify (fun (x:int) -> x + 1 > x)", "CX: x = max_int -- overflow wraps to min_int"),
        ("cx_float_assoc", "verify (fun (a:float) b c -> (a +. b) +. c = a +. (b +. c))", "CX: a=1e30, b= -1e30, c=1.0 -- floating point not associative"),
    ]

    trees_imandra = [
        ("bst_insert_preserves", "theorem bst_insert_preserves x t = is_bst t ==> is_bst (bst_insert x t)", "[@@induct t] [@@auto]"),
        ("bst_member_after_insert", "theorem bst_member_after_insert x t = bst_member x (bst_insert x t)", "[@@induct t] [@@auto]"),
        ("tree_mirror_involutive", "theorem tree_mirror_involutive t = mirror (mirror t) = t", "[@@induct t]"),
        ("tree_size_positive", "theorem tree_size_positive t = tree_size t >= 0", "[@@induct t]"),
        ("tree_flatten_length", "theorem tree_flatten_length t = List.length (flatten t) = tree_size t", "[@@induct t]"),
        ("heap_extract_min_sorted", "theorem heap_extract_min_sorted h = is_heap h ==> sorted (heapsort h)", "[@@induct h] [@@auto]"),
        ("avl_balanced", "theorem avl_balanced t = is_avl t ==> abs (height (left t) - height (right t)) <= 1", "[@@induct t] [@@auto]"),
        ("rbt_black_height", "theorem rbt_black_height t = is_rbt t ==> black_height (left t) = black_height (right t)", "[@@induct t] [@@auto]"),
    ]

    numerics = [
        ("abs_diff_symmetric", "theorem abs_diff_symmetric x y = abs (x - y) = abs (y - x)", "[@@auto]"),
        ("sqr_nonneg", "theorem sqr_nonneg x = x * x >= 0", "[@@auto]"),
        ("ge_trans", "theorem ge_trans x y z = x >= y ==> y >= z ==> x >= z", "[@@auto]"),
        ("eq_refl_trans", "theorem eq_refl_trans x y = x = y ==> y = x", "[@@auto]"),
        ("neg_neg", "theorem neg_neg x = -(-x) = x", "[@@auto]"),
        ("sub_self_zero", "theorem sub_self_zero x = x - x = 0", "[@@auto]"),
        ("mul_distrib_sub", "theorem mul_distrib_sub x y z = x * (y - z) = x*y - x*z", "[@@auto]"),
        ("pow_zero", "theorem pow_zero x = x > 0 ==> x ** 0 = 1", "[@@auto]"),
        ("pow_succ", "theorem pow_succ x n = n >= 0 ==> x ** (n+1) = x * (x ** n)", "[@@induct n] [@@auto]"),
        ("gcd_self", "theorem gcd_self n = n >= 0 ==> gcd n n = n", "[@@auto]"),
        ("gcd_zero", "theorem gcd_zero n = n >= 0 ==> gcd n 0 = n", "[@@auto]"),
        ("divides_refl", "theorem divides_refl n = n <> 0 ==> divides n n", "[@@auto]"),
    ]

    records = [
        ("record_set_get", "theorem record_set_get r v = (set_field r v).field = v", "[@@auto]"),
        ("record_get_set_idempotent", "theorem record_get_set_idempotent r = set_field r (r.field) = r", "[@@auto]"),
        ("record_set_comm", "theorem record_set_comm r v1 v2 = set_f2 (set_f1 r v1) v2 = set_f1 (set_f2 r v2) v1", "[@@auto]"),
        ("record_eq_fields", "theorem record_eq_fields r1 r2 = r1.a = r2.a ==> r1.b = r2.b ==> r1 = r2", "[@@auto]"),
        ("option_some_inj", "theorem option_some_inj x y = Some x = Some y ==> x = y", "[@@auto]"),
        ("option_none_not_some", "theorem option_none_not_some x = None <> Some x", "[@@auto]"),
        ("tuple_fst_snd", "theorem tuple_fst_snd p = (fst p, snd p) = p", "[@@auto]"),
    ]

    state_machines = [
        ("fsm_deterministic", "theorem fsm_deterministic s e = forall s1 s2. transition s e s1 ==> transition s e s2 ==> s1 = s2", "[@@auto]"),
        ("fsm_reachable_trans", "theorem fsm_reachable_trans s1 s2 s3 = reachable s1 s2 ==> reachable s2 s3 ==> reachable s1 s3", "[@@induct] [@@auto]"),
        ("fsm_initial_reachable", "theorem fsm_initial_reachable s = s = initial_state ==> reachable s s", "[@@auto]"),
        ("fsm_no_deadlock", "theorem fsm_no_deadlock s = reachable initial_state s ==> exists e s'. transition s e s'", "[@@auto]"),
        ("fsm_invariant_preserve", "theorem fsm_invariant_preserve s e s' = inv s ==> transition s e s' ==> inv s'", "[@@auto]"),
        ("safety_property", "theorem safety_property s = reachable initial_state s ==> not (is_error s)", "[@@induct] [@@auto]"),
        ("liveness_property", "theorem liveness_property s = reachable initial_state s ==> eventually goal_state s", "[@@auto]"),
    ]

    crypto = [
        ("hash_deterministic", "theorem hash_deterministic m1 m2 = m1 = m2 ==> hash m1 = hash m2", "[@@auto]"),
        ("signature_verify", "theorem signature_verify sk pk m = keypair sk pk ==> verify pk m (sign sk m) = true", "[@@auto]"),
        ("encrypt_decrypt", "theorem encrypt_decrypt k m = decrypt k (encrypt k m) = m", "[@@auto]"),
        ("merkle_root_unique", "theorem merkle_root_unique l1 l2 = merkle_root l1 = merkle_root l2 ==> l1 = l2", "[@@auto]"),
        ("xor_involutive", "theorem xor_involutive x y = xor (xor x y) y = x", "[@@auto]"),
        ("nonce_unique", "theorem nonce_unique n1 n2 = generate_nonce n1 = generate_nonce n2 ==> n1 = n2", "[@@auto]"),
    ]

    blockchain = [
        ("block_prev_chain", "theorem block_prev_chain b = valid_chain b ==> prev_hash (head b) = hash (tail b)", "[@@induct b] [@@auto]"),
        ("tx_balance_conservation", "theorem tx_balance_conservation tx = valid_tx tx ==> sum_inputs tx = sum_outputs tx + fee tx", "[@@auto]"),
        ("utxo_no_double_spend", "theorem utxo_no_double_spend tx1 tx2 utxo = valid_tx tx1 ==> valid_tx tx2 ==> disjoint (inputs tx1) (inputs tx2)", "[@@auto]"),
        ("consensus_majority", "theorem consensus_majority votes = count_yes votes > length votes / 2 ==> accepted votes", "[@@auto]"),
        ("longest_chain", "theorem longest_chain c1 c2 = valid_chain c1 ==> valid_chain c2 ==> height c1 >= height c2 ==> canonical c1", "[@@auto]"),
    ]

    algebra = [
        ("group_identity_unique", "theorem group_identity_unique e1 e2 = is_identity e1 ==> is_identity e2 ==> e1 = e2", "[@@auto]"),
        ("group_inverse_unique", "theorem group_inverse_unique a b c = op a b = identity ==> op a c = identity ==> b = c", "[@@auto]"),
        ("monoid_left_id", "theorem monoid_left_id a = op identity a = a", "[@@auto]"),
        ("monoid_right_id", "theorem monoid_right_id a = op a identity = a", "[@@auto]"),
        ("ring_distrib", "theorem ring_distrib a b c = mul a (add b c) = add (mul a b) (mul a c)", "[@@auto]"),
        ("ring_zero_mul", "theorem ring_zero_mul a = mul zero a = zero", "[@@auto]"),
        ("semilat_idempotent", "theorem semilat_idempotent a = meet a a = a", "[@@auto]"),
    ]

    concurrency = [
        ("mutex_exclusive", "theorem mutex_exclusive s = acquired s ==> not (available s)", "[@@auto]"),
        ("lock_release", "theorem lock_release s = acquire (release (acquire s)) = acquire s", "[@@auto]"),
        ("queue_ordering", "theorem queue_ordering q msgs = push q msgs ==> fifo_order (drain q)", "[@@induct msgs] [@@auto]"),
        ("actor_isolation", "theorem actor_isolation a b m = send a b m ==> state a = state a", "[@@auto]"),
        ("atomic_read_write", "theorem atomic_read_write x v = read (write x v) = v", "[@@auto]"),
        ("cas_success", "theorem cas_success x old new = read x = old ==> cas x old new = (true, write x new)", "[@@auto]"),
        ("deadlock_free", "theorem deadlock_free tree = acyclic tree ==> not (deadlocked tree)", "[@@induct tree] [@@auto]"),
    ]

    databases = [
        ("acid_atomicity", "theorem acid_atomicity tx db = commit tx db = Some db' \\/ commit tx db = None", "[@@auto]"),
        ("rollback_inverse", "theorem rollback_inverse tx db = rollback tx (apply tx db) = db", "[@@auto]"),
        ("isolation_serializable", "theorem isolation_serializable t1 t2 db = serializable [t1; t2] db = serializable [t2; t1] db", "[@@auto]"),
        ("index_consistent", "theorem index_consistent idx tbl = valid_index idx tbl ==> forall k. lookup idx k = table_lookup tbl k", "[@@auto]"),
        ("foreign_key", "theorem foreign_key p c = valid_db (p, c) ==> forall r in c. exists parent in p. fk_match r parent", "[@@auto]"),
        ("normalization_bcnf", "theorem normalization_bcnf r = bcnf r ==> third_nf r", "[@@auto]"),
    ]

    networking = [
        ("tcp_in_order", "theorem tcp_in_order conn pkts = established conn ==> tcp_deliver conn pkts = sort_by_seq pkts", "[@@induct pkts] [@@auto]"),
        ("packet_checksum", "theorem packet_checksum p = valid_packet p ==> verify_checksum p = true", "[@@auto]"),
        ("routing_loop_free", "theorem routing_loop_free graph = valid_routing graph ==> acyclic (next_hop graph)", "[@@auto]"),
        ("tls_handshake_secrecy", "theorem tls_handshake_secrecy c s = secure_handshake c s ==> secret_key_safe c s", "[@@auto]"),
        ("retry_idempotent", "theorem retry_idempotent req = idempotent req ==> retry req = send req", "[@@auto]"),
    ]

    security = [
        ("auth_token_valid", "theorem auth_token_valid t = verify_token t = Some user ==> user = decode t", "[@@auto]"),
        ("rbac_permission", "theorem rbac_permission u r p = has_role u r && role_has_perm r p ==> authorized u p", "[@@auto]"),
        ("password_hash_oneway", "theorem password_hash_oneway p1 p2 = hash_pw p1 = hash_pw p2 ==> p1 = p2 \\/ collision p1 p2", "[@@auto]"),
        ("input_sanitize", "theorem input_sanitize s = safe (sanitize s)", "[@@auto]"),
        ("session_expiry", "theorem session_expiry s t = expired s t ==> not (valid_session s t)", "[@@auto]"),
        ("audit_log_append", "theorem audit_log_append log e = append log e = log ++ [e]", "[@@auto]"),
    ]

    ml_correctness = [
        ("gradient_descent_converge", "theorem gd_converge f lr x0 = convex f ==> lr > 0 ==> lr <= 1 / lipschitz f ==> converges (gd f lr x0)", "[@@auto]"),
        ("softmax_sum_one", "theorem softmax_sum_one xs = List.length xs > 0 ==> List.fold_left (+.) 0.0 (softmax xs) = 1.0", "[@@auto]"),
        ("relu_nonneg", "theorem relu_nonneg x = relu x >= 0.0", "[@@auto]"),
        ("sigmoid_bounded", "theorem sigmoid_bounded x = 0.0 <= sigmoid x && sigmoid x <= 1.0", "[@@auto]"),
        ("loss_nonneg", "theorem loss_nonneg y y_hat = mse y y_hat >= 0.0", "[@@auto]"),
        ("backprop_chain", "theorem backprop_chain f g x = gradient (compose f g) x = gradient f (g x) *. gradient g x", "[@@auto]"),
    ]

    all_categories = [
        ("arithmetic", arithmetic),
        ("lists", lists),
        ("verification", verification),
        ("finance", finance),
        ("counterexamples", counterexamples),
        ("trees", trees_imandra),
        ("numerics", numerics),
        ("records", records),
        ("state_machines", state_machines),
        ("crypto", crypto),
        ("blockchain", blockchain),
        ("algebra", algebra),
        ("concurrency", concurrency),
        ("databases", databases),
        ("networking", networking),
        ("security", security),
        ("ml_correctness", ml_correctness),
    ]

    proofs = Dict{String,Any}[]
    for (category, entries) in all_categories
        for (name, goal, tactic) in entries
            keywords = [m.captures[1] for m in eachmatch(r"\[@@(\w+)\]", tactic)]
            if isempty(keywords)
                keywords = ["auto"]
            end
            seen = Set{String}(); unique_kw = String[]
            for kw in keywords
                kw ∉ seen && (push!(seen, kw); push!(unique_kw, kw))
                length(unique_kw) >= 20 && break
            end
            push!(proofs, Dict{String,Any}(
                "id" => 0,
                "prover" => "Imandra",
                "theorem" => name,
                "goal" => goal,
                "context" => unique_kw,
                "tactic_proof" => tactic,
                "source" => "imandra_synthetic/$(category)",
            ))
        end
    end
    return proofs
end

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

"""
    write_prover(prover_name::String, entries::Vector{Dict{String,Any}}, start_id::Int) -> Int

Write entries for a single prover, assigning IDs. Returns count.
"""
function write_prover(prover_name::String, entries::Vector{Dict{String,Any}}, start_id::Int)::Int
    output_file = joinpath(OUTPUT_DIR, "proof_states_$(lowercase(prover_name)).jsonl")
    stats_file = joinpath(OUTPUT_DIR, "stats_$(lowercase(prover_name)).json")

    current_id = start_id
    for entry in entries
        entry["id"] = current_id
        current_id += 1
    end

    open(output_file, "w") do fh
        for entry in entries
            println(fh, JSON3.write(entry))
        end
    end

    stats = Dict{String,Any}(
        "prover" => prover_name,
        "total_proofs" => length(entries),
        "all_synthetic" => true,
        "id_range" => [start_id, current_id - 1],
        "output_file" => output_file,
    )
    open(stats_file, "w") do fh
        JSON3.pretty(fh, stats)
    end

    println("  [$(prover_name)] $(length(entries)) proofs -> $(output_file)")
    return length(entries)
end


"""
    run() -> Int

Generate synthetic proofs for all small-community provers.
"""
function run()::Int
    mkpath(OUTPUT_DIR)

    println("[Synthetic Provers] Generating proofs for small-community provers ...")
    println("=" ^ 60)

    total = 0

    nuprl = generate_nuprl()
    total += write_prover("Nuprl", nuprl, 88000)

    minlog = generate_minlog()
    total += write_prover("Minlog", minlog, 88500)

    twelf = generate_twelf()
    total += write_prover("Twelf", twelf, 89000)

    imandra = generate_imandra()
    total += write_prover("Imandra", imandra, 89500)

    println("=" ^ 60)
    println("[Synthetic Provers] TOTAL: $(total) proofs across 4 provers")
    return total
end

if abspath(PROGRAM_FILE) == abspath(@__FILE__)
    run()
end
