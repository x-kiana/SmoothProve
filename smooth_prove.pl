:- use_module(library(thread)).

is_var(X) :- freeze(X, atom(X)).

% is_atomic_prop(A) when A is syntactically an atomic proposition
is_atomic_prop(X) :- is_var(X).
is_atomic_prop(A = B) :- is_set(A), is_set(B).
is_atomic_prop(in(A, B)) :- is_set(A), is_set(B).

% is_prop(A) when A is syntactically a proposition
is_prop(A) :- is_atomic_prop(A).
is_prop(top).
is_prop(bot).
is_prop(and(A, B)) :- is_prop(A), is_prop(B).
is_prop(or(A, B)) :- is_prop(A), is_prop(B).
is_prop(A -> B) :- is_prop(A), is_prop(B).
is_prop(forall(X, A)) :- is_var(X), is_prop(A).
is_prop(exists(X, A)) :- is_var(X), is_prop(A).

% is_set(S) when S is syntactically a set
is_set(X) :- is_var(X).
is_set(def(X, S)) :- is_var(X), is_prop(S).

% is_env_elem(E) when E is syntactically an environment element
is_env_elem(use(L, P)) :- is_var(L), is_prop(P).
is_env_elem(set(S)) :- is_var(S).
is_env_elem(prop(P)) :- is_var(P).

% is_env(E) when E is syntactically an environment
is_env(E) :- maplist(is_env_elem, E).

% is_use_deriv(D) when D is syntactically a derivation tree of a use judgement
is_use_deriv(hypU(X)) :- is_prop(X).
is_use_deriv(andE1(Use)) :- is_use_deriv(Use).
is_use_deriv(andE2(Use)) :- is_use_deriv(Use).
is_use_deriv(impE(Use, Verif)) :- is_use_deriv(Use), is_verif_deriv(Verif).
is_use_deriv(forallE(Use, Set)) :- is_use_deriv(Use), is_set_deriv(Set).
is_use_deriv(refl(Set)) :- is_set_deriv(Set).
is_use_deriv(dd(Verif)) :- is_verif_deriv(Verif).

% is_prop_deriv(D) when D is syntactically a derivation tree of a prop judgement
is_prop_deriv(hypP).
is_prop_deriv(eqP(A, B)) :- is_set_deriv(A), is_set_deriv(B).
is_prop_deriv(inP(A, B)) :- is_set_deriv(A), is_set_deriv(B).
is_prop_deriv(topP).
is_prop_deriv(botP).
is_prop_deriv(andP(Prop1, Prop2)) :- is_prop_deriv(Prop1), is_prop_deriv(Prop2).
is_prop_deriv(orP(Prop1, Prop2)) :- is_prop_deriv(Prop1), is_prop_deriv(Prop2).
is_prop_deriv(impP(L, Prop1, Prop2)) :- is_var(L), is_prop_deriv(Prop1), is_prop_deriv(Prop2).
is_prop_deriv(forallP(Prop)) :- is_prop_deriv(Prop).
is_prop_deriv(existsP(Prop)) :- is_prop_deriv(Prop).

% is_verif_deriv(D) when D is syntactically a derivation tree of a verif judgement
is_verif_deriv(atomic(Use, Prop)) :- is_use_deriv(Use), is_prop_deriv(Prop).
is_verif_deriv(topI).
is_verif_deriv(botE(Use, Prop)) :- is_use_deriv(Use), is_prop_deriv(Prop).
is_verif_deriv(andI(VOne, VTwo)) :- is_verif_deriv(VOne), is_verif_deriv(VTwo).
is_verif_deriv(orI1(Verif, Prop)) :- is_verif_deriv(Verif), is_prop_deriv(Prop).
is_verif_deriv(orI2(Prop, Verif)) :- is_prop_deriv(Prop), is_verif_deriv(Verif).
is_verif_deriv(orE(L1, L2, Use, Verif1, Verif2)) :- 
  is_var(L1), is_var(L2), is_use_deriv(Use), is_verif_deriv(Verif1), is_verif_deriv(Verif2).
is_verif_deriv(impI(X, Prop, Verif)) :- 
  is_var(X), is_prop_deriv(Prop), is_verif_deriv(Verif).
is_verif_deriv(forallI(X, Verif)) :- is_var(X), is_verif_deriv(Verif).
is_verif_deriv(existsI(Prop, Set, Verif)) :- 
  is_prop_deriv(Prop), is_set_deriv(Set), is_verif_deriv(Verif).
is_verif_deriv(existsE(S2, L2, Use, Verif)) :- 
  is_var(S2), is_var(L2), is_use_deriv(Use), is_verif_deriv(Verif).


% is_set_deriv(D) when D is syntactically a derivation tree of a set judgement
is_set_deriv(hypS).
is_set_deriv(ddS(Verif)) :- is_verif_deriv(Verif).

% check_set(Env, Deriv, Set) holds when Deriv proves that Set is a set
check_set(Env, hypS, S) :- member(set(S), Env).
% TODO: Definite description things
% check_set(_, ddS(_), def(_, _)) :- false.

% check_prop(Env, Deriv, Prop) holds when Deriv proves that Prop is a proposition
check_prop(Env, hypP, Prop) :- member(prop(Prop), Env).
check_prop(Env, eqP(AP, BP), (A = B)) :-
  check_set(Env, AP, A),
  check_set(Env, BP, B).
check_prop(Env, inP(AP, BP), in(A, B)) :- 
  check_set(Env, AP, A),
  check_set(Env, BP, B).
check_prop(_, topP, top).
check_prop(_, botP, bot).
check_prop(Env, andP(AP, BP), and(A, B)) :-
  check_prop(Env, AP, A),
  check_prop(Env, BP, B).
check_prop(Env, orP(AP, BP), or(A, B)) :-
  check_prop(Env, AP, A), 
  check_prop(Env, BP, B).
check_prop(Env, impP(L, AP, BP), (A -> B)) :-
  check_prop(Env, AP, A), 
  check_prop([use(L, A) | Env], BP, B).
check_prop(Env, forallP(AP), forall(S, A)) :-
  check_prop([set(S) | Env], AP, A).
check_prop(Env, existsP(AP), exists(S, A)) :-
  check_prop([set(S) | Env], AP, A).

% check_use(Env, Deriv, Prop) holds when Deriv proves Prop use
% check_use(Env, andE1(UseD, Prop), Prop) :- member(use(XY, and(X, Y)), Env), check_use(Env, UseD, and(Prop, _)).
%check_use(Env, andE1(UseD, Prop), Prop) :-
 % member(use(_, and(Prop, _)), Env),
 % check_use(Env, UseD, and(Prop, _)).

check_use(Env, refl(SetD), (A = A)) :- check_set(Env, SetD, A).
check_use(Env, hypU(L), Prop) :- member(use(L,Prop), Env).
check_use(Env, andE1(UseD), Prop) :- check_use(Env, UseD, and(Prop, _)).
check_use(Env, andE2(UseD), Prop) :- check_use(Env, UseD, and(_, Prop)).
check_use(Env, impE(UseD, VerifD), Prop) :-
  check_use(Env, UseD, Hyp -> Prop),
  check_verif(Env, VerifD, Hyp).
check_use(Env, forallE(UseD, SetD), Prop) :-
  check_use(Env, UseD, forall(X, PropWithX)),
  check_set(Env, SetD, E),
  subst(X, E, PropWithX, Prop).
% TODO: Definite description things: need to define proposition contexts to check this one
% check_use(_, dd(_), _) :- false.
% add check_use dd

% check_verif(Env, Deriv, Prop) holds when Deriv proves Prop verif
check_verif(Env, atomic(UseD, PropD), AtomicProp) :-
  is_atomic_prop(AtomicProp),
  check_use(Env, UseD, AtomicProp),
  check_prop(Env, PropD, AtomicProp).
check_verif(_, topI, top).
check_verif(Env, andI(AD, BD), and(A, B)) :-
  check_verif(Env, AD, A),
  check_verif(Env, BD, B).
check_verif(Env, orI1(AD, BD), or(A, B)) :-
  check_verif(Env, AD, A),
  check_prop(Env, BD, B).
check_verif(Env, orI2(AD, BD), or(A, B)) :-
  check_prop(Env, AD, A),
  check_verif(Env, BD, B).
check_verif(Env, impI(L, AD, BD), (A -> B)) :-
  check_prop(Env, AD, A),
  check_verif([use(L, A)|Env], BD, B).
check_verif(Env, forallI(Y, AD), forall(X, A)) :-
  subst(X, Y, A, AWithY),
  check_verif([set(Y)|Env], AD, AWithY).
check_verif(Env, existsI(S2, E, PropD, SetD, VerifD), exists(S1, Prop)) :-
  subst(S1, S2, Prop, PropWithS2),
  check_prop([set(S2) |Env], PropD, PropWithS2),
  check_set(Env, SetD, E),
  subst(S1, E, Prop, PropWithE),
  check_verif([set(E) | Env], VerifD, PropWithE ).
check_verif(Env, orE(L1, L2, Use, Verif1D, Verif2D), Prop) :-
  check_use(Env, Use, or(A, B)),
  check_verif([use(L1, A)|Env], Verif1D, Prop),
  check_verif([use(L2, B)|Env], Verif2D, Prop).
check_verif(Env, existsE(S2, L1, UseD, VerifD), Prop) :-
  check_use(Env, UseD, exists(S1, HypWithS1)),
  subst(S1, S2, HypWithS1, HypeWithS2),
  check_verif([set(S2), use(L1, HypeWithS2) | Env], VerifD, Prop).
check_verif(Env, botE(UseD, PropD), Prop) :-
  check_use(Env, UseD, bot),
  check_prop(Env, PropD, Prop).

% Wrapper for checking any judgement and making sure everything's well-formed
check(Env, D, Prop, verif) :- is_env(Env), is_prop(Prop), check_verif(Env, D, Prop).
check(Env, D, Prop, use) :- is_env(Env), is_prop(Prop), check_use(Env, D, Prop).
check(Env, D, Prop, prop) :- is_env(Env), is_prop(Prop), check_prop(Env, D, Prop).
check(Env, D, Set, set) :- is_env(Env), is_set(Set), check_set(Env, D, Set).

% subst(X, Prop, PWithX, PWithoutX) holds when PWithoutX = PWithX[Prop/X]
subst(X, Prop, X, Prop).
subst(_, _, top, top).
subst(_, _, bot, bot).
subst(X, Prop, and(A, B), and(AwoX, BwoX)) :-
  subst(X, Prop, A, AwoX),
  subst(X, Prop, B, BwoX).
subst(X, Prop, or(A, B), or(AwoX, BwoX)) :-
  subst(X, Prop, A, AwoX),
  subst(X, Prop, B, BwoX).
subst(X, Prop, A -> B, AwoX -> BwoX) :-
  subst(X, Prop, A, AwoX),
  subst(X, Prop, B, BwoX).
subst(X, Prop, forall(Y, B), forall(Y, BwoX)) :- subst(X, Prop, B, BwoX).
subst(X, Prop, exists(Y, B), exists(Y, BwoX)) :- subst(X, Prop, B, BwoX).
subst(X, Prop, A = B, AwoX = BwoX) :-
  subst(X, Prop, A, AwoX),
  subst(X, Prop, B, BwoX).
subst(X, Prop, in(A, B), in(AwoX, BwoX)) :-
  subst(X, Prop, A, AwoX),
  subst(X, Prop, B, BwoX).

% Trying to get different search strategies to work - depth first
% midfs(true).
% midfs(member(X, L)) :- member(X, L).
% midfs((A, B)) :-
%   midfs(A),
%   midfs(B).
% midfs(Goal) :-
%   Goal \= true,
%   Goal \= (_, _),
%   clause(Goal, Body),
%   midfs(Body).
% 

% an implementation of breadth-first search - seems to be quite slow
% mibfs(P) :- mibfs([], P).
% 
% mibfs([], true).
% mibfs([Goal | Goals], true) :- mibfs(Goals, Goal).
% mibfs(Goals, member(X, L)) :- member(X, L), mibfs(Goals, true).
% mibfs(Goals, atom(A)) :- atom(A), mibfs(Goals, true).
% mibfs(Goals, (A, B)) :-
%   append(Goals, [A, B], NewGoals),
%   mibfs(NewGoals, true).
% mibfs(Goals, P) :-
%   P \= true,
%   P \= (_, _),
%   P \= atom(_),
%   P \= member(_, _),
%   clause(P, Body),
%   append(Goals, [Body], NewGoals),
%   mibfs(NewGoals, true).

% Cool example where if you give it a bit of structure it can complete the proof
% Unguided: check([prop(a), prop(b), prop(c), use(aUse, a), use(bUse, b), use(x, and(a, b) -> c)], D, c, verif).
% Guided: check([prop(a), prop(b), prop(c), use(aUse, a), use(bUse, b), use(x, and(a, b) -> c)], atomic(impE(U, andI(A, B)), P), c, verif).
% Bigger Guided: check([prop(a), prop(b), prop(c)], impI(f, _, impI(a, _, impI(b, _, atomic(impE(U, andI(A, B)), _)))), (and(a, b) -> c) -> (a -> (b -> c)), verif).

% Can do all sets are equal to themselves
% check([], D, forall(x, x = x), verif).

% Example using bottom elimination
% check([use(bUse, bot), prop(a), prop(b)], botE(X, Y), and(a, b), verif).

% Implication transitivity
% check([prop(a), prop(b), prop(c), use(ab, a -> b), use(bc, b -> c)], impI(a, _, atomic(impE(BC, atomic(impE(AB, A), _)), _)), a -> c, verif).
