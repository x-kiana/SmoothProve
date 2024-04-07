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
is_prop(all(X, A)) :- is_var(X), is_prop(A).
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
is_prop_deriv(hypP(X)) :- is_var(X).
% TODO: Should = be here?
is_prop_deriv(seteqP(A, B)) :- is_set_deriv(A), is_set_deriv(B).
is_prop_deriv(subsetP(A, B)) :- is_set_deriv(A), is_set_deriv(B).
is_prop_deriv(topP).
is_prop_deriv(botP).
is_prop_deriv(andP(Prop1, Prop2)) :- is_prop_deriv(Prop1), is_prop_deriv(Prop2).
is_prop_deriv(orP(Prop1, Prop2)) :- is_prop_deriv(Prop1), is_prop_deriv(Prop2).
is_prop_deriv(impP(Prop1, Prop2)) :- is_prop_deriv(Prop1), is_prop_deriv(Prop2).
is_prop_deriv(forallP(Prop)) :- is_prop_deriv(Prop).
is_prop_deriv(existsP(Prop)) :- is_prop_deriv(Prop).

% is_verif_deriv(D) when D is syntactically a derivation tree of a verif judgement
is_verif_deriv(atomic(Use, Prop)) :- is_use_deriv(Use), is_prop_deriv(Prop).
is_verif_deriv(topI).
is_verif_deriv(botE(Use, Prop)) :- is_use_deriv(Use), is_prop_deriv(Prop).
is_verif_deriv(andI(VOne, VTwo)) :- is_verif_deriv(VOne), is_verif_deriv(VTwo).
is_verif_deriv(orI1(Verif, Prop)) :- is_verif_deriv(Verif), is_prop_deriv(Prop).
is_verif_deriv(orI2(Prop, Verif)) :- is_prop_deriv(Prop), is_verif_deriv(Verif).
is_verif_deriv(orE(Use, Verif1, Verif2)) :- is_use_deriv(Use), is_verif_deriv(Verif1), is_verif_deriv(Verif2).
is_verif_deriv(impI(Prop, Verif)) :- is_prop_deriv(Prop), is_verif_deriv(Verif).
is_verif_deriv(forallI(Verif)) :- is_verif_deriv(Verif).
is_verif_deriv(existsI(Prop, Set, Verif)) :- is_prop_deriv(Prop), is_set_deriv(Set), is_verif_deriv(Verif).
is_verif_deriv(existsE(Use, Verif)) :- is_use_deriv(Use), is_verif_deriv(Verif).


% is_set_deriv(D) when D is syntactically a derivation tree of a set judgement
is_set_deriv(hypS(X)) :- is_set(X).
is_set_deriv(ddS(Verif)) :- is_verif_deriv(Verif).

% check_set(Env, Deriv, Set) holds when Deriv proves that Set is a set
check_set(Env, hypS(S), S) :- member(set(S), Env).
check_set(Env, ddS(Verif), def(X, S)) :- check_verif(Env, Verif, S).

% check_prop(Env, Deriv, Prop) holds when Deriv proves that Prop is a proposition

% TODO: Double check this with Chester
check_prop(Env, hypP(Prop), Prop) :- 
  member(prop(Prop), Env).
check_prop(Env, seteqP(AP, BP), (A = B)) :-
  check_set(Env, AP, A),
  check_set(Env, BP, B).
check_prop(Env, subsetP(AP, BP), in(A, B)) :- 
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
check_prop(Env, impP(AP, BP), (A -> B)) :-
  check_prop(Env, AP, A), 
  check_prop([use(_,A) | Env], BP, B).
check_prop(Env, forallP(AP), all(X, A)) :-
  check_prop([set(X) | Env], AP, A).
check_prop(Env, existsP(AP), exists(X, A)) :-
  check_prop([set(X) | Env], AP, A).     
  



% check_use(Env, Deriv, Prop) holds when Deriv proves Prop use

check_use(Env, hypU(PropP), use(L, Prop)) :-
  member(use(L,Prop), Env),
  check_prop(Env, PropP, Prop).
% is_use_deriv(andE1(Use))
% is_use_deriv(andE2(Use)) 
% is_use_deriv(impE(Use, Verif)) 
% is_use_deriv(forallE(Use, Set)) 
% is_use_deriv(refl(Set))
% is_use_deriv(dd(Verif)) 

% check_verif(Env, Deriv, Prop) holds when Deriv proves Prop verif

check_verif(_, topI, top).
check_verif(Env, botE(UseD, PropD), Prop) :-
  check_use(Env, UseD, bot),
  check_prop(Env, PropD, Prop).
check_verif(Env, andI(AD, BD), and(A, B)) :-
  check_verif(Env, AD, A),
  check_verif(Env, BD, B).
check_verif(Env, orI1(AD, BD), or(A, B)) :-
  check_verif(Env, AD, A),
  check_prop(Env, BD, B).
check_verif(Env, orI2(AD, BD), or(A, B)) :-
  check_prop(Env, AD, A),
  check_verif(Env, BD, B).
check_verif(Env, orE(UseP, Verif1P, Verif2P), Prop) :-
  check_use(Env, UseP, or(A, B)),
  check_verif([use(_, A)|Env], Verif1P, Prop),
  check_verif([use(_, B)|Env], Verif2P, Prop).
check_verif(Env, impI(AD, BD), (A -> B)) :-
  check_prop(Env, AD, A),
  check_verif([use(_, A)|Env], BD, B).
check_verif(Env, forallI(AD), all(X, A)) :-
  check_verif([set(S)|Env], AD, A).
check_verif(Env, existsI(PropD, SetD, VerifD), exists(_, A)) :-
  check_prop([set(_)|Env], PropD, A),
  check_set(Env, SetD, _),
  check_verif(Env, VerifD, A).
check_verif(Env, existsE(UseD, VerifD), Prop) :-
  check_use(Env, UseD, exists(X, A)),
  check_verif([set(S2), use(L, A) | Env], VerifD, Prop).
