% is_atomic_prop(A) when A is syntactically an atomic proposition
is_atomic_prop(X) :- freeze(X, atom(X)).
is_atomic_prop(A = B) :- is_set(A), is_set(B).
is_atomic_prop(in(A, B)) :- is_set(A), is_set(B).

% is_prop(A) when A is syntactically a proposition
is_prop(A) :- is_atomic_prop(A).

% is_set(S) when S is syntactically a set

% is_env_elem(E) when E is syntactically an environment element

% is_env(E) when E is syntactically an environment

% check_set(Env, Deriv, Set) holds when Deriv proves that Set is a set

% check_prop(Env, Deriv, Prop) holds when Deriv proves that Prop is a proposition

% check_use(Env, Deriv, Prop) holds when Deriv proves Prop use

% check_verif(Env, Deriv, Prop) holds when Deriv proves Prop verif
