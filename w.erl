% [1] Bastiaan Heeren, Jurriaan Hage, and Doaitse Swierstra. Generalizing
%     Hindley-Milner type inference algorithms. Technical Report UU-CS-2002-031,
%     Institute of Information and Computing Sciences, Utrecht University, 2002.

-module(w).

-export([ ftv/1
        , apply_subst/2
        , generalize/2
        , instantiate/1
        , type_infer/2 ]).

-type evar() :: {evar, string()}.
-type elit() :: {elit, lit()}.
-type eapp() :: {eapp, exp(), exp()}.
-type eabs() :: {eabs, string(), exp()}.
-type elet() :: {elet, string(), exp(), exp()}.

-type exp() :: evar() | elit() | eapp() | eabs() | elet().

-type lint() :: {lint, integer()}.
-type lbool() :: {lbool, boolean()}.

-type lit() :: lint() | lbool().

-type tvar() :: {tvar, string()}.
-type tint() :: {tint}.
-type tbool() :: {tbool}.
-type tfun() :: {tfun, type(), type()}.

-type type() :: tvar() | tint() | tbool() | tfun().

-type type_scheme() :: {type_scheme, list(string), type()}.

-type type_env() :: {type_env, maps:map(string(), type_scheme())}.

-type types() :: type() | type_scheme() | type_env() | list(types()).

-spec type_env_remove(type_env(), string()) -> type_env().
type_env_remove({type_env, Env}, X) ->
    {type_env, maps:remove(X, Env)}.

-spec ftv(types()) -> sets:set(string).
% -spec ftv(type()) -> sets:set(string).
ftv({tvar, N}) ->
    sets:from_list([N], {version, 2});
ftv({tint}) ->
    sets:new({version, 2});
ftv({tbool}) ->
    sets:new({version, 2});
ftv({tfun, T1, T2}) ->
    sets:union(ftv(T1), ftv(T2));
% -spec ftv(type_scheme()) -> sets:set(string).
ftv({type_scheme, Vars, Type}) ->
    sets:subtract(ftv(Type), sets:from_list(Vars));
% -spec ftv(type_env) -> sets:set(string).
ftv({type_env, env}) ->
    ftv(maps:values(env));
% -spec ftv(list(types())) -> sets:set(string).
ftv([]) ->
    sets:new({version, 2});
ftv([Type | Types]) ->
    sets:union(ftv(Type), ftv(Types)).

% A substitution is a mapping of type variables to types. [1]
-type subst() :: maps:map(string, type()).

-spec compose_subst(subst(), subst()) -> subst().
compose_subst(S1, S2) ->
    maps:merge(maps:map(fun(T) -> apply_subst(S1, T) end, S2), S2).

% TODO: The return type is the same type as the second arg.
-spec apply_subst(subst(), types()) -> type().
% -spec apply_subst(subst(), type()) -> type().
apply_subst(Subst, {tvar, N}) ->
    % When a substitution is applied, the type variables that are not in the
    % domain of the substitution are to remain unchanged. [1]
    case maps:find(N, Subst) of
        {ok, T} ->
            T;
        error ->
            N
    end;
apply_subst(_Subst, {tint}) ->
    {tint};
apply_subst(_Subst, {tbool}) ->
    {tbool};
apply_subst(Subst, {tfun, T1, T2}) ->
    {tfun, apply_subst(Subst, T1), apply_subst(Subst, T2)};
% -spec apply_subst(subst(), type_scheme()) -> type_scheme().
apply_subst(Subst, {type_scheme, Vars, Type}) ->
    % A substitution only replaces free type variables, so the quantified type
    % variables in a type scheme are not affected by a substitution. [1]

    % Keep only free type variables in the substitution.
    SubstWithoutBound = maps:without(Subst, Vars),
    {type_scheme, Vars, apply_subst(SubstWithoutBound, Type)};
% -spec apply_subst(subst(), type_env()) -> type_env().
apply_subst(Subst, {type_env, env}) ->
    % Apply the substitution to the type schemes of the environment.
    {type_env, maps:map(fun (TypeScheme) -> apply_subst(Subst, TypeScheme) end, env)};
% -spec apply_subst(subst(), list(types)) -> list(types).
apply_subst(_Subst, []) ->
    [];
apply_subst(Subst, [Type | Types]) ->
    [apply_subst(Subst, Type)|apply_subst(Subst, Types)].

% Generalizing a type t with respect to a type environment env entails the
% quantification of the type variables that are free in t but do not occur
% in env. [1]
-spec generalize(type_env(), type()) -> type_scheme().
generalize(TypeEnv, Type) ->
    Quantified = sets:subtract(ftv(Type), ftv(TypeEnv)),
    {type_scheme, sets:to_list(Quantified), Type}.

% An instantiation of a type scheme is obtained by the replacement of the
% quantified type variables by fresh type variables. [1]
-spec instantiate(type_scheme()) -> type_scheme().
instantiate({type_scheme, Vars, Type}) ->
    % Fresh type variables are type variables with new names.
    FreshVars = lists:map(fun(_) -> "a" ++ integer_to_list(erlang:monotonic_time()) end, lists:seq(1, length(Vars))),

    {type_scheme, FreshVars, Type}.

% For two types t1 and t2 , mgu(t1,t2) returns the most general unifier, which
% is a substitution. By definition, it holds for a unifier S that
% S(t1) = S(t2). [1]
-spec mgu(type(), type()) -> subst().
mgu({tfun, T1, U1}, {tfun, T2, U2}) ->
    S1 = mgu(T1, T2),
    S2 = mgu(apply_subst(S1, U1), apply_subst(S1, U2)),
    compose_subst(S1, S2);
mgu({tint}, {tint}) ->
    maps:new();
mgu({tbool}, {tbool}) ->
    maps:new();
mgu({tvar, _}, {tvar, _}) ->
    maps:new();
mgu(T, {tvar, N}) ->
    mgu({tvar, N}, T);
mgu({tvar, N}, T) ->
    case sets:is_element(N, ftv(T)) of
        true ->
            % Can't substitute N with T if N appears in T.
            erlang:error("Occurs check");
        false ->
            maps:from_list([{N, T}])
    end;
mgu(_, _) ->
    erlang:error("Can't unify types").

-spec type_infer(type_env(), exp()) -> {subst(), type()}.
type_infer({type_env, Env}, {evar, N}) ->
    case maps:find(N, Env) of
        {ok, Sigma} ->
            {maps:new(), instantiate(Sigma)};
        error ->
            erlang:error("unbound variable")
    end;
type_infer({type_env, _}, {elit, L}) ->
    case L of
        {lint, _} ->
            {maps:new(), {tint}};
        {lbool, _} ->
            {maps:new(), {tbool}}
    end;
type_infer(TypeEnv, {eabs, X, E}) ->
    FreshVar = "a" ++ integer_to_list(erlang:monotonic_time()),
    {type_env, Env} = type_env_remove(TypeEnv, X),
    {S1, T1} = type_infer(maps:merge(Env, maps:from_list([{X, FreshVar}])), E),
    {S1, {tfun, apply_subst(S1, FreshVar), T1}};
type_infer(TypeEnv, {eapp, E1, E2}) ->
    FreshVar = "a" ++ integer_to_list(erlang:monotonic_time()),
    {S1, T1} = type_infer(TypeEnv, E1),
    {S2, T2} = type_infer(apply_subst(S1, TypeEnv), E2),
    S3 = mgu(apply_subst(S2, T1), {tfun, T2, FreshVar}),
    {compose_subst(compose_subst(S1, S2), S3), apply_subst(S3, FreshVar)};
type_infer(TypeEnv, {elet, X, E1, E2}) ->
    {S1, T1} = type_infer(TypeEnv, E1),
    {type_env, Env1} = apply_subst(S1, type_env_remove(TypeEnv, X)),
    Env2 = maps:from_list([{X, generalize(apply_subst(S1, TypeEnv), T1)}]),
    {S2, T2} = type_infer(maps:merge(Env1, Env2), E2),
    {compose_subst(S1, S2), T2}.
