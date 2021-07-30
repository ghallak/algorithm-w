-module(w).

-export([ ftv/1
        , apply_subst/2 ]).

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
