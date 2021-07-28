-module(w).

-export([ftv/1]).

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

-type scheme() :: {scheme, list(string), type()}.

-type type_env() :: {type_env, maps:map(string(), scheme())}.

-spec ftv(type() | scheme() | type_env()) -> sets:set(string).
ftv({tvar, N}) ->
    sets:from_list([N], {version, 2});
ftv({tint}) ->
    sets:new({version, 2});
ftv({tbool}) ->
    sets:new({version, 2});
ftv({tfun, T1, T2}) ->
    sets:union(ftv(T1), ftv(T2));
ftv({scheme, Vars, Type}) ->
    sets:subtract(ftv(Type), sets:from_list(Vars));
ftv([]) ->
    sets:new({version, 2});
ftv([Type | Types]) ->
    sets:union(ftv(Type), ftv(Types));
ftv({type_env, env}) ->
    ftv(maps:values(env)).
