-module(tests).

-export([ e0/0
        , e1/0
        , e2/0
        , e3/0
        , e4/0
        , e5/0 ]).

% let id = λx → x
% in id
e0() ->
    {elet,
        "id",
        {eabs,
            "x",
            {evar, "x"}
        },
        {evar, "id"}
    }.

% let id = λx → x
% in id id
e1() ->
    {elet,
        "id",
        {eabs,
            "x",
            {evar, "x"}},
        {eapp,
            {evar, "id"},
            {evar, "id"}
        }
    }.


% let id = λx → let y = x
%               in y
% in id id
e2() ->
    {elet,
        "id",
        {eabs,
            "x",
            {elet,
                "y",
                {evar, "x"},
                {evar, "y"}
            }
        },
        {eapp,
            {evar, "id"},
            {evar, "id"}
        }
    }.

% let id = λx → let y = x
%               in y
% in (id id) 2
e3() ->
    {elet,
        "id",
        {eabs,
            "x",
            {elet,
                "y",
                {evar, "x"},
                {evar, "y"}
            }
        },
        {eapp,
            {eapp,
                {evar, "id"},
                {evar, "id"}
            },
            {elit, {lint, 2}}
        }
    }.

% let id = λx → x x
% in id
e4() ->
    {elet,
        "id",
        {eabs,
            "x",
            {eapp,
                {evar, "x"},
                {evar, "x"}
            }
        },
        {evar, "id"}
    }.

% λm → let y = m
%      in let x = y True
%         in x
e5() ->
    {eabs,
        "m",
        {elet,
            "y",
            {evar, "m"},
            {elet,
                "x",
                {eapp,
                    {evar, "y"},
                    {elit, {lbool, true}}
                },
                {evar, "x"}
            }
        }
    }.
