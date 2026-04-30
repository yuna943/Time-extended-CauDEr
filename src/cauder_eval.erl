-module(cauder_eval).

%% API
-export([seq/3, expr/3, abstract/1, concrete/1, is_value/1, is_reducible/2]).
-export([match_rec_pid/6, match_rec_uid/4, match_rec/3]).
-export([clause_line/3]).

-include("cauder_message.hrl").
-include("cauder_stack.hrl").
-include("cauder_eval.hrl").

-export_type([result/0, label/0]).

-type result() :: #result{}.  %result() という名前の型は #result{} レコード型である という宣言。

-type label() ::
    label_tau()
    | label_self()
    | label_node()
    | label_nodes()
    | label_start()
    | label_spawn_fun()
    | label_spawn_mfa()
    | label_send()
    | label_receive()
    | label_registered()
    | label_whereis()
    | label_register()
    | label_unregister().

-type label_tau() :: #label_tau{}.
-type label_self() :: #label_self{}.
-type label_node() :: #label_node{}.
-type label_nodes() :: #label_nodes{}.
-type label_start() :: #label_start{}.
-type label_spawn_fun() :: #label_spawn_fun{}.
-type label_spawn_mfa() :: #label_spawn_mfa{}.
-type label_send() :: #label_send{}.
-type label_receive() :: #label_receive{}.
-type label_registered() :: #label_registered{}.
-type label_whereis() :: #label_whereis{}.
-type label_register() :: #label_register{}.
-type label_unregister() :: #label_unregister{}.

%%%=============================================================================
%%% API
%%%=============================================================================

%%------------------------------------------------------------------------------
%% @doc Evaluates the first reducible expression from the given list.
%% 与えられた式リストのうち、最初に簡約可能な（reducible）式を評価します。
%% Evaluates the first reducible expression from the given list of expressions,
%% given an environment and a call stack, then returns a record with the updated
%% information and a label indicating the type of step performed.
%% 環境（environment）と呼び出しスタック（call stack）が与えられたうえで、
%% 最初の簡約可能な式を評価し、その結果として更新された情報と、
%% どの種類のステップが実行されたかを示すラベルを含むレコードを返す
%% @see is_reducible/2

%% 式のリスト（Expressions）を左から順に見ていき、最初に “reducible（評価可能）” な式を 1 個だけ評価する関数
%% Erlang の 逐次評価 を CauDEr の内部表現で再現したもの
-spec eval_list(Bindings, Expressions, Stack) -> Result when
    Bindings :: cauder_bindings:bindings(),
    Expressions :: [cauder_syntax:abstract_expr()],
    Stack :: cauder_stack:stack(),
    Result :: cauder_eval:result().

eval_list(Bs, [E | Es], Stk) -> %Bs:環境, E:式, Es:残りの式リスト, Stk:スタック
    case is_reducible(E, Bs) of
        true ->
            R = #result{expr = Es1} = expr(Bs, E, Stk), %expr(Bs, E, Stk) がステップ実行, 返り値 #result{} の中から新しい式リスト expr = Es1 を取り出す
            R#result{expr = Es1 ++ Es};  %評価した式の結果 Es1 と 残りの式 Es を連結して、新しい式リストとして返す
        false ->
            R = #result{expr = Es1} = eval_list(Bs, Es, Stk),	%再帰的に eval_list を呼び出して、残りの式 Es の中から最初に reducible な式を評価する
            R#result{expr = [E | Es1]} %評価しなかった式 E を、新しい式リストの先頭に追加して返す
    end.

%%------------------------------------------------------------------------------
%% @doc Evaluates the given sequence of expression.
%% 与えられた式列（シーケンス）を評価する。
%% If the first expression in the sequence is reducible, then it is evaluated,
%% otherwise it is consumed, given an environment and a call stack.
%% Also if the first expression is not reducible, and there are no more
%% expressions in the sequence, then consumes the first element in the call
%% stack and retrieves the stored information.
%% Returns a record with the updated information and a label indicating the type
%% of step performed.
%% 最初の式が reducible（評価可能） であれば、その式を評価する。
%% そうでない場合は、環境（environment）と呼び出しスタック（call stack）を用いてその式を「消費（consume）」する。
%% また、最初の式が reducible ではなく、さらに式列に残りの式がない場合には、
%% 呼び出しスタックの先頭要素を取り出し（consume）、そこに保存されていた情報を復元する。
%% 戻り値としては、更新された情報と、
%% どの種類のステップが実行されたかを示す “ラベル” を含むレコードを返す。
%% @see is_reducible/2

-spec seq(Bindings, Expressions, Stack) -> Result when
    Bindings :: cauder_bindings:bindings(),
    Expressions :: [cauder_syntax:abstract_expr()],
    Stack :: cauder_stack:stack(),
    Result :: cauder_eval:result().

seq(Bs, [E | Es], Stk) ->
    case is_reducible(E, Bs) of
        false ->
            case Es of
                [] ->
                    Line = element(2, E),
                    {Entry, Stk1} = cauder_stack:pop(Stk),
                    case Entry of
                        {value, #s_function{env = Bs1, expr = Es1, var = Var}} ->
                            Es2 = cauder_syntax:replace_variable(Es1, setelement(2, Var, Line), concrete(E)),
                            #result{env = Bs1, expr = Es2, stack = Stk1};
                        {value, #s_block{expr = Es1, var = Var}} ->
                            Es2 = cauder_syntax:replace_variable(Es1, setelement(2, Var, Line), concrete(E)),
                            #result{env = Bs, expr = Es2, stack = Stk1}
                    end;
                _ ->
                    #result{env = Bs, expr = Es, stack = Stk}
            end;
        true ->
            #result{env = Bs1, expr = Es1, stack = Stk1} = Result = expr(Bs, E, Stk),
            case cauder_stack:pop(Stk1) of
                {{value, #s_function{env = Bs2, expr = Es2} = Entry}, Stk} ->
                    Entry1 = Entry#s_function{env = Bs1, expr = Es1 ++ Es},
                    Result#result{
                        env = Bs2,
                        expr = Es2,
                        stack = cauder_stack:push(Entry1, Stk)
                    };
                {{value, #s_block{expr = Es2} = Entry}, Stk} ->
                    Entry1 = Entry#s_block{expr = Es1 ++ Es},
                    Result#result{
                        expr = Es2,
                        stack = cauder_stack:push(Entry1, Stk)
                    };
                {{value, _}, _} ->
                    Result#result{
                        expr = Es1 ++ Es
                    }
            end
    end.

%%------------------------------------------------------------------------------
%% @doc Evaluates the given `Expression' and returns a tuple with an updated
%% environment, the expression that resulted from the evaluation, and a label.
%% 与えられた Expression を評価し、
%% 更新された環境、評価の結果として得られた式、そしてラベルを含むタプルを返す。
-spec expr(Bindings, Expression, Stack) -> Result when
    Bindings :: cauder_bindings:bindings(),
    Expression :: cauder_syntax:abstract_expr(),
    Stack :: cauder_stack:stack(),
    Result :: cauder_eval:result().

expr(Bs, {var, Line, Name}, Stk) ->
    {ok, Value} = cauder_bindings:find(Name, Bs),
    #result{env = Bs, expr = [{value, Line, Value}], stack = Stk};
expr(Bs, E = {cons, Line, H0, T0}, Stk) ->  %リスト構築式を1ステップ評価する処理  [H0 | T0]
    case is_reducible(H0, Bs) of
        true ->
            R = #result{expr = [H]} = expr(Bs, H0, Stk),  %H0 を評価して H に結果を格納
            case is_value(H) andalso is_value(T0) of
                true -> R#result{expr = [{value, Line, [concrete(H) | concrete(T0)]}]}; %R は #result{...} というレコード型。その中の expr フィールドを更新して返す
                false -> R#result{expr = [setelement(3, E, H)]}
            end;
        false ->
            case is_reducible(T0, Bs) of
                true ->
                    R = #result{expr = [T]} = expr(Bs, T0, Stk),
                    case is_value(H0) andalso is_value(T) of
                        true -> R#result{expr = [{value, Line, [concrete(H0) | concrete(T)]}]};
                        false -> R#result{expr = [setelement(4, E, T)]}
                    end;
                false ->
                    #result{env = Bs, expr = [{value, Line, [concrete(H0) | concrete(T0)]}], stack = Stk}
            end
    end;
expr(Bs, E = {tuple, Line, Es0}, Stk) ->
    R = #result{expr = Es} = eval_list(Bs, Es0, Stk),
    case is_value(Es) of
        true ->
            Tuple = list_to_tuple(lists:map(fun concrete/1, Es)),
            #result{env = Bs, expr = [{value, Line, Tuple}], stack = Stk};
        false ->
            R#result{expr = [setelement(3, E, Es)]}
    end;
expr(Bs, {'if', Line, Cs}, Stk0) -> %Line は行番号 Cs は if の条件節
    case match_if(Bs, Cs) of %条件節のガードを上から順に試し、マッチすれば {match, Body} を返す
        {match, Body} ->
            Var = cauder_utils:temp_variable(Line),
            Entry = #s_block{type = 'if', expr = Body, var = Var},
            Stk = cauder_stack:push(Entry, Stk0),
            #result{env = Bs, expr = [Var], stack = Stk}; %結果レコードを返す 
        nomatch ->
            error(if_clause) 
    end;
expr(Bs0, E = {'case', Line, A, Cs}, Stk0) -> % E:タプル, A：評価する対象式, Cs：case の節（clausesのこと。clauseは、{clause, Line, Patterns, Guards, Body} という構造で表現される すなわち条件分岐の一単位)
    case is_reducible(A, Bs0) of
        true ->
            eval_and_update({Bs0, A, Stk0}, {3, E}); %例えばcase 1+2 of ... の場合はまず 1+2 を 3 にする作業。
        false ->
            case match_case(Bs0, Cs, A) of
                {match, Bs, Body} ->
                    Var = cauder_utils:temp_variable(Line),
                    Entry = #s_block{type = 'case', expr = Body, var = Var},
                    Stk = cauder_stack:push(Entry, Stk0),
                    #result{env = Bs, expr = [Var], stack = Stk};
                nomatch ->
                    error({case_clause, concrete(A)})
            end
    end;
%% TODO Support receive with timeout
expr(Bs, {'receive', Line, Cs}, Stk0) ->
    % TODO One of these variables is not necessary
	%io:format("[expr DEBUG] receive Line = ~p Cs = ~p (after Time = infinity Ab = [])~n", [Line, Cs]),
    Var = cauder_utils:temp_variable(Line),
    VarBody = cauder_utils:temp_variable(Line),
    Entry = #s_block{type = 'receive', expr = [VarBody], var = Var},
    Stk = cauder_stack:push(Entry, Stk0),
    Label = #label_receive{var = VarBody, clauses = Cs, timeout = infinity},
    #result{env = Bs, expr = [Var], stack = Stk, label = Label};
expr(Bs, {'receive', Line, Cs, {'after', T, Ab}}, Stk0) ->
    % TODO One of these variables is not necessary
	%io:format("[expr DEBUG] receive Line = ~p Cs = ~p after Time = ~p Ab = ~p~n", [Line, Cs, T, Ab]),
    Var = cauder_utils:temp_variable(Line),
    VarBody = cauder_utils:temp_variable(Line),
    Entry = #s_block{type = 'receive', expr = [VarBody], var = Var},
    Stk = cauder_stack:push(Entry, Stk0),
    Label = #label_receive{var = VarBody, clauses = Cs, timeout = {T, Ab}},
    #result{env = Bs, expr = [Var], stack = Stk, label = Label};
% TODO Support fun() as entry point argument?
% TODO Handle calls to interpreted fun() from uninterpreted module
expr(Bs, {'make_fun', Line, Name, Cs}, Stk0) -> %Erlang の fun（無名関数）を内部的に生成
    {ok, M} = cauder_stack:current_module(Stk0), %現在のモジュール名を取得
    Arity = length(element(3, hd(Cs))), %引数の数を計算
    Info = {{M, Name}, Bs, Cs}, 
    Fun =
        case Arity of
            0 -> fun() -> {[], Info} end;
            1 -> fun(A) -> {[A], Info} end;
            2 -> fun(A, B) -> {[A, B], Info} end;
            3 -> fun(A, B, C) -> {[A, B, C], Info} end;
            4 -> fun(A, B, C, D) -> {[A, B, C, D], Info} end;
            5 -> fun(A, B, C, D, E) -> {[A, B, C, D, E], Info} end;
            % TODO Support more arities
            _ -> error({argument_limit, Arity})
        end,
    #result{env = Bs, expr = [{value, Line, Fun}], stack = Stk0};
expr(Bs, E = {bif, Line, M, F, As}, Stk) ->
    case is_reducible(As, Bs) of
        true ->
            eval_and_update({Bs, As, Stk}, {5, E});
        false ->
            Value = apply(M, F, lists:map(fun concrete/1, As)),
            #result{env = Bs, expr = [{value, Line, Value}], stack = Stk}
    end;
expr(Bs, {self, Line}, Stk) ->
    Var = cauder_utils:temp_variable(Line),
    Label = #label_self{var = Var},
    #result{env = Bs, expr = [Var], stack = Stk, label = Label};
expr(Bs, {node, Line}, Stk) ->
    Var = cauder_utils:temp_variable(Line),
    Label = #label_node{var = Var},
    #result{env = Bs, expr = [Var], stack = Stk, label = Label};
expr(Bs, {nodes, Line}, Stk) ->
    Var = cauder_utils:temp_variable(Line),
    Label = #label_nodes{var = Var},
    #result{env = Bs, expr = [Var], stack = Stk, label = Label};
expr(Bs, {registered, Line}, Stk) ->
    Var = cauder_utils:temp_variable(Line),
    Label = #label_registered{var = Var},
    #result{env = Bs, expr = [Var], stack = Stk, label = Label};
expr(Bs, E = {whereis, Line, Atom}, Stk) ->
    case is_reducible(Atom, Bs) of
        true ->
            eval_and_update({Bs, Atom, Stk}, {3, E});
        false ->
            Var = cauder_utils:temp_variable(Line),
            Label = #label_whereis{var = Var, atom = concrete(Atom)},
            #result{env = Bs, expr = [Var], stack = Stk, label = Label}
    end;
expr(Bs, E = {register, Line, Atom, Pid}, Stk) ->
    case is_reducible(Atom, Bs) of
        true ->
            eval_and_update({Bs, Atom, Stk}, {3, E});
        false ->
            case is_reducible(Pid, Bs) of
                true ->
                    eval_and_update({Bs, Pid, Stk}, {4, E});
                false ->
                    Var = cauder_utils:temp_variable(Line),
                    Label = #label_register{var = Var, atom = concrete(Atom), pid = concrete(Pid)},
                    #result{env = Bs, expr = [Var], stack = Stk, label = Label}
            end
    end;
expr(Bs, E = {unregister, Line, Atom}, Stk) ->
    case is_reducible(Atom, Bs) of
        true ->
            eval_and_update({Bs, Atom, Stk}, {3, E});
        false ->
            Var = cauder_utils:temp_variable(Line),
            Label = #label_unregister{var = Var, atom = concrete(Atom)},
            #result{env = Bs, expr = [Var], stack = Stk, label = Label}
    end;
expr(Bs, E = {spawn, Line, Fun}, Stk) ->
    case is_reducible(Fun, Bs) of
        true ->
            eval_and_update({Bs, Fun, Stk}, {3, E});
        false ->
            Var = cauder_utils:temp_variable(Line),
            Label = #label_spawn_fun{var = Var, function = Fun},
            #result{env = Bs, expr = [Var], stack = Stk, label = Label}
    end;
expr(Bs, E = {spawn, Line, N, Fun}, Stk) ->
    case is_reducible(N, Bs) of
        true ->
            eval_and_update({Bs, N, Stk}, {3, E});
        false ->
            case is_reducible(Fun, Bs) of
                true ->
                    eval_and_update({Bs, Fun, Stk}, {4, E});
                false ->
                    Var = cauder_utils:temp_variable(Line),
                    Label = #label_spawn_fun{var = Var, node = concrete(N), function = Fun},
                    #result{env = Bs, expr = [Var], stack = Stk, label = Label}
            end
    end;
expr(Bs, E = {spawn, Line, M, F, As}, Stk) ->
    case is_reducible(M, Bs) of
        true ->
            eval_and_update({Bs, M, Stk}, {3, E});
        false ->
            case is_reducible(F, Bs) of
                true ->
                    eval_and_update({Bs, F, Stk}, {4, E});
                false ->
                    case is_reducible(As, Bs) of
                        true ->
                            eval_and_update({Bs, As, Stk}, {5, E});
                        false ->
                            Var = cauder_utils:temp_variable(Line),
                            Label = #label_spawn_mfa{
                                var = Var,
                                module = concrete(M),
                                function = concrete(F),
                                args = concrete(As)
                            },
                            #result{env = Bs, expr = [Var], stack = Stk, label = Label}
                    end
            end
    end;
expr(Bs, E = {spawn, Line, N, M, F, As}, Stk) ->
    case is_reducible(N, Bs) of
        true ->
            eval_and_update({Bs, N, Stk}, {3, E});
        false ->
            case is_reducible(M, Bs) of
                true ->
                    eval_and_update({Bs, M, Stk}, {4, E});
                false ->
                    case is_reducible(F, Bs) of
                        true ->
                            eval_and_update({Bs, F, Stk}, {5, E});
                        false ->
                            case is_reducible(As, Bs) of
                                true ->
                                    eval_and_update({Bs, As, Stk}, {6, E});
                                false ->
                                    Var = cauder_utils:temp_variable(Line),
                                    Label = #label_spawn_mfa{
                                        var = Var,
                                        node = concrete(N),
                                        module = concrete(M),
                                        function = concrete(F),
                                        args = concrete(As)
                                    },
                                    #result{env = Bs, expr = [Var], stack = Stk, label = Label}
                            end
                    end
            end
    end;
expr(Bs, E = {start, Line, N}, Stk) ->
    case is_reducible(N, Bs) of
        true ->
            eval_and_update({Bs, N, Stk}, {3, E});
        false ->
            Var = cauder_utils:temp_variable(Line),
            Label = #label_start{var = Var, name = concrete(N)},
            #result{env = Bs, expr = [Var], stack = Stk, label = Label}
    end;
expr(Bs, E = {start, Line, H, N}, Stk) ->
    case is_reducible(H, Bs) of
        true ->
            eval_and_update({Bs, H, Stk}, {3, E});
        false ->
            case is_reducible(N, Bs) of
                true ->
                    eval_and_update({Bs, N, Stk}, {4, E});
                false ->
                    Var = cauder_utils:temp_variable(Line),
                    Label = #label_start{var = Var, name = concrete(N), host = concrete(H)},
                    #result{env = Bs, expr = [Var], stack = Stk, label = Label}
            end
    end;
expr(Bs, E = {Send, _, L, R}, Stk) when Send =:= 'send' orelse Send =:= 'send_op' ->
    case is_reducible(L, Bs) of
        true ->
            eval_and_update({Bs, L, Stk}, {3, E});
        false ->
            case is_reducible(R, Bs) of
                true ->
                    eval_and_update({Bs, R, Stk}, {4, E});
                false ->
                    Label = #label_send{dst = concrete(L), val = concrete(R)},
                    #result{env = Bs, expr = [R], stack = Stk, label = Label}
            end
    end;
expr(Bs0, E = {local_call, Line, F, As}, Stk0) ->
    case is_reducible(As, Bs0) of
        true ->
            eval_and_update({Bs0, As, Stk0}, {4, E});
        false ->
            {ok, M} = cauder_stack:current_module(Stk0),
            A = length(As),
            {_, Cs} = cauder_utils:fundef_lookup({M, F, A}),
            {match, Bs, Body} = match_fun(Cs, As),
            Var = cauder_utils:temp_variable(Line),
            Entry = #s_function{mfa = {M, F, A}, env = Bs, expr = Body, var = Var},
            Stk = cauder_stack:push(Entry, Stk0),
            #result{env = Bs0, expr = [Var], stack = Stk}
    end;
expr(Bs0, E = {remote_call, Line, M, F, As}, Stk0) ->
    case is_reducible(As, Bs0) of
        true -> eval_and_update({Bs0, As, Stk0}, {5, E});
        false -> eval_remote_call(M, F, As, Stk0, Line, Bs0)
    end;
% TODO Handle calls to self/0, spawn/1, spawn/3
expr(Bs0, E = {apply, Line, M0, F0, As}, Stk0) ->
    case is_reducible(M0, Bs0) of
        true ->
            eval_and_update({Bs0, M0, Stk0}, {3, E});
        false ->
            case is_reducible(F0, Bs0) of
                true ->
                    eval_and_update({Bs0, F0, Stk0}, {4, E});
                false ->
                    case is_reducible(As, Bs0) of
                        true ->
                            eval_and_update({Bs0, As, Stk0}, {5, E});
                        false ->
                            M = concrete(M0),
                            F = concrete(F0),
                            eval_remote_call(M, F, As, Stk0, Line, Bs0)
                    end
            end
    end;
expr(Bs0, E = {apply_fun, Line, Fun, As}, Stk0) ->
    case is_reducible(Fun, Bs0) of
        true ->
            eval_and_update({Bs0, Fun, Stk0}, {3, E});
        false ->
            case is_reducible(As, Bs0) of
                true ->
                    eval_and_update({Bs0, As, Stk0}, {4, E});
                false ->
                    A = length(As),
                    {env, [{{M, F}, Bs1, Cs}]} = erlang:fun_info(concrete(Fun), env),
                    {match, Bs2, Body} = match_fun(Cs, As),
                    Var = cauder_utils:temp_variable(Line),
                    Bs = cauder_bindings:merge(Bs1, Bs2),
                    Entry = #s_function{mfa = {M, F, A}, env = Bs, expr = Body, var = Var},
                    Stk = cauder_stack:push(Entry, Stk0),
                    #result{env = Bs0, expr = [Var], stack = Stk}
            end
    end;
expr(Bs0, E = {match, _, Lhs, Rhs}, Stk) ->
    case is_reducible(Lhs, Bs0) of
        true ->
            eval_and_update({Bs0, Lhs, Stk}, {3, E});
        false ->
            case is_reducible(Rhs, Bs0) of
                true ->
                    eval_and_update({Bs0, Rhs, Stk}, {4, E});
                false ->
                    case match(Bs0, [Lhs], [Rhs]) of
                        {match, Bs} -> #result{env = Bs, expr = [Rhs], stack = Stk};
                        nomatch -> error({badmatch, concrete(Rhs)})
                    end
            end
    end;
expr(Bs, E = {op, Line, Op, As}, Stk) ->
    case is_reducible(As, Bs) of
        true ->
            eval_and_update({Bs, As, Stk}, {4, E});
        false ->
            Value = apply(erlang, Op, lists:map(fun concrete/1, As)),
            #result{env = Bs, expr = [{value, Line, Value}], stack = Stk}
    end;
expr(Bs, E = {'andalso', Line, Lhs, Rhs}, Stk) ->
    case is_reducible(Lhs, Bs) of
        true ->
            eval_and_update({Bs, Lhs, Stk}, {3, E});
        false ->
            case Lhs of
                {value, _, false} ->
                    #result{env = Bs, expr = [Lhs], stack = Stk};
                {value, _, true} ->
                    case is_reducible(Rhs, Bs) of
                        true ->
                            eval_and_update({Bs, Rhs, Stk}, {4, E});
                        false ->
                            Value = apply(erlang, 'and', [concrete(Lhs), concrete(Rhs)]),
                            #result{env = Bs, expr = [{value, Line, Value}], stack = Stk}
                    end
            end
    end;
expr(Bs, E = {'orelse', Line, Lhs, Rhs}, Stk) ->
    case is_reducible(Lhs, Bs) of
        true ->
            eval_and_update({Bs, Lhs, Stk}, {3, E});
        false ->
            case Lhs of
                {value, _, true} ->
                    #result{env = Bs, expr = [Lhs], stack = Stk};
                {value, _, false} ->
                    case is_reducible(Rhs, Bs) of
                        true ->
                            eval_and_update({Bs, Rhs, Stk}, {4, E});
                        false ->
                            Value = apply(erlang, 'or', [concrete(Lhs), concrete(Rhs)]),
                            #result{env = Bs, expr = [{value, Line, Value}], stack = Stk}
                    end
            end
    end.

eval_remote_call(M, F, As, Stk0, Line, Bs0) ->
    A = length(As),
	case {M,F} of
		{timer, sleep} ->
			As_new = hd(As),
			Time = concrete(As_new),
			%io:format("[eval_remote_call DEBUG] timer:sleep(~p)~n", [Time]),
			Var = cauder_utils:temp_variable(Line),
			VarBody = cauder_utils:temp_variable(Line),
			Entry = #s_block{type = 'receive', expr = [VarBody], var = Var},
			Stk = cauder_stack:push(Entry, Stk0),
			Label = #label_receive{var = VarBody, clauses = [], timeout = {As_new, [{value, Line, ok}]}},
			#result{env = Bs0, expr = [Var], stack = Stk, label = Label};
		{_,_} ->
			case cauder_utils:fundef_lookup({M, F, A}) of
				{Exported, Cs} ->
					% Check if function is accessible
					case cauder_stack:current_module(Stk0) of
						{ok, M} -> ok;
						{ok, _} -> true = Exported;
						error when Stk0 =:= [] -> ok
					end,
					{match, Bs, Body} = match_fun(Cs, As),
					Var = cauder_utils:temp_variable(Line),
					Entry = #s_function{mfa = {M, F, A}, env = Bs, expr = Body, var = Var},
					Stk = cauder_stack:push(Entry, Stk0),
					#result{env = Bs0, expr = [Var], stack = Stk};
				error ->
					Value = apply(M, F, lists:map(fun concrete/1, As)),
					#result{env = Bs0, expr = [{value, Line, Value}], stack = Stk0}
			end
    end.

%%%=============================================================================

-spec match_if(Bindings, Clauses) -> {match, Body} | nomatch when
    Bindings :: cauder_bindings:bindings(),
    Clauses :: cauder_syntax:af_clause_seq(),
    Body :: cauder_syntax:af_body().

match_if(_, []) ->
    nomatch;
match_if(Bs, [{'clause', _, [], G, B} | Cs]) ->
    case concrete(eval_guard_seq(Bs, G)) of
        true -> {match, B};
        false -> match_if(Bs, Cs)
    end.

-spec match_case(Bindings, Clauses, Argument) -> {match, ScopeBindings, Body} | nomatch when
    Bindings :: cauder_bindings:bindings(),
    Clauses :: cauder_syntax:af_clause_seq(),
    Argument :: cauder_syntax:af_literal(),
    ScopeBindings :: cauder_bindings:bindings(),
    Body :: cauder_syntax:af_body().

match_case(Bs, Cs, V) -> match_clause(Bs, Cs, [V]).

-spec match_fun(Clauses, Arguments) -> {match, ScopeBindings, Body} | nomatch when
    Clauses :: cauder_syntax:af_clause_seq(),
    Arguments :: [cauder_syntax:af_literal()],
    ScopeBindings :: cauder_bindings:bindings(),
    Body :: cauder_syntax:af_body().

match_fun(Cs, Vs) -> match_clause(cauder_bindings:new(), Cs, Vs).

-spec match_rec_pid(Clauses, Bindings, RecipientPid, Mail, Sched, Sys) ->
    {NewBindings, Body, {Message, QueuePosition}, NewMail} | nomatch
when
    Clauses :: cauder_syntax:af_clause_seq(),  %
    Bindings :: cauder_bindings:bindings(), %現在の変数束縛
    RecipientPid :: cauder_process:id(),  %メッセージを受信するプロセスの PID
    Mail :: cauder_mailbox:mailbox(),   %そのプロセスのメールボックス
    Sched :: cauder_message:scheduler(),  %CauDEr のメッセージスケジューラ
    Sys :: cauder_system:system(),    %CauDEr のシステム状態
    NewBindings :: cauder_bindings:bindings(),  %パターンマッチ後に更新された変数束縛
    Body :: cauder_syntax:af_body(),   %該当する receive 句の Body
    Message :: cauder_message:message(),  %マッチしたメッセージ
    QueuePosition :: pos_integer(),  %マッチしたメッセージが mailbox の何番目にあったか
    NewMail :: cauder_mailbox:mailbox(). %メールボックスからそのメッセージを削除した後の新しい Mailbox

match_rec_pid(Cs, Bs, Pid, Mail, Sched, Sys) -> %receive 式のパターンマッチ処理を担当する関数
    case cauder_mailbox:find_destination(Pid, Mail) of
        [] ->
            nomatch;
        QueueList ->
            case Sched of
                ?SCHEDULER_Manual -> %スケジューラが manual モードのときの処理。receive がどのメッセージを選ぶかを ユーザが選択できる。
                    FoldQueue =  %無名関数。　1つのメッセージ Msg に対して「receive のパターンにマッチするか」をチェックし、マッチした場合は Map1 に追加する
                        fun(Msg, Map1) -> 
                            case match_rec(Cs, Bs, #message{uid = Uid} = Msg) of
                                {match, Bs1, Body} -> maps:put(Uid, {Bs1, Body, Msg}, Map1); %メッセージの UID をキーに、環境・マッチした Body・メッセージを map に追加する	
                                nomatch -> skip
                            end
                        end,
                    FoldQueueList = fun(Queue, Map0) -> lists:foldl(FoldQueue, Map0, queue:to_list(Queue)) end,  %キュー内のすべてのメッセージに対して receive パターンをチェックし、マッチしたものを map にまとめる
                    MatchingBranchesMap = lists:foldl(FoldQueueList, maps:new(), QueueList),
                    case maps:size(MatchingBranchesMap) of
                        0 ->
                            nomatch;
                        _ ->
                            MatchingMessages = lists:map(fun({_, _, Msg}) -> Msg end, maps:values(MatchingBranchesMap)),
                            case cauder:suspend_task(Pid, MatchingMessages, Sys) of
                                % TODO Use suspend time
                                {_SuspendTime, {resume, Uid}} ->
                                    cauder:resume_task(), %Erlang モジュールの関数を呼び出す 
                                    {Bs1, Body, Msg} = maps:get(Uid, MatchingBranchesMap),
                                    {QPos, NewMail} = cauder_mailbox:remove(Msg, Mail),
                                    {Bs1, Body, {Msg, QPos}, NewMail};
                                % TODO Use suspend time
                                {_SuspendTime, cancel} ->
                                    throw(cancel)
                            end
                    end;
                ?SCHEDULER_Random ->
                    MatchingBranches = lists:filtermap(  %マッチしたメッセージと対応する環境・本文のリスト MatchingBranchesを作成する
                        fun(Queue) ->
                            {value, Msg} = queue:peek(Queue),
                            case match_rec(Cs, Bs, Msg) of
                                {match, Bs1, Body} -> {true, {Bs1, Body, Msg}};
                                nomatch -> false
                            end
                        end,
                        QueueList
                    ),
                    case length(MatchingBranches) of
                        0 ->
                            nomatch;
                        Length ->
                            {Bs1, Body, Msg} = lists:nth(rand:uniform(Length), MatchingBranches),
                            {QPos, NewMail} = cauder_mailbox:remove(Msg, Mail),
                            {Bs1, Body, {Msg, QPos}, NewMail}
                    end
            end
    end.

-spec match_rec(Clauses, Bindings, Message) -> {match, NewBindings, Body} | nomatch when  %メッセージの値を抽象化して、各節のパターンと比較する
    Clauses :: cauder_syntax:af_clause_seq(),
    Bindings :: cauder_bindings:bindings(),
    Message :: cauder_message:message(),
    NewBindings :: cauder_bindings:bindings(),
    Body :: cauder_syntax:af_body().

match_rec(Cs, Bs0, #message{val = Value}) -> match_clause(Bs0, Cs, [abstract(Value)]).  %abstract/1 は Erlang 値を「CauDEr が扱う式形式」にする関数

-spec match_rec_uid(Clauses, Bindings, Uid, Mail) -> %特定のメッセージ UID（固有 ID）を持つメッセージを mailbox から探し、そのメッセージが receive の各 clause にマッチするか調べるための関数
    {NewBindings, Body, {Message, QueuePosition}, NewMail} | nomatch
when
    Clauses :: cauder_syntax:af_clause_seq(),
    Bindings :: cauder_bindings:bindings(),
    Uid :: cauder_message:uid(),
    Mail :: cauder_mailbox:mailbox(),
    NewBindings :: cauder_bindings:bindings(),
    Body :: cauder_syntax:af_body(),
    Message :: cauder_message:message(),
    QueuePosition :: pos_integer(),
    NewMail :: cauder_mailbox:mailbox().

match_rec_uid(Cs, Bs0, Uid, Mail0) ->
    case cauder_mailbox:take(Uid, Mail0) of
        error ->
            nomatch;
        {{Msg, QPos}, Mail1} ->
            case match_clause(Bs0, Cs, [abstract(Msg#message.val)]) of
                {match, Bs, Body} -> {Bs, Body, {Msg, QPos}, Mail1};
                nomatch -> nomatch
            end
    end.


-spec match_clause(Bindings, Clauses, Arguments) -> {match, ScopeBindings, Body} | nomatch when %Erlang の case / receive / fun clause のパターンマッチを実行する関数
    Bindings :: cauder_bindings:bindings(),
    Clauses :: cauder_syntax:af_clause_seq(),
    Arguments :: [cauder_syntax:af_literal()],
    ScopeBindings :: cauder_bindings:bindings(),
    Body :: cauder_syntax:af_body().

match_clause(_, [], _) ->
    nomatch;
match_clause(Bs0, [{'clause', _, Ps, G, B} | Cs], Vs) ->
    case match(Bs0, Ps, Vs) of
        {match, Bs} ->
            case concrete(eval_guard_seq(Bs, G)) of
                true -> {match, Bs, B};
                false -> match_clause(Bs0, Cs, Vs)
            end;
        nomatch ->
            match_clause(Bs0, Cs, Vs)
    end.

-spec clause_line(Bindings, Clauses, Arguments) -> Line when  %複数の clause（節） を持つ構造において、どの clause が選ばれるかを行番号で返す関数
    Bindings :: cauder_bindings:bindings(),
    Clauses :: cauder_syntax:af_clause_seq(),
    Arguments :: [cauder_syntax:af_literal()],
    Line :: non_neg_integer().

clause_line(_, [], _) ->
    -1;
clause_line(Bs0, [{'clause', Line, Ps, G, _} | Cs], Vs) ->
    case match(Bs0, Ps, Vs) of
        {match, Bs} ->
            case concrete(eval_guard_seq(Bs, G)) of
                true -> Line;
                false -> clause_line(Bs0, Cs, Vs)
            end;
        nomatch ->
            clause_line(Bs0, Cs, Vs)
    end.

%% Tries to match a list of values against a list of patterns using the given environment.
%% The list of values should have no variables.
%% 指定された環境（Bindings）を使って、値のリストをパターンのリストにマッチさせようとする。
%% 値のリストには変数を含んではならない。
-spec match(Bindings, Patterns, Arguments) -> {match, NewBindings} | nomatch when
    Bindings :: cauder_bindings:bindings(),
    Patterns :: [cauder_syntax:af_pattern()],
    Arguments :: [cauder_syntax:af_literal()],
    NewBindings :: cauder_bindings:bindings().
%match が成功した場合はBindings（変数環境）を更新したものを返す
match(Bs, [], []) ->
    {match, Bs};
match(Bs0, [Pat | Ps0], [{value, _, Val} | Vs0]) when length(Ps0) == length(Vs0) ->
    case catch match1(Pat, Val, Bs0) of
        {match, Bs} -> match(Bs, Ps0, Vs0);
        nomatch -> nomatch
    end;
match(_Bs, _Ps, _Vs) ->
    nomatch.

% TODO Organize arguments to be consistent
-spec match1(Pattern, Term, Bindings) -> {match, NewBindings} | no_return() when  %単一のパターン（af_pattern） と単一の値（Term） を比較してパターンマッチをする関数
    Pattern :: cauder_syntax:af_pattern(),
    Term :: term(),
    Bindings :: cauder_bindings:bindings(),
    NewBindings :: cauder_bindings:bindings().

match1({value, _, V}, V, Bs) ->
    {match, Bs};
match1({var, _, '_'}, _, Bs) ->
    {match, Bs};
match1({var, _, Name}, Value, Bs0) ->
    case cauder_bindings:find(Name, Bs0) of
        {ok, Value} ->
            {match, Bs0};
        {ok, _} ->
            throw(nomatch);
        error ->
            Bs1 = cauder_bindings:add(Name, Value, Bs0),
            {match, Bs1}
    end;
match1({match, _, Pat1, Pat2}, Term, Bs0) ->
    {match, Bs1} = match1(Pat1, Term, Bs0),
    match1(Pat2, Term, Bs1);
match1({cons, _, H, T}, [H1 | T1], Bs0) ->
    {match, Bs} = match1(H, H1, Bs0),
    match1(T, T1, Bs);
match1({tuple, _, Es}, Tuple, Bs) when length(Es) =:= tuple_size(Tuple) ->
    match_tuple(Es, Tuple, 1, Bs);
match1(_, _, _) ->
    throw(nomatch).

-spec match_tuple(Values, Tuple, Index, Bindings) -> {match, NewBindings} | no_return() when %タプルの各要素とパターンの各要素を順番にマッチングするための補助関数
    Values :: [cauder_syntax:af_literal()],
    Tuple :: tuple(),
    Index :: pos_integer(),
    Bindings :: cauder_bindings:bindings(),
    NewBindings :: cauder_bindings:bindings().

match_tuple([], _, _, Bs) ->
    {match, Bs};
match_tuple([E | Es], Tuple, I, Bs0) ->
    {match, Bs} = match1(E, element(I, Tuple), Bs0),
    match_tuple(Es, Tuple, I + 1, Bs).

-spec eval_guard_seq(Bindings, Guards) -> Boolean when %ガード式のリスト（ガードシーケンス）を評価し、そのうち 1 つでも true になれば全体を true とする関数
    Bindings :: cauder_bindings:bindings(),
    Guards :: cauder_syntax:af_guard_seq(),
    Boolean :: cauder_syntax:af_boolean().

eval_guard_seq(_, []) ->
    abstract(true);
eval_guard_seq(Bs, Gs) when is_list(Gs) ->
    % In a guard sequence, guards are evaluated until one is true. The remaining guards, if any, are not evaluated.
    % See: https://erlang.org/doc/reference_manual/expressions.html#guard-sequences
    abstract(lists:any(fun(G) -> concrete(eval_guard(Bs, G)) end, Gs)).

-spec eval_guard(Bindings, Guard) -> Boolean when %1つのガード（AND のまとまり）を評価する関数で、ガード内のすべてのテストが true のときだけ true を返す
    Bindings :: cauder_bindings:bindings(),
    Guard :: cauder_syntax:af_guard(),
    Boolean :: cauder_syntax:af_boolean().

eval_guard(Bs, G) when is_list(G) ->
    abstract(lists:all(fun(Gt) -> concrete(eval_guard_test(Bs, Gt)) end, G)).

-spec eval_guard_test(Bindings, GuardTest) -> GuardTest | Boolean when
    Bindings :: cauder_bindings:bindings(),
    GuardTest :: cauder_syntax:af_guard_test(),
    Boolean :: cauder_syntax:af_boolean().

eval_guard_test(Bs, Gt) ->
    case is_reducible(Gt, Bs) of
        true ->
            #result{expr = [Gt1]} = expr(Bs, Gt, cauder_stack:new()),
            eval_guard_test(Bs, Gt1);
        false ->
            Gt
    end.

%%%=============================================================================

%%------------------------------------------------------------------------------
%% @doc Converts the given Erlang term into its abstract form.

-spec abstract(Term) -> Literal when
    Term :: term(),
    Literal :: cauder_syntax:af_literal().

abstract(Value) -> {value, 0, Value}.

%%------------------------------------------------------------------------------
%% @doc Converts the given abstract literal element into the Erlang term that it
%% represents.

-spec concrete(Literal) -> Term when
    Literal :: cauder_syntax:af_literal(),
    Term :: term().

concrete({value, _, Value}) -> Value;
concrete({cons, _, {value, _, H}, {value, _, T}}) -> [H | T].

%%------------------------------------------------------------------------------
%% @doc Checks if the given abstract expression (or list of expressions) can be
%% reduced any further or not, given an environment.

-spec is_reducible(Expression | [Expression], Bindings) -> IsReducible when
    Expression :: cauder_syntax:abstract_expr(),
    Bindings :: cauder_bindings:bindings(),
    IsReducible :: boolean().

is_reducible([], _) ->
    false;
is_reducible([E | Es], Bs) ->
    is_reducible(E, Bs) orelse is_reducible(Es, Bs);
is_reducible({value, _, _}, _) ->
    false;
is_reducible({var, _, '_'}, _) ->
    false;
is_reducible({var, _, Name}, Bs) ->
    not cauder_utils:is_temp_variable_name(Name) andalso cauder_bindings:is_bound(Name, Bs);
is_reducible({cons, _, H, T}, Bs) ->
    is_reducible(H, Bs) orelse is_reducible(T, Bs);
is_reducible({tuple, _, Es}, Bs) ->
    is_reducible(Es, Bs);
is_reducible(E, _) when is_tuple(E) ->
    true.

%%------------------------------------------------------------------------------
%% @doc Checks if the given abstract expression is a literal value.

-spec is_value(Expression | [Expression]) -> IsValue when
    Expression :: cauder_syntax:abstract_expr(),
    IsValue :: boolean().

is_value([]) -> true;
is_value([E | Es]) -> is_value(E) andalso is_value(Es);
is_value({value, _, _}) -> true;
is_value({cons, _, H, T}) -> is_value(H) andalso is_value(T);
is_value({tuple, _, Es}) -> is_value(Es);
is_value(E) when is_tuple(E) -> false.

-spec eval_and_update({Bindings, Expression | [Expression], Stack}, {Index, Tuple}) -> Result when
    Bindings :: cauder_bindings:bindings(),
    Expression :: cauder_syntax:abstract_expr(),
    Stack :: cauder_stack:stack(),
    Index :: pos_integer(),
    Tuple :: tuple(),
    Result :: cauder_eval:result().

eval_and_update({Bs, Es, Stk}, {Index, Tuple}) when is_list(Es) ->
    R = #result{expr = Es1} = eval_list(Bs, Es, Stk),
    R#result{expr = [setelement(Index, Tuple, Es1)]};
eval_and_update({Bs, E, Stk}, {Index, Tuple}) ->
    R = #result{expr = [E1]} = expr(Bs, E, Stk),
    R#result{expr = [setelement(Index, Tuple, E1)]}.
