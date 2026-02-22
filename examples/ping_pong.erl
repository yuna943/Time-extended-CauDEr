-module(ping_pong).
-export([start/0, ping/1, pong/0]).

%% プログラム開始
start() ->
    PidPong = spawn(?MODULE, pong, []),
    PidPing = spawn(?MODULE, ping, [PidPong]),
    ok.

%% Ping プロセス
ping(PidPong) ->
    PidPong ! {ping, self()},
    ping_loop(PidPong).

ping_loop(PidPong) ->
    receive
        {pong, From} ->
            io:format("Ping received pong from ~p~n", [From]),
            PidPong ! {ping, self()},
            ping_loop(PidPong)
    end.

%% Pong プロセス
pong() ->
    receive
        {ping, From} ->
            io:format("Pong received ping from ~p~n", [From]),
            From ! {pong, self()},
            pong()
    end.
