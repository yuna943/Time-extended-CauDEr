-module(time_new). 
-export([main/0, p1/1, p2/1, p3/0]).


main() ->
	Pid = spawn(?MODULE, p3, []),
	spawn(?MODULE, p1, [Pid]),
	spawn(?MODULE, p2, [Pid]).


p3() -> 
	receive
		{N} ->
			io:format("Received: ~p~n", [N])
	end.

p1(Pid) ->
	receive after 2 -> ok end, % 0〜20ms 遅延
	Pid ! {1}.

p2(Pid) ->
	receive after 1 -> ok end, % 0〜20ms 遅延
	Pid ! {2}.

