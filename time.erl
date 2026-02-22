-module(time). 
-export([main/0, p1/1, p2/1, p3/0]).


main() ->
	Pid = spawn(?MODULE, p3, []),
	spawn(?MODULE, p1, [Pid]),
	spawn(?MODULE, p2, [Pid]).

p1(Pid) ->
	timer:sleep(2),
	Pid ! {1}.

p2(Pid) ->
	timer:sleep(1),
	Pid ! {2}.

p3() -> 
	receive
		{N} ->
			io:format("Received: ~p~n", [N])
	end.


