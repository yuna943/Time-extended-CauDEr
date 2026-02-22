-module(cauder_app).

-behaviour(application).

%% application callbacks
-export([start/2, stop/1]).

%%%===================================================================
%%% Application callbacks
%%%===================================================================
%% start/2 関数は StartType と StartArgs を受け取る という宣言
-spec start(StartType, StartArgs) -> {ok, Pid} | {ok, Pid, State} | {error, Reason} when
    StartType :: application:start_type(),  %アプリを起動する方法を指定する型
    StartArgs :: term(),  %ユーザーが application:start(App, Args) をしたときの Args がここに入る。別な意味はなく、自由な値。
    Pid :: pid(),   %以下戻り値の説明　 {ok, Pid}:start/2 が Supervisor の PID を返す 一般的な形
    State :: term(),  %{ok, Pid, State}:アプリケーションに アプリケーション内部状態 を持たせたい場合に使う Rare ケース
    Reason :: term(). %{error, Reason}:アプリケーションの起動に失敗した場合に使う

%%引数が []（何も指定されていない）なら、自動的に [wx] をつけて起動する
%%つまり、GUI ウィンドウ（wxWidgets）を起動するモード
start(normal, []) ->
    start(normal, [wx]);
%%引数がある場合は、そのまま supervisor を起動
start(normal, Args) ->
    cauder_sup:start_link(Args).

-spec stop(State) -> ok when
    State :: term().

stop(_State) ->
    ok.
