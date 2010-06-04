%% -*- erlang-indent-level: 2 -*-
%%-----------------------------------------------------------------------
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2010. All Rights Reserved.
%%
%% The contents of this file are subject to the Erlang Public License,
%% Version 1.1, (the "License"); you may not use this file except in
%% compliance with the License. You should have received a copy of the
%% Erlang Public License along with this software. If not, it can be
%% retrieved online at http://www.erlang.org/.
%%
%% Software distributed under the License is distributed on an "AS IS"
%% basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See
%% the License for the specific language governing rights and limitations
%% under the License.
%%
%% %CopyrightEnd%
%%

%%%-------------------------------------------------------------------
%%% File        : dialyzer_behaviours.erl
%%% Authors     : Stavros Aronis <aronisstav@gmail.com>
%%% Description : Tools for analyzing proper behaviour usage.
%%%
%%% Created     : 28 Oct 2009 by Stavros Aronis <aronisstav@gmail.com>
%%%-------------------------------------------------------------------
%%% NOTE: This module is currently experimental -- do NOT rely on it!
%%%-------------------------------------------------------------------

-module(dialyzer_behaviours).

-export([check_callbacks/4,
	 get_behaviour_apis/1,
	 scan_behaviours/3,
	 translatable_behaviours/1,
	 translate_behaviour_api_call/5,
	 translate_callgraph/3]).

%%--------------------------------------------------------------------

-include("dialyzer.hrl").

%%--------------------------------------------------------------------

-record(state, {plt        :: dialyzer_plt:plt(),
		codeserver :: dialyzer_codeserver:codeserver(),
		filename   :: string(),
		behlines   :: [{atom(), number()}]}).

%%--------------------------------------------------------------------

-spec scan_behaviours([module()], dialyzer_codeserver:codeserver(), 
		      dialyzer_plt:plt()) -> {[atom()], [atom()]}.

scan_behaviours(Modules, Codeserver, Plt) ->
  scan_behaviours(Modules, Codeserver, Plt, [], []).

-spec check_callbacks(module(), [{cerl:cerl(), cerl:cerl()}],
		      dialyzer_plt:plt(),
		      dialyzer_codeserver:codeserver()) -> [dial_warning()].

check_callbacks(Module, Attrs, Plt, Codeserver) ->
  {Behaviours, BehLines} = get_behaviours(Attrs),
  case Behaviours of
    [] -> [];
     _ -> {_Var,Code} =
	    dialyzer_codeserver:lookup_mfa_code({Module,module_info,0},
						Codeserver),
	  File = get_file(cerl:get_ann(Code)),
	  State = #state{plt = Plt, codeserver = Codeserver, filename = File,
			 behlines = BehLines},
	  Warnings = get_warnings(Module, Behaviours, Plt),
	  [add_tag_file_line(Module, W, State) || W <- Warnings]
  end.

-spec translatable_behaviours(cerl:c_module()) -> [{atom(),[_]}].

translatable_behaviours(Tree) ->
  Attrs = cerl:module_attrs(Tree),
  {Behaviours, _BehLines} = get_behaviours(Attrs),
  [{B, Calls} || B <- Behaviours, (Calls = behaviour_api_calls(B)) =/= []].

-spec get_behaviour_apis([atom()]) -> [mfa()].

get_behaviour_apis(Behaviours) ->
  get_behaviour_apis(Behaviours, []).

-spec translate_behaviour_api_call(_, _, _, _, _) -> _.

translate_behaviour_api_call(_Fun, _ArgTypes, _Args, _Module, []) ->
  plain_call;
translate_behaviour_api_call({Module, Fun, Arity}, ArgTypes, Args,
			     CallbackModule, BehApiInfo) ->
  case lists:keyfind(Module, 1, BehApiInfo) of
    false -> plain_call;
    {Module, Calls} ->
      case lists:keyfind({Fun, Arity}, 1, Calls) of
	false -> plain_call;
	{{Fun, Arity}, {CFun, CArity, COrder}} ->
	  {{CallbackModule, CFun, CArity},
	   [nth_or_0(N, ArgTypes, erl_types:t_any()) || N <-COrder],
	   [nth_or_0(N, Args, bypassed) || N <-COrder]}
      end
  end;
translate_behaviour_api_call(_Fun, _ArgTypes, _Args, _Module, _BehApiInfo) ->
  plain_call.

-spec translate_callgraph([{atom(), _}], atom(), dialyzer_callgraph:callgraph())
			  -> dialyzer_callgraph:callgraph().

translate_callgraph([{Behaviour,_}|Behaviours], Module, Callgraph) ->
  UsedCalls = [Call || {_From, {M, _F, _A}} = Call <-
			 dialyzer_callgraph:get_behaviour_api_calls(Callgraph),
		       M =:= Behaviour],
  Calls = [{{Behaviour, API, Arity}, Callback} ||
	    {{API, Arity}, Callback} <- behaviour_api_calls(Behaviour)],
  DirectCalls = [{From, {Module, Fun, Arity}} ||
		  {From, To} <- UsedCalls,{API, {Fun, Arity, _Ord}} <- Calls,
		  To =:= API],
  NewCallgraph = dialyzer_callgraph:add_edges(DirectCalls, Callgraph),
  translate_callgraph(Behaviours, Module, NewCallgraph);
translate_callgraph([], _Module, Callgraph) ->
  Callgraph.

%%--------------------------------------------------------------------

get_behaviours(Attrs) ->
  BehaviourListsAndLine = [{cerl:concrete(L2), hd(cerl:get_ann(L2))} ||
		  {L1, L2} <- Attrs, cerl:is_literal(L1),
		  cerl:is_literal(L2), cerl:concrete(L1) =:= 'behaviour'],
  Behaviours = lists:append([Behs || {Behs,_} <- BehaviourListsAndLine]),
  BehLines = [{B,L} || {L1,L} <- BehaviourListsAndLine, B <- L1],
  {Behaviours, BehLines}.

get_warnings(Module, Behaviours, Plt) ->
  get_warnings(Module, Behaviours, Plt, []).

get_warnings(_, [], _, Acc) ->
  Acc;
get_warnings(Module, [Behaviour|Rest], Plt, Acc) ->
  Warnings = check_behaviour(Module, Behaviour, Plt),
  get_warnings(Module, Rest, Plt, Warnings ++ Acc).

check_behaviour(Module, Behaviour, Plt) ->
  Callbacks = dialyzer_plt:get_callbacks(Behaviour, Plt),
  case Callbacks of
    [] -> [];
     _ -> check_all_callbacks(Module, Behaviour, Callbacks, Plt)
  end.

check_all_callbacks(Module, Behaviour, Callbacks, State) ->
  check_all_callbacks(Module, Behaviour, Callbacks, State, []).

check_all_callbacks(Module, Behaviour, [Callback|Rest], Plt, Acc) ->
  Warns = check_callback(Module, Behaviour, Callback, Plt),
  check_all_callbacks(Module, Behaviour, Rest, Plt, Warns ++ Acc);
check_all_callbacks(_Module, _Behaviour, [], _Plt, Acc) ->
  Acc.

check_callback(Module, Behaviour, {_M, F, A} = Callback, Plt) ->
  case dialyzer_plt:lookup_callback_contract(Plt, Callback) of
    {value, Contract} ->
      ContractReturn = dialyzer_contracts:get_contract_return(Contract),
      ContractArgs = dialyzer_contracts:get_contract_args(Contract),
      case dialyzer_plt:lookup(Plt, {Module, F, A}) of
	{value, {InferredReturn, InferredArgs}} ->
	  Warn1 = case unifiable(InferredReturn, ContractReturn) of
		    [] -> [];
		    Offenders ->
		      [{callback_type_mismatch,
			[Behaviour, F, A, erl_types:t_sup(Offenders)]}]
		  end,
	  ZipArgs = lists:zip3(lists:seq(1, A), InferredArgs, ContractArgs),
	  Warn2 = [{callback_arg_type_mismatch,
		    [Behaviour, F, A, N,
		     erl_types:t_sup(Offenders)]} ||
		    {Offenders, N} <- [check_callback_1(V) || V <- ZipArgs],
		    Offenders =/= []],
	  Warn1 ++ Warn2;
	_ -> [{callback_missing, [Behaviour, F, A]}]
      end;
    _ -> []
  end.

check_callback_1({N, T1, T2}) ->
  {unifiable(T1, T2), N}.

unifiable(Type1, Type2) ->
  List1 = erl_types:t_elements(Type1),
  List2 = erl_types:t_elements(Type2),
  [T || T <- List1,
	lists:all(fun(T1) ->
		      erl_types:t_is_none(erl_types:t_inf(T, T1, opaque))
		  end, List2)].

add_tag_file_line(_Module, {Tag, [B|_R]} = Warn, State)
  when Tag =:= spec_missing;
       Tag =:= invalid_spec;
       Tag =:= callback_missing ->
  {B, Line} = lists:keyfind(B, 1, State#state.behlines),
  {?WARN_BEHAVIOUR, {State#state.filename, Line}, Warn};
add_tag_file_line(Module, {_Tag, [_B, Fun, Arity|_R]} = Warn, State) ->
  {_A, FunCode} =
    dialyzer_codeserver:lookup_mfa_code({Module, Fun, Arity},
					State#state.codeserver),
  Anns = cerl:get_ann(FunCode),
  FileLine = {get_file(Anns), get_line(Anns)},
  {?WARN_BEHAVIOUR, FileLine, Warn}.

get_line([Line|_]) when is_integer(Line) -> Line;
get_line([_|Tail]) -> get_line(Tail);
get_line([]) -> -1.

get_file([{file, File}|_]) -> File;
get_file([_|Tail]) -> get_file(Tail).

%%------------------------------------------------------------------------------

scan_behaviours([], _Codeserver, _Plt, KnownAcc, UnknownAcc) ->
  {KnownAcc, UnknownAcc};
scan_behaviours([M|Rest], Codeserver, Plt, KnownAcc, UnknownAcc) ->
  Tree = dialyzer_codeserver:lookup_mod_code(M, Codeserver),
  Attrs = cerl:module_attrs(Tree),
  {Behaviours, _BehLines} = get_behaviours(Attrs),
  {Known, Unknown} = find_behaviours(Behaviours, Codeserver, Plt),
  scan_behaviours(Rest, Codeserver, Plt,
		  Known ++ KnownAcc, Unknown ++ UnknownAcc).

find_behaviours(Behaviours, Codeserver, Plt) ->
  find_behaviours(Behaviours, Codeserver, Plt, [], []).

find_behaviours([], _Codeserver, _Plt, KnownAcc, UnknownAcc) ->
  {lists:reverse(KnownAcc), lists:reverse(UnknownAcc)};
find_behaviours([Behaviour|Rest], Codeserver, Plt, KnownAcc, UnknownAcc) ->
  Found = 
    case dialyzer_plt:get_callbacks(Behaviour, Plt) of
      [_|_] -> true;
      [] ->
	{_, CBContDict} = dialyzer_codeserver:get_temp_contracts(Codeserver),
	case dict:find(Behaviour, CBContDict) of
	  error -> false;
	  {ok, Dict} ->
	    case dict:to_list(Dict) of
	      [_|_] -> true;
	      []    -> false
	    end
	end
    end,
  case Found of
      false -> find_behaviours(Rest, Codeserver, Plt, 
			       KnownAcc, [Behaviour | UnknownAcc]);
      true  -> find_behaviours(Rest, Codeserver, Plt, 
			       [Behaviour | KnownAcc], UnknownAcc)
  end.

%-------------------------------------------------------------------------------

get_behaviour_apis([], Acc) ->
  Acc;
get_behaviour_apis([Behaviour | Rest], Acc) ->
  MFAs = [{Behaviour, Fun, Arity} ||
	   {{Fun, Arity}, _} <- behaviour_api_calls(Behaviour)],
  get_behaviour_apis(Rest, MFAs ++ Acc).

%-------------------------------------------------------------------------------

nth_or_0(0, _List, Zero) ->
  Zero;
nth_or_0(N, List, _Zero) ->
  lists:nth(N, List).

%-------------------------------------------------------------------------------

behaviour_api_calls(gen_server) ->
  [{{start_link, 3}, {init, 1, [2]}},
   {{start_link, 4}, {init, 1, [3]}},
   {{start, 3}, {init, 1, [2]}},
   {{start, 4}, {init, 1, [3]}},
   {{call, 2}, {handle_call, 3, [2, 0, 0]}},
   {{call, 3}, {handle_call, 3, [2, 0, 0]}},
   {{multi_call, 2}, {handle_call, 3, [2, 0, 0]}},
   {{multi_call, 3}, {handle_call, 3, [3, 0, 0]}},
   {{multi_call, 4}, {handle_call, 3, [3, 0, 0]}},
   {{cast, 2}, {handle_cast, 2, [2, 0]}},
   {{abcast, 2}, {handle_cast, 2, [2, 0]}},
   {{abcast, 3}, {handle_cast, 2, [3, 0]}}];
behaviour_api_calls(_Other) ->
  [].
