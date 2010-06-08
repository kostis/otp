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
	 get_registering_apis/1,
	 scan_behaviours/3,
	 translatable_behaviours/0,
	 translate_behaviour_api_call/5,
	 translate_callgraph/3]).

-export_type([behaviour/0, behaviour_api_dict/0]).

-define(TRANSLATABLE_BEHAVIOURS, [gen_server]).

%%--------------------------------------------------------------------

-include("dialyzer.hrl").

%%--------------------------------------------------------------------

-type behaviour() :: atom().

-record(state, {plt        :: dialyzer_plt:plt(),
		codeserver :: dialyzer_codeserver:codeserver(),
		filename   :: file:filename(),
		behlines   :: [{behaviour(), non_neg_integer()}]}).

%%--------------------------------------------------------------------

-spec scan_behaviours([module()], dialyzer_codeserver:codeserver(),
                      dialyzer_plt:plt()) ->
  {[behaviour()], [behaviour()]}.

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

-spec translatable_behaviours() -> behaviour_api_dict().

translatable_behaviours() ->
  [{B, Calls} || B <- ?TRANSLATABLE_BEHAVIOURS, 
		 (Calls = behaviour_api_calls(B)) =/= []].

-spec get_behaviour_apis([behaviour()]) -> [mfa()].

get_behaviour_apis(Behaviours) ->
  get_behaviour_apis(Behaviours, []).

-spec translate_behaviour_api_call(dialyzer_races:mfa_or_funlbl(),
				   [erl_types:erl_type()],
				   [dialyzer_races:core_vars()],
				   behaviour_api_dict(),
				   [{atom(), module()}]) ->
				      {{dialyzer_races:mfa_or_funlbl(),
					[erl_types:erl_type()],
					[dialyzer_races:core_vars()]},
				       [{atom(), module()}]}
					| 'plain_call'.

translate_behaviour_api_call(_Fun, _ArgTypes, _Args, [], _CallbackAssocs) ->
  plain_call;
translate_behaviour_api_call({Module, Fun, Arity}, ArgTypes, Args,
			     BehApiInfo, CallbackAssocs) ->
%  io:format("\nCheck:~p",[{Module, Fun, Arity}]),
  CA = CallbackAssocs,
  Query =
  case lists:keyfind(Module, 1, BehApiInfo) of
    false -> plain_call;
    {Module, Calls} ->
      case lists:keyfind({Fun, Arity}, 1, Calls) of
	false -> plain_call;
	{{Fun, Arity}, TranslationInfo, Directive} ->
	  TI = TranslationInfo,
	  case Directive of
	    {create, no, _} -> plain_call;
	    {create,  N, M} ->
	      case cerl:concrete(nth_or_0(M, Args, foo)) of
		CallbackModule when is_atom(CallbackModule) ->
		  CM = CallbackModule,
		  case cerl:concrete(nth_or_0(N, Args, foo)) of
		    {_,Name} when is_atom(Name) -> {CM, TI, [{Name,CM}|CA]};
		    Name when is_atom(Name)     -> {CM, TI, [{Name,CM}|CA]};
		    _                           -> plain_call
		  end;
		_ -> plain_call
	      end;
	    {refer, N} ->
	      case CA of
		[] -> plain_call;
		 _ ->
		  case cerl:concrete(nth_or_0(N, Args, foo)) of
		    Name when is_atom(Name) ->
		      case lists:keyfind(Name,1,CA) of
			{_,CM} -> {CM, TI, CA};
			false  -> plain_call
		      end;
		    _ -> plain_call
		  end
	      end
	  end
      end
  end,
  case Query of
    plain_call -> Query;
    {Callback, {CFun, CArity, COrder}, NewCallbackAssocs} ->
      Call = {{Callback, CFun, CArity},
	      [nth_or_0(N, ArgTypes, erl_types:t_any()) || N <-COrder],
	      [nth_or_0(N, Args, bypassed) || N <-COrder]},
%      io:format("\nTranslation: ~p",[Call]),
      {Call, NewCallbackAssocs}
  end;
translate_behaviour_api_call(_Fun, _ArgTypes, _Args, _BehApiInfo,
			     _CallbackAssocs) ->
  plain_call.

-spec translate_callgraph(behaviour_api_dict(), atom(),
			  dialyzer_callgraph:callgraph()) ->
			     dialyzer_callgraph:callgraph().

translate_callgraph([{Behaviour,_}|Behaviours], Module, Callgraph) ->
  UsedCalls = [Call || {_From, {M, _F, _A}} = Call <-
			 dialyzer_callgraph:get_behaviour_api_calls(Callgraph),
		       M =:= Behaviour],
  Calls = [{{Behaviour, API, Arity}, Callback} ||
	    {{API, Arity}, Callback, _} <- behaviour_api_calls(Behaviour)],
  DirectCalls = [{From, {Module, Fun, Arity}} ||
		  {From, To} <- UsedCalls,{API, {Fun, Arity, _Ord}} <- Calls,
		  To =:= API],
  NewCallgraph = dialyzer_callgraph:add_behaviour_edges(DirectCalls, Callgraph),
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

%%-----------------------------------------------------------------------------

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

%------------------------------------------------------------------------------

get_behaviour_apis([], Acc) ->
  Acc;
get_behaviour_apis([Behaviour | Rest], Acc) ->
  MFAs = [{Behaviour, Fun, Arity} ||
	   {{Fun, Arity}, _, _} <- behaviour_api_calls(Behaviour)],
  get_behaviour_apis(Rest, MFAs ++ Acc).

%------------------------------------------------------------------------------

nth_or_0(0, _List, Zero) ->
  Zero;
nth_or_0(N, List, _Zero) ->
  lists:nth(N, List).

%------------------------------------------------------------------------------
-spec get_registering_apis(behaviour_api_dict()) -> [mfa()].

get_registering_apis(BehApiDict) ->
  get_registering_apis(BehApiDict, []).

get_registering_apis([{Behaviour, APIInfo}|Rest], Acc) ->
  NewRegAPIs = [{Behaviour, Fun, Arity} ||
		 {{Fun, Arity}, _, {create, N, _}} <- APIInfo,
		 is_integer(N)],
  get_registering_apis(Rest, NewRegAPIs ++ Acc);
get_registering_apis([], Acc) -> Acc.

%------------------------------------------------------------------------------
-type behaviour_api_dict()::[{behaviour(), behaviour_api_info()}].
-type behaviour_api_info()::[{original_fun(), replacement_fun(), directive()}].
-type original_fun()::{atom(), arity()}.
-type replacement_fun()::{atom(), arity(), arg_list()}.
-type directive()::{'create', name_arg(), callback_module_arg()} |
		   {'refer', name_arg()}.
-type arg_list()::[original_fun_arg()].
-type name_arg()::'no' | original_fun_arg().
-type callback_module_arg()::original_fun_arg().
-type original_fun_arg()::byte().

-spec behaviour_api_calls(behaviour()) -> behaviour_api_info().

behaviour_api_calls(gen_server) ->
  [{{start_link, 3}, {init, 1, [2]}, {create, no, 1}},
   {{start_link, 4}, {init, 1, [3]}, {create, 1, 2}},
   {{start, 3}, {init, 1, [2]}, {create, no, 1}},
   {{start, 4}, {init, 1, [3]}, {create, 1, 2}},
   {{call, 2}, {handle_call, 3, [2, 0, 0]}, {refer, 1}},
   {{call, 3}, {handle_call, 3, [2, 0, 0]}, {refer, 1}},
   {{multi_call, 2}, {handle_call, 3, [2, 0, 0]}, {refer, 1}},
   {{multi_call, 3}, {handle_call, 3, [3, 0, 0]}, {refer, 2}},
   {{multi_call, 4}, {handle_call, 3, [3, 0, 0]}, {refer, 2}},
   {{cast, 2}, {handle_cast, 2, [2, 0]}, {refer, 1}},
   {{abcast, 2}, {handle_cast, 2, [2, 0]}, {refer, 1}},
   {{abcast, 3}, {handle_cast, 2, [3, 0]}, {refer, 2}}];
behaviour_api_calls(_Other) ->
  [].
