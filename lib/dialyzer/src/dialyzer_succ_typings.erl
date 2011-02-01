%% -*- erlang-indent-level: 2 -*-
%%-----------------------------------------------------------------------
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2006-2011. All Rights Reserved.
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
%%% File    : dialyzer_succ_typings.erl
%%% Author  : Tobias Lindahl <tobiasl@it.uu.se>
%%% Description :
%%%
%%% Created : 11 Sep 2006 by Tobias Lindahl <tobiasl@it.uu.se>
%%%-------------------------------------------------------------------
-module(dialyzer_succ_typings).

-export([analyze_callgraph/3,
	 analyze_callgraph/6,
	 analyze_scc_parallel/3,
	 check_fixpoint/4,
	 insert_into_plt_parallel/1,
	 get_warnings/8,
	 get_warnings_from_module_parallel/4,
	 refine_one_module_parallel/3,
	 refine_one_scc_parallel/3]).

%% These are only intended as debug functions.
-export([doit/1, get_top_level_signatures/3]).

%%-define(DEBUG, true).
%%-define(DEBUG_PP, true).

-ifdef(DEBUG).
-define(debug(X__, Y__), io:format(X__, Y__)).
-else.
-define(debug(X__, Y__), ok).
-endif.

%%-define(LOCAL_DEBUG,true).

-ifdef(LOCAL_DEBUG).
-define(ldebug(X__, Y__), io:format(X__, Y__)).
-else.
-define(ldebug(X__, Y__), ok).
-endif.

%%-define(REPORT, true).

-ifdef(REPORT).
-define(report(X__, Y__), io:format(X__, Y__)).
-else.
-define(report(X__, Y__), ok).
-endif.

%%-define(REPORT_TIME, true).

-ifdef(REPORT_TIME).
-define(report_elapsed_time(T1__, T2__, What__),
	begin
	  ElapsedTime = T2__ - T1__,
	  Mins = ElapsedTime div 60000,
	  Secs = (ElapsedTime rem 60000) / 1000,
	  io:format("Completed: ~p  Time: in secs: ~p in mins: ~wm~.2fs\n", 
		    [What__, ElapsedTime / 1000, Mins, Secs])
	end).
-else.
-define(report_elapsed_time(T1__, T2__, What__), ok).
-endif.

-define(TYPE_LIMIT, 4).

%%--------------------------------------------------------------------

-include("dialyzer.hrl").

%%--------------------------------------------------------------------
%% State record -- local to this module

-type parent() :: 'none' | pid().

-record(st, {callgraph          :: dialyzer_callgraph:callgraph(),
	     codeserver         :: dialyzer_codeserver:codeserver(),
	     no_warn_unused     :: set(),
	     parallel           :: boolean(),
	     parent = none      :: parent(),
	     old_plt            :: dialyzer_plt:plt(),
	     plt                :: dialyzer_plt:plt(),
	     fast_plt = false   :: boolean()}).

-type st() :: #st{}.

-export_type([st/0]).

%%--------------------------------------------------------------------

-spec analyze_callgraph(dialyzer_callgraph:callgraph(), dialyzer_plt:plt(),
			dialyzer_codeserver:codeserver()) ->
	 dialyzer_plt:plt().

analyze_callgraph(Callgraph, Plt, Codeserver) ->
  EmptyPlt = dialyzer_plt:new(),
  analyze_callgraph(Callgraph, Plt, EmptyPlt, Codeserver, none, false).

-spec analyze_callgraph(dialyzer_callgraph:callgraph(), dialyzer_plt:plt(),
			dialyzer_plt:plt(), dialyzer_codeserver:codeserver(),
			parent(), boolean()) ->
         dialyzer_plt:plt().

analyze_callgraph(Callgraph, Plt, OldPlt, Codeserver, Parent, Parallel) ->
  State = #st{callgraph = Callgraph, plt = Plt, old_plt = OldPlt, 
	      codeserver = Codeserver, parent = Parent, parallel = Parallel,
          fast_plt = dialyzer_callgraph:get_fast_plt(Callgraph)},
  %% {_T1, _} = statistics(wall_clock),
  true =  dialyzer_coordinator:make_global_st(Callgraph, Codeserver, 
					      Plt, Parallel),
  State2 = get_refined_success_typings(State),
  Plt2 = 
    case Parallel of
      true ->
	dialyzer_coordinator:delete_global_st(Plt);
      false ->
	State2#st.plt
    end,
  {_T2, _} = statistics(wall_clock),
  %% io:format("\nAnalyze callgraph in total ~w\n", [(T2-T1)/1000]),
  Plt2.

%%--------------------------------------------------------------------

get_refined_success_typings(State) ->
  case find_succ_typings(State) of
    {fixpoint, State1} -> 
      State1;
    {not_fixpoint, NotFixpoint1, State1} ->
      Callgraph = State1#st.callgraph,
      NotFixpoint2 = [lookup_name(F, State1) || F <- NotFixpoint1],
      {ModulePostorder, ModuleDigraph} = 
	dialyzer_callgraph:module_postorder_from_funs(NotFixpoint2, Callgraph),
      case refine_succ_typings(ModulePostorder, ModuleDigraph, State1) of
	{fixpoint, State2} ->
	  State2;
	{not_fixpoint, NotFixpoint3, State2} ->
	  Callgraph1 = State2#st.callgraph,
	  %% Need to reset the callgraph.
	  NotFixpoint4 = [lookup_name(F, State2) || F <- NotFixpoint3],
	  Callgraph2 = dialyzer_callgraph:reset_from_funs(NotFixpoint4, 
							  Callgraph1),
	  get_refined_success_typings(State2#st{callgraph = Callgraph2})
      end
  end.

-type doc_plt() :: 'undefined' | dialyzer_plt:plt().
-spec get_warnings(dialyzer_callgraph:callgraph(), dialyzer_plt:plt(),
		   doc_plt(), dialyzer_codeserver:codeserver(), set(),
		   pid(), boolean(), boolean()) ->
	 {[dial_warning()], dialyzer_plt:plt(), doc_plt()}.

get_warnings(Callgraph, Plt, DocPlt, Codeserver,
	     NoWarnUnused, Parent, BehavioursChk, Parallel) ->
  %% {_T1,_} = statistics(wall_clock),
  InitState = #st{callgraph = Callgraph, codeserver = Codeserver,
		  no_warn_unused = NoWarnUnused, parallel = Parallel, 
		  parent = Parent, plt = Plt, old_plt = dialyzer_plt:new(),
		  fast_plt = dialyzer_callgraph:get_fast_plt(Callgraph)},
  true = dialyzer_coordinator:make_global_st(Callgraph, Codeserver, 
					     Plt, Parallel),
  NewState = get_refined_success_typings(InitState),
  Mods = dialyzer_callgraph:modules(NewState#st.callgraph),
  CWarns = dialyzer_contracts:get_invalid_contract_warnings(Mods, Codeserver,
							    NewState#st.plt, 
							    Parallel),
  ?report("Get Warnings from Modules starting......\n", []),
  {_T2, _} = statistics(wall_clock),
  Warnings = get_warnings_from_modules(Mods, NewState, BehavioursChk, 
				       CWarns, Parallel),
  {_T3, _} = statistics(wall_clock),
  ?report_elapsed_time(_T2, _T3, "GetWarnings"),
  Plt1 =
    case Parallel of
      true ->
	dialyzer_coordinator:delete_global_st(Plt);
      false ->
	NewState#st.plt
    end,
  NewDocPlt = insert_into_doc_plt(Mods, Plt1, DocPlt),  
  %% {_T4, _} = statistics(wall_clock),
  %% io:format("\nAnalyze callgraph in total ~w\n", [(_T4-_T1)/1000]),
  {Warnings, Plt1, NewDocPlt}.

get_warnings_from_modules([M|Ms], State, BehavioursChk, Acc, false) 
  when is_atom(M) ->
  {Warnings1, Warnings2, Warnings3} = 
    get_warnings_from_module(M, State, BehavioursChk),
  get_warnings_from_modules(Ms, State, BehavioursChk,
			    [Warnings1, Warnings2, Warnings3|Acc], false);
get_warnings_from_modules([], _State, _, Acc, false) ->
  lists:flatten(Acc);

get_warnings_from_modules(Mods, #st{callgraph = Callgraph, 
				    no_warn_unused = NoWarnUnused,
				    parent = Parent}, 
			  BehavioursChk, CWarns, true) ->
  NewState = #st{callgraph = dialyzer_callgraph:shrink(Callgraph), 
		 no_warn_unused = NoWarnUnused, parallel = true, 
		 parent = Parent},
  dialyzer_coordinator:coordinate_warnings(Mods, NewState, 
					   BehavioursChk, CWarns).

-spec get_warnings_from_module_parallel(module(), st(), boolean(), pid()) -> 'ok'.

get_warnings_from_module_parallel(M, State, BehavioursChk, ServerPid) ->
  {Warnings1, Warnings2, Warnings3} =
    get_warnings_from_module(M, State, BehavioursChk),
  ServerPid ! {warnings, [Warnings1, Warnings2, Warnings3]},
  ok.

get_warnings_from_module(M, State, BehavioursChk) when is_atom(M) ->
  #st{callgraph = Callgraph, codeserver = Codeserver,
      no_warn_unused = NoWarnUnused, plt = Plt, parallel = Parallel,
      parent = Parent} = State,
  send_log(Parent, io_lib:format("Getting warnings for ~w\n", [M])),
  ModCode = dialyzer_codeserver:lookup_mod_code(M, Codeserver, Parallel),
  Records = dialyzer_codeserver:lookup_mod_records(M, Codeserver, Parallel),
  Contracts = dialyzer_codeserver:lookup_mod_contracts(M, Codeserver, Parallel),
  AllFuns = collect_fun_info([ModCode]),
  %% Check if there are contracts for functions that do not exist
  Warnings1 = 
    dialyzer_contracts:contracts_without_fun(Contracts, AllFuns, Callgraph, 
					     Parallel),
  Warnings2 =
    dialyzer_dataflow:get_warnings(ModCode, Plt, Callgraph, Records, 
				   NoWarnUnused, Parallel),
  Attrs = cerl:module_attrs(ModCode),
  Warnings3 = if BehavioursChk ->
		  dialyzer_behaviours:check_callbacks(M, Attrs, Plt, 
						      Codeserver, Parallel);
		 true -> []
	      end,
  {Warnings1, Warnings2, Warnings3}.

refine_succ_typings(ModulePostorder, ModuleDigraph, 
		    #st{parallel = Parallel, parent = Parent, 
			callgraph = Callgraph} = State) ->
  ?report("Refine Success Typings starting......\n", []),
  {_T1, _} = statistics(wall_clock),
  A =
    case Parallel of
      true ->
	LightCallgraph = dialyzer_callgraph:shrink(Callgraph),
	case dialyzer_coordinator:coordinate_refine(ModuleDigraph,
						    LightCallgraph,
						    Parent) of
	  fixpoint -> {fixpoint, State};
	  {not_fixpoint, NotFixpoint} -> {not_fixpoint, NotFixpoint, State}
	end;
      false->
	?debug("Module postorder: ~p\n", [ModulePostorder]),
	refine_succ_typings_serial(ModulePostorder, State, [])
    end,
  {_T2, _} = statistics(wall_clock),
  ?report_elapsed_time(_T1, _T2, "Refine success typings"),
  A.

refine_succ_typings_serial([SCC|SCCs], State, Fixpoint) ->
  Msg = io_lib:format("Dataflow of one SCC: ~w\n", [SCC]),
  send_log(State#st.parent, Msg),
  ?ldebug("~s", [Msg]),
  case SCC of
    [M] ->  
      {ReachedFixpoint, NewFixpoint} = refine_one_module(M, State),
      FixpointFromScc = ordsets:from_list([FunLbl || 
					    {FunLbl,_Type} <- NewFixpoint]),
      NewState = 
	case ReachedFixpoint of
	  false ->
	    insert_into_plt(NewFixpoint, State);
	  true ->
	    State
	end;
    [_|_] -> 
      {NewState, FixpointFromScc} = refine_one_scc(SCC, State)
  end,
  NewFixpoint2 = ordsets:union(Fixpoint, FixpointFromScc),
  refine_succ_typings_serial(SCCs, NewState, NewFixpoint2);
refine_succ_typings_serial([], State, Fixpoint) ->
  case Fixpoint =:= [] of
    true -> {fixpoint, State};
    false -> {not_fixpoint, Fixpoint, State}
  end.

-spec refine_one_module_parallel(module(), dialyzer_callgraph:callgraph(), 
				 pid()) -> 'ok'.

refine_one_module_parallel(M, Callgraph, ServerPid) ->
  State = #st{callgraph = Callgraph, parallel = true},
  Msg = case refine_one_module(M, State) of
	  {true, []} ->
	    {true, [M], ordsets:new()};
	  {false, NotFixpoint} ->
	    Lbls = [FunLbl || {FunLbl,_Type} <- NotFixpoint],
	    {false, [M], NotFixpoint, ordsets:from_list(Lbls)}
	end,
  ServerPid ! Msg,
  ok.

-spec refine_one_scc_parallel(dialyzer_callgraph:scc(), 
			      dialyzer_callgraph:callgraph(), pid()) -> 'ok'.
			     
refine_one_scc_parallel(SCC, Callgraph, ServerPid) ->
  State = #st{callgraph = Callgraph, parallel = true},
  {_NewState, FixpointFromScc} = refine_one_scc(SCC, State),
  ServerPid ! {true, SCC, FixpointFromScc},
  ok.

refine_one_module(M, State) ->
  #st{callgraph = Callgraph, codeserver = CodeServer,
      parallel = Parallel, plt = PLT} = State,
  ModCode = dialyzer_codeserver:lookup_mod_code(M, CodeServer, Parallel),
  AllFuns = collect_fun_info([ModCode]),
  FunTypes = get_fun_types_from_plt(AllFuns, State),
  Records = dialyzer_codeserver:lookup_mod_records(M, CodeServer, Parallel),
  NewFunTypes =
    dialyzer_dataflow:get_fun_types(ModCode, PLT, Callgraph, Records, Parallel),
  case reached_fixpoint(FunTypes, NewFunTypes) of
    true ->
      {true, ordsets:new()};
    {false, NotFixpoint} ->
      ?debug("Not fixpoint\n", []),
      {false, NotFixpoint}
  end.

refine_one_scc(SCC, State) ->
  refine_one_scc(SCC, State, []).

refine_one_scc(SCC, State, AccFixpoint) ->
  {NewState, FixpointFromScc} = refine_mods_in_scc(SCC, State, []),
  case FixpointFromScc =:= [] of
    true -> {NewState, AccFixpoint};
    false ->
      NewAccFixpoint = ordsets:union(AccFixpoint, FixpointFromScc),
      refine_one_scc(SCC, NewState, NewAccFixpoint)
  end.

refine_mods_in_scc([Mod|Mods], State, Fixpoint) ->
  {ReachedFixpoint, NewFixpoint} = refine_one_module(Mod, State),
  NewState = 
    case ReachedFixpoint of
      false ->
	insert_into_plt(NewFixpoint, State);
      true ->
	State
    end,
  FixpointFromModule = ordsets:from_list([FunLbl || 
					   {FunLbl,_Type} <- NewFixpoint]),
  NewFixpoint2 = ordsets:union(FixpointFromModule, Fixpoint),
  refine_mods_in_scc(Mods, NewState, NewFixpoint2);
refine_mods_in_scc([], State, Fixpoint) ->
  {State, Fixpoint}.

reached_fixpoint(OldTypes, NewTypes) ->
  reached_fixpoint(OldTypes, NewTypes, false).

reached_fixpoint_strict(OldTypes, NewTypes) ->
  case reached_fixpoint(OldTypes, NewTypes, true) of
    true -> true;
    {false, _} -> false
  end.

reached_fixpoint(OldTypes0, NewTypes0, Strict) ->
  MapFun = fun(_Key, Type) ->
	       case is_failed_or_not_called_fun(Type) of
		 true -> failed_fun;
		 false -> erl_types:t_limit(Type, ?TYPE_LIMIT)
	       end
	   end,
  OldTypes = dict:map(MapFun, OldTypes0),
  NewTypes = dict:map(MapFun, NewTypes0),
  compare_types(OldTypes, NewTypes, Strict).

is_failed_or_not_called_fun(Type) ->
  erl_types:any_none([erl_types:t_fun_range(Type)|erl_types:t_fun_args(Type)]).

compare_types(Dict1, Dict2, Strict) ->
  List1 = lists:keysort(1, dict:to_list(Dict1)),
  List2 = lists:keysort(1, dict:to_list(Dict2)),
  compare_types_1(List1, List2, Strict, []).

compare_types_1([{X, _Type1}|Left1], [{X, failed_fun}|Left2],
		Strict, NotFixpoint) ->
  compare_types_1(Left1, Left2, Strict, NotFixpoint);
compare_types_1([{X, failed_fun}|Left1], [{X, _Type2}|Left2],
		Strict, NotFixpoint) ->
  compare_types_1(Left1, Left2, Strict, NotFixpoint);
compare_types_1([{X, Type1}|Left1], [{X, Type2}|Left2], Strict, NotFixpoint) ->
  Res = case Strict of
	  true -> erl_types:t_is_equal(Type1, Type2);
	  false -> erl_types:t_is_subtype(Type1, Type2, opaque)
	end,
  case Res of
    true -> compare_types_1(Left1, Left2, Strict, NotFixpoint);
    false -> compare_types_1(Left1, Left2, Strict, [{X, Type2}|NotFixpoint])
  end;
compare_types_1([_|Left1], List2, Strict, NotFixpoint) ->
  %% If the function was not called.
  compare_types_1(Left1, List2, Strict, NotFixpoint);
compare_types_1([], [], _Strict, NotFixpoint) ->
  case NotFixpoint =:= [] of
    true -> true;
    false -> {false, NotFixpoint}
  end.

find_succ_typings(#st{callgraph = Callgraph, parallel = Parallel, 
		      parent = Parent} = State) ->
  ?report("Find Success Typings starting...\n", []),
  {_T1, _} = statistics(wall_clock),
  Q =
    case Parallel of
      true ->
	case dialyzer_coordinator:coordinate_find(Callgraph, Parent) of
	  fixpoint -> {fixpoint, State};
	  {not_fixpoint, NotFixpoint} -> {not_fixpoint, NotFixpoint, State}
	end;
      false ->
	find_succ_typings(State, [])
    end,
  {_T2, _} = statistics(wall_clock),
  ?report_elapsed_time(_T1, _T2, "Find success typings"),
  Q.

find_succ_typings(#st{callgraph = Callgraph, parent = Parent, 
		      fast_plt = Fast} = State,
		  NotFixpoint) ->
  case dialyzer_callgraph:take_scc(Callgraph) of
    {ok, SCC, NewCallgraph} ->
      Msg = io_lib:format("Typesig analysis for SCC: ~w\n", [format_scc(SCC)]),
      send_log(Parent, Msg),
      {SuccTypes, PltContracts, NewNotFixpoint1, State0} =
  	analyze_scc(SCC, State#st{callgraph = NewCallgraph}, Fast),
      State1 = insert_into_plt(SuccTypes, State0),
      ContrPlt = dialyzer_plt:insert_contract_list(State1#st.plt, PltContracts),
      NewState = State1#st{plt = ContrPlt},
      NewNotFixpoint2 = ordsets:union(NewNotFixpoint1, NotFixpoint),
      find_succ_typings(NewState, NewNotFixpoint2);
    none ->
      ?ldebug("\n==================== Typesig done ====================\n", []),
      case check_fixpoint(NotFixpoint, Callgraph, Fast, false) of
	true  -> {fixpoint, State};
	false -> {not_fixpoint, NotFixpoint, State}
      end
  end.
 
-spec check_fixpoint(ordset(_), dialyzer_callgraph:callgraph() | 'undefined',
		     boolean(), boolean()) -> boolean().

check_fixpoint(Fixpoint, Callgraph, Fast, Parallel) ->
  case Fast of
    false -> Fixpoint =:= [];
    true  -> has_escaping(Fixpoint, Callgraph, Parallel)
  end.

has_escaping([Label|Rest], Callgraph, Parallel) ->
  case dialyzer_callgraph:is_escaping(Label, Callgraph, Parallel) of
    true -> true;
    false -> has_escaping(Rest, Callgraph, Parallel)
  end;
has_escaping([], _Callgraph, _Parallel) ->
  false.

-spec analyze_scc_parallel(dialyzer_callgraph:scc(), pid(), boolean()) -> 'ok'. 

analyze_scc_parallel(SCC, ServerPid, Fast) ->
  {_T1, _} = statistics(wall_clock),
  {SuccTypes, PltContracts, NotFixpoint, _NewState} = 
    analyze_scc(SCC, #st{parallel = true}, Fast),
  {_T2, _} = statistics(wall_clock),
  %% ?report_elapsed_time(_T1, _T2, SCC),
  ServerPid ! {results, SCC, SuccTypes, PltContracts, NotFixpoint},
  ok.

analyze_scc(SCC, #st{callgraph = Callgraph,
		     parallel = Parallel} = State, true) ->
  NeedAnalysis = dialyzer_callgraph:need_analysis(SCC, Callgraph, Parallel),
  fast_analyze_scc(SCC, State, NeedAnalysis);
analyze_scc(SCC, State, false) ->
  {SuccTypes, PltContracts, NotFixpoint, _AllFuns} = 
    slow_analyze_scc(SCC, State),
  {dict:to_list(SuccTypes), PltContracts, NotFixpoint, State}. 

slow_analyze_scc(SCC, #st{codeserver = Codeserver, 
			  parallel = Parallel} = State) ->
  MO = lists:usort([M || {M,_,_} <- SCC]),
  ModRecords = [{M, dialyzer_codeserver:lookup_mod_records(M, Codeserver, 
							   Parallel)}
		|| M <- MO],
  ModRecDict = dict:from_list(ModRecords),
  SCC_Info = [{MFA,
	       dialyzer_codeserver:lookup_mfa_code(MFA, Codeserver, Parallel),
	       dict:fetch(M, ModRecDict)}
	      || {M, _, _} = MFA <- SCC],
  Contracts1 = [{MFA, dialyzer_codeserver:lookup_mfa_contract(MFA, Codeserver, 
							      Parallel)}
 		|| {_, _, _} = MFA <- SCC],
  Contracts2 = [{MFA, Contract} || {MFA, {ok, Contract}} <- Contracts1],
  Contracts3 = orddict:from_list(Contracts2),
  find_succ_types_for_scc(SCC_Info, Contracts3, State).

fast_analyze_scc(SCC, #st{callgraph= Callgraph, parallel = Parallel} = State, 
		 true) ->
  {SuccTypes, PltContracts, NotFixpoint2, AllFuns} = 
    slow_analyze_scc(SCC, State),
  {NewCallgraph, NotFixpoint} =
    case differ_from_old_plt(AllFuns, State, SuccTypes) of
      true  ->
	?ldebug("changed",[]),
	{dialyzer_callgraph:changed(SCC, Callgraph, Parallel), NotFixpoint2};
      false ->
	?ldebug("unchanged",[]),
	{Callgraph, []}
    end,
  NewState = State#st{callgraph = NewCallgraph},
  {dict:to_list(SuccTypes), PltContracts, NotFixpoint, NewState}; 
fast_analyze_scc(SCC, State, false) ->
  ?ldebug("\n~p: ",[SCC]),
  ?ldebug("Skipped",[]),
  OldTypes = get_old_succ_types(SCC, State),
  PltContracts = get_old_plt_contracts(SCC, State),
  %% State1 =
  %%  State#st{plt = dialyzer_plt:insert_list(State#st.plt, OldTypes)},
  {OldTypes, PltContracts, [], State}. 

get_old_succ_types(SCC, #st{parallel = Parallel, old_plt = Plt}) ->
  get_old_succ_types(SCC, Plt, Parallel, []).

get_old_succ_types([SCC|Rest], Plt, Parallel, Acc) ->
  case dialyzer_plt:lookup_old(Plt, SCC, Parallel) of
    none ->
      get_old_succ_types(Rest, Plt, Parallel, Acc);
    {value, {_RetT, _ArgT} = Type} ->
      get_old_succ_types(Rest, Plt, Parallel, [{SCC, Type}|Acc])
  end;
get_old_succ_types([], _Plt, _Parallel, Acc) ->
  Acc.

get_old_plt_contracts(SCC, #st{parallel = Parallel, old_plt = Plt}) ->
  get_old_plt_contracts(SCC, Plt, Parallel, []).

get_old_plt_contracts([{_M,_F,_A} = SCC|Rest], Plt, Parallel, Acc) ->
  case dialyzer_plt:lookup_old_contract(Plt, SCC, Parallel) of
    {value, Contract} ->
      get_old_plt_contracts(Rest, Plt, Parallel, [{SCC, Contract}|Acc]);
    none ->
      get_old_plt_contracts(Rest, Plt, Parallel, Acc)
  end;
get_old_plt_contracts([_SCC|Rest], Plt, Parallel, Acc) ->
  get_old_plt_contracts(Rest, Plt, Parallel, Acc);
get_old_plt_contracts([], _Plt, _Parallel, Acc) ->
  Acc.

find_succ_types_for_scc(SCC_Info, Contracts, #st{codeserver = Codeserver,
						 callgraph = Callgraph, 
						 parallel = Parallel, 
						 plt = Plt} = State) ->
  %% Assume that the PLT contains the current propagated types
  AllFuns = collect_fun_info([Fun || {_MFA, {_Var, Fun}, _Rec} <- SCC_Info]),
  PropTypes = get_fun_types_from_plt(AllFuns, State),
  MFAs = [MFA || {MFA, {_Var, _Fun}, _Rec} <- SCC_Info],
  NextLabel = dialyzer_codeserver:get_next_core_label(Codeserver, Parallel),
  FunTypes = dialyzer_typesig:analyze_scc(SCC_Info, NextLabel, Callgraph, 
					  Plt, PropTypes, MFAs ,Parallel),
  AllFunSet = sets:from_list([X || {X, _} <- AllFuns]),
  FilteredFunTypes = dict:filter(fun(X, _) ->
				      sets:is_element(X, AllFunSet)
				  end, FunTypes),
  %% Check contracts
  PltContracts = dialyzer_contracts:check_contracts(Contracts, Callgraph,
						    FilteredFunTypes, Parallel),
  ContractFixpoint =
    lists:all(fun({MFA, _C}) ->
		  %% Check the non-deleted PLT
		  case dialyzer_plt:lookup_contract(Plt, MFA, Parallel) of
		    none -> false;
		    {value, _} -> true
		  end
	      end, PltContracts),
  case (ContractFixpoint andalso
	reached_fixpoint_strict(PropTypes, FilteredFunTypes)) of
    true ->
      {FilteredFunTypes, PltContracts, ordsets:new(), AllFuns};
    false ->
      {FilteredFunTypes, PltContracts,
       ordsets:from_list([Fun || {Fun, _Arity} <- AllFuns]), AllFuns}
  end.

differ_from_old_plt(AllFuns, State, NewTypes) ->
  OldTypes = get_fun_types_from_old_plt(AllFuns, State),
  not reached_fixpoint_strict(OldTypes, NewTypes).

get_fun_types_from_old_plt(FunList, State) ->
  get_fun_types_from_old_plt(FunList, State, dict:new()).

get_fun_types_from_old_plt([{FunLabel, Arity}|Left], State, Map) ->
  Type = lookup_old_fun_type(FunLabel, Arity, State),
  get_fun_types_from_old_plt(Left, State, dict:store(FunLabel, Type, Map));
get_fun_types_from_old_plt([], _State, Map) ->
  Map.

get_fun_types_from_plt(FunList, State) ->
  get_fun_types_from_plt(FunList, State, dict:new()).

get_fun_types_from_plt([{FunLabel, Arity}|Left], State, Map) ->
  Type = lookup_fun_type(FunLabel, Arity, State),
  get_fun_types_from_plt(Left, State, dict:store(FunLabel, Type, Map));
get_fun_types_from_plt([], _State, Map) ->
  Map.

collect_fun_info(Trees) ->
  collect_fun_info(Trees, []).

collect_fun_info([Tree|Trees], List) ->
  Fun = fun(SubTree, Acc) ->
	    case cerl:is_c_fun(SubTree) of
	      true ->
		[{cerl_trees:get_label(SubTree), cerl:fun_arity(SubTree)}|Acc];
	      false -> Acc
	    end
	end,
  collect_fun_info(Trees, cerl_trees:fold(Fun, List, Tree));
collect_fun_info([], List) ->
  List.

lookup_fun_type(Label, Arity, #st{parallel = Parallel, plt = Plt} = State) ->
  ID = lookup_name(Label, State),
  case dialyzer_plt:lookup(Plt, ID, Parallel) of
    none -> erl_types:t_fun(Arity, erl_types:t_any());
    {value, {RetT, ArgT}} -> erl_types:t_fun(ArgT, RetT)
  end.

lookup_old_fun_type(Label, Arity, #st{parallel = Parallel, 
				      old_plt = Plt} = State) ->
  ID = lookup_name(Label, State),
  case dialyzer_plt:lookup_old(Plt, ID, Parallel) of
    none -> erl_types:t_fun(Arity, erl_types:t_any());
    {value, {RetT, ArgT}} -> erl_types:t_fun(ArgT, RetT)
  end.

insert_into_doc_plt(_M, _Plt, undefined) ->
  undefined;
insert_into_doc_plt([], _Plt, DocPlt) ->
  DocPlt;
insert_into_doc_plt([M|Ms], Plt, DocPlt) ->
  case dialyzer_plt:lookup_module(Plt, M) of
    {value, List} ->
      SuccTypes = [{MFA, {Ret, Args}} || {{_M,F,_A} = MFA, Ret, Args} <- List,
					 F =/= 'module_info'],
      NewDocPlt = dialyzer_plt:insert_list(DocPlt, SuccTypes),
      insert_into_doc_plt(Ms, Plt, NewDocPlt);
    none ->
      insert_into_doc_plt(Ms, Plt, DocPlt)
  end.

-spec insert_into_plt_parallel([{label(), erl_types:erl_type()}]) -> 'ok'.
			 
insert_into_plt_parallel(SuccTypes) ->
  _ = insert_into_plt(SuccTypes, #st{parallel = true}),
  ok.
      
insert_into_plt(SuccTypes0, #st{parallel = Parallel, plt = Plt} = State) ->
  SuccTypes = format_succ_types(SuccTypes0, State),
  debug_pp_succ_typings(SuccTypes),
  State#st{plt = dialyzer_plt:insert_list(Plt, SuccTypes, Parallel)}.

format_succ_types(SuccTypes, State) ->
  format_succ_types(SuccTypes, State, []).

format_succ_types([{Label, Type0}|Left], State, Acc) ->
  Type = erl_types:t_limit(Type0, ?TYPE_LIMIT+1),
  Id = lookup_name(Label, State),
  NewTuple = {Id, {erl_types:t_fun_range(Type), erl_types:t_fun_args(Type)}},
  format_succ_types(Left, State, [NewTuple|Acc]);
format_succ_types([], _State, Acc) ->
  Acc.

-ifdef(DEBUG).
debug_pp_succ_typings(SuccTypes) ->
  ?debug("Succ typings:\n", []),
  [?debug("  ~w :: ~s\n",
	  [MFA, erl_types:t_to_string(erl_types:t_fun(ArgT, RetT))])
   || {MFA, {RetT, ArgT}} <- SuccTypes],
  ?debug("Contracts:\n", []),
  [?debug("  ~w :: ~s\n",
	  [MFA, erl_types:t_to_string(erl_types:t_fun(ArgT, RetFun(ArgT)))])
   || {MFA, {contract, RetFun, ArgT}} <- SuccTypes],
  ?debug("\n", []),
  ok.
-else.
debug_pp_succ_typings(_) ->
  ok.
-endif.

lookup_name(F, #st{callgraph = CG, parallel = Parallel}) ->
  case dialyzer_callgraph:lookup_name(F, CG, Parallel) of
    error -> F;
    {ok, Name} -> Name
  end.

send_log(none, _Msg) ->
  ok;
send_log(Parent, Msg) ->
  Parent ! {self(), log, lists:flatten(Msg)},
  ok.

format_scc(SCC) ->
  [MFA || {_M, _F, _A} = MFA <- SCC].

%% ============================================================================
%%
%%  Debug interface.
%%
%% ============================================================================

-spec doit(atom() | file:filename()) -> 'ok'.

doit(Module) ->
  {ok, AbstrCode} = dialyzer_utils:get_abstract_code_from_src(Module),
  {ok, Code} = dialyzer_utils:get_core_from_abstract_code(AbstrCode),
  {ok, Records} = dialyzer_utils:get_record_and_type_info(AbstrCode),
  %% contract typing info in dictionary format
  {ok, Contracts} =
    dialyzer_utils:get_spec_info(cerl:concrete(cerl:module_name(Code)),
                                 AbstrCode, Records),
  Sigs0 = get_top_level_signatures(Code, Records, Contracts),
  M = if is_atom(Module) ->
	  list_to_atom(filename:basename(atom_to_list(Module)));
	 is_list(Module) ->
	  list_to_atom(filename:basename(Module))
      end,
  Sigs1 = [{{M, F, A}, Type} || {{F, A}, Type} <- Sigs0],
  Sigs = ordsets:from_list(Sigs1),
  io:format("==================== Final result ====================\n\n", []),
  pp_signatures(Sigs, Records),
  ok.

-spec get_top_level_signatures(cerl:c_module(), dict(), dict()) ->
	 [{{atom(), arity()}, erl_types:erl_type()}].

get_top_level_signatures(Code, Records, Contracts) ->
  Tree = cerl:from_records(Code),
  {LabeledTree, NextLabel} = cerl_trees:label(Tree),
  Plt = get_def_plt(),
  ModuleName = cerl:atom_val(cerl:module_name(LabeledTree)),
  Plt1 = dialyzer_plt:delete_module(Plt, ModuleName),
  Plt2 = analyze_module(LabeledTree, NextLabel, Plt1, Records, Contracts),
  M = cerl:concrete(cerl:module_name(Tree)),
  Functions = [{M, cerl:fname_id(V), cerl:fname_arity(V)}
	       || {V, _F} <- cerl:module_defs(LabeledTree)],
  %% First contracts check
  AllContracts = dict:fetch_keys(Contracts),
  ErrorContracts = AllContracts -- Functions,
  lists:foreach(fun(C) ->
		    io:format("Contract for non-existing function: ~w\n",[C])
		end, ErrorContracts),
  Types = [{MFA, dialyzer_plt:lookup(Plt2, MFA)} || MFA <- Functions],
  Sigs = [{{F, A}, erl_types:t_fun(ArgT, RetT)}
	  || {{_M, F, A}, {value, {RetT, ArgT}}} <- Types],
  ordsets:from_list(Sigs).

get_def_plt() ->
  try
    dialyzer_plt:from_file(dialyzer_plt:get_default_plt())
  catch
    error:no_such_file -> dialyzer_plt:new();
    throw:{dialyzer_error, _} -> dialyzer_plt:new()
  end.

pp_signatures([{{_, module_info, 0}, _}|Left], Records) ->
  pp_signatures(Left, Records);
pp_signatures([{{_, module_info, 1}, _}|Left], Records) ->
  pp_signatures(Left, Records);
pp_signatures([{{M, F, _A}, Type}|Left], Records) ->
  TypeString =
    case cerl:is_literal(Type) of
%% Commented out so that dialyzer does not complain
%%      false ->
%%        "fun(" ++ String = erl_types:t_to_string(Type, Records),
%%        string:substr(String, 1, length(String)-1);
      true ->
	io_lib:format("~w", [cerl:concrete(Type)])
    end,
  io:format("~w:~w~s\n", [M, F, TypeString]),
  pp_signatures(Left, Records);
pp_signatures([], _Records) ->
  ok.

-ifdef(DEBUG_PP).
debug_pp(Tree, _Map) ->
  Tree1 = strip_annotations(Tree),
  io:put_chars(cerl_prettypr:format(Tree1)),
  io:nl().

strip_annotations(Tree) ->
  cerl_trees:map(fun(T) ->
		     case cerl:is_literal(T) orelse cerl:is_c_values(T) of
		       true -> cerl:set_ann(T, []);
		       false ->
			 Label = cerl_trees:get_label(T),
			 cerl:set_ann(T, [{'label', Label}])
		     end
		 end, Tree).
-else.
debug_pp(_Tree, _Map) ->
  ok.
-endif. % DEBUG_PP

%%
%% Analysis of a single module
%%
analyze_module(LabeledTree, NextLbl, Plt, Records, Contracts) ->
  debug_pp(LabeledTree, dict:new()),
  CallGraph1 = dialyzer_callgraph:new(),
  CallGraph2 = dialyzer_callgraph:scan_core_tree(LabeledTree, CallGraph1),
  {CallGraph3, _Ext} = dialyzer_callgraph:remove_external(CallGraph2),
  CallGraph4 = dialyzer_callgraph:finalize(CallGraph3),
  CodeServer1 = dialyzer_codeserver:new(),
  Mod = cerl:concrete(cerl:module_name(LabeledTree)),
  CodeServer2 = dialyzer_codeserver:insert(Mod, LabeledTree, CodeServer1),
  CodeServer3 = dialyzer_codeserver:set_next_core_label(NextLbl, CodeServer2),
  CodeServer4 = dialyzer_codeserver:store_records(Mod, Records, CodeServer3),
  CodeServer5 = dialyzer_codeserver:store_contracts(Mod, Contracts, CodeServer4),
  Res = analyze_callgraph(CallGraph4, Plt, CodeServer5),
  dialyzer_callgraph:delete(CallGraph4),
  dialyzer_codeserver:delete(CodeServer5),
  Res.
