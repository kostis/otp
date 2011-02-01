%% -*- erlang-indent-level: 2 -*-
%%----------------------------------------------------------------------
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2011. All Rights Reserved.
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
%%%---------------------------------------------------------------------
%%% File        : dialyzer_coordinator.erl
%%% Authors     : Ypatia Tsavliri <ypatia.tsav@gmail.com>
%%% Description : This module coordinates parallel dialyzer.
%%% Created     : 23 Jun 2010 by Ypatia Tsavliri <ypatia.tsav@gmail.com>
%%%---------------------------------------------------------------------

-module(dialyzer_coordinator).

-export([coordinate_find/2,
	 coordinate_refine/3,
	 coordinate_warnings/4,
	 make_global_st/4,
	 delete_global_st/1]).

-include("dialyzer.hrl").

%%----------------------------------------------------------------------

-spec coordinate_find(dialyzer_callgraph:callgraph(), pid()) ->
	 'fixpoint' | {'not_fixpoint', ordset(label())}.

coordinate_find(Callgraph, Parent) ->
  Fast = dialyzer_callgraph:get_fast_plt(Callgraph),
  Digraph = dialyzer_callgraph:get_digraph2(Callgraph),
  CondensedDigraph = digraph_utils:condensation(Digraph),
  ServerPid = self(),
  Edges = [digraph:edge(CondensedDigraph, E)
	   || E <- digraph:edges(CondensedDigraph)],
  SelfEdges = [E || {E, V, V, _} <- Edges],
  true = digraph:del_edges(CondensedDigraph, SelfEdges),
  ReadyList = dialyzer_callgraph:digraph_leaves(CondensedDigraph),
  CoordinatorPid =
    spawn(fun () ->
	      find_succ_typings_in_parallel(Parent, CondensedDigraph, 
					    ReadyList, Fast, ServerPid)
	  end),
  find_server([], CondensedDigraph, Fast, CoordinatorPid).

-spec coordinate_refine(digraph(), dialyzer_callgraph:callgraph(), pid()) ->
	 'fixpoint' | {'not_fixpoint', ordset(label())}.

coordinate_refine(ModuleDigraph, Callgraph, Parent) ->
  ServerPid = self(),
  ReadyList = dialyzer_callgraph:digraph_leaves(ModuleDigraph),
  CoordinatorPid =
    spawn(fun () ->
	      refine_succ_typings_in_parallel(Parent, ModuleDigraph, Callgraph,
					      ReadyList, ServerPid)
	  end),
  refine_server([], ModuleDigraph, CoordinatorPid).

-spec coordinate_warnings([module()], dialyzer_succ_typings:st(), boolean(),
			  [dial_warning()]) -> [dial_warning()].

coordinate_warnings(Modules, State, BehavioursChk, CWarns) ->
  ServerPid = self(),
  lists:foreach(fun (M) ->
		    spawn(fun () ->
			      dialyzer_succ_typings:get_warnings_from_module_parallel(M, State, BehavioursChk, ServerPid)
			  end)
		end, Modules),
  Warns = [receive {warnings, Warnings} -> Warnings end || _M <- Modules],
  lists:flatten(CWarns ++ Warns).

find_server(NotFixpoint, CondensedDigraph, Fast, CoordinatorPid) ->
  receive
    {results, SCC, SuccTypes, PltContracts, NewNotFixPoint1} ->
      NewNotFixpoint2 = ordsets:union(NewNotFixPoint1, NotFixpoint),
      Parents = get_parents(SCC, CondensedDigraph),
      dialyzer_succ_typings:insert_into_plt_parallel(SuccTypes),
      true = dialyzer_plt:insert_contract_list(undefined, PltContracts, true),
      case Parents of
	[] ->
	  ok;
	_->
	  CoordinatorPid ! Parents,
	  ok
      end,
      true = digraph:del_vertex(CondensedDigraph, SCC),
      case digraph:no_vertices(CondensedDigraph) =:= 0 of
	true ->
	  CoordinatorPid ! stop,
	  case dialyzer_succ_typings:check_fixpoint(NewNotFixpoint2, undefined, 
						    Fast, true) of
	    true -> fixpoint;
	    false -> {not_fixpoint, NewNotFixpoint2}
	  end;
	false ->
	  find_server(NewNotFixpoint2, CondensedDigraph, Fast, CoordinatorPid)
      end
  end.

refine_server(NotFixpoint, ModuleDigraph, CoordinatorPid) ->
  receive
    {true, M, FixpointFromScc} ->
      ok;
    {false, M, DictFixpoint, FixpointFromScc} ->
      dialyzer_succ_typings:insert_into_plt_parallel(DictFixpoint)
  end,
  NewFixpoint = ordsets:union(NotFixpoint, FixpointFromScc),
  Parents = get_parents(M, ModuleDigraph),
  case Parents of
    [] ->
      ok;
    _->
      CoordinatorPid ! Parents,
      ok
  end,
  true = digraph:del_vertex(ModuleDigraph, M),
  case digraph:no_vertices(ModuleDigraph) =:= 0 of
    true ->
      CoordinatorPid ! stop,
      case NewFixpoint =:= [] of
	true -> fixpoint;
	false -> {not_fixpoint, NewFixpoint}
      end;
    false ->
      refine_server(NewFixpoint, ModuleDigraph, CoordinatorPid)		
  end.

-spec find_succ_typings_in_parallel(pid(), digraph(),
				    [dialyzer_callgraph:scc()],
				    boolean(), pid()) -> no_return().

find_succ_typings_in_parallel(Parent, CondensedDigraph, ReadyList, 
			      Fast, ServerPid) ->
  case digraph:no_vertices(CondensedDigraph) =:= 0 of
    true ->
      %% io:format ( "\nTypesig done"),
      receive stop ->
	  exit(normal)
      end;
    false ->
      lists:foreach(fun (SCC) ->
			spawn(fun () ->
				  dialyzer_succ_typings:analyze_scc_parallel(SCC, ServerPid, Fast)
			      end)
		    end, ReadyList),
      lists:foreach(fun (SCC) ->
			update_info(SCC, Parent, "Typesig analysis of SCC:")
		    end, ReadyList),
      receive NewReadyList -> ok end,
      find_succ_typings_in_parallel(Parent, CondensedDigraph, NewReadyList,
				    Fast, ServerPid)
  end.

-spec refine_succ_typings_in_parallel(pid(), digraph(),
				      dialyzer_callgraph:callgraph(),
				      [dialyzer_callgraph:scc()],
				      pid()) -> no_return().

refine_succ_typings_in_parallel(Parent, ModuleDigraph, Callgraph, 
				ReadyList, ServerPid) ->
  case digraph:no_vertices(ModuleDigraph) =:= 0 of
    true ->
      receive stop ->
	  exit(normal)
      end;
    false ->
      lists:foreach(fun (SCC) ->
			spawn(fun () ->
				  case SCC of 
				    [M] -> 
				      dialyzer_succ_typings:refine_one_module_parallel(M, Callgraph, ServerPid);
				    [_|_] -> 
				      dialyzer_succ_typings:refine_one_scc_parallel(SCC, Callgraph, ServerPid)
				  end 
			      end)
		    end, ReadyList),
      lists:foreach(fun (SCC) ->
			update_info(SCC, Parent, "Dataflow of one SCC:")
		    end, ReadyList),
      receive NewReadyList -> ok end,
      refine_succ_typings_in_parallel(Parent, ModuleDigraph, Callgraph, 
				      NewReadyList, ServerPid)	    
  end.

update_info(SCC, Parent, Mode) ->
  Msg = io_lib:format("~s ~w\n", [Mode,  [MFA || {_M, _F, _A} = MFA <- SCC]]),
  %% io:format("MESSAGE : ~p \n",[Msg]),
  %% ?debug("~s", [Msg]),
  Parent ! {self(), log, lists:flatten(Msg)}.

get_parents(Node, Digraph) ->
  Vertices = digraph:in_neighbours(Digraph, Node),
  [V || V <- Vertices, digraph:out_degree(Digraph, V) =:= 1].

-spec make_global_st(dialyzer_callgraph:callgraph(), 
		     dialyzer_codeserver:codeserver(),
		     dialyzer_plt:plt(), boolean()) -> true.

make_global_st(Callgraph, Codeserver, Plt, Parallel) ->
  case Parallel of
    true ->
      ?Codeserver = ets:new(?Codeserver, [protected, named_table]),
      true = ets:insert(?Codeserver, 
			{next_core_label,  
			 dialyzer_codeserver:get_next_core_label(Codeserver)}),
      ?Cs_Records = ets:new(?Cs_Records, [protected, named_table]),
      true = ets:insert(?Cs_Records, 
			dict:to_list(
			  dialyzer_codeserver:get_records(Codeserver))),
      ?Cs_Contracts = ets:new(?Cs_Contracts, [protected, named_table]),
      true = ets:insert(?Cs_Contracts, 
			dict:to_list(
			  dialyzer_codeserver:get_contracts(Codeserver))),
      ?Cs_Exported_Types = ets:new(?Cs_Exported_Types,[protected, named_table]),
      true = ets:insert(?Cs_Exported_Types, 
			{exp_types, 
			 dialyzer_codeserver:get_exported_types(Codeserver)}),
      ?Callgraph = ets:new(?Callgraph, [protected, named_table]),
      true = ets:insert(?Callgraph, 
			[{selfrec, dialyzer_callgraph:get_self_rec(Callgraph)},
			 {esc, dialyzer_callgraph:get_escaping(Callgraph)}]),
      ?Cg_RecVarMap = ets:new(?Cg_RecVarMap, [protected, named_table]),
      true = ets:insert(?Cg_RecVarMap, 
			dict:to_list(
			  dialyzer_callgraph:get_rec_var_map(Callgraph))),
      ?Cg_RevNameMap = ets:new(?Cg_RevNameMap, [protected, named_table]),
      true = ets:insert(?Cg_RevNameMap, 
			dict:to_list(
			  dialyzer_callgraph:get_rev_name_map(Callgraph))),
      ?Cg_NameMap = ets:new(?Cg_NameMap, [protected, named_table]),
      true = ets:insert(?Cg_NameMap, 
			dict:to_list(
			  dialyzer_callgraph:get_name_map(Callgraph))),
      ?Cg_Calls = ets:new(?Cg_Calls, [protected, named_table]),
      true = ets:insert(?Cg_Calls, 
			dict:to_list(dialyzer_callgraph:get_calls(Callgraph))),
      ?Plt_Info = ets:new(?Plt_Info, [public, named_table]), 
      ?OldPlt_Info = ets:new(?OldPlt_Info, [protected, named_table]), 
      Infos = dict:to_list(dialyzer_plt:get_info(Plt)),
      true = ets:insert(?Plt_Info, Infos),
      true = ets:insert(?OldPlt_Info, Infos),
      ?Plt_Contracts = ets:new(?Plt_Contracts, [protected, named_table]), 
      ?OldPlt_Contracts = ets:new(?OldPlt_Contracts, [protected, named_table]), 
      PltContracts = dict:to_list(dialyzer_plt:get_contracts(Plt)),
      true = ets:insert(?Plt_Contracts, PltContracts),
      true = ets:insert(?OldPlt_Contracts, PltContracts);
    false ->
      true
  end.

-spec delete_global_st(dialyzer_plt:plt()) -> dialyzer_plt:plt().
		  
delete_global_st(Plt) ->
  Contracts = ets:tab2list(?Plt_Contracts),
  Plt1 = dialyzer_plt:set_contracts(Plt, dict:from_list(Contracts)),
  Plt_Info = ets:tab2list(?Plt_Info),
  Plt2 = dialyzer_plt:set_info(Plt1, dict:from_list(Plt_Info)),
  ets:delete(?Codeserver),
  ets:delete(?Cs_Records),
  ets:delete(?Cs_Contracts),
  ets:delete(?Cs_Exported_Types),
  ets:delete(?Callgraph),
  ets:delete(?Cg_RecVarMap),
  ets:delete(?Cg_RevNameMap),
  ets:delete(?Cg_NameMap),
  ets:delete(?Cg_Calls),
  ets:delete(?Plt_Info),
  ets:delete(?Plt_Contracts),
  ets:delete(?OldPlt_Info),
  ets:delete(?OldPlt_Contracts),
  ets:delete(?Mfa_Codeserver),
  ets:delete(?Mod_Codeserver),
  Plt2.
