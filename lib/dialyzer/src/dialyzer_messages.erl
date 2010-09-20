%% -*- erlang-indent-level: 2 -*-
%%-----------------------------------------------------------------------
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2008-2009. All Rights Reserved.
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

%%%----------------------------------------------------------------------
%%% File    : dialyzer_messages.erl
%%% Author  : Maria Christakis <christakismaria@gmail.com>
%%% Description : Utility functions for message analysis
%%%
%%% Created : 12 Feb 2010 by Maria Christakis <christakismaria@gmail.com>
%%%----------------------------------------------------------------------
-module(dialyzer_messages).

%% Message Analysis

-export([add_clauses_pid/2,  get_race_list_ret/2, is_call_to_self/3,
         is_call_to_send/1, is_call_to_spawn/1, is_call_to_spawn/3,
         is_call_to_whereis/1, msg/1, prioritize_msg_warns/1,
         var_call_assignment/5, var_fun_assignment/3]).

%% Record Interfaces

-export([add_edge/2, add_msg/2, add_pid/3, add_pid_tags/2,
         create_indirect_pid_tag_for_self/2,
         create_indirect_pid_tags_for_spawn/3,
         create_pid_tag_for_self/1, create_pid_tag_for_spawn/2,
         create_rcv_tag/2, create_send_tag/4, get_proc_reg/1,
         get_rcv_tags/1, get_send_tags/1, get_var_fun_tab/1,
         get_warnings/1, get_whereis_argtypes/1, new/0,
         put_proc_reg/2, put_rcv_tags/2, put_send_tags/2,
         put_whereis_argtypes/2, update_proc_reg/4]).

%% Exported Types

-export_type([msgs/0, pid_fun/0]).

-include("dialyzer.hrl").
-include("dialyzer_heisenbugs.hrl").

%%% ===========================================================================
%%%
%%%  Definitions
%%%
%%% ===========================================================================

-define(no_args, no_args).
-define(undef, undef).

%%% ===========================================================================
%%%
%%%  Types and Records
%%%
%%% ===========================================================================

-type dest()     :: label() | ?no_label | [atom()].
-type pid_kind() :: 'self' | 'spawn'.
-type proc_reg() :: {dict(), [mfa_or_funlbl()]}.
%% process registry associating atoms to pids and
%% mfas that contain the associations
%% (i.e. the 'register' calls)

-record(pid_fun,  {kind            :: pid_kind(),
                   pid = ?no_label :: label() | ?no_label,
                   pid_mfa         :: mfa_or_funlbl(), %% fun that owns the pid
                   fun_mfa         :: mfa_or_funlbl(),
                   indirect = ?undef :: mfa_or_funlbl() | ?undef}).

-record(rcv_fun,  {msgs = []       :: [erl_types:erl_type()],
                   fun_mfa         :: mfa_or_funlbl(),
                   file_line       :: file_line()}).

-record(send_fun, {pid             :: dest(),
                   msg             :: erl_types:erl_type(),
                   fun_mfa         :: mfa_or_funlbl(),
                   file_line       :: file_line()}).

-record(msgs,     {edges     = []  :: [dialyzer_callgraph:callgraph_edge()],
                   old_pids  = []  :: [#pid_fun{}], %% already analyzed pid tags
                   pid_tags  = []  :: [#pid_fun{}],
                   rcv_tags  = []  :: [#rcv_fun{}],
                   send_tags = []  :: [#send_fun{}],
                   proc_reg     = {dict:new(), []} :: proc_reg(),
                   var_call_tab = dict:new()       :: dict(),
                   var_fun_tab  = dict:new()       :: dict(),
                   whereis_argtypes = []          :: [erl_types:erl_type()],
                   warnings  = []  :: [dial_warning()]}).

%%% ===========================================================================
%%%
%%%  Exported Types
%%%
%%% ===========================================================================

-type pid_fun() :: #pid_fun{}.
-opaque msgs()  :: #msgs{}.

%%% ===========================================================================
%%%
%%%  Message Analysis
%%%
%%% ===========================================================================

-spec msg(dialyzer_dataflow:state()) -> dialyzer_dataflow:state().

msg(State) ->
  PidTags = dialyzer_dataflow:state__get_pid_tags(State),
  Callgraph = dialyzer_dataflow:state__get_callgraph(State),
  Digraph = dialyzer_callgraph:get_digraph(Callgraph),
  Msgs = dialyzer_callgraph:get_msgs(Callgraph),
  Edges = Msgs#msgs.edges,
  Filter = fun(E) ->
               case digraph:edge(Digraph, E) of
                 false -> true;
                 _ -> false
               end
           end,
  ExtraEdges = [E || E <- Edges, Filter(E)],
  dialyzer_callgraph:add_edges(ExtraEdges, Callgraph),
  AllPidTags = Msgs#msgs.pid_tags,
  OldPidTags = Msgs#msgs.old_pids,
  PidTags1 = PidTags -- OldPidTags,
  {OldPidTags1, PidTagGroups} = group_pid_tags(PidTags1, AllPidTags,
                                               OldPidTags, Digraph),
  SortedSendTags = lists:usort(Msgs#msgs.send_tags),
  SortedRcvTags = lists:usort(Msgs#msgs.rcv_tags),
  ProcReg = Msgs#msgs.proc_reg,
  VCTab = Msgs#msgs.var_call_tab,
  State1 = msg1(PidTagGroups, SortedSendTags, SortedRcvTags, ProcReg,
                VCTab, ExtraEdges, State),
  Callgraph1 = dialyzer_dataflow:state__get_callgraph(State1),
  Msgs1 = dialyzer_callgraph:get_msgs(Callgraph1),
  Msgs2 = renew_analyzed_pid_tags(OldPidTags1, Msgs1),
  Callgraph2 = dialyzer_callgraph:put_msgs(Msgs2, Callgraph1),
  digraph:del_edges(Digraph, ExtraEdges),
  dialyzer_dataflow:state__put_callgraph(Callgraph2, State1).

msg1(PidTagGroups, SendTags, RcvTags, ProcReg, VCTab, Edges, State) ->
  Callgraph1 = dialyzer_dataflow:state__get_callgraph(State),
  Warns = msg1(PidTagGroups, SendTags, RcvTags, ProcReg, VCTab, [],
               Edges, Callgraph1),
  Msgs1 = dialyzer_callgraph:get_msgs(Callgraph1),
  Msgs2 = add_warnings(Warns, Msgs1),
  Callgraph2 = dialyzer_callgraph:put_msgs(Msgs2, Callgraph1),
  State1 = dialyzer_dataflow:state__put_callgraph(Callgraph2, State),
  dialyzer_dataflow:state__put_pid_tags([], State1).

msg1(PidTagGroups, SendTags, RcvTags, ProcReg, VCTab, Warns, Edges,
     Callgraph) ->
  case PidTagGroups of
    [] -> Warns;
    [H|T] ->
      {PidTag, MsgVarMap} = H,
      Kind = PidTag#pid_fun.kind,
      {Pid, PidMFA, CurrFun} =
        case Kind of
          'self' ->
            {PidTag#pid_fun.pid, PidTag#pid_fun.pid_mfa,
             PidTag#pid_fun.fun_mfa};
          'spawn' ->
            {PidTag#pid_fun.pid, PidTag#pid_fun.pid_mfa,
             case PidTag#pid_fun.indirect of
               ?undef -> PidTag#pid_fun.fun_mfa;
               Other -> Other
             end}
        end,
      Digraph = dialyzer_callgraph:get_digraph(Callgraph),
      CFSendTags = find_control_flow_send_tags(CurrFun, PidMFA, SendTags,
                                               Digraph),
      PidSendTags = go_from_pid_tag(CurrFun, Pid, CFSendTags, ProcReg,
                                    VCTab, MsgVarMap, Callgraph),
      digraph:del_edges(Digraph, Edges),
      PidMFAs =
        case Kind =:= 'self' of
          true -> backward_msg_analysis(PidMFA, Digraph);
          false -> [PidMFA]
        end,
      CFRcvTags = find_control_flow_rcv_tags(PidMFAs, RcvTags, Digraph),
      dialyzer_callgraph:add_edges(Edges, Callgraph),
      Warns1 = warn_unused_send_rcv_stmts(PidSendTags, CFRcvTags),
      msg1(T, SendTags, RcvTags, ProcReg, VCTab, Warns1 ++ Warns, Edges,
           Callgraph)
  end.

go_from_pid_tag(MFA, Pid, SendTags, ProcReg, VCTab, MsgVarMap, Callgraph) ->
  Code =
    case ets:lookup(cfgs, MFA) of
      [] -> [];
      [{MFA, _Args, _Ret, C}] -> C
    end,
  forward_msg_analysis(Pid, Code, SendTags, ProcReg, VCTab, MsgVarMap,
                       Callgraph).

%%% ===========================================================================
%%%
%%%  Forward Analysis
%%%
%%% ===========================================================================

forward_msg_analysis(_Pid, _Code, [], _ProcReg, _VCTab, _MsgVarMap,
                     _Callgraph) ->
  [];
forward_msg_analysis(Pid, Code, SendTags, {RegDict, RegMFAs}, VCTab,
                     MsgVarMap, Callgraph) ->
  SendMFAs = [S#send_fun.fun_mfa || S <- SendTags],
  MsgVarMap1 = bind_reg_labels(RegDict, MsgVarMap),
  PidSendTags = forward_msg_analysis(Pid, Code, SendTags,
                                     lists:usort(RegMFAs ++ SendMFAs),
                                     RegDict, VCTab, [], [], MsgVarMap1,
                                     Callgraph),
  lists:usort(PidSendTags).

forward_msg_analysis(Pid, Code, SendTags, MFAs, RegDict, VCTab, Calls,
                     Spawns, MsgVarMap, Callgraph) ->
  case Code of
    [] -> find_pid_send_tags(Pid, SendTags, RegDict, MsgVarMap);
    [Head|Tail] ->
      {NewPidSendTags, NewMsgVarMap} =
        case Head of
          'self' -> {[], MsgVarMap};
          #dep_call{} -> {[], MsgVarMap};
          #warn_call{} -> {[], MsgVarMap};
          #fun_call{caller = Caller, callee = Callee, arg_types = ArgTypes,
                    vars = CallVars} ->
            Digraph = dialyzer_callgraph:get_digraph(Callgraph),
            PidSendTags =
              case follow_call(Callee, MFAs, Digraph) of
                true ->
                  case lists:member({Caller, Callee}, Calls) of
                    true -> [];
                    false ->
                      case ets:lookup(cfgs, Callee) of
                        [] -> [];
                        [{Callee, DefVars, _DefRet, CalleeCode}] ->
                          MsgVarMap1 =
                            dialyzer_races:race_var_map(DefVars, CallVars,
                                                        MsgVarMap, 'bind'),
                          forward_msg_analysis(Pid, CalleeCode, SendTags,
                                               MFAs, RegDict, VCTab,
                                               [{Caller, Callee}|Calls],
                                               Spawns, MsgVarMap1, Callgraph)
                      end
                  end;
                false -> []
              end,
            MsgVarMap2 =
              case dialyzer_callgraph:lookup_label(Callee, Callgraph) of
                'error' -> MsgVarMap;
                {'ok', CalleeLabel} ->
                  case dict:find(CalleeLabel, VCTab) of
                    'error' -> MsgVarMap;
                    {'ok', RetLabel} ->
                      PidCallVars = find_pid_call_vars(ArgTypes, CallVars,
                                                       erl_types:t_pid(),
                                                       Pid, MsgVarMap),
                      dialyzer_races:bind_dict_vars_list(RetLabel, PidCallVars,
                                                         MsgVarMap)
                  end
              end,
            {PidSendTags, MsgVarMap2};
          #spawn_call{caller = Caller, callee = Callee, vars = CallVars} ->
            Digraph = dialyzer_callgraph:get_digraph(Callgraph),
            PidSendTags =
              case follow_call(Callee, MFAs, Digraph) of
                true ->
                  case lists:member({Caller, Callee}, Spawns) of
                    true -> [];
                    false ->
                      case ets:lookup(cfgs, Callee) of
                        [] -> [];
                        [{Callee, DefVars, _DefRet, CalleeCode}] ->
                          MsgVarMap1 =
                            dialyzer_races:race_var_map(DefVars, CallVars,
                                                        MsgVarMap, 'bind'),
                          forward_msg_analysis(Pid, CalleeCode, SendTags,
                                               MFAs, RegDict, VCTab, Calls,
                                               [{Caller, Callee}|Spawns],
                                               MsgVarMap1, Callgraph)
                      end
                  end;
                false -> []
              end,
            {PidSendTags, MsgVarMap};
          'beg_case' -> {[], MsgVarMap};
          #beg_clause{arg = Arg, pats = Pats, guard = Guard} ->
            {MsgVarMap1, _} =
              dialyzer_races:race_var_map_guard(Arg, Pats, Guard, MsgVarMap,
                                                'bind'),
            {[], MsgVarMap1};
          #end_clause{arg = Arg, pats = Pats, guard = Guard} ->
            {MsgVarMap1, _} =
              dialyzer_races:race_var_map_guard(Arg, Pats, Guard, MsgVarMap,
                                                'unbind'),
            {[], MsgVarMap1};
          #end_case{clauses = Clauses} ->
            {[], dialyzer_races:race_var_map_clauses(Clauses, MsgVarMap)};
          #let_tag{var = Var, arg = Arg} ->
            {[], dialyzer_races:race_var_map(Var, Arg, MsgVarMap, 'bind')}
        end,
      NewPidSendTags ++
        forward_msg_analysis(Pid, Tail, SendTags, MFAs, RegDict, VCTab,
                             Calls, Spawns, NewMsgVarMap, Callgraph)
  end.

%%% ===========================================================================
%%%
%%%  Utilities
%%%
%%% ===========================================================================

-spec add_clauses_pid([cerl:cerl()], dialyzer_dataflow:state()) ->
      dialyzer_dataflow:state().

add_clauses_pid([], State) ->
  State;
add_clauses_pid([C|Cs], State) ->
  [Pat] = cerl:clause_pats(C),
  case cerl:is_c_tuple(Pat) of
    true ->
      case cerl:tuple_arity(Pat) =:= 2 of
        true ->
          [PidArg, _RefArg] = cerl:tuple_es(Pat),
          case cerl:is_c_var(PidArg) of
            true ->
              dialyzer_messages:add_pid('spawn', cerl_trees:get_label(PidArg),
                                        State);
            false -> add_clauses_pid(Cs, State)
          end;
        false -> add_clauses_pid(Cs, State)
      end;
    false -> add_clauses_pid(Cs, State)
  end.

backward_msg_analysis(CurrFun, Digraph) ->
  Calls = digraph:edges(Digraph),
  Parents = dialyzer_races:fixup_race_backward(CurrFun, Calls, Calls, [],
                                               ?local),
  UParents = lists:usort(Parents),
  filter_parents(UParents, Digraph).

bif_msg(RcvMsg) ->
  %% {'DOWN', Ref, Type, Obj, Info}
  Msg1 = erl_types:t_tuple(
           [erl_types:t_atom('DOWN')|lists:duplicate(4, erl_types:t_any())]),
  Inf1 = erl_types:t_inf(Msg1, RcvMsg),
  case erl_types:t_is_tuple(Inf1) of
    true -> Inf1;
    false ->
      %% {'EXIT', Pid, Reason}
      Msg2 =
        erl_types:t_tuple(
          [erl_types:t_atom('EXIT')|lists:duplicate(2, erl_types:t_any())]),
      Inf2 = erl_types:t_inf(Msg2, RcvMsg),
      case erl_types:t_is_tuple(Inf2) of
        true -> Inf2;
        false -> erl_types:t_none()
      end
  end.

bind_dict_vars(Label1, Label2, Dict) ->
  TempDict = dialyzer_races:bind_dict_vars(Label1, Label2, Dict),
  dialyzer_races:bind_dict_vars(Label2, Label1, TempDict).

bind_reg_labels(RegDict, MsgVarMap) ->
  Keys = dict:fetch_keys(RegDict),
  bind_reg_labels(Keys, RegDict, MsgVarMap).

bind_reg_labels([], _RegDict, MsgVarMap) ->
  MsgVarMap;
bind_reg_labels([K|Keys], RegDict, MsgVarMap) ->
  {ok, [L|Labels]} = dict:find(K, RegDict),
  MsgVarMap1 = dialyzer_races:bind_dict_vars_list(L, Labels, MsgVarMap),
  bind_reg_labels(Keys, RegDict, MsgVarMap1).

filter_parents(UParents, Digraph) ->
  dialyzer_races:filter_parents(UParents, UParents, Digraph).

find_control_flow_rcv_tags(PidFuns, RcvTags, Digraph) ->
  ReachableFrom = digraph_utils:reachable(PidFuns, Digraph),
  find_control_flow_rcv_tags(PidFuns, RcvTags, [], ReachableFrom).

find_control_flow_rcv_tags(_PidFuns, [], Acc, _ReachableFrom) ->
  Acc;
find_control_flow_rcv_tags(_PidFuns, _RcvTags, Acc, []) ->
  Acc;
find_control_flow_rcv_tags(PidFuns, [#rcv_fun{fun_mfa = RcvFun} = H|T],
                           Acc, ReachableFrom) ->
  NewAcc =
    case lists:member(RcvFun, PidFuns) of
      true -> [H|Acc];
      false ->
        case lists:member(RcvFun, ReachableFrom) of
          true -> [H|Acc];
          false -> Acc
        end
    end,
  find_control_flow_rcv_tags(PidFuns, T, NewAcc, ReachableFrom).

find_control_flow_send_tags(PidFun1, PidFun2, SendTags, Digraph) ->
  ReachableFrom = digraph_utils:reachable(lists:usort([PidFun1, PidFun2]),
                                          Digraph),
  find_control_flow_send_tags(PidFun1, PidFun2, SendTags, [],
                              ReachableFrom).

find_control_flow_send_tags(_PidFun1, _PidFun2, [], Acc, _ReachableFrom) ->
  Acc;
find_control_flow_send_tags(_PidFun1, _PidFun2, _SendTags, Acc, []) ->
  Acc;
find_control_flow_send_tags(PidFun1, PidFun2,
                            [#send_fun{fun_mfa = SendFun} = H|T],
                            Acc, ReachableFrom) ->
  NewAcc =
    case PidFun1 =:= SendFun orelse PidFun2 =:= SendFun of
      true -> [H|Acc];
      false ->
        case lists:member(SendFun, ReachableFrom) of
          true -> [H|Acc];
          false -> Acc
        end
    end,
  find_control_flow_send_tags(PidFun1, PidFun2, T, NewAcc, ReachableFrom).

find_pid_call_vars(ArgTypes, Vars, PidType, Pid, MVM) ->
  find_pid_call_vars(ArgTypes, Vars, PidType, Pid, MVM, []).

find_pid_call_vars([], [], _PidType, _Pid, _MVM, Acc) ->
  Acc;
find_pid_call_vars([AT|ATs], [V|Vs], PidType, Pid, MVM, Acc) ->
  NewAcc =
    case erl_types:t_is_subtype(PidType, AT) of
      true ->
        case cerl:is_c_var(V) of
          true ->
            L = cerl_trees:get_label(V),
            case L =:= Pid orelse
              dialyzer_races:are_bound_labels(Pid, L, MVM) orelse
              dialyzer_races:are_bound_labels(L, Pid, MVM) of
              true -> [L|Acc];
              false -> Acc
            end;
          false -> Acc
        end;
      false -> Acc
    end,
  find_pid_call_vars(ATs, Vs, PidType, Pid, MVM, NewAcc).

find_pid_send_tags(Pid, CFSendTags, RegDict, MsgVarMap) ->
  find_pid_send_tags(Pid, CFSendTags, RegDict, [], MsgVarMap).

find_pid_send_tags(_Pid, [], _RegDict, Acc, _MsgVarMap) ->
  Acc;
find_pid_send_tags(Pid, [#send_fun{pid = SendPid} = H|T], RegDict, Acc,
                   MVM) ->
  NewAcc =
    case SendPid =:= ?no_label of
      true -> Acc;
      false ->
        case is_list(SendPid) of
          true ->
            Checks = [is_bound_reg_name(A, Pid, RegDict, MVM) || A <- SendPid],
            case lists:any(fun(E) -> E end, Checks) of
              true -> [H|Acc];
              false -> Acc
            end;
          false ->
            case Pid =:= SendPid of
              true -> [H|Acc];
              false ->
                case dialyzer_races:are_bound_labels(Pid, SendPid, MVM) orelse
                  dialyzer_races:are_bound_labels(SendPid, Pid, MVM) of
                  true -> [H|Acc];
                  false -> Acc
                end
            end
        end
    end,
  find_pid_send_tags(Pid, T, RegDict, NewAcc, MVM).

follow_call(Callee, MFAs, Digraph) ->
  lists:any(fun(E) -> E end,
            [follow_call_pred(Callee, MFA, Digraph) || MFA <- MFAs]).

follow_call_pred(From, From, _Digraph) ->
  true;
follow_call_pred(From, To, Digraph) ->
  case digraph:get_path(Digraph, From, To) of
    false -> false;
    _Vertices when is_list(_Vertices) -> true
  end.

get_case_ret(RaceList) ->
  case RaceList of
    [] -> {[], []};
    [H|T] ->
      case H of
        #end_clause{} ->
          {RaceList1, Ret1} = get_clause_ret(T),
          {RaceList2, Ret2} = get_case_ret(RaceList1),
          {RaceList2, Ret1 ++ Ret2};
        'beg_case' -> {T, []}
      end
  end.

get_clause(RaceList, NestingLevel) ->
  case RaceList of
    [] -> [];
    [H|T] ->
      {NestingLevel1, Return} =
        case H of
          'beg_case' -> {NestingLevel - 1, false};
          #end_case{} -> {NestingLevel + 1, false};
          #beg_clause{} ->
            case NestingLevel =:= 0 of
              true -> {NestingLevel, true};
              false -> {NestingLevel, false}
            end;
          _Other -> {NestingLevel, false}
        end,
      case Return of
        true -> [];
        false -> [H|get_clause(T, NestingLevel1)]
      end
  end.

get_clause_ret(RaceList) ->
  Ret = get_ret_paths(get_clause(RaceList, 0)),
  {get_rest_after_clause(RaceList, 0), Ret}.

-spec get_race_list_ret(dialyzer_races:code(), erl_types:erl_type()) ->
      [dialyzer_races:pid_tags()].

get_race_list_ret([], _RetType) -> [];
get_race_list_ret(RaceList, RetType) ->
  PidType = erl_types:t_pid(),
  case erl_types:t_is_subtype(PidType, RetType) of
    true -> get_ret_paths(RaceList);
    false -> []
  end.

get_rest_after_clause(RaceList, NestingLevel) ->
  case RaceList of
    [] -> [];
    [H|T] ->
      {NestingLevel1, Return} =
        case H of
          'beg_case' -> {NestingLevel - 1, false};
          #end_case{} -> {NestingLevel + 1, false};
          #beg_clause{} ->
            case NestingLevel =:= 0 of
              true -> {NestingLevel, true};
              false -> {NestingLevel, false}
            end;
          _Other -> {NestingLevel, false}
        end,
      case Return of
        true -> T;
        false -> get_rest_after_clause(T, NestingLevel1)
      end
  end.

get_ret_paths(RaceList) ->
  case RaceList of
    [] -> [];
    [H|T] ->
      case H of
        #end_case{} ->
          {RaceList1, Ret} = get_case_ret(T),
          Ret ++ get_ret_paths(RaceList1);
        'self' -> [H|get_ret_paths(T)];
        #fun_call{callee = Callee} ->
          Ret =
            case ets:lookup(cfgs, Callee) of
              [] -> [];
              [{Callee, _Args, CRet, _C}] -> CRet
            end,
          Ret ++ get_ret_paths(T);
        #dep_call{} -> get_ret_paths(T);
        #spawn_call{} -> [H|get_ret_paths(T)];
        #warn_call{} -> get_ret_paths(T);
        #let_tag{} -> get_ret_paths(T)
      end
  end.

%% Groups pid tags that refer to the same process
%% in the form of the highest ancestor
group_pid_tags([], _Tags, OldTags, _Digraph) ->
  {OldTags, []};
group_pid_tags([#pid_fun{kind = Kind, pid = Pid, pid_mfa = PidMFA,
                         indirect = Indirect} = H|T],
               Tags, OldTags, Digraph) ->
  {NewOldTags, Group} =
    case lists:member(H, OldTags) of
      true -> {OldTags, []};
      false ->
        ReachableFrom = digraph_utils:reachable([PidMFA], Digraph),
        ReachingTo = digraph_utils:reaching([PidMFA], Digraph),
        case Kind =/= 'self' of
          true ->
            case Indirect of
              ?undef ->
                {RetTags, RetDad, RetMVM} =
                  group_spawn_pid_tags(H, Tags, [H|OldTags], ReachableFrom,
                                       ReachingTo, Digraph, [], true, [],
                                       dict:new()),
                case RetDad#pid_fun.pid =:= ?no_label of
                  true -> {OldTags, []};
                  false -> {RetTags, [{RetDad, RetMVM}]}
                end;
              _Else -> {OldTags, []}
            end;
          false ->
            case Pid =:= ?no_label of
              true -> {OldTags, []};
              false ->
                {RetTags, RetDad, RetMVM} =
                  group_self_pid_tags(H, Tags, [H|OldTags], ReachableFrom,
                                      ReachingTo, Digraph, H, dict:new()),
                DadPidMFA = RetDad#pid_fun.pid_mfa,
                ReachingToDad = digraph_utils:reaching([DadPidMFA], Digraph),
                case lists:any(fun(ETag) ->
                                   is_below_spawn(ETag, ReachingToDad)
                               end, Tags) of
                  true -> {OldTags, []};
                  false -> {RetTags, [{RetDad, RetMVM}]}
                end
            end
        end
    end,
  {RetOldTags, RetGroups} = group_pid_tags(T, Tags, NewOldTags, Digraph),
  {RetOldTags, Group ++ RetGroups}.

group_self_pid_tags(_CurrTag, [], OldTags, _ReachableFrom, _ReachingTo,
                    _Digraph, Dad, MsgVarMap) ->
  {OldTags, Dad, MsgVarMap};
group_self_pid_tags(#pid_fun{pid = CurrPid, pid_mfa = CurrPidMFA} = CurrTag,
                    [#pid_fun{kind = Kind, pid = Pid, pid_mfa = PidMFA} = H|T],
                    OldTags, ReachableFrom, ReachingTo, Digraph,
                    #pid_fun{pid_mfa = DadPidMFA} = Dad, MsgVarMap) ->
  {NewOldTags, NewDad, NewMsgVarMap} =
    case Kind =/= 'self' orelse Pid =:= ?no_label orelse CurrTag =:= H orelse
      lists:member(H, OldTags) of
      true -> {OldTags, Dad, MsgVarMap};
      false ->
        case CurrPidMFA =:= PidMFA of
          true ->
            {[H|OldTags], Dad, bind_dict_vars(CurrPid, Pid, MsgVarMap)};
          false ->
            case lists:member(PidMFA, ReachableFrom) of
              true ->
                {[H|OldTags], Dad, bind_dict_vars(CurrPid, Pid, MsgVarMap)};
              false ->
                case lists:member(PidMFA, ReachingTo) of
                  true ->
                    case digraph:get_path(Digraph, PidMFA, DadPidMFA) of
                      false ->
                        {[H|OldTags], Dad,
                         bind_dict_vars(CurrPid, Pid, MsgVarMap)};
                      _Vertices ->
                        {[H|OldTags], H,
                         bind_dict_vars(CurrPid, Pid, MsgVarMap)}
                    end;
                  false -> {OldTags, Dad, MsgVarMap}
                end
            end
        end
    end,
  group_self_pid_tags(CurrTag, T, NewOldTags, ReachableFrom, ReachingTo,
                      Digraph, NewDad, NewMsgVarMap).

group_spawn_pid_tags(CurrTag, [], OldTags, _ReachableFrom, _ReachingTo,
                     _Digraph, OldTagsAcc, true, IndirectTags, MsgVarMap) ->
  {IndirectTags ++ lists:usort(OldTagsAcc ++ OldTags), CurrTag, MsgVarMap};
group_spawn_pid_tags(CurrTag, [], OldTags, _ReachableFrom, _ReachingTo,
                     _Digraph, _OldTagsAcc, false, IndirectTags, MsgVarMap) ->
  {IndirectTags ++ OldTags, CurrTag, MsgVarMap};
group_spawn_pid_tags(#pid_fun{pid = CurrPid, fun_mfa = CurrFunMFA,
                              pid_mfa = CurrPidMFA,
                              indirect = CurrIndirect} = CurrTag,
                     [#pid_fun{kind = Kind, pid = Pid, fun_mfa = FunMFA,
                               pid_mfa = PidMFA, indirect = Indirect} = H|T],
                     OldTags, ReachableFrom, ReachingTo, Digraph,
                     OldTagsAcc, AddOldTags, IndirectTags, MsgVarMap) ->
  {NewOldTagsAcc, NewAddOldTags, NewIndirectTags, NewCurrTag, NewMsgVarMap} =
    case Kind =/= 'self' of
      true ->
        case CurrTag =:= H of
          true ->
            {OldTagsAcc, AddOldTags, IndirectTags, CurrTag, MsgVarMap};
          false ->
            case (CurrFunMFA =:= FunMFA) andalso
              (CurrPidMFA =:= PidMFA) andalso (Indirect =/= ?undef) of
              true ->
                MsgVarMap1 =
                  case Pid =:= ?no_label of
                    true -> MsgVarMap;
                    false -> bind_dict_vars(CurrPid, Pid, MsgVarMap)
                  end,
                case CurrIndirect =/= ?undef of
                  true ->
                    Path = digraph:get_path(Digraph, Indirect,
                                            CurrIndirect),
                    case Path of
                      false ->
                        {OldTagsAcc, AddOldTags, [H|IndirectTags], CurrTag,
                         MsgVarMap1};
                      _Vertices ->
                        {OldTagsAcc, AddOldTags, [H|IndirectTags], H,
                         MsgVarMap1}
                    end;
                  false ->
                    {OldTagsAcc, AddOldTags, [H|IndirectTags], H,
                     MsgVarMap1}
                end;
              false ->
                {OldTagsAcc, AddOldTags, IndirectTags, CurrTag, MsgVarMap}
            end
        end;
      false ->
        case Pid =:= ?no_label of
          true ->
            {OldTagsAcc, AddOldTags, IndirectTags, CurrTag, MsgVarMap};
          false ->
            case CurrPidMFA =:= PidMFA of
              true ->
                {[H|OldTagsAcc], AddOldTags, IndirectTags, CurrTag,
                 bind_dict_vars(CurrPid, Pid, MsgVarMap)};
              false ->
                case lists:member(PidMFA, ReachableFrom) of
                  true ->
                    {[H|OldTagsAcc], AddOldTags, IndirectTags, CurrTag,
                     bind_dict_vars(CurrPid, Pid, MsgVarMap)};
                  false ->
                    case lists:member(PidMFA, ReachingTo) of
                      true ->
                        {OldTagsAcc, false, IndirectTags, CurrTag, MsgVarMap};
                      false ->
                        {OldTagsAcc, AddOldTags, IndirectTags, CurrTag,
                         MsgVarMap}
                    end
                end
            end
        end
    end,
  group_spawn_pid_tags(NewCurrTag, T, OldTags, ReachableFrom, ReachingTo,
                       Digraph, NewOldTagsAcc, NewAddOldTags, NewIndirectTags,
                       NewMsgVarMap).

is_below_spawn(_Tag, []) ->
  false;
is_below_spawn(#pid_fun{kind = 'self'}, _ReachingTo) ->
  false;
is_below_spawn(#pid_fun{kind = 'spawn', pid_mfa = PidMFA}, ReachingTo) ->
  lists:member(PidMFA, ReachingTo).

is_bound_reg_name(Atom, Pid, RegDict, MVM) ->
  case dict:find(Atom, RegDict) of
    'error' -> false;
    {'ok', List} ->
      Checks = [begin
                  E =:= Pid orelse
                    dialyzer_races:are_bound_labels(Pid, E, MVM) orelse
                    dialyzer_races:are_bound_labels(E, Pid, MVM)
                end || E <- List],
      lists:any(fun(E) -> E end, Checks)
  end.

-spec is_call_to_make_fun(cerl:cerl()) -> boolean().

is_call_to_make_fun(Tree) ->
  case cerl:is_c_call(Tree) of
    false -> false;
    true ->
      Mod = cerl:call_module(Tree),
      Name = cerl:call_name(Tree),
      Arity = cerl:call_arity(Tree),
      cerl:is_c_atom(Mod)
	andalso cerl:is_c_atom(Name)
	andalso (cerl:atom_val(Name) =:= 'make_fun')
	andalso (cerl:atom_val(Mod) =:= 'erlang')
	andalso (Arity =:= 3)
  end.

-spec is_call_to_self(cerl:cerl(), module(), dict()) ->
      {boolean(), boolean()}.

%% Returns {direct_call_boolean, indirect_call_boolean}
is_call_to_self(Tree, M, VFTab) ->
  case cerl:is_c_call(Tree) of
    false ->
      case cerl:is_c_apply(Tree) of
        true ->
          ApplyOp = cerl:apply_op(Tree),
          case cerl:var_name(ApplyOp) of
            {F, A} ->
              MFA = {M, F, A},
              Ret =
                case ets:lookup(cfgs, MFA) of
                  [] -> [];
                  [{MFA, _Args, R, _Code}] -> R
                end,
              {false, lists:member('self', Ret)};
            _ ->
              case dict:find(cerl_trees:get_label(ApplyOp), VFTab) of
                'error' -> {false, false};
                {'ok', FunLabel} ->
                  Ret =
                    case ets:lookup(cfgs, FunLabel) of
                      [] -> [];
                      [{FunLabel, _Args, R, _Code}] -> R
                    end,
                  {false, lists:member('self', Ret)}
              end
          end;
        false -> {false, false}
      end;
    true ->
      Mod = cerl:call_module(Tree),
      Name = cerl:call_name(Tree),
      Arity = cerl:call_arity(Tree),
      case cerl:is_c_atom(Mod) andalso cerl:is_c_atom(Name) of
        true ->
          case {cerl:atom_val(Mod), cerl:atom_val(Name), Arity} of
            {'erlang', 'self', 0} -> {true, false};
            MFA ->
              Ret =
                case ets:lookup(cfgs, MFA) of
                  [] -> [];
                  [{MFA, _Args, R, _Code}] -> R
                end,
              {false, lists:member('self', Ret)}
          end;
        false -> {false, false}
      end
  end.

-spec is_call_to_send(cerl:cerl()) -> boolean().

is_call_to_send(Tree) ->
  case cerl:is_c_call(Tree) of
    false -> false;
    true ->
      Mod = cerl:call_module(Tree),
      Name = cerl:call_name(Tree),
      Arity = cerl:call_arity(Tree),
      cerl:is_c_atom(Mod)
	andalso cerl:is_c_atom(Name)
	andalso (cerl:atom_val(Name) =:= '!')
	andalso (cerl:atom_val(Mod) =:= 'erlang')
	andalso (Arity =:= 2)
  end.

-spec is_call_to_spawn(cerl:cerl()) -> boolean().

%% For the spawn calls that return tuples of the kind:
%% {pid(), reference()}
is_call_to_spawn(Tree) ->
  case cerl:is_c_call(Tree) of
    false -> false;
    true ->
      Mod = cerl:call_module(Tree),
      Name = cerl:call_name(Tree),
      Arity = cerl:call_arity(Tree),
      case cerl:is_c_atom(Mod) andalso cerl:is_c_atom(Name) of
        true ->
          case {cerl:atom_val(Mod), cerl:atom_val(Name), Arity} of
            {'erlang', 'spawn_monitor', 1} -> true;
            {'erlang', 'spawn_monitor', 3} -> true;
            {'erlang', 'spawn_opt', 2} -> true;
            {'erlang', 'spawn_opt', 4} -> true;
            _Other -> false
          end;
        false -> false
      end
  end.

-spec is_call_to_spawn(cerl:cerl(), module(), dict()) ->
      {boolean(), 'false' | [dialyzer_races:pid_tags()]}.

is_call_to_spawn(Tree, M, VFTab) ->
  case cerl:is_c_call(Tree) of
    false ->
      case cerl:is_c_apply(Tree) of
        true ->
          ApplyOp = cerl:apply_op(Tree),
          case cerl:var_name(ApplyOp) of
            {F, A} ->
              MFA = {M, F, A},
              Ret =
                case ets:lookup(cfgs, MFA) of
                  [] -> [];
                  [{MFA, _Args, R, _Code}] -> R
                end,
              {false, Ret};
            _ ->
              case dict:find(cerl_trees:get_label(ApplyOp), VFTab) of
                'error' -> {false, false};
                {'ok', FunLabel} ->
                  Ret =
                    case ets:lookup(cfgs, FunLabel) of
                      [] -> [];
                      [{FunLabel, _Args, R, _Code}] -> R
                    end,
                  {false, Ret}
              end
          end;
        false -> {false, false}
      end;
    true ->
      Mod = cerl:call_module(Tree),
      Name = cerl:call_name(Tree),
      Arity = cerl:call_arity(Tree),
      case cerl:is_c_atom(Mod) andalso cerl:is_c_atom(Name) of
        true ->
          case {cerl:atom_val(Mod), cerl:atom_val(Name), Arity} of
            {'erlang', 'spawn', 1} -> {true, false};
            {'erlang', 'spawn', 2} -> {true, false};
            {'erlang', 'spawn', 3} -> {true, false};
            {'erlang', 'spawn', 4} -> {true, false};
            {'erlang', 'spawn_link', 1} -> {true, false};
            {'erlang', 'spawn_link', 2} -> {true, false};
            {'erlang', 'spawn_link', 3} -> {true, false};
            {'erlang', 'spawn_link', 4} -> {true, false};
            {'erlang', 'spawn_monitor', 1} -> {true, false};
            {'erlang', 'spawn_monitor', 3} -> {true, false};
            {'erlang', 'spawn_opt', 2} -> {true, false};
            {'erlang', 'spawn_opt', 3} -> {true, false};
            {'erlang', 'spawn_opt', 4} -> {true, false};
            {'erlang', 'spawn_opt', 5} -> {true, false};
            MFA ->
              Ret =
                case ets:lookup(cfgs, MFA) of
                  [] -> [];
                  [{MFA, _Args, R, _Code}] -> R
                end,
              {false, Ret}
          end;
        false -> {false, false}
      end
  end.

-spec is_call_to_whereis(cerl:cerl()) -> boolean().

is_call_to_whereis(Tree) ->
  case cerl:is_c_call(Tree) of
    false -> false;
    true ->
      Mod = cerl:call_module(Tree),
      Name = cerl:call_name(Tree),
      Arity = cerl:call_arity(Tree),
      cerl:is_c_atom(Mod)
	andalso cerl:is_c_atom(Name)
	andalso (cerl:atom_val(Name) =:= whereis)
	andalso (cerl:atom_val(Mod) =:= erlang)
	andalso (Arity =:= 1)
  end.

lists_intersection(List1, List2) ->
  Diff1 = List1 -- List2, %% elements that exist in List1 but not in List2
  Diff2 = List2 -- List1, %% elements that exist in List2 but not in List1
  (List1 ++ List2) -- (Diff1 ++ Diff2).

make_fun_args(Tree) ->
  [Mod, Fun, Arity] = cerl:call_args(Tree),
  case cerl:is_literal(Mod) andalso cerl:is_literal(Fun) andalso
    cerl:is_literal(Arity) of
    true ->
      M = cerl:concrete(Mod),
      F = cerl:concrete(Fun),
      A = cerl:concrete(Arity),
      {M, F, A};
    false -> ?no_args
  end.

renew_analyzed_pid_tags(OldPidTags, Msgs) ->
  Msgs#msgs{old_pids = OldPidTags}.

-spec var_call_assignment(non_neg_integer(), [cerl:cerl()],
                          erl_types:erl_type(), erl_types:erl_type(),
                          msgs()) ->
      msgs().

var_call_assignment(ArgLabel, [Var], ArgTypes, PidType,
                    #msgs{var_call_tab = VCTab} = Msgs) ->
  case erl_types:t_is_subtype(PidType, ArgTypes) of
    true ->
      case cerl:is_c_var(Var) of
        true ->
          VarLabel = cerl_trees:get_label(Var),
          VCTab1 = dict:store(ArgLabel, VarLabel, VCTab),
          Msgs#msgs{var_call_tab = VCTab1};
        false -> Msgs
      end;
    false -> Msgs
  end;
var_call_assignment(_ArgLabel, _Vars, _ArgTypes, _PidType, Msgs) ->
  Msgs.

-spec var_fun_assignment(cerl:cerl(), [cerl:cerl()],
                         dialyzer_callgraph:callgraph()) ->
      msgs().

var_fun_assignment(Arg, [Var], Callgraph) ->
  Msgs = dialyzer_callgraph:get_msgs(Callgraph),
  VFTab = Msgs#msgs.var_fun_tab,
  case cerl:is_c_fun(Arg) of
    true ->
      case cerl:is_c_var(Var) of
        true ->
          ArgLabel = cerl_trees:get_label(Arg),
          VarLabel = cerl_trees:get_label(Var),
          VFTab1 = dict:store(VarLabel, ArgLabel, VFTab),
          Msgs#msgs{var_fun_tab = VFTab1};
        false -> Msgs
      end;
    false ->
      case cerl:is_c_var(Var) of
        true ->
          case is_call_to_make_fun(Arg) of
            true ->
              case make_fun_args(Arg) of
                ?no_args -> Msgs;
                MFA ->
                  case dialyzer_callgraph:lookup_label(MFA, Callgraph) of
                    'error' -> Msgs;
                    {'ok', ArgLabel} ->
                      VarLabel = cerl_trees:get_label(Var),
                      VFTab1 = dict:store(VarLabel, ArgLabel, VFTab),
                      Msgs#msgs{var_fun_tab = VFTab1}
                  end
              end;
            false -> Msgs
          end;    
        false -> Msgs
      end
  end;
var_fun_assignment(_Arg, _Vars, Callgraph) ->
  dialyzer_callgraph:get_msgs(Callgraph).

%%% ===========================================================================
%%%
%%%  Warning Utilities
%%%
%%% ===========================================================================

add_warnings(Warns, #msgs{warnings = OldWarns} = Msgs) ->
  Msgs#msgs{warnings = Warns ++ OldWarns}.

check_rcv_pats([], _FileLine, Warns) ->
  Warns;
check_rcv_pats([Check], FileLine, Warns) ->
  warn_unused_rcv_pats(Check, FileLine, Warns);
check_rcv_pats([H|T], FileLine, Warns) ->
  Check = lists:foldl(fun(X, Acc) ->
                          lists:zipwith(fun(Y, Z) -> Y orelse Z end, Acc, X)
                      end, H, T),
  warn_unused_rcv_pats(Check, FileLine, Warns).

check_sent_msgs(SentMsgs, RcvTags, Warns) ->
  NoSends = length(SentMsgs),
  check_sent_msgs(SentMsgs, RcvTags, lists:duplicate(NoSends, true), Warns).

check_sent_msgs(_SentMsgs, [], Checks, Warns) ->
  {Checks, Warns};
check_sent_msgs(SentMsgs, [#rcv_fun{msgs = Msgs, file_line = FileLine}|T],
                PrevChecks, Warns) ->
  Checks = [[erl_types:t_is_subtype(SentMsg, Msg) || Msg <- Msgs]
            || SentMsg <- SentMsgs],
  Checks1 = [lists:any(fun(E) -> E end, Check) || Check <- Checks],
  Warns1 =
    case lists:any(fun(E) -> E end, lists:flatten(Checks1)) of
      true -> check_rcv_pats(Checks, FileLine, Warns);
      false ->
        W = {?WARN_MESSAGE, FileLine, {message_unused_rcv_stmt_no_msg, []}},
        [W|Warns]
    end,
  Checks2 = [lists:all(fun(E) -> not E end, Check) || Check <- Checks],
  NewChecks = lists:zipwith(fun(X, Y) -> X andalso Y end, PrevChecks, Checks2),
  check_sent_msgs(SentMsgs, T, NewChecks, Warns1).

format_suffix(Num) ->
  Rem = Num rem 10,
  integer_to_list(Num) ++
    case Rem of
      1 -> "st";
      2 -> "nd";
      3 -> "rd";
      _ -> "th"
    end.

format_unused_pats(UnusedPats) ->
  format_unused_pats(UnusedPats, "").

format_unused_pats([Num], Acc) ->
  Acc ++ format_suffix(Num);
format_unused_pats([Num1, Num2], Acc) ->
  Acc ++ format_suffix(Num1) ++ " and " ++ format_suffix(Num2);
format_unused_pats([Num|Nums], Acc) ->
  NewAcc = Acc ++ format_suffix(Num) ++ ", ",
  format_unused_pats(Nums, NewAcc).

-spec prioritize_msg_warns([dial_warning()]) -> [dial_warning()].

prioritize_msg_warns(Warns) ->
  SortedWarns = sort_warns(Warns),
  Warns1 = prioritize_warns1(SortedWarns, []),
  prioritize_warns3(Warns1, []).

prioritize_warns1([], Acc) ->
  Acc;
prioritize_warns1([Ws|Warns], Acc) ->
  NewAcc =
    case Ws of
      [] -> Acc;
      [H|T] -> [prioritize_warns2(T, H)|Acc]
    end,
  prioritize_warns1(Warns, NewAcc).

prioritize_warns2([], PrioWarn) ->
  PrioWarn;
prioritize_warns2(_Warns, {?WARN_MESSAGE, _FL,
                           {message_unused_rcv_stmt_no_send, _}} = PrioWarn) ->
  PrioWarn;
prioritize_warns2(_Warns, {?WARN_MESSAGE, _FL,
                           {message_unused_send_stmt, _ }} = PrioWarn) ->
  PrioWarn;
prioritize_warns2([{?WARN_MESSAGE, FL, {Type, Pats}} = H|T],
                  {?WARN_MESSAGE, FL, {PrioType, PrioPats}} = PrioWarn) ->
  NewPrioWarn =
    case PrioType of
      message_unused_rcv_stmt_no_msg ->
        case Type of
          message_unused_rcv_stmt_no_send -> H;
          _Other -> PrioWarn
        end;
      message_rcv_stmt_unused_pats ->
        case Type of
          message_unused_rcv_stmt_no_send -> H;
          message_unused_rcv_stmt_no_msg -> H;
          message_rcv_stmt_unused_pats ->
            {?WARN_MESSAGE, FL, {PrioType, lists_intersection(PrioPats, Pats)}}
        end
    end,
  prioritize_warns2(T, NewPrioWarn).

prioritize_warns3([], Acc) ->
  Acc;
prioritize_warns3([{?WARN_MESSAGE, _FL, {message_rcv_stmt_unused_pats, []}}|
                   Warns], Acc) ->
  prioritize_warns3(Warns, Acc);
prioritize_warns3([{?WARN_MESSAGE, FL, {message_rcv_stmt_unused_pats, Pats}}|
                   Warns], Acc) ->
  W =
    case lists:usort(Pats) of
      [_] = Pat ->
        {?WARN_MESSAGE, FL,
         {message_rcv_stmt_unused_pats, [{one, format_unused_pats(Pat)}]}};
      Sorted ->
        {?WARN_MESSAGE, FL,
         {message_rcv_stmt_unused_pats, [{more, format_unused_pats(Sorted)}]}}
    end,
  prioritize_warns3(Warns, [W|Acc]);
prioritize_warns3([W|Warns], Acc) ->
  prioritize_warns3(Warns, [W|Acc]).

sort_warns(Warns) ->
  case lists:keysort(2, Warns) of
    [] -> [];
    [{?WARN_MESSAGE, FileLine, _}|_Ws] = Sorted ->
      sort_warns(Sorted, FileLine, [])
  end.

sort_warns([], _FileLine, Acc) ->
  Acc;
sort_warns(Warns, FileLine, Acc) ->
  {NewWarns, NewFileLine, NewAccElem} = sort_warns1(Warns, FileLine, []),
  sort_warns(NewWarns, NewFileLine, [NewAccElem|Acc]).

sort_warns1([], FileLine, Acc) ->
  {[], FileLine, Acc};
sort_warns1([{?WARN_MESSAGE, FileLine, _} = W|Ws], FileLine, Acc) ->
  sort_warns1(Ws, FileLine, [W|Acc]);
sort_warns1([{?WARN_MESSAGE, FL, _}|_Ws] = Warns, _FileLine, Acc) ->
  {Warns, FL, Acc}.

warn_unused_rcv_pats(Bools, FileLine, Warns) ->
  UnusedPats = warn_unused_rcv_pats1(Bools, length(Bools), []),
  case UnusedPats of
    [] -> Warns;
    _Else ->
      W = {?WARN_MESSAGE, FileLine,
           {message_rcv_stmt_unused_pats, UnusedPats}},
      [W|Warns]
  end.

warn_unused_rcv_pats1([], _Counter, Acc) ->
  lists:sort(Acc);
warn_unused_rcv_pats1([Bool|Bools], Counter, Acc) ->
  NewAcc =
    case Bool of
      true -> Acc;
      false -> [Counter|Acc]
    end,
  warn_unused_rcv_pats1(Bools, Counter - 1, NewAcc).

warn_unused_send_rcv_stmts(SendTags, RcvTags) ->
  warn_unused_send_rcv_stmts(SendTags, RcvTags, []).

warn_unused_send_rcv_stmts([], [], Warns) ->
  Warns;
warn_unused_send_rcv_stmts([],
                           [#rcv_fun{msgs = Msgs, file_line = FileLine} = H|T],
                           Warns) ->
  BifMsgs = [B || B <- [bif_msg(M) || M <- Msgs], B =/= erl_types:t_none()],
  case BifMsgs of
    [] ->
      W = {?WARN_MESSAGE, FileLine, {message_unused_rcv_stmt_no_send, []}},
      warn_unused_send_rcv_stmts([], T, [W|Warns]);
    _Other ->
      {_, Ws} = check_sent_msgs(BifMsgs, [H], Warns),
      warn_unused_send_rcv_stmts([], T, Ws ++ Warns)
  end;
warn_unused_send_rcv_stmts(SendTags, RcvTags, Warns) ->
  SentMsgs = [T#send_fun.msg || T <- SendTags],
  {Checks, Warns1} = check_sent_msgs(SentMsgs, RcvTags, Warns),
  warn_unused_send_stmts(Checks, SendTags, Warns1).

warn_unused_send_stmts([], [], Warns) ->
  Warns;
warn_unused_send_stmts([Check|Checks], [#send_fun{file_line = FileLine}|Tags],
                       Warns) ->
  Warns1 =
    case Check of
      true ->
        W = {?WARN_MESSAGE, FileLine, {message_unused_send_stmt, []}},
        [W|Warns];
      false -> Warns
    end,
  warn_unused_send_stmts(Checks, Tags, Warns1).

%%% ===========================================================================
%%%
%%%  Record Interfaces
%%%
%%% ===========================================================================

-spec add_edge(dialyzer_callgraph:callgraph_edge(),
               dialyzer_dataflow:state()) ->
      dialyzer_dataflow:state().

add_edge(Edge, State) ->
  Callgraph = dialyzer_dataflow:state__get_callgraph(State),
  Msgs = dialyzer_callgraph:get_msgs(Callgraph),
  Edges = Msgs#msgs.edges,
  case lists:member(Edge, Edges) of
    true -> State;
    false ->
      NewMsgs = Msgs#msgs{edges = [Edge|Edges]},
      NewCallgraph = dialyzer_callgraph:put_msgs(NewMsgs, Callgraph),
      dialyzer_dataflow:state__put_callgraph(NewCallgraph, State)
  end.

-spec add_msg(erl_types:erl_type(), dialyzer_dataflow:state()) ->
      dialyzer_dataflow:state().

add_msg(RcvMsg, State) ->
  Callgraph = dialyzer_dataflow:state__get_callgraph(State),
  Msgs = dialyzer_callgraph:get_msgs(Callgraph),
  RcvTags = Msgs#msgs.rcv_tags,
  [H|T] = RcvTags,
  RcvMsgs = H#rcv_fun.msgs,
  NewMsgs = Msgs#msgs{rcv_tags = [H#rcv_fun{msgs = [RcvMsg|RcvMsgs]}|T]},
  NewCallgraph = dialyzer_callgraph:put_msgs(NewMsgs, Callgraph),
  dialyzer_dataflow:state__put_callgraph(NewCallgraph, State).

-spec add_pid(pid_kind(), non_neg_integer(), dialyzer_dataflow:state()) ->
      dialyzer_dataflow:state().

add_pid(Kind, Label, State) ->
  PidTags = dialyzer_dataflow:state__get_pid_tags(State),
  case PidTags of
    [] -> State;
    [H|T] ->
      case H#pid_fun.kind =:= Kind of
        true ->
          NewPidTags = [H#pid_fun{pid = Label}|T],
          dialyzer_dataflow:state__put_pid_tags(NewPidTags, State);
        false -> State
      end
  end.

-spec add_pid_tags([pid_fun()], msgs()) -> msgs().

add_pid_tags(PidTags, #msgs{pid_tags = PT} = Msgs) ->
  Msgs#msgs{pid_tags = lists:usort(PidTags ++ PT)}.

-spec create_indirect_pid_tag_for_self(non_neg_integer(),
                                       dialyzer_dataflow:state()) ->
      dialyzer_dataflow:state().

create_indirect_pid_tag_for_self(Label, State) ->
  Races = dialyzer_dataflow:state__get_races(State),
  CurrFun = dialyzer_races:get_curr_fun(Races),
  PidTags = dialyzer_dataflow:state__get_pid_tags(State),
  NewPidTag = #pid_fun{kind = 'self', pid = Label, pid_mfa = CurrFun,
                       fun_mfa = CurrFun},
  dialyzer_dataflow:state__put_pid_tags([NewPidTag|PidTags], State).

-spec create_indirect_pid_tags_for_spawn([dialyzer_races:pid_tags()],
                                         non_neg_integer(),
                                         dialyzer_dataflow:state()) ->
      dialyzer_dataflow:state().

create_indirect_pid_tags_for_spawn([], _Label, State) ->
  State;
create_indirect_pid_tags_for_spawn(['self'|T], Label, State) ->
  create_indirect_pid_tags_for_spawn(T, Label, State);
create_indirect_pid_tags_for_spawn([H|T], Label, State) ->
  #spawn_call{caller = Caller, callee = Callee} = H,
  Races = dialyzer_dataflow:state__get_races(State),
  CurrFun = dialyzer_races:get_curr_fun(Races),
  PidTags = dialyzer_dataflow:state__get_pid_tags(State),
  NewPidTag = #pid_fun{kind = 'spawn', pid = Label, pid_mfa = Callee,
                       fun_mfa = Caller, indirect = CurrFun},
  State1 = dialyzer_dataflow:state__put_pid_tags([NewPidTag|PidTags],
                                                 State),
  create_indirect_pid_tags_for_spawn(T, Label, State1).

-spec create_pid_tag_for_self(mfa_or_funlbl()) -> pid_fun().

create_pid_tag_for_self(CurrFun) ->
  #pid_fun{kind = 'self', pid_mfa = CurrFun, fun_mfa = CurrFun}.

-spec create_pid_tag_for_spawn(mfa_or_funlbl(), mfa_or_funlbl()) -> pid_fun().

create_pid_tag_for_spawn(PidMFA, CurrFun) ->
  #pid_fun{kind = 'spawn', pid_mfa = PidMFA, fun_mfa = CurrFun}.

-spec create_rcv_tag(mfa_or_funlbl(), file_line()) -> #rcv_fun{}.

create_rcv_tag(FunMFA, FileLine) ->
  #rcv_fun{fun_mfa = FunMFA, file_line = FileLine}.

-spec create_send_tag(dest(), erl_types:erl_type(), mfa_or_funlbl(),
                      file_line()) ->
      #send_fun{}.

create_send_tag(Pid, Msg, FunMFA, FileLine) ->
  #send_fun{pid = Pid, msg = Msg, fun_mfa = FunMFA,
            file_line = FileLine}.

-spec get_proc_reg(msgs()) -> proc_reg().

get_proc_reg(#msgs{proc_reg = ProcReg}) ->
  ProcReg.

-spec get_rcv_tags(msgs()) -> [#rcv_fun{}].

get_rcv_tags(#msgs{rcv_tags = RcvTags}) ->
  RcvTags.

-spec get_send_tags(msgs()) -> [#send_fun{}].

get_send_tags(#msgs{send_tags = SendTags}) ->
  SendTags.

-spec get_var_fun_tab(msgs()) -> dict().

get_var_fun_tab(#msgs{var_fun_tab = VFTab}) ->
  VFTab.

-spec get_warnings(msgs()) -> [dial_warning()].

get_warnings(#msgs{warnings = Warnings}) ->
  Warnings.

-spec get_whereis_argtypes(msgs()) -> [erl_types:erl_type()].

get_whereis_argtypes(#msgs{whereis_argtypes = WhereisArgtypes}) ->
  WhereisArgtypes.

-spec new() -> msgs().

new() -> #msgs{}.

-spec put_proc_reg(proc_reg(), msgs()) -> msgs().

put_proc_reg(ProcReg, Msgs) ->
  Msgs#msgs{proc_reg = ProcReg}.

-spec put_rcv_tags([#rcv_fun{}], msgs()) -> msgs().

put_rcv_tags(RcvTags, Msgs) ->
  Msgs#msgs{rcv_tags = RcvTags}.

-spec put_send_tags([#send_fun{}], msgs()) -> msgs().

put_send_tags(SendTags, Msgs) ->
  Msgs#msgs{send_tags = SendTags}.

-spec put_whereis_argtypes([erl_types:erl_type()], msgs()) -> msgs().

put_whereis_argtypes(WhereisArgtypes, Msgs) ->
  Msgs#msgs{whereis_argtypes = WhereisArgtypes}.

-spec update_proc_reg(label(), [atom()], mfa_or_funlbl(), proc_reg()) ->
      proc_reg().

update_proc_reg(_Label, [], RegMFA, {RegDict, RegMFAs} = ProcReg) ->
  case lists:member(RegMFA, RegMFAs) of
    true -> ProcReg;
    false -> {RegDict, [RegMFA|RegMFAs]}
  end;
update_proc_reg(Label, [Atom|Atoms], RegMFA, {RegDict, RegMFAs}) ->
  LabelsToStore =
    case dict:find(Atom, RegDict) of
      'error' -> [Label];
      {'ok', L} ->
        case lists:member(Label, L) of
          true -> L;
          false -> [Label|L]
        end
    end,
  update_proc_reg(Label, Atoms, RegMFA,
                  {dict:store(Atom, LabelsToStore, RegDict), RegMFAs}).
