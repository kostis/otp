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

-export([msg/1]).

%% Record Interfaces

-export([add_msg/2, add_pid/3, add_pid_tag/3, add_pid_tags/2,
         create_pid_tag_for_self/2, create_rcv_tag/2,
         create_send_tag/3, get_race_list_ret/3,
         get_rcv_tags/1, get_send_tags/1, new/0,
         put_rcv_tags/2, put_send_tags/2]).

%% Exported Types

-export_type([msgs/0, pid_fun/0]).

-include("dialyzer.hrl").
-include("dialyzer_heisenbugs.hrl").

%%% ===========================================================================
%%%
%%%  Types and Records
%%%
%%% ===========================================================================

-type pid_kind() :: 'self'.

-record(pid_fun,  {kind            :: pid_kind(),
                   pid = ?no_label :: label() | ?no_label,
                   pid_mfas        :: [mfa_or_funlbl()], % funs that own the pid
                   fun_mfa         :: mfa_or_funlbl()}).

-record(rcv_fun,  {msgs = []       :: [erl_types:erl_type()],
                   fun_mfa         :: mfa_or_funlbl(),
                   file_line       :: file_line()}).

-record(send_fun, {pid             :: label(),
                   msg             :: erl_types:erl_type(),
                   fun_mfa         :: mfa_or_funlbl()}).

-record(msgs,     {old_pids  = []  :: [#pid_fun{}], % already analyzed pid tags
                   pid_tags  = []  :: [#pid_fun{}],
                   rcv_tags  = []  :: [#rcv_fun{}],
                   send_tags = []  :: [#send_fun{}]}).

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
  AllPidTags = Msgs#msgs.pid_tags,
  OldPidTags = Msgs#msgs.old_pids,
  PidTags1 = PidTags -- OldPidTags,
  PidTagGroups = group_pid_tags(PidTags1, AllPidTags, Digraph),
  PidTagGroups1 = keep_subsets(PidTagGroups),
  State1 = msg1(PidTagGroups1, State),
  Callgraph1 = dialyzer_dataflow:state__get_callgraph(State1),
  Msgs1 = dialyzer_callgraph:get_msgs(Callgraph1),
  Msgs2 = add_analyzed_pid_tags(PidTags, Msgs1),
  Callgraph2 = dialyzer_callgraph:put_msgs(Msgs2, Callgraph1),
  dialyzer_dataflow:state__put_callgraph(Callgraph2, State1).

msg1(PidTagGroups, State) ->
  RetState =
    case PidTagGroups of
      [] -> State;
      [H|T] ->
        {Pids, PidMFAs, CurrFuns} = unzip_pid_tag_groups(H),
        Callgraph = dialyzer_dataflow:state__get_callgraph(State),
        Digraph = dialyzer_callgraph:get_digraph(Callgraph),
        Msgs = dialyzer_callgraph:get_msgs(Callgraph),
        SendTags = lists:usort(Msgs#msgs.send_tags),
        CFSendTags = find_control_flow_send_tags(CurrFuns, SendTags, Digraph),
        PidSendTags = go_from_pid_tags(CurrFuns, CurrFuns, Pids, CFSendTags,
                                       Callgraph),
        RcvTags =  lists:usort(Msgs#msgs.rcv_tags),
        UniquePidMFAs = lists:usort(PidMFAs),
        FilteredPidMFAs = filter_parents(UniquePidMFAs, Digraph),
        CFRcvTags = find_control_flow_rcv_tags(FilteredPidMFAs, RcvTags,
                                               Digraph),
        State1 = warn_unused_rcv_stmts(PidSendTags, CFRcvTags, State),
        %% HERE
        msg1(T, State1)
    end,
  dialyzer_dataflow:state__put_pid_tags([], RetState).

go_from_pid_tags([], _PidMFAs, _Pids, _SendTags, _Callgraph) ->
  [];
go_from_pid_tags([MFA|MFAs], PidMFAs, Pids, SendTags, Callgraph) ->
  Code =
    case ets:lookup(cfgs, MFA) of
      [] -> [];
      [{MFA, _Args, _Ret, C}] -> C
    end,
  PidSendTags = forward_msg_analysis(Pids, Code, PidMFAs, SendTags, Callgraph),
  PidSendTags ++ go_from_pid_tags(MFAs, PidMFAs, Pids, SendTags, Callgraph).

%%% ===========================================================================
%%%
%%%  Forward Analysis
%%%
%%% ===========================================================================

forward_msg_analysis(_Pids, _Code, _PidMFAs, [], _Callgraph) ->
  [];
forward_msg_analysis(Pids, Code, PidMFAs, SendTags, Callgraph) ->
  SendMFAs = [S#send_fun.fun_mfa || S <- SendTags],
  forward_msg_analysis(Pids, Code, SendTags, lists:usort(PidMFAs ++ SendMFAs),
                       [], dict:new(), Callgraph).

forward_msg_analysis(Pids, Code, SendTags, MFAs, Calls, MsgVarMap, Callgraph) ->
  case Code of
    [] -> find_pid_send_tags(Pids, SendTags, MsgVarMap);
    [Head|Tail] ->
      {NewPidSendTags, NewMsgVarMap} =
        case Head of
          'self' -> {[], MsgVarMap};
          #dep_call{} -> {[], MsgVarMap};
          #warn_call{} -> {[], MsgVarMap};
          #fun_call{caller = Caller, callee = MFAorLabel, vars = CallVars} ->
            Callee =
              case is_integer(MFAorLabel) of
                true ->
                  case dialyzer_callgraph:lookup_name(MFAorLabel, Callgraph) of
                    error -> MFAorLabel;
                    {ok, MFA} -> MFA
                  end;
                false -> MFAorLabel
              end,
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
                          forward_msg_analysis(Pids, CalleeCode, SendTags, MFAs,
                                               [{Caller, Callee}|Calls],
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
        forward_msg_analysis(Pids, Tail, SendTags, MFAs, Calls, NewMsgVarMap,
                             Callgraph)
  end.

%%% ===========================================================================
%%%
%%%  Utilities
%%%
%%% ===========================================================================

add_analyzed_pid_tags(PidTags, #msgs{old_pids = OldPidTags} = Msgs) ->
  Msgs#msgs{old_pids = lists:usort(PidTags ++ OldPidTags)}.

backward_msg_analysis(CurrFun, Digraph) ->
  Calls = digraph:edges(Digraph),
  Parents = dialyzer_races:fixup_race_backward(CurrFun, Calls, Calls, [],
                                               ?local),
  UParents = lists:usort(Parents),
  filter_parents(UParents, Digraph).

filter_parents(UParents, Digraph) ->
  dialyzer_races:filter_parents(UParents, UParents, Digraph).

find_control_flow_rcv_tags(PidFuns, RcvTags, Digraph) ->
  Accs = [find_control_flow_rcv_tags(PidFun, RcvTags, [], Digraph)
          || PidFun <- PidFuns],
  lists:usort(lists:flatten(Accs)).

find_control_flow_rcv_tags(_PidFun, [], Acc, _Digraph) ->
  Acc;
find_control_flow_rcv_tags(PidFun, [#rcv_fun{fun_mfa = RcvFun} = H|T],
                           Acc, Digraph) ->
  NewAcc =
    case PidFun =:= RcvFun of
      true -> [H|Acc];
      false ->
        case digraph:get_path(Digraph, PidFun, RcvFun) of
          false -> Acc;
          _List when is_list(_List) -> [H|Acc]
        end
    end,
  find_control_flow_rcv_tags(PidFun, T, NewAcc, Digraph).

find_control_flow_send_tags([], _SendTags, _Digraph) ->
  [];
find_control_flow_send_tags([PidFun|Tail], SendTags, Digraph) ->
  CFSendTags = find_control_flow_send_tags(PidFun, SendTags, [], Digraph),
  CFSendTags ++ find_control_flow_send_tags(Tail, SendTags, Digraph).

find_control_flow_send_tags(_PidFun, [], Acc, _Digraph) ->
  Acc;
find_control_flow_send_tags(PidFun, [#send_fun{fun_mfa = SendFun} = H|T],
                            Acc, Digraph) ->
  NewAcc =
    case PidFun =:= SendFun of
      true -> [H|Acc];
      false ->
        case digraph:get_path(Digraph, PidFun, SendFun) of
          false -> Acc;
          _List when is_list(_List) -> [H|Acc]
        end
    end,
  find_control_flow_send_tags(PidFun, T, NewAcc, Digraph).

find_pid_send_tags(Pids, CFSendTags, MsgVarMap) ->
  PidSendTags = [find_pid_send_tags(P, CFSendTags, [], MsgVarMap) || P <- Pids],
  lists:usort(lists:flatten(PidSendTags)).

find_pid_send_tags(_Pid, [], Acc, _MsgVarMap) ->
  Acc;
find_pid_send_tags(Pid, [#send_fun{pid = SendPid} = H|T], Acc, MsgVarMap) ->
  NewAcc =
    case Pid =:= SendPid of
      true -> [H|Acc];
      false ->
        case dialyzer_races:are_bound_labels(Pid, SendPid, MsgVarMap) orelse
          dialyzer_races:are_bound_labels(SendPid, Pid, MsgVarMap) of
          true -> [H|Acc];
          false -> Acc
        end
    end,
  find_pid_send_tags(Pid, T, NewAcc, MsgVarMap).

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

get_clause_ret(RaceList, State) ->
  case RaceList of
    [] -> [];
    [H|T] ->
      case H of
        #beg_clause{} -> [];
        #end_case{} -> get_race_list_ret1(T, 0, State);
        'self' -> ['self'];
        #fun_call{callee = Callee} ->
          Callgraph = dialyzer_dataflow:state__get_callgraph(State),
          {ok, MFA} =
            case is_integer(Callee) of
              true ->
                case dialyzer_callgraph:lookup_name(Callee, Callgraph) of
                  error -> {ok, Callee};
                  OkMFA -> OkMFA
                end;
              false -> {ok, Callee}
            end,
          case ets:lookup(cfgs, MFA) of
            [] -> [];
            [{MFA, _Args, Ret, _C}] -> Ret
          end;
        _ -> []
      end
  end.

%% Groups self tags that refer to the same process
group_pid_tags([], _Tags, _Digraph) ->
  [];
group_pid_tags([#pid_fun{kind = Kind, pid = Pid, fun_mfa = CurrFun} = H|T],
               Tags, Digraph) ->
  Group =
    case Kind =/= 'self' of
      true -> [];
      false ->
        case Pid =:= ?no_label of
          true -> [];
          false ->
            ReachableFrom = digraph_utils:reachable([CurrFun], Digraph),
            ReachingTo = digraph_utils:reaching([CurrFun], Digraph),
            [group_pid_tags1(H, ReachableFrom, ReachingTo, Tags)]
        end
    end,
  Group ++ group_pid_tags(T, Tags, Digraph).

group_pid_tags1(CurrTag, _ReachableFrom, _ReachingTo, []) ->
  [CurrTag];
group_pid_tags1(CurrTag, ReachableFrom, ReachingTo,
                [#pid_fun{kind = Kind, pid = Pid, fun_mfa = CurrFun} = H|T]) ->
  Member =
    case Kind =/= 'self' orelse Pid =:= ?no_label orelse CurrTag =:= H of
      true -> [];
      false ->
        case lists:member(CurrFun, ReachableFrom) orelse
          lists:member(CurrFun, ReachingTo) of
          true -> [H];
          false -> []
        end
    end,
  Member ++ group_pid_tags1(CurrTag, ReachableFrom, ReachingTo, T).

keep_subsets(Groups) ->
  keep_subsets(Groups, Groups, []).

keep_subsets([], Groups, Acc) ->
  lists:usort(Groups -- Acc);
keep_subsets([H|T], Groups, Acc) ->
  NewAcc = 
    case lists:member(H, Acc) of
      true -> Acc;
      false -> keep_subsets1(H, Groups, Acc)
    end,
  keep_subsets(T, Groups, NewAcc).

keep_subsets1(_G, [], Acc) ->
  Acc;
keep_subsets1(G, [H|T], Acc) ->
  NewAcc = 
    case G =:= H of
      true -> Acc;
      false ->
        case G -- H of
          [] -> [H|Acc];
          _ -> Acc
        end
    end,
  keep_subsets1(G, T, NewAcc).

unzip_pid_tag_groups(Ts) -> unzip_pid_tag_groups(Ts, [], [], []).

unzip_pid_tag_groups([#pid_fun{pid = X,
                               pid_mfas = Y,
                               fun_mfa = Z}|
                      Ts], Xs, Ys, Zs) ->
  unzip_pid_tag_groups(Ts, [X|Xs], Y ++ Ys, [Z|Zs]);
unzip_pid_tag_groups([], Xs, Ys, Zs) ->
  {Xs, Ys, Zs}.

-spec get_race_list_ret(dialyzer_races:code(), erl_types:erl_type(),
                        dialyzer_dataflow:state()) ->
      dialyzer_races:code().

get_race_list_ret([], _RetType, _State) -> [];
get_race_list_ret([#end_case{}|RaceList], RetType, State) ->
  PidType = erl_types:t_pid(),
  case erl_types:t_is_subtype(PidType, RetType) of
    true -> lists:flatten(get_race_list_ret1(RaceList, 0, State));
    false -> []
  end.

get_race_list_ret1(RaceList, NestingLevel, State) ->
  case RaceList of
    [] -> [];
    [H|T] ->
      {Ret, NestingLevel1} =
        case H of
          'beg_case' -> {[], NestingLevel - 1};
          #end_clause{} ->
            case NestingLevel =:= 0 of
              true -> {get_clause_ret(T, State), NestingLevel};
              false -> {[], NestingLevel}
            end;
          #end_case{} -> {[], NestingLevel + 1};
          _ -> {[], NestingLevel}
        end,
      case NestingLevel1 =:= -1 of
        true -> Ret;
        false ->
          Ret ++ get_race_list_ret1(T, NestingLevel1, State)
      end
  end.
        
%%% ===========================================================================
%%%
%%%  Warning Format Utilities
%%%
%%% ===========================================================================

check_sent_msgs(_SentMsgs, [], State) ->
  State;
check_sent_msgs(SentMsgs, [#rcv_fun{msgs = Msgs, file_line = FileLine}|T],
                State) ->
  Checks = [lists:any(fun(Msg) -> erl_types:t_is_subtype(SentMsg, Msg) end,
                      Msgs)
            || SentMsg <- SentMsgs],
  State1 = 
    case lists:any(fun(E) -> E end, lists:flatten(Checks)) of
      true -> State;
      false ->
        W = {?WARN_MESSAGE, FileLine, {message_unused_rcv_stmt_no_msg, []}},
        dialyzer_dataflow:state__add_warning(W, State)
    end,
  check_sent_msgs(SentMsgs, T, State1).

warn_unused_rcv_stmts([], [], State) ->
  State;
warn_unused_rcv_stmts([], [#rcv_fun{file_line = FileLine}|T], State) ->
  W = {?WARN_MESSAGE, FileLine, {message_unused_rcv_stmt_no_send, []}},
  State1 = dialyzer_dataflow:state__add_warning(W, State),
  warn_unused_rcv_stmts([], T, State1);
warn_unused_rcv_stmts(SendTags, RcvTags, State) ->
  SentMsgs = [T#send_fun.msg || T <- SendTags],
  check_sent_msgs(SentMsgs, RcvTags, State).

%%% ===========================================================================
%%%
%%%  Record Interfaces
%%%
%%% ===========================================================================

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
  [H|T] = PidTags,
  case H#pid_fun.kind =:= Kind of
    true ->
      NewPidTags = [H#pid_fun{pid = Label}|T],
      dialyzer_dataflow:state__put_pid_tags(NewPidTags, State);
    false -> State
  end.  

-spec add_pid_tag(pid_kind(), non_neg_integer(), dialyzer_dataflow:state()) ->
      dialyzer_dataflow:state().

add_pid_tag(Kind, Label, State) ->
  Callgraph = dialyzer_dataflow:state__get_callgraph(State),
  Digraph = dialyzer_callgraph:get_digraph(Callgraph),
  Races = dialyzer_dataflow:state__get_races(State),
  CurrFun = dialyzer_races:get_curr_fun(Races),
  Dads = backward_msg_analysis(CurrFun, Digraph),
  PidTags = dialyzer_dataflow:state__get_pid_tags(State),
  NewPidTag = #pid_fun{kind = Kind, pid = Label, pid_mfas = Dads,
                       fun_mfa = CurrFun},
  dialyzer_dataflow:state__put_pid_tags([NewPidTag|PidTags], State).

-spec add_pid_tags([pid_fun()], msgs()) -> msgs().

add_pid_tags(PidTags, #msgs{pid_tags = PT} = Msgs) ->
  Msgs#msgs{pid_tags = lists:usort(PidTags ++ PT)}.

-spec create_pid_tag_for_self(mfa_or_funlbl(), digraph()) ->
      pid_fun().

create_pid_tag_for_self(CurrFun, Digraph) ->
  Dads = backward_msg_analysis(CurrFun, Digraph),
  #pid_fun{kind = 'self', pid_mfas = Dads, fun_mfa = CurrFun}.

-spec create_rcv_tag(mfa_or_funlbl(), file_line()) -> #rcv_fun{}.

create_rcv_tag(FunMFA, FileLine) ->
  #rcv_fun{fun_mfa = FunMFA, file_line = FileLine}.

-spec create_send_tag(label(), erl_types:erl_type(), mfa_or_funlbl()) ->
      #send_fun{}.

create_send_tag(Pid, Msg, FunMFA) ->
  #send_fun{pid = Pid, msg = Msg, fun_mfa = FunMFA}.

-spec get_rcv_tags(msgs()) -> [#rcv_fun{}].

get_rcv_tags(#msgs{rcv_tags = RcvTags}) ->
  RcvTags.

-spec get_send_tags(msgs()) -> [#send_fun{}].

get_send_tags(#msgs{send_tags = SendTags}) ->
  SendTags.

-spec new() -> msgs().

new() -> #msgs{}.

-spec put_rcv_tags([#rcv_fun{}], msgs()) -> msgs().

put_rcv_tags(RcvTags, Msgs) ->
  Msgs#msgs{rcv_tags = RcvTags}.

-spec put_send_tags([#send_fun{}], msgs()) -> msgs().

put_send_tags(SendTags, Msgs) ->
  Msgs#msgs{send_tags = SendTags}.
