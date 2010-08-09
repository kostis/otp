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
         create_pid_tag_for_self/1, create_rcv_tag/2,
         create_send_tag/4, get_race_list_ret/3,
         get_proc_reg/1, get_rcv_tags/1, get_send_tags/1,
         new/0, put_proc_reg/2, put_rcv_tags/2,
         put_send_tags/2, update_proc_reg/4]).

%% Exported Types

-export_type([msgs/0, pid_fun/0]).

-include("dialyzer.hrl").
-include("dialyzer_heisenbugs.hrl").

%%% ===========================================================================
%%%
%%%  Types and Records
%%%
%%% ===========================================================================

-type dest()     :: label() | ?no_label | [atom()].
-type pid_kind() :: 'self'.
-type proc_reg() :: {dict(), [mfa_or_funlbl()]}.
% process registry associating atoms to pids and
% mfas that contain the associations
% (i.e. the 'register' calls)

-record(pid_fun,  {kind            :: pid_kind(),
                   pid = ?no_label :: label() | ?no_label,
                   pid_mfa         :: mfa_or_funlbl(), % fun that owns the pid
                   fun_mfa         :: mfa_or_funlbl()}).

-record(rcv_fun,  {msgs = []       :: [erl_types:erl_type()],
                   fun_mfa         :: mfa_or_funlbl(),
                   file_line       :: file_line()}).

-record(send_fun, {pid             :: dest(),
                   msg             :: erl_types:erl_type(),
                   fun_mfa         :: mfa_or_funlbl(),
                   file_line       :: file_line()}).

-record(msgs,     {old_pids  = []  :: [#pid_fun{}], % already analyzed pid tags
                   pid_tags  = []  :: [#pid_fun{}],
                   rcv_tags  = []  :: [#rcv_fun{}],
                   send_tags = []  :: [#send_fun{}],
                   proc_reg  = {dict:new(), []} :: proc_reg()}).

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
  {OldPidTags1, PidTagGroups} = group_pid_tags(PidTags1, AllPidTags,
                                               OldPidTags, Digraph),
  SortedSendTags = lists:usort(Msgs#msgs.send_tags),
  SortedRcvTags = lists:usort(Msgs#msgs.rcv_tags),
  ProcReg = Msgs#msgs.proc_reg,
  State1 = msg1(PidTagGroups, SortedSendTags, SortedRcvTags, ProcReg, State),
  Callgraph1 = dialyzer_dataflow:state__get_callgraph(State1),
  Msgs1 = dialyzer_callgraph:get_msgs(Callgraph1),
  Msgs2 = renew_analyzed_pid_tags(OldPidTags1, Msgs1),
  Callgraph2 = dialyzer_callgraph:put_msgs(Msgs2, Callgraph1),
  dialyzer_dataflow:state__put_callgraph(Callgraph2, State1).

msg1(PidTagGroups, SendTags, RcvTags, ProcReg, State) ->
  Callgraph = dialyzer_dataflow:state__get_callgraph(State),
  Warns = msg1(PidTagGroups, SendTags, RcvTags, ProcReg, [], Callgraph),
  State1 = prioritize_warns(Warns, State),
  dialyzer_dataflow:state__put_pid_tags([], State1).

msg1(PidTagGroups, SendTags, RcvTags, ProcReg, Warns, Callgraph) ->
  case PidTagGroups of
    [] -> Warns;
    [H|T] ->
      {#pid_fun{kind = Kind, pid = Pid, pid_mfa = PidMFA, fun_mfa = CurrFun},
       MsgVarMap} = H,
      Digraph = dialyzer_callgraph:get_digraph(Callgraph),
      CFSendTags = find_control_flow_send_tags(CurrFun, SendTags, Digraph),
      PidSendTags = go_from_pid_tag(CurrFun, Pid, CFSendTags, ProcReg,
                                    MsgVarMap, Callgraph),
      PidMFAs =
        case Kind =:= 'self' of
          true -> backward_msg_analysis(CurrFun, Digraph);
          false -> [PidMFA]
        end,
      CFRcvTags = find_control_flow_rcv_tags(PidMFAs, RcvTags, Digraph),
      Warns1 = warn_unused_send_rcv_stmts(PidSendTags, CFRcvTags),
      msg1(T, SendTags, RcvTags, ProcReg, Warns1 ++ Warns, Callgraph)
  end.

go_from_pid_tag(MFA, Pid, SendTags, ProcReg, MsgVarMap, Callgraph) ->
  Code =
    case ets:lookup(cfgs, MFA) of
      [] -> [];
      [{MFA, _Args, _Ret, C}] -> C
    end,
  forward_msg_analysis(Pid, Code, SendTags, ProcReg, MsgVarMap, Callgraph).

%%% ===========================================================================
%%%
%%%  Forward Analysis
%%%
%%% ===========================================================================

forward_msg_analysis(_Pid, _Code, [], _ProcReg, _MsgVarMap, _Callgraph) ->
  [];
forward_msg_analysis(Pid, Code, SendTags, {RegDict, RegMFAs}, MsgVarMap,
                     Callgraph) ->
  SendMFAs = [S#send_fun.fun_mfa || S <- SendTags],
  PidSendTags = forward_msg_analysis(Pid, Code, SendTags,
                                     lists:usort(RegMFAs ++ SendMFAs),
                                     RegDict, [], MsgVarMap, Callgraph),
  lists:usort(PidSendTags).

forward_msg_analysis(Pid, Code, SendTags, MFAs, RegDict, Calls, MsgVarMap,
                     Callgraph) ->
  case Code of
    [] -> find_pid_send_tags(Pid, SendTags, RegDict, MsgVarMap);
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
                          forward_msg_analysis(Pid, CalleeCode, SendTags,
                                               MFAs, RegDict,
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
        forward_msg_analysis(Pid, Tail, SendTags, MFAs, RegDict, Calls,
                             NewMsgVarMap, Callgraph)
  end.

%%% ===========================================================================
%%%
%%%  Utilities
%%%
%%% ===========================================================================

backward_msg_analysis(CurrFun, Digraph) ->
  Calls = digraph:edges(Digraph),
  Parents = dialyzer_races:fixup_race_backward(CurrFun, Calls, Calls, [],
                                               ?local),
  UParents = lists:usort(Parents),
  filter_parents(UParents, Digraph).

bind_dict_vars(Label1, Label2, Dict) ->
  TempDict = dialyzer_races:bind_dict_vars(Label1, Label2, Dict),
  dialyzer_races:bind_dict_vars(Label2, Label1, TempDict).

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

find_control_flow_send_tags(PidFun, SendTags, Digraph) ->
  ReachableFrom = digraph_utils:reachable([PidFun], Digraph),
  find_control_flow_send_tags(PidFun, SendTags, [], ReachableFrom).

find_control_flow_send_tags(_PidFun, [], Acc, _ReachableFrom) ->
  Acc;
find_control_flow_send_tags(_PidFun, _SendTags, Acc, []) ->
  Acc;
find_control_flow_send_tags(PidFun, [#send_fun{fun_mfa = SendFun} = H|T],
                            Acc, ReachableFrom) ->
  NewAcc =
    case PidFun =:= SendFun of
      true -> [H|Acc];
      false ->
        case lists:member(SendFun, ReachableFrom) of
          true -> [H|Acc];
          false -> Acc
        end
    end,
  find_control_flow_send_tags(PidFun, T, NewAcc, ReachableFrom).

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

%% Groups self tags that refer to the same process
%% in the form of the highest ancestor
group_pid_tags([], _Tags, OldTags, _Digraph) ->
  {OldTags, []};
group_pid_tags([#pid_fun{kind = Kind, pid = Pid, fun_mfa = CurrFun} = H|T],
               Tags, OldTags, Digraph) ->
  {NewOldTags, Group} =
    case Kind =/= 'self' of
      true -> {OldTags, []};
      false ->
        case Pid =:= ?no_label of
          true -> {OldTags, []};
          false ->
            case lists:member(H, OldTags) of
              true -> {OldTags, []};
              false ->
                ReachableFrom = digraph_utils:reachable([CurrFun], Digraph),
                ReachingTo = digraph_utils:reaching([CurrFun], Digraph),
                {RetTags, RetDad, RetMVM} =
                  group_pid_tags1(H, Tags, [H|OldTags], ReachableFrom,
                                  ReachingTo, Digraph, H, dict:new()),
                {RetTags, [{RetDad, RetMVM}]}
            end
        end
    end,
  {RetOldTags, RetGroups} = group_pid_tags(T, Tags, NewOldTags, Digraph),
  {RetOldTags, Group ++ RetGroups}.

group_pid_tags1(_CurrTag, [], OldTags, _ReachableFrom, _ReachingTo, _Digraph,
                Dad, MsgVarMap) ->
  {OldTags, Dad, MsgVarMap};
group_pid_tags1(#pid_fun{pid = CurrTagPid, fun_mfa = CurrTagFun} = CurrTag,
                [#pid_fun{kind = Kind, pid = Pid, fun_mfa = CurrFun} = H|T],
                OldTags, ReachableFrom, ReachingTo, Digraph,
                #pid_fun{fun_mfa = DadCurrFun} = Dad, MsgVarMap) ->
  {NewOldTags, NewDad, NewMsgVarMap} =
    case Kind =/= 'self' orelse Pid =:= ?no_label orelse CurrTag =:= H orelse
      lists:member(H, OldTags) of
      true -> {OldTags, Dad, MsgVarMap};
      false ->
        case CurrTagFun =:= CurrFun of
          true ->
            {[H|OldTags], Dad, bind_dict_vars(CurrTagPid, Pid, MsgVarMap)};
          false ->
            case lists:member(CurrFun, ReachableFrom) of
              true ->
                {[H|OldTags], Dad, bind_dict_vars(CurrTagPid, Pid, MsgVarMap)};
              false ->
                case lists:member(CurrFun, ReachingTo) of
                  true ->
                    case digraph:get_path(Digraph, CurrFun, DadCurrFun) of
                      false ->
                        {[H|OldTags], Dad,
                         bind_dict_vars(CurrTagPid, Pid, MsgVarMap)};
                      _Vertices ->
                        {[H|OldTags], H,
                         bind_dict_vars(CurrTagPid, Pid, MsgVarMap)}
                    end;
                  false -> {OldTags, Dad, MsgVarMap}
                end
            end
        end
    end,
  group_pid_tags1(CurrTag, T, NewOldTags, ReachableFrom, ReachingTo, Digraph,
                  NewDad, NewMsgVarMap).

is_bound_reg_name(Atom, Pid, RegDict, MVM) ->
  case dict:find(Atom, RegDict) of
    'error' -> false;
    {ok, List} ->
      Checks = [begin
                  E =:= Pid orelse
                    dialyzer_races:are_bound_labels(Pid, E, MVM) orelse
                    dialyzer_races:are_bound_labels(E, Pid, MVM)
                end || E <- List],
      lists:any(fun(E) -> E end, Checks)
  end.

renew_analyzed_pid_tags(OldPidTags, Msgs) ->
  Msgs#msgs{old_pids = OldPidTags}.
        
%%% ===========================================================================
%%%
%%%  Warning Utilities
%%%
%%% ===========================================================================

add_warns([], State) ->
  State;
add_warns([W|Warns], State) ->
  State1 = dialyzer_dataflow:state__add_warning(W, State),
  add_warns(Warns, State1).

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

prioritize_warns(Warns, State) ->
  SortedWarns = sort_warns(Warns),
  Warns1 = prioritize_warns1(SortedWarns, []),
  add_warns(Warns1, State).

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
prioritize_warns2([{?WARN_MESSAGE, _FL, {Type, _}} = H|T],
                  {?WARN_MESSAGE, _FL, {PrioType, _}} = PrioWarn) ->
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
          _Other -> PrioWarn
        end
    end,
  prioritize_warns2(T, NewPrioWarn).

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
           {message_rcv_stmt_unused_pats, [format_unused_pats(UnusedPats)]}},
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
warn_unused_send_rcv_stmts([], [#rcv_fun{file_line = FileLine}|T], Warns) ->
  W = {?WARN_MESSAGE, FileLine, {message_unused_rcv_stmt_no_send, []}},
  warn_unused_send_rcv_stmts([], T, [W|Warns]);
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
  Races = dialyzer_dataflow:state__get_races(State),
  CurrFun = dialyzer_races:get_curr_fun(Races),
  PidTags = dialyzer_dataflow:state__get_pid_tags(State),
  NewPidTag = #pid_fun{kind = Kind, pid = Label, fun_mfa = CurrFun},
  dialyzer_dataflow:state__put_pid_tags([NewPidTag|PidTags], State).

-spec add_pid_tags([pid_fun()], msgs()) -> msgs().

add_pid_tags(PidTags, #msgs{pid_tags = PT} = Msgs) ->
  Msgs#msgs{pid_tags = lists:usort(PidTags ++ PT)}.

-spec create_pid_tag_for_self(mfa_or_funlbl()) -> pid_fun().

create_pid_tag_for_self(CurrFun) ->
  #pid_fun{kind = 'self', fun_mfa = CurrFun}.

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
