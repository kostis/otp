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
%%% File    : dialyzer_deadlocks.erl
%%% Author  : Maria Christakis <christakismaria@gmail.com>
%%% Description : Utility functions for deadlock detection 
%%%
%%% Created : 30 Jan 2010 by Maria Christakis <christakismaria@gmail.com>
%%%----------------------------------------------------------------------
-module(dialyzer_deadlocks).

%% Deadlock Analysis

-export([store_call/6, deadlock/1]).

-export_type([dls/0]).

-include("dialyzer.hrl").

%%% ===========================================================================
%%%
%%%  Local Types
%%%
%%% ===========================================================================

-record(dl, {mfa1      :: mfa(),
             mfa2      :: mfa(),
             args      :: [dialyzer_races:core_vars()],
             arg_types :: [erl_types:erl_type()],
             state     :: _, %% XXX: recursive 
             file_line :: file_line()}).

%%% ===========================================================================
%%%
%%%  Exported Types
%%%
%%% ===========================================================================

-type dls() :: [#dl{}].

%%% ===========================================================================
%%%
%%%  Deadlock Analysis
%%%
%%% ===========================================================================

-spec store_call(mfa_or_funlbl(), mfa(),
                 [dialyzer_races:core_vars()],
                 [erl_types:erl_type()], file_line(),
                 dialyzer_dataflow:state()) ->
      dialyzer_dataflow:state().

store_call(Fun, RealFun, Args, ArgTypes, {File, Line}, State) ->
  case Fun of
    {gen_server, call, A} when A =:= 2 orelse A =:= 3 ->
      CleanState = dialyzer_dataflow:state__records_only(State),
      state__renew_tags(#dl{mfa1 = Fun, mfa2 = RealFun,
                            args = Args, arg_types = ArgTypes,
                            state = CleanState,
                            file_line = {File, Line}},
                        State);
    _Other -> State
  end.

-spec deadlock(dialyzer_dataflow:state()) -> dialyzer_dataflow:state().

deadlock(State) ->
  Callgraph = dialyzer_dataflow:state__get_callgraph(State),
  Digraph = dialyzer_callgraph:get_digraph(Callgraph),
  Tags = dialyzer_callgraph:get_deadlocks(Callgraph),
  warn_about_cycles(Tags, Digraph, State).

warn_about_cycles([], _Digraph, State) ->
  State;
warn_about_cycles([#dl{mfa2 = MFA} = Tag|Tags] = L, Digraph, State) ->
  {NewTags, NewState} = 
    case digraph:get_cycle(Digraph, MFA) of
      false -> {Tags, State};
      [MFA|SyncMFAs] ->
        SyncCalls = [C || T <- SyncMFAs -- [MFA],
                          (C = lists:keyfind(T, 3, L)) =/= false],
        Warn = get_dl_warn(Tag, SyncCalls),
%%         Tags1 = Tags -- SyncCalls,
%%         Callgraph = dialyzer_dataflow:state__get_callgraph(State),
%%         Callgraph1 = dialyzer_callgraph:put_deadlocks(Tags1, Callgraph),
%%         State1 = dialyzer_dataflow:state__put_callgraph(Callgraph1, State),
%%         State2 = dialyzer_dataflow:state__add_warning(Warn, State1),
%%         {Tags1, State2}
        {Tags, dialyzer_dataflow:state__add_warning(Warn, State)}
    end,
  warn_about_cycles(NewTags, Digraph, NewState).

%%% ===========================================================================
%%%
%%%  Utilities
%%%
%%% ===========================================================================

state__renew_tags(#dl{mfa2 = MFA} = Tag, State) ->
  Callgraph = dialyzer_dataflow:state__get_callgraph(State),
  Tags = dialyzer_callgraph:get_deadlocks(Callgraph),
  case lists:keymember(MFA, 3, Tags) of
    true -> State;
    false ->
      NewTags = [Tag|Tags],
      NewCallgraph = dialyzer_callgraph:put_deadlocks(NewTags, Callgraph),
      dialyzer_dataflow:state__put_callgraph(NewCallgraph, State)
  end.

%%% ===========================================================================
%%%
%%%  Warning Format Utilities
%%%
%%% ===========================================================================

get_dl_warn(#dl{mfa1 = MFA,
                args = Args,
                arg_types = ArgTypes,
                state = CleanState,
                file_line = FileLine},
            SyncCalls) ->
  {M, F, _A} = MFA,
  Arguments = dialyzer_dataflow:format_args(Args, ArgTypes, CleanState),
  {?WARN_DEADLOCK, FileLine,
   {deadlock, [M, F, Arguments,
               get_reason(lists:keysort(7, SyncCalls))]}}.

get_reason([]) ->
  "will result in a deadlock since it forms a circular "
  "sequence of synchronous calls with itself";
get_reason(SyncCalls) ->
  get_reason(SyncCalls, "will result in a deadlock since it forms a circular "
                        "sequence of synchronous calls with the calls ").

get_reason([#dl{mfa1 = MFA, args = Args, arg_types = ArgTypes,
                state = CleanState, file_line = {File, Line}}|T],
           Reason) ->
  {M, F, _A} = MFA,
  R =
    Reason ++
    case M of
      gen_server ->
        case F of
          call -> "gen_server:call"
        end
    end ++
    dialyzer_dataflow:format_args(Args, ArgTypes, CleanState) ++
    " in " ++
    filename:basename(File) ++
    " on line " ++
    lists:flatten(io_lib:write(Line)),
  case T of
    [] -> R;
    _ -> get_reason(T, R ++ ", ")
  end.
