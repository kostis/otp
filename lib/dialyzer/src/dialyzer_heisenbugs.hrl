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
%%% File    : dialyzer_heisenbugs.hrl
%%% Author  : Maria Christakis <christakismaria@gmail.com>
%%% Description : Header file for concurrency analysis
%%%
%%% Created : 15 Feb 2010 by Maria Christakis <christakismaria@gmail.com>
%%%----------------------------------------------------------------------

%%% ===========================================================================
%%%
%%%  Definitions
%%%
%%% ===========================================================================

-define(local, 5).

-define(no_arg, no_arg).
-define(no_label, no_label).
-define(bypassed, bypassed).

%%% ===========================================================================
%%%
%%%  Types
%%%
%%% ===========================================================================

-type label_type()  :: label() | [label()] | {label()} | ?no_label.
-type args()        :: [label_type() | [string()]].
-type core_vars()   :: cerl:cerl() | ?no_arg | ?bypassed.
-type var_to_map1() :: core_vars() | [cerl:cerl()].

-type dep_calls()  :: 'whereis' | 'ets_lookup' | 'mnesia_dirty_read'.
-type warn_calls() :: 'register' | 'unregister' | 'ets_insert'
                    | 'mnesia_dirty_write'.

%%% ===========================================================================
%%%
%%%  Records
%%%
%%% ===========================================================================

-record(beg_clause, {arg        :: var_to_map1(),
                     pats       :: var_to_map1(),
                     guard      :: cerl:cerl()}).

-record(end_clause, {arg        :: var_to_map1(),
                     pats       :: var_to_map1(),
                     guard      :: cerl:cerl()}).

-record(end_case,   {clauses    :: [#end_clause{}]}).

-record(dep_call,   {call_name  :: dep_calls(),
                     args       :: args(),
                     arg_types  :: [erl_types:erl_type()],
                     vars       :: [core_vars()],
                     state      :: _, %% XXX: recursive
                     file_line  :: file_line(),
                     var_map    :: dict()}).

-record(fun_call,   {caller     :: mfa_or_funlbl(),
                     callee     :: mfa_or_funlbl(),
                     arg_types  :: [erl_types:erl_type()],
                     vars       :: [core_vars()]}).

-record(let_tag,    {var        :: var_to_map1(),
                     arg        :: var_to_map1()}).

-record(spawn_call, {caller     :: mfa_or_funlbl(),
                     callee     :: mfa_or_funlbl(),
                     vars       :: [core_vars()]}).

-record(warn_call,  {call_name  :: warn_calls(),
                     args       :: args(),
                     var_map    :: dict()}).
