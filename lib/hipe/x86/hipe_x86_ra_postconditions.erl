%% -*- erlang-indent-level: 2 -*-
%%
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2001-2010. All Rights Reserved.
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

-ifdef(HIPE_AMD64).
-define(HIPE_X86_RA_POSTCONDITIONS,	hipe_amd64_ra_postconditions).
-define(HIPE_X86_REGISTERS,		hipe_amd64_registers).
-define(HIPE_X86_SPECIFIC,		hipe_amd64_specific).
-define(ECX,				rcx).
-else.
-define(HIPE_X86_RA_POSTCONDITIONS,	hipe_x86_ra_postconditions).
-define(HIPE_X86_REGISTERS,		hipe_x86_registers).
-define(HIPE_X86_SPECIFIC,		hipe_x86_specific).
-define(ECX,				ecx).
-endif.

-module(?HIPE_X86_RA_POSTCONDITIONS).

-export([check_and_rewrite/4]).

-include("../x86/hipe_x86.hrl").
-define(HIPE_INSTRUMENT_COMPILER, true).
-include("../main/hipe.hrl").
-include("../flow/cfg.hrl").
-include("../flow/hipe_bb.hrl").
-define(count_temp(T), ?cons_counter(counter_mfa_mem_temps, T)).

%%-define(MAX_RANGE_SPLIT_ITERATIONS, 10).
-define(MAX_SPILL_COUNT, 9).

check_and_rewrite(Defun, Coloring, Strategy, Options) ->
  %% io:format("Converting\n"),
  TempMap = hipe_temp_map:cols2tuple(Coloring, ?HIPE_X86_SPECIFIC),
  %% io:format("Rewriting\n"),
  #defun{code=Code0} = Defun,
  ?ASSERT(lists:all(fun ({Id, V}) -> element(Id+1, TempMap) =:= V end, Coloring)),
  case proplists:get_bool(range_split, Options)
    andalso proplists:get_value(regalloc, Options) =/= linear_scan of
    true ->
      ?option_time(
	check_and_rewrite_range_split(Defun, Coloring, Strategy, TempMap, Code0),
	"Live range splitting", Options);
    false ->
      check_and_rewrite_spill(Defun, Coloring, Strategy, TempMap, Code0)
  end.

check_and_rewrite_spill(Defun, _Coloring, Strategy, TempMap, Code0) ->
  {Code1, DidSpill} = do_insns(Code0, TempMap, Strategy, [], false),
  {Defun#defun{code = Code1, var_range = {0, hipe_gensym:get_var(x86)}},
   DidSpill}.

%%
%% Auxiliary functions
%%

delay2([_A]) -> [];
delay2([A | [B|_]=Rest]) -> [{A,B} | delay2(Rest)].

delay3([_A]) -> [];
delay3([_A, _B]) -> [];
delay3([A | [B, C|_]=Rest]) -> [{A, B, C} | delay3(Rest)].

find(_Pred, [])   -> notfound;
find(Pred, [H|R]) ->
  case Pred(H) of
    true  -> {found, H};
    false -> find(Pred, R)
  end.

-define(IMPLIES(A, B), (not(A) orelse (B))).

-define(WHENFALSE(Expr, Do), case (Expr) of
			       true -> true;
			       false -> Do, false
			     end).

gb_trees_from_list(KeyValues) ->
  lists:foldl(fun ({Key,Val}, Tree) -> gb_trees:insert(Key, Val, Tree) end,
	      gb_trees:empty(), KeyValues).

replace_code(Cfg, Lbl, NewCode) ->
  Table = Cfg#cfg.table,
  {Block, Succ, Pred} = gb_trees:get(Lbl, Table),
  NewBlock = Block#bb{code = NewCode},
  NewTable = gb_trees:update(Lbl, {NewBlock, Succ, Pred}, Table),
  Cfg#cfg{table = NewTable}.

get_temp([], _TempId) -> notfound;
get_temp([I|Is], TempId) ->
  Temps = ?HIPE_X86_SPECIFIC:defines(I) ++ ?HIPE_X86_SPECIFIC:uses(I),
  case find(fun (#x86_temp{reg=Reg}) when Reg =:= TempId -> true;
                (_) -> false
	    end, Temps) of
    {found, _Temp} = Found -> Found;
    notfound -> get_temp(Is, TempId)
  end.

liveness_of_bb(BB, LiveOut) ->
  Fun = fun (I, [Lo|_]=Los) ->
	    Uses = ordsets:from_list(?HIPE_X86_SPECIFIC:uses(I)),
	    Defs = ordsets:from_list(?HIPE_X86_SPECIFIC:defines(I)),
	    LOut = ordsets:from_list(Lo),
	    [ordsets:to_list(ordsets:union(Uses, ordsets:subtract(LOut, Defs))) 
	     | Los]
	end,
  [LiveInNew | LiveOutNew] = lists:foldr(Fun, [LiveOut], hipe_bb:code(BB)),
  {LiveInNew, LiveOutNew}.

complete_liveness(Cfg, Liveness) ->
  gb_trees:map(
    fun (K, _V) ->
	BB = hipe_x86_cfg:bb(Cfg, K),
	LiveOut = ?HIPE_X86_SPECIFIC:liveout(Liveness, K),
	{Li, Los} = liveness_of_bb(BB, LiveOut),
	?ASSERT(length(Los) =:= length(hipe_bb:code(BB))),
	R = delay2([ordsets:from_list(temp_ids(Temps)) || Temps <- [Li|Los]]),
	?ASSERT(length(hipe_bb:code(BB)) =:= length(R)),
	R
    end,
    Liveness).

%%
%% Constructs a map SpillId to colour to spill, from Coloring
%%
get_partial_spills(Defun, Coloring) ->
  Spilled = ordsets:from_list([Id || {Id, {spill, _}} <- Coloring]),
  %% if it is over MAX_SPILL_COUNT spill only formals (function arguments)
  case length(Spilled) > ?MAX_SPILL_COUNT of
    true ->
      Formals = ordsets:from_list(temp_ids(Defun#defun.formals)),
      ordsets:intersection(Formals, Spilled);
    false ->
      Spilled
  end.

construct_partial_spills(Defun, Coloring) ->
  %% pick a color which is the least likely to be used
  Color = lists:last(?HIPE_X86_REGISTERS:allocatable()),
  Spills = [{Id, Color} || Id <- get_partial_spills(Defun, Coloring)],
  gb_trees_from_list(Spills).

check_and_rewrite_range_split(Defun, Coloring, Strategy, TempMap, Code0) ->
  ?inc_counter(range_split_iterations, 1),
  Cfg = ?HIPE_X86_SPECIFIC:defun_to_cfg(Defun),
  ?ASSERT(?HIPE_X86_SPECIFIC:defun_to_cfg(hipe_x86_cfg:linearise(
	     ?HIPE_X86_SPECIFIC:defun_to_cfg(hipe_x86_cfg:linearise(Cfg))))
	  == ?HIPE_X86_SPECIFIC:defun_to_cfg(hipe_x86_cfg:linearise(Cfg))),
  Spills = get_partial_spills(Defun, Coloring),
  %% Additional heuristic so that a temp cannot be continually spilled;
  %% this will be optional as it only sometimes improves performance
  NotSpilt = ordsets:to_list(ordsets:subtract(ordsets:from_list(Spills), ordsets:from_list(get(range_split_spills)))),
  put(range_split_spills, Spills),
  R =
    case NotSpilt =:= [] of
      true ->
	check_and_rewrite_spill(Defun, ignore, Strategy, TempMap, Code0);
      false ->
	SpillCosts = construct_partial_spills(Defun, Coloring),
	Temps =
	  gb_trees_from_list(lists:map(fun (Id) ->
					   {found, Temp} = get_temp(Code0, Id),
					   {Id, Temp}
				       end, NotSpilt)),
	NewTemps =
	  gb_trees_from_list(lists:map(fun (Id) ->
					   {Id, hipe_x86:mk_new_nonallocatable_temp(hipe_x86:temp_type(gb_trees:get(Id, Temps)))}
				       end, NotSpilt)),
	{NewCfg, DidSpill1} =
	  do_rs_cfg(Cfg, NotSpilt, Coloring, SpillCosts, Temps, NewTemps),
	case DidSpill1 of
	  true -> {hipe_x86_cfg:linearise(NewCfg), true};
	  false ->
	    %% no IRs were found (graph colorer failed to color); try to spill
	    check_and_rewrite_spill(Defun, ignore, Strategy, TempMap, Code0)
	end
    end,
  {__ResultingDefun,_} = R,
  %% postcondition: all reloads through all posible paths upwards have a store
  ?ASSERT(reloads_closed(__ResultingDefun, NewTemps)),
  R.

-ifdef(DO_ASSERT).

enumerate_list(List) -> lists:zip(lists:seq(1,length(List)), List).

is_store(I, _SpillId, SpilledId) ->
  lists:member(SpilledId, temp_ids(hipe_x86_liveness:defines(I))).

is_reload(I, SpillId, SpilledId) ->
  (temp_ids(hipe_x86_liveness:defines(I)) =:= [SpillId])
    andalso
      (temp_ids(hipe_x86_liveness:uses(I)) =:= [SpilledId]).

reloads_closed(Defun, NewTemps) ->
  Cfg = ?HIPE_X86_SPECIFIC:defun_to_cfg(Defun),
  lists:all(
    fun (SpillId) ->
	lists:all(
	  fun (Lbl) ->
	      TempId = hipe_x86:temp_reg(gb_trees:get(SpillId, NewTemps)),
	      reloads_closed_for_bb(Cfg, Lbl, SpillId, TempId)
	  end, hipe_x86_cfg:labels(Cfg))
    end, gb_trees:keys(NewTemps)).

reloads_closed_for_bb(Cfg, Lbl, SpillId, SpilledId) ->
  Code = get_code(Cfg, Lbl),
  NumberedCode = lists:zip(lists:seq(1, length(Code)), Code),
  lists:all(fun ({In, I}) ->
		?IMPLIES(is_reload(I, SpillId, SpilledId),
			 reload_has_a_store(Cfg, Lbl, I, In, SpillId, SpilledId))
	    end, NumberedCode).

reload_has_a_store(Cfg, Lbl, I, In, SpillId, SpilledId) ->
  F = bfs_search_upwards(Cfg, Lbl, In,
    fun (Instr) ->
	is_store(Instr, SpillId, SpilledId) orelse
	is_reload(Instr, SpillId, SpilledId)
    end),
  ?WHENFALSE(lists:all(fun (Instr) -> is_store(Instr, SpillId, SpilledId) end, F),
	     io:format("~nCould not find a store for ~w in ~w at ~w~nFound was: ~p~n", [I, Lbl, In, F])) .

bfs_search_upwards(Cfg, Lbl, Nr, F) ->
  bfs_search_upwards(Cfg, Lbl, Nr, F, []).

bfs_search_upwards(Cfg, Lbl, Nr, F, Visited) ->
  Code = enumerate_list(get_code(Cfg, Lbl)),
  C = lists:reverse(case Nr of
		      all -> Code;
		      _ -> lists:filter(fun ({N, _I}) -> N < Nr end, Code)
		    end),
  case lists:member(Lbl, Visited) of
    true -> [];
    false ->
      case find(fun ({_,I}) -> F(I) end, C) of
	{found, {_,X}} -> [X];
	notfound ->
	  Preds = hipe_x86_cfg:pred(Cfg, Lbl),
	  case Preds of
	    [] -> notfound;
	    _ ->
	      NewVisited = [Lbl|Visited],
	      Pr = [bfs_search_upwards(Cfg, L, all, F, NewVisited) || L <- Preds],
	      case lists:any(fun (notfound) -> true;
				 (_) -> false
			     end, Pr) of
		true -> notfound;
		false -> lists:flatten(Pr)
	      end
	  end
      end
  end.

-endif.

%%
%% Live Range splitting for all partial spills
%%
do_rs_cfg(Cfg, Spills, Coloring, SpillCosts, Temps, NewTemps) ->
  Liveness = ?HIPE_X86_SPECIFIC:analyze(Cfg),
  lists:foldr(
    fun (SpillId, {Cfg0, DidSpill}) ->
        LivenessComplete = complete_liveness(Cfg0, Liveness),
        SpillColor = gb_trees:get(SpillId, SpillCosts),
        InterfVars0 = interfering_vars(Coloring, SpillColor),
        InterfVars = case length(Spills) > ?MAX_SPILL_COUNT of
                            true -> InterfVars0 ++ (Spills -- [SpillId]);
                            false -> InterfVars0
                        end,
        Apps = cfg_traverse_flow(Cfg0, SpillId, LivenessComplete, InterfVars),
        case Apps of
          [] -> {Cfg0, DidSpill}; % did not find any interfering live ranges
          _ ->
            Map = construct_app_map(Apps),
	    Temp = gb_trees:get(SpillId, Temps),
	    NewTemp = gb_trees:get(SpillId, NewTemps),
            {cfg_apply_apps(Cfg0, Map, SpillId, Temp, NewTemp), true}
        end
    end,
    {Cfg, false}, Spills).

bb_from_app({_,BB,_,_}) -> BB;
bb_from_app({storep,BB}) -> BB.

insert_In({storep,_}, {Storeps, InMap}) ->
  {Storeps ++ [storep], InMap};
insert_In({Type,_,In,Where}, {Storeps, InMap}) ->
  NewInMap = case gb_trees:lookup(In, InMap) of
    {value, {B, C, A}} ->
      gb_trees:update(In,
	case Where of
	  b -> {B ++ [Type], C, A};
	  c -> {B, C ++ [Type], A};
	  a -> {B, C, A ++ [Type]}
	end, InMap);
    none -> gb_trees:insert(In,
	case Where of
	  b -> {[Type], [], []};
	  c -> {[], [Type], []};
	  a -> {[], [], [Type]}
	end, InMap)
  end,
  {Storeps, NewInMap}.

insert_app(App, Map) ->
  BB = bb_from_app(App),
  case gb_trees:lookup(BB, Map) of
    {value, InMap} -> gb_trees:update(BB, insert_In(App, InMap), Map);
    none -> gb_trees:insert(BB, insert_In(App, {[], gb_trees:empty()}), Map)
  end.

construct_app_map(Apps) ->
  lists:foldr(fun (App, Map) -> insert_app(App, Map) end, gb_trees:empty(), Apps).

app_mk_edge_instr(_SpillId, store, Temp, NewTemp) ->
  hipe_x86:mk_move(Temp, NewTemp);
app_mk_edge_instr(_SpillId, reload, Temp, NewTemp) ->
  hipe_x86:mk_move(NewTemp, Temp).

app_comment(SpillId, Type) -> hipe_x86:mk_comment({Type, SpillId}).

app_instr(I, SpillId, Temp, NewTemp, B, C, A) ->
  Before =
    case B of
      [reload,store] ->
	[app_mk_edge_instr(SpillId, reload, Temp, NewTemp),
	 app_mk_edge_instr(SpillId, store, Temp, NewTemp)];
      [store,reload] ->
	[app_mk_edge_instr(SpillId, reload, Temp, NewTemp),
	 app_mk_edge_instr(SpillId, store, Temp, NewTemp)];
      [X1] ->
	[app_comment(SpillId, X1), app_mk_edge_instr(SpillId,X1,Temp,NewTemp)];
      [] -> []
    end,
  After  = case A of
	     [ X2] -> [app_mk_edge_instr(SpillId, X2, Temp, NewTemp)];
	     [] -> []
	   end,
  Rename = case C of
	     [_X3] -> [map_temp(rename_temp(SpillId, NewTemp), I)];
	     [] -> [I]
	   end,
  Before ++ Rename ++ After.

app_instr_storep(Storeps, Code, Temp, NewTemp) ->
  case Storeps of
    [] -> Code;
    [_] ->
      [Last|Other] = lists:reverse(Code),
      N = case hipe_x86_cfg:is_branch(Last) of
	    true ->
	      [Last, app_comment(Temp, storep), hipe_x86:mk_move(Temp, NewTemp)];
	    false ->
	      [hipe_x86:mk_move(Temp, NewTemp), app_comment(Temp, storep), Last]
	  end,
      lists:reverse(N ++ Other)
  end.

cfg_apply_apps(Cfg, Map, SpillId, Temp, NewTemp) ->
  lists:foldr(
    fun (Lbl, Cfg0) ->
	Code = get_code(Cfg0, Lbl),
	{Storeps, InMap} = gb_trees:get(Lbl,Map),
	NewCodeI = lists:map(
	  fun ({I,In}) ->
	      case gb_trees:lookup(In, InMap) of
		{value, {B, C, A}} ->
		  app_instr(I, SpillId, Temp, NewTemp, B, C, A);
		none -> [I]
	      end
	  end, lists:zip(Code, lists:seq(1, length(Code)))),
	NewCodeF = lists:flatten(NewCodeI),
	NewCode = app_instr_storep(Storeps, NewCodeF, Temp, NewTemp),
	replace_code(Cfg0, Lbl, NewCode)
    end, Cfg, gb_trees:keys(Map)).

union_lists(Lsts) ->
  ordsets:union([ordsets:from_list(L) || L <- Lsts]).

merge_liveness(LT) ->
  LiveInsLiveOuts = gb_trees:values(LT),
  {LiveIns, LiveOuts} = lists:unzip(LiveInsLiveOuts),
  {union_lists(LiveIns), union_lists(LiveOuts)}.

merge_defs(DefsT) ->
  union_lists(gb_trees:values(DefsT)).

gb_trees_from_keys(F, Keys) ->
  gb_trees_from_list([{K, F(K)} || K <- Keys]).

cfg_traverse_flow(Cfg, SpillId, Liveness, InterferingVars) ->
  BBs = hipe_x86_cfg:labels(Cfg),
  lists:foldl(
    fun (Lbl, Apps0) ->
	%% Predecessors
	PredBBs = hipe_x86_cfg:pred(Cfg, Lbl),
	MapFun = fun (_, I) ->
		     temp_ids(?HIPE_X86_SPECIFIC:defines(I))
		 end,
	PredLivenessInit =
	  gb_trees_from_keys(fun (P) ->
				 lists:last(gb_trees:get(P, Liveness))
			     end, PredBBs),
	PredI =
	  gb_trees_from_keys(fun (P) -> lists:last(get_code(Cfg, P)) end,
			     PredBBs),
	PredDefs = gb_trees:map(MapFun, PredI),

	%% Successors
	SuccBBs = hipe_x86_cfg:succ(Cfg, Lbl),
	SuccLivenessInit =
	  gb_trees_from_keys(fun (S) ->
				 [LiLo|_] = gb_trees:get(S, Liveness),
				 LiLo
			     end, SuccBBs),
	SuccI =
	  gb_trees_from_keys(fun (S) -> hd(get_code(Cfg, S)) end, SuccBBs),
	SuccDefs = gb_trees:map(MapFun, SuccI),

	Code    = get_code(Cfg, Lbl),
	Defs    = [temp_ids(?HIPE_X86_SPECIFIC:defines(I)) || I <- Code],
	DefsT   = [gb_trees_from_list([{Lbl, Def}]) || Def <- Defs],
	Live    = gb_trees:get(Lbl, Liveness),
	LiveT   = [gb_trees_from_list([{Lbl, LiLo}]) || LiLo <- Live],
	%% PCN - Previous Current Next
	PCNDef  = delay3([PredDefs] ++ DefsT ++ [SuccDefs]),
	PCNLive = delay3([PredLivenessInit] ++ LiveT ++ [SuccLivenessInit]),
	PCNLiveMerged = delay3([merge_liveness(PredLivenessInit)] ++ Live ++
				 [merge_liveness(SuccLivenessInit)]),
	PCNDefsMerged = delay3([merge_defs(PredDefs)] ++ Defs ++
				 [merge_defs(SuccDefs)]),
	N = length(Code),
	Nr = lists:seq(1,N),
	?ASSERT(N =:= length(Live)),
	?ASSERT(N =:= length(PCNLive)),
	?ASSERT(N =:= length(PCNLiveMerged)),
	?ASSERT(N =:= length(PCNDefsMerged)),
	?ASSERT(N =:= length(PCNDef)),
	NewApps = traverse_flow_run_detect(
		    Code, PCNDef, PCNDefsMerged, PCNLive, PCNLiveMerged,
		    Nr, N, SpillId, InterferingVars, Lbl, ordsets:new()),
	ordsets:union(Apps0, NewApps)
    end,
    ordsets:new(), BBs).

traverse_flow_run_detect([], [], [], [], [], [], _, _, _, _, Apps) -> Apps;
traverse_flow_run_detect([I|Code],
			 [{PD,CD,ND}|PCNDef],
			 [{PDM,CDM,NDM}|PCNDefsMerged],
			 [{PL,CL,NL}|PCNLive],
			 [{PLM,CLM,NLM}|PCNLiveMerged],
			 [In|Nr],
			 CodeLength, SpillId, InterferingVars, Lbl, Apps) ->
  NewApps =
    ordsets:union(Apps,
		  detect(PL, CL, NL, PLM, CLM, NLM, PD, CD, ND, PDM, CDM, NDM,
			 Lbl, I, In, CodeLength, SpillId, InterferingVars)),
  traverse_flow_run_detect(Code, PCNDef, PCNDefsMerged, PCNLive, PCNLiveMerged,
			   Nr, CodeLength, SpillId, InterferingVars, Lbl, NewApps).

interfering_vars(Coloring, SpillColor) ->
  [Id || {Id, {reg, X}} <- Coloring, X =:= SpillColor].
  %%++ (get_partial_spills(Defun, Coloring) -- [SpillColor]).

is_live(SpillId, {LiveIn, LiveOut}) ->
  lists:member(SpillId, LiveIn) orelse lists:member(SpillId, LiveOut).

is_interfering(InterferingVars, IsSpillLive, {LiveIn, LiveOut}, SpillId, Defs) ->
  InterferingVars2 = ordsets:from_list(InterferingVars),
  LiveOut2 = ordsets:from_list(LiveOut),
  LiveIn2 = ordsets:from_list(LiveIn),
  Defs2 = ordsets:from_list(Defs),
  IsSpillLive
  andalso
  (((ordsets:intersection(InterferingVars2, LiveIn2) =/= [])
      orelse (ordsets:intersection(InterferingVars2, LiveOut2) =/= [])) orelse
    ((ordsets:intersection(InterferingVars2, Defs2) =/= []) andalso
      lists:member(SpillId, LiveOut2))
    orelse
    (lists:member(SpillId, Defs2) andalso
      (ordsets:intersection(InterferingVars2, LiveOut2) =/= []))).

detect(PLiveT, _CLiveT, _NLiveT,
       PLive, CLive, NLive,
       PDefT, _CDefT, _NDefT,
       PDef, CDef, NDef, BBLbl,
       I, In, _N, SpillId, InterferingVars) ->
  CL = is_live(SpillId, CLive),
  CI = is_interfering(InterferingVars, CL, CLive, SpillId, CDef),
  PL = is_live(SpillId, PLive),
  PI = is_interfering(InterferingVars, PL, PLive, SpillId, PDef),
  NL = is_live(SpillId, NLive),
  NI = is_interfering(InterferingVars, NL, NLive, SpillId, NDef),
  StorePred =
    case ((In =:= 1) andalso PI andalso CL andalso not(CI)) of
      true ->
	[{storep, L} || L <- [K || K <- gb_trees:keys(PLiveT),
				   begin
				     LV = gb_trees:get(K, PLiveT),
				     IsLive = is_live(SpillId, LV),
				     IsLive andalso
				       not is_interfering(
					     InterferingVars,
					     IsLive,
					     LV,
					     SpillId,
					     gb_trees:get(K, PDefT))
				   end]];
      false -> []
    end,
  %% Stores
  IsBranch = hipe_x86_cfg:is_branch(I),
  %% Invariant: currently the last instructions is always a branch
  %% IsBranch iff _N = In
  ?ASSERT((not(IsBranch) or (_N =:= In)) and (not(_N =:= In) or IsBranch)),
  Store =
    case not(CI) andalso CL andalso NI of
      true ->
	case IsBranch of
	  true  -> [{store, BBLbl, In, b}];
	  false -> [{store, BBLbl, In, a}]
	end;
      false -> []
    end,
  Reload =
    case PI andalso CL andalso not(CI) of
      true -> [{reload, BBLbl, In, b}];
      false -> []
    end,
  Temps = temp_ids(?HIPE_X86_SPECIFIC:defines(I) ++ ?HIPE_X86_SPECIFIC:uses(I)),
  IsUsedInInstr = lists:member(SpillId, Temps),
  Rename =
    case CI andalso IsUsedInInstr of
      true -> [{rename, BBLbl, In, c}];
      false -> []
    end,
  ordsets:union([ordsets:from_list(Reload),
		 ordsets:from_list(Rename),
		 ordsets:from_list(Store),
		 ordsets:from_list(StorePred)]).

get_code(CFG, Lbl) ->
  hipe_bb:code(hipe_x86_cfg:bb(CFG, Lbl)).

temp_ids(Temps) ->
  [hipe_x86:temp_reg(T) || T <- Temps].

rename_temp(TempId, NewTemp) ->
  ?ASSERT(TempId =/= hipe_x86:temp_reg(NewTemp)),
  fun (TempI) ->
      case TempI of
        #x86_mem{base=T, off=O} ->
          TempI#x86_mem{base=((rename_temp(TempId,NewTemp))(T)),
			off=((rename_temp(TempId,NewTemp))(O))};
        #x86_temp{reg=Reg} when Reg =:= TempId -> NewTemp;
        _ -> TempI
      end
  end.

map_temp(F, I) ->
  case I of
    #alu{src=Src, dst=Dst} -> I#alu{src=F(Src), dst=F(Dst)};
    #call{'fun'=Fun} -> I#call{'fun'=F(Fun)};
    #cmovcc{src=Src, dst=Dst} -> I#cmovcc{src=F(Src), dst=F(Dst)};
    #cmp{src=Src, dst=Dst} -> I#cmp{src=F(Src), dst=F(Dst)};
    #comment{} -> I;
    #fmove{src=Src, dst=Dst} -> I#fmove{src=F(Src), dst=F(Dst)};
    #fp_binop{src=Src, dst=Dst} -> I#fp_binop{src=F(Src), dst=F(Dst)};
    #fp_unop{arg=Arg} -> I#fp_unop{arg=F(Arg)};
    #imul{src=Src, temp=Temp} -> I#imul{src=F(Src), temp=F(Temp)};
    #jcc{} -> I;
    #jmp_fun{'fun'=Fun} -> I#jmp_fun{'fun'=F(Fun)};
    #jmp_label{} -> I;
    #jmp_switch{temp=T, jtab=Tab} -> I#jmp_switch{temp=F(T), jtab=F(Tab)};
    #label{} -> I;
    #lea{mem=Mem, temp=Temp} -> I#lea{mem=F(Mem), temp=F(Temp)};
    #move{src=Src, dst=Dst} -> I#move{src=F(Src), dst=F(Dst)};
    #move64{dst=Dst} -> I#move64{dst=F(Dst)};
    #movsx{src=Src, dst=Dst} -> I#movsx{src=F(Src), dst=F(Dst)};
    #movzx{src=Src, dst=Dst} -> I#movzx{src=F(Src), dst=F(Dst)};
    #pseudo_call{'fun'=Fun} -> I#pseudo_call{'fun'=F(Fun)};
    #pseudo_jcc{} -> I;
    #pseudo_spill{args=Args} -> I#pseudo_spill{args=lists:map(F, Args)};
    #pseudo_tailcall{'fun'=Fun, stkargs=Args} ->
      I#pseudo_tailcall{'fun'=F(Fun), stkargs=lists:map(F, Args)};
    #pseudo_tailcall_prepare{} -> I;
    #push{src=Src} -> I#push{src=F(Src)};
    #pop{dst=Dst} -> I#pop{dst=F(Dst)};
    #shift{src=Src, dst=Dst} -> I#shift{src=F(Src), dst=F(Dst)};
    #test{src=Src, dst=Dst} -> I#test{src=F(Src), dst=F(Dst)}
  end.

do_insns([I|Insns], TempMap, Strategy, Accum, DidSpill0) ->
  {NewIs, DidSpill1} = do_insn(I, TempMap, Strategy),
  do_insns(Insns, TempMap, Strategy, lists:reverse(NewIs, Accum), DidSpill0 or DidSpill1);
do_insns([], _TempMap, _Strategy, Accum, DidSpill) ->
  {lists:reverse(Accum), DidSpill}.

do_insn(I, TempMap, Strategy) ->	% Insn -> {Insn list, DidSpill}
  case I of
    #alu{} ->
      do_alu(I, TempMap, Strategy);
    #cmp{} ->
      do_cmp(I, TempMap, Strategy);
    #imul{} ->
      do_imul(I, TempMap, Strategy);
    #jmp_switch{} ->
      do_jmp_switch(I, TempMap, Strategy);
    #lea{} ->
      do_lea(I, TempMap, Strategy);
    #move{} ->
      do_move(I, TempMap, Strategy);
    #move64{} ->
      do_move64(I, TempMap, Strategy);
    #movsx{} ->
      do_movx(I, TempMap, Strategy);
    #movzx{} ->
      do_movx(I, TempMap, Strategy);
    #fmove{} ->
      do_fmove(I, TempMap, Strategy);
    #shift{} ->
      do_shift(I, TempMap, Strategy);
    _ ->
      %% comment, jmp*, label, pseudo_call, pseudo_jcc, pseudo_tailcall,
      %% pseudo_tailcall_prepare, push, ret
      {[I], false}
  end.

%%% Fix an alu op.

do_alu(I, TempMap, Strategy) ->
  #alu{src=Src0,dst=Dst0} = I,
  {FixSrc,Src,FixDst,Dst,DidSpill} =
    do_binary(Src0, Dst0, TempMap, Strategy),
  {FixSrc ++ FixDst ++ [I#alu{src=Src,dst=Dst}], DidSpill}.

%%% Fix a cmp op.

do_cmp(I, TempMap, Strategy) ->
  #cmp{src=Src0,dst=Dst0} = I,
  {FixSrc, Src, FixDst, Dst, DidSpill} =
    do_binary(Src0, Dst0, TempMap, Strategy),
  {FixSrc ++ FixDst ++ [I#cmp{src=Src,dst=Dst}], DidSpill}.

%%% Fix an imul op.

do_imul(I, TempMap, Strategy) ->
  #imul{imm_opt=ImmOpt,src=Src0,temp=Temp0} = I,
  {FixSrc,Src,DidSpill1} = fix_src_operand(Src0, TempMap, Strategy),	% temp1
  {FixTempSrc,Temp,FixTempDst,DidSpill2} =
    case is_spilled(Temp0, TempMap) of
      false ->
	{[], Temp0, [], false};
      true ->
	Reg = spill_temp0('untagged', Strategy),
	{case ImmOpt of
	   [] -> [hipe_x86:mk_move(Temp0, Reg)];	% temp *= src
	   _ -> []					% temp = src * imm
	 end,
	 Reg,
	 [hipe_x86:mk_move(Reg, Temp0)],
	 true}
    end,
  {FixSrc ++ FixTempSrc ++ [I#imul{src=Src,temp=Temp}] ++ FixTempDst,
   DidSpill1 or DidSpill2}.

%%% Fix a jmp_switch op.

-ifdef(HIPE_AMD64).
do_jmp_switch(I, TempMap, Strategy) ->
  #jmp_switch{temp=Temp, jtab=Tab} = I,
  case is_spilled(Temp, TempMap) of
    false ->
      case is_spilled(Tab, TempMap) of
        false ->
          {[I], false};
        true ->
          NewTab = spill_temp('untagged', Strategy),
          {[hipe_x86:mk_move(Tab, NewTab), I#jmp_switch{jtab=Tab}],
	   true}
      end;
    true ->
      case is_spilled(Tab, TempMap) of
        false ->
          NewTmp = spill_temp('untagged', Strategy),
          {[hipe_x86:mk_move(Temp, NewTmp), I#jmp_switch{temp=NewTmp}],
	   true};
        true ->
          NewTmp = spill_temp('untagged', Strategy),
          NewTab = spill_temp0('untagged', Strategy),
          {[hipe_x86:mk_move(Temp, NewTmp),
            hipe_x86:mk_move(Tab, NewTab),
            I#jmp_switch{temp=NewTmp, jtab=NewTab}],
	   true}
      end
  end.
-else.	% not AMD64
do_jmp_switch(I, TempMap, Strategy) ->
  #jmp_switch{temp=Temp} = I,
  case is_spilled(Temp, TempMap) of
    false ->
      {[I], false};
    true ->
      NewTmp = spill_temp('untagged', Strategy),
      {[hipe_x86:mk_move(Temp, NewTmp), I#jmp_switch{temp=NewTmp}],
       true}
  end.
-endif.	% not AMD64

%%% Fix a lea op.

do_lea(I, TempMap, Strategy) ->
  #lea{temp=Temp} = I,
  case is_spilled(Temp, TempMap) of
    false ->
      {[I], false};
    true ->
      NewTmp = spill_temp('untagged', Strategy),
      {[I#lea{temp=NewTmp}, hipe_x86:mk_move(NewTmp, Temp)],
       true}
  end.

%%% Fix a move op.

do_move(I, TempMap, Strategy) ->
  #move{src=Src0,dst=Dst0} = I,
  {FixSrc, Src, FixDst, Dst, DidSpill} =
    do_check_byte_move(Src0, Dst0, TempMap, Strategy),
  {FixSrc ++ FixDst ++ [I#move{src=Src,dst=Dst}],
   DidSpill}.

-ifdef(HIPE_AMD64).

%%% AMD64 has no issues with byte moves.
do_check_byte_move(Src0, Dst0, TempMap, Strategy) ->
  do_binary(Src0, Dst0, TempMap, Strategy).

-else.	% not AMD64

%%% x86 can only do byte moves to a subset of the integer registers.
do_check_byte_move(Src0, Dst0, TempMap, Strategy) ->
  case Dst0 of
    #x86_mem{type=byte} ->
      do_byte_move(Src0, Dst0, TempMap, Strategy);
    _ ->
      do_binary(Src0, Dst0, TempMap, Strategy)
  end.

do_byte_move(Src0, Dst0, TempMap, Strategy) ->
  {FixSrc, Src, DidSpill1} = fix_src_operand(Src0, TempMap, Strategy),
  {FixDst, Dst, DidSpill2} = fix_dst_operand(Dst0, TempMap, Strategy),
  Reg = hipe_x86_registers:eax(),
  {FixSrc3, Src3} = % XXX: this just checks Src, the result is known!
    case Src of
      #x86_imm{} ->
	{FixSrc, Src};
      #x86_temp{reg=Reg} ->	% small moves must start from reg 1->4
	{FixSrc, Src}		% so variable sources are always put in eax
    end,
  {FixSrc3, Src3, FixDst, Dst,
   DidSpill2 or DidSpill1}.

-endif.	% not AMD64

%%% Fix a move64 op.

do_move64(I, TempMap, Strategy) ->
  #move64{dst=Dst} = I,
  case is_spilled(Dst, TempMap) of
    false ->
      {[I], false};
    true ->
      Reg = clone(Dst, Strategy),
      {[I#move64{dst=Reg}, hipe_x86:mk_move(Reg, Dst)], true}
  end.

%%% Fix a movx op.

do_movx(I, TempMap, Strategy) ->
  {{FixSrc, Src, DidSpill1}, {FixDst, Dst, DidSpill2}} =
    case I of
      #movsx{src=Src0,dst=Dst0} ->
	{fix_src_operand(Src0, TempMap, Strategy),
	 fix_dst_operand(Dst0, TempMap, Strategy)};
      #movzx{src=Src0,dst=Dst0} ->
	{fix_src_operand(Src0, TempMap, Strategy),
	 fix_dst_operand(Dst0, TempMap, Strategy)}
    end,
  {I3, DidSpill3} =
    case is_spilled(Dst, TempMap) of
      false ->
	I2 = case I of
	       #movsx{} ->
		 [hipe_x86:mk_movsx(Src, Dst)];
	       #movzx{} ->
		 [hipe_x86:mk_movzx(Src, Dst)]
	     end,
	{I2, false};
      true ->
	Dst2 = clone(Dst, Strategy),
	I2 =
	  case I of
	    #movsx{} ->
	      [hipe_x86:mk_movsx(Src, Dst2), hipe_x86:mk_move(Dst2, Dst)];
	    #movzx{} ->
	      [hipe_x86:mk_movzx(Src, Dst2), hipe_x86:mk_move(Dst2, Dst)]
	  end,
	{I2, true}
    end,
  {FixSrc++FixDst++I3,
   DidSpill3 or DidSpill2 or DidSpill1}.

%%% Fix an fmove op.

do_fmove(I, TempMap, Strategy) ->
  #fmove{src=Src0,dst=Dst0} = I,
  {FixSrc, Src, DidSpill1} = fix_src_operand(Src0, TempMap, Strategy),
  {FixDst, Dst, DidSpill2} = fix_dst_operand(Dst0, TempMap, Strategy),
  %% fmoves from memory position to memory position is handled
  %% by the f.p. register allocator.
  {FixSrc ++ FixDst ++ [I#fmove{src=Src,dst=Dst}],
   DidSpill1 or DidSpill2}.

%%% Fix a shift operation.
%%% 1. remove pseudos from any explicit memory operands
%%% 2. if the source is a register or memory position
%%%    make sure to move it to %ecx

do_shift(I, TempMap, Strategy) ->
  #shift{src=Src0,dst=Dst0} = I,
  {FixDst, Dst, DidSpill} = fix_dst_operand(Dst0, TempMap, Strategy),
  Reg = ?HIPE_X86_REGISTERS:?ECX(),
  case Src0 of
    #x86_imm{} ->
      {FixDst ++ [I#shift{dst=Dst}], DidSpill};
    #x86_temp{reg=Reg}  ->
      {FixDst ++ [I#shift{dst=Dst}], DidSpill}
  end.

%%% Fix the operands of a binary op.
%%% 1. remove pseudos from any explicit memory operands
%%% 2. if both operands are (implicit or explicit) memory operands,
%%%    move src to a reg and use reg as src in the original insn

do_binary(Src0, Dst0, TempMap, Strategy) ->
  {FixSrc, Src, DidSpill1} = fix_src_operand(Src0, TempMap, Strategy),
  {FixDst, Dst, DidSpill2} = fix_dst_operand(Dst0, TempMap, Strategy),
  {FixSrc3, Src3, DidSpill3} =
    case is_mem_opnd(Src, TempMap) of
      false ->
	{FixSrc, Src, false};
      true ->
	case is_mem_opnd(Dst, TempMap) of
	  false ->
	    {FixSrc, Src, false};
	  true ->
	    Src2 = clone(Src, Strategy),
	    FixSrc2 = FixSrc ++ [hipe_x86:mk_move(Src, Src2)],
	    {FixSrc2, Src2, true}
	end
    end,
  {FixSrc3, Src3, FixDst, Dst,
   DidSpill3 or DidSpill2 or DidSpill1}.

%%% Fix any x86_mem operand to not refer to any spilled temps.

fix_src_operand(Opnd, TmpMap, Strategy) ->
  fix_mem_operand(Opnd, TmpMap, temp1(Strategy)).

temp1('normal') -> [];
temp1('linearscan') -> ?HIPE_X86_REGISTERS:temp1().

fix_dst_operand(Opnd, TempMap, Strategy) ->
  fix_mem_operand(Opnd, TempMap, temp0(Strategy)).

temp0('normal') -> [];
temp0('linearscan') -> ?HIPE_X86_REGISTERS:temp0().

fix_mem_operand(Opnd, TempMap, RegOpt) ->   % -> {[fixupcode], newop, DidSpill}
  case Opnd of
    #x86_mem{base=Base,off=Off} ->
      case is_mem_opnd(Base, TempMap) of
	false ->
	  case is_mem_opnd(Off, TempMap) of
	    false ->
	      {[], Opnd, false};
	    true ->
	      Temp = clone2(Off, RegOpt),
	      {[hipe_x86:mk_move(Off, Temp)],
	       Opnd#x86_mem{off=Temp},
	       true}
	  end;
	true ->
	  Temp = clone2(Base, RegOpt),
	  case is_mem_opnd(Off, TempMap) of
	    false ->		% imm/reg(pseudo)
	      {[hipe_x86:mk_move(Base, Temp)],
	       Opnd#x86_mem{base=Temp},
	       true};
	    true ->		% pseudo(pseudo)
	      {[hipe_x86:mk_move(Base, Temp),
		hipe_x86:mk_alu('add', Off, Temp)],
	       Opnd#x86_mem{base=Temp, off=hipe_x86:mk_imm(0)},
	       true}
	  end
      end;
    _ ->
      {[], Opnd, false}
  end.

%%% Check if an operand denotes a memory cell (mem or pseudo).

is_mem_opnd(Opnd, TempMap) ->
  R =
    case Opnd of
      #x86_mem{} -> true;
      #x86_temp{} ->
	Reg = hipe_x86:temp_reg(Opnd),
	case hipe_x86:temp_is_allocatable(Opnd) of
	  true ->
	    case tuple_size(TempMap) > Reg of
	      true ->
		case
		  hipe_temp_map:is_spilled(Reg, TempMap) of
		  true ->
		    ?count_temp(Reg),
		    true;
		  false -> false
		end;
	      _ ->
		%% impossible, but was true in ls post and false in normal post
		exit({?MODULE,is_mem_opnd,Reg}),
		false
	    end;
	  false -> true
	end;
      _ -> false
    end,
  %% io:format("Op ~w mem: ~w\n",[Opnd,R]),
  R.

%%% Check if an operand is a spilled Temp.

is_spilled(Temp, TempMap) ->
  case hipe_x86:temp_is_allocatable(Temp) of
    true ->
      Reg = hipe_x86:temp_reg(Temp),
      case tuple_size(TempMap) > Reg of
	true ->
	  case hipe_temp_map:is_spilled(Reg, TempMap) of
	    true ->
	      ?count_temp(Reg),
	      true;
	    false ->
	      false
	  end;
	false ->
	  false
      end;
    false -> true
  end.

%%% Make Reg a clone of Dst (attach Dst's type to Reg).

clone(Dst, Strategy) ->
  Type =
    case Dst of
      #x86_mem{} -> hipe_x86:mem_type(Dst);
      #x86_temp{} -> hipe_x86:temp_type(Dst)
    end,
  spill_temp(Type, Strategy).

spill_temp0(Type, 'normal') ->
  hipe_x86:mk_new_temp(Type);
spill_temp0(Type, 'linearscan') ->
  hipe_x86:mk_temp(?HIPE_X86_REGISTERS:temp0(), Type).

spill_temp(Type, 'normal') ->
  hipe_x86:mk_new_temp(Type);
spill_temp(Type, 'linearscan') ->
  hipe_x86:mk_temp(?HIPE_X86_REGISTERS:temp1(), Type).

%%% Make a certain reg into a clone of Dst

clone2(Dst, RegOpt) ->
  Type =
    case Dst of
      #x86_mem{} -> hipe_x86:mem_type(Dst);
      #x86_temp{} -> hipe_x86:temp_type(Dst)
    end,
  case RegOpt of
    [] -> hipe_x86:mk_new_temp(Type);
    Reg -> hipe_x86:mk_temp(Reg, Type)
  end.
