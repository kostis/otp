%%
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2008-2012. All Rights Reserved.
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
%% This file is generated DO NOT EDIT

%% @doc See external documentation: <a href="http://www.wxwidgets.org/manuals/stable/wx_wxfiledataobject.html">wxFileDataObject</a>.
%% <p>This class is derived (and can use functions) from:
%% <br />{@link wxDataObject}
%% </p>
%% @type wxFileDataObject().  An object reference, The representation is internal
%% and can be changed without notice. It can't be used for comparsion
%% stored on disc or distributed for use on other nodes.

-module(wxFileDataObject).
-include("wxe.hrl").
-export([addFile/2,destroy/1,getFilenames/1,new/0]).

%% inherited exports
-export([parent_class/1]).

-export_type([wxFileDataObject/0]).
%% @hidden
parent_class(wxDataObject) -> true;
parent_class(_Class) -> erlang:error({badtype, ?MODULE}).

-type wxFileDataObject() :: wx:wx_object().
%% @doc See <a href="http://www.wxwidgets.org/manuals/stable/wx_wxfiledataobject.html#wxfiledataobjectwxfiledataobject">external documentation</a>.
-spec new() -> wxFileDataObject().
new() ->
  wxe_util:construct(?wxFileDataObject_new,
  <<>>).

%% @doc See <a href="http://www.wxwidgets.org/manuals/stable/wx_wxfiledataobject.html#wxfiledataobjectaddfile">external documentation</a>.
-spec addFile(This, Filename) -> ok when
	This::wxFileDataObject(), Filename::unicode:chardata().
addFile(#wx_ref{type=ThisT,ref=ThisRef},Filename)
 when is_list(Filename) ->
  ?CLASS(ThisT,wxFileDataObject),
  Filename_UC = unicode:characters_to_binary([Filename,0]),
  wxe_util:cast(?wxFileDataObject_AddFile,
  <<ThisRef:32/?UI,(byte_size(Filename_UC)):32/?UI,(Filename_UC)/binary, 0:(((8- ((0+byte_size(Filename_UC)) band 16#7)) band 16#7))/unit:8>>).

%% @doc See <a href="http://www.wxwidgets.org/manuals/stable/wx_wxfiledataobject.html#wxfiledataobjectgetfilenames">external documentation</a>.
-spec getFilenames(This) -> [[unicode:charlist()]] when
	This::wxFileDataObject().
getFilenames(#wx_ref{type=ThisT,ref=ThisRef}) ->
  ?CLASS(ThisT,wxFileDataObject),
  wxe_util:call(?wxFileDataObject_GetFilenames,
  <<ThisRef:32/?UI>>).

%% @doc Destroys this object, do not use object again
-spec destroy(This::wxFileDataObject()) -> ok.
destroy(Obj=#wx_ref{type=Type}) ->
  ?CLASS(Type,wxFileDataObject),
  wxe_util:destroy(?wxFileDataObject_destroy,Obj),
  ok.
 %% From wxDataObject
