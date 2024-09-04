-module(example).
-compile(export_all).

p1(CIn, COut) ->
  io:format("~p~n", [COut]),
  COut ! 42.

mainPar() ->
  % {PTo,PFrm} = {self(),self()}, % spawn here; we can send COut (self()); CIn doesn't exist; PFrm doesn't exist?
% check functions are processes based on type signatures?
% a receive is always going to be from us, so I don't think it matters? We just set the relevant variables to anything
  PTo = spawn(?MODULE, p1, [chan,self()]),
  receive
    X ->
      io:format("~p~n",[X])
  end.

% TODO: figure out how to get our channels working.

