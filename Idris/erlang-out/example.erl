-module(example).
-compile(export_all).
id ( X )  -> 
	X .

const ( X , Y )  -> 
	?MODULE:id( X  ) .

p1 ( CIn , COut )  -> 
	COut ! 42 ,
	halt .

mainPar (  )  -> 
	PTo = 	spawn( ?MODULE , p1  , [ chan  , self()  ]  ) ,
	receive
		Msg -> 		halt 
	end.


