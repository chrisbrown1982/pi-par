-module(parSumEuler).
-compile(export_all).
spawnN ( N , 0 , ToTy , FrmTy , P )  -> 
	[];
spawnN ( N , (Num) , ToTy , FrmTy , P )  -> 
	S = 	spawn( ?MODULE , P  , [ chan  , self()  ]  ) ,
	R = 	?MODULE:spawnN(  ( N  + 2  )  , Num-1  , ToTy  , FrmTy  , P  ) ,
	 ( [{N ,S } | R ] ) .

sendN ( [] )  -> 
	{};
sendN ( ([{M,{T,{C,Msg}}}|Cs]) )  -> 
	C  ! Msg ,
	?MODULE:sendN( Cs  ) ,
	{}.

recN ( Ty , [] )  -> 
	[];
recN ( Ty , ([{M,C}|Chs]) )  -> 
	receive
		M1 -> 		Msgs = 		?MODULE:recN( Ty  , Chs  ) ,
		 ( [M1  | Msgs ] ) 
	end.

p ( PIn , POut )  -> 
	receive
		X -> 		POut  ! 42 ,
		halt 
	end.

test (  )  -> 
	C = 	spawn( ?MODULE , p  , [ chan  , self()  ]  ) ,
	 ( utils:fst( C  )  )  ! 42 ,
	receive
		V -> 		halt 
	end.

convertChans ( T , [] , Msgs )  -> 
	[];
convertChans ( T , ([{M,C}|Rest]) , ([Msg|Msgs]) )  -> 
	[	{M ,{T ,{utils:fst( C  ) ,Msg }}} | 	?MODULE:convertChans( T  , Rest  , Msgs  ) ].

inChans ( [] )  -> 
	[];
inChans ( ([{M,I}|Chs]) )  -> 
	[	{ ( M  + 1  ) ,I } | 	?MODULE:inChans( Chs  ) ].

farm4 ( InTy , OutTy , Nw , W , Input )  -> 
	Res = 	?MODULE:spawnN( Nw  , InTy  , OutTy  , W  ) ,
	?MODULE:sendN(  ( ?MODULE:convertChans( InTy  , Res  , Input  )  )  ) ,
	Msgs = 	?MODULE:recN( OutTy  ,  ( ?MODULE:inChans( Res  )  )  ) ,
	Msgs .

w ( PIn , POut )  -> 
	halt .

gcd2 ( A , 0 )  -> 
	A ;
gcd2 ( A , B )  -> 
	?MODULE:gcd2( B  ,  ( A  rem B  )  ) .

relPrime ( X , Y )  -> 
		 ( 	?MODULE:gcd2( X  , Y  )  )  == 	1 .

mkList ( N )  -> 
	lists:seq( 	1  , 	N  ) .

euler ( N )  -> 
	length(  ( lists:filter(  ( fun ( X ) -> ?MODULE:relPrime( N  , X  )  end  )  ,  ( ?MODULE:mkList( N  )  )  )  )  ) .

sumEuler ( N )  -> 
	lists:sum(  ( lists:map(  ( fun ( X ) -> ?MODULE:euler(  ( X  )  )  end  )  ,  ( ?MODULE:mkList( N  )  )  )  )  ) .

eW ( PIn , POut )  -> 
	receive
		X -> 		POut  !  ( lists:map(  ( fun ( Y ) -> ?MODULE:euler(  ( Y  )  )  end  )  , X  )  ) ,
		halt 
	end.

fib([X|R]) when X =< 1 ->
  X;
fib([X|R]) ->
  fib([X-1]) + fib([X-2]) + fib([X-3]) + fib([X-4]).

testFib() ->
    fib([35]),
    fib([35]),  
    fib([35]),
    fib([35]).

worker ( PIn , POut )  -> 
	receive
		X -> 		(fib(X)) ,
                    POut ! 42,
		halt 
	end.

farmTest (Nw, Size  )  -> 
	Res = 	?MODULE:spawnN( 0  , Nw  , nat  , nat  , eW  ) ,
   % L =  utils:n_length_chunks(  ( ?MODULE:mkList( 10000  )  )  , 2500 ) ,
        L = utils:unshuffle(Nw, ?MODULE:mkList(Size)),
	?MODULE:sendN(  ( ?MODULE:convertChans( nat  , Res  , L )  )  ) ,
	Msgs = 	?MODULE:recN( nat  ,  ( ?MODULE:inChans( Res  )  )  ) ,
	% io:format("~w", [Msgs]).
    Msgs. 

run_examples(X, Y) ->
  erlang:system_flag(schedulers_online, X),
  io:format("SumEuler: ~p~n", [sk_profile:benchmark(fun ?MODULE:farmTest/2, [X,Y], 1)]),
  io:format("Done with examples on ~p cores.~n------~n", [X]).
