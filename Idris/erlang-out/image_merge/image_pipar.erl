-module(image_pipar).
-compile(export_all).
spawnN ( N , 0 , ToTy , FrmTy , P, C )  -> 
	[];
spawnN ( N , (Num) , ToTy , FrmTy , P, C )  -> 
	S = 	spawn( ?MODULE , P  , [ chan  , C  ]  ) ,
	R = 	?MODULE:spawnN(  ( N  + 2  )  , Num-1  , ToTy  , FrmTy  , P, C  ) ,
	 ( [{N ,S } | R ] ) 
.
sendN ( [] )  -> 
	{};
sendN ( ([{M,{T,{C,Msg}}}|Cs]) )  -> 
	C  ! Msg ,
	?MODULE:sendN( Cs  ) ,
	{}
.
roundRobin ( MsgT , [] , [] )  -> 
	{};
roundRobin ( MsgT , [] , ([{M,C}|Chs]) )  -> 
	%C  ! mend ,
	%?MODULE:roundRobin( msgt  , [] , Chs  ) ,
	{};
roundRobin ( MsgT , ([M|Ms]) , [] )  -> 
	{};
roundRobin ( MsgT , ([Ms|Msgs]) , ([{M,C}|Chs]) )  -> 
	C  ! Ms ,
	?MODULE:roundRobin( msgt  , Msgs  ,  ( lists:append(Chs  , [{M ,C }]) )  ) ,
	{}
.
roundRobinRec ( 0 , X )  -> 
	[];
roundRobinRec ( (N) , [] )  -> 
	[];
roundRobinRec ( (N) , ([{M,C}|Chs]) )  -> 
	receive
		M1 -> 	 
		 	Msgs = 		?MODULE:roundRobinRec( N-1  ,  ( lists:append(Chs  , [{M ,C }]) )  ) ,
		 ( [M1  | Msgs ] ) 
	end
.
pipeMessages ( [] , X )  -> 
	{};
pipeMessages ( ([{M,Inc}|Ics]) , [] )  -> 
	{};
pipeMessages ( ([{M,Inc}|Ics]) , ([{M2,Oc}|Ocs]) )  -> 
	receive
		M1 -> case M1 of
	 ( {msg,Msg} )  -> 
	Oc  !  ( {msg ,Msg } ) ,
	?MODULE:pipeMessages(  ( lists:append(Ics  , [{M ,Inc }]) )  ,  ( lists:append(Ocs  , [{M2 ,Oc }]) )  ) ;
	         ( mend )  -> 
        Oc  ! mend ,
        ?MODULE:pipeMessages( Ics  , Ocs  ) 
end
	end
.

pipeMessages2 ( 0, [] )  ->
        {};
pipeMessages2 ( N, ([{M2,Oc}|Ocs]) )  ->
        receive
                M1 -> case M1 of
         ( {msg,Msg} )  ->
        Oc  !  ( {msg ,Msg } ) ,
        ?MODULE:pipeMessages2( N-1,  ( lists:append(Ocs  , [{M2 ,Oc }]) )  )
	     %    ( mend )  ->
        %Oc  ! mend ,
        %?MODULE:pipeMessages2( Ocs  ) 
end
        end
.


recNChan ( Ty , [] )  -> 
	[];
recNChan ( Ty , ([{M,C}|Chs]) )  -> 
	receive
		M1 -> 		Msgs = 		?MODULE:recNChan( Ty  , Chs  ) ,
		 ( [M1  | Msgs ] ) 
	end
.
p ( PIn , POut )  -> 
	receive
		X -> 		POut  ! 42 ,
		halt 
	end
.
test (  )  -> 
	C = 	spawn( ?MODULE , p  , [ chan  , self()  ]  ) ,
	 ( utils:fst( C  )  )  ! 42 ,
	receive
		V -> 		halt 
	end
.
convertChans ( T , [] , Msgs )  -> 
	[];
convertChans ( T , ([{M,C}|Rest]) , ([Msg|Msgs]) )  -> 
	[{M ,{T ,{utils:fst( C  ) ,Msg }}} | ?MODULE:convertChans( T  , Rest  , Msgs  ) ]
.
convertChansRR ( [] )  -> 
	[];
convertChansRR ( ([{M,C}|Rest]) )  -> 
	[{M , ( utils:fst( C  )  ) } | ?MODULE:convertChansRR( Rest  ) ]
.
inChans ( [] )  -> 
	[];
inChans ( ([{M,I}|Chs]) )  -> 
	[{ ( utils:s( M  )  ) ,utils:snd( I  ) } | ?MODULE:inChans( Chs  ) ]
.
outChans ( [] )  -> 
	[];
outChans ( ([{M,I}|Chs]) )  -> 
	[{M ,utils:fst( I  ) } | ?MODULE:outChans( Chs  ) ]
.
farm4 ( InTy , OutTy , Nw , W , Input )  -> 
	Res = 	?MODULE:spawnN( 0  , 4  , InTy  , OutTy  , W  ) ,
	?MODULE:sendN(  ( ?MODULE:convertChans( InTy  , Res  , Input  )  )  ) ,
	Msgs = 	?MODULE:recNChan( OutTy  ,  ( ?MODULE:inChans( Res  )  )  ) ,
	Msgs 
.
iW ( PIn , POut )  -> 
	receive
		X -> case X of
	 ( mend )  -> 
        	
	eos ;
	 ( {msg,M} )  ->
	POut  !  ( {msg , ( list_merge:convertMerge(list_merge:readImage(M  ))) } ) ,

	Y = 	?MODULE:iW( PIn  , POut  ) ,
	{}
end
	end
.

mkMsg ([] )  ->
        [ ];
mkMsg ( ([X|Xs]) )  ->
        [{msg ,X } | ?MODULE:mkMsg( Xs  ) ].

mergeFarm ( Nw ,X )  -> 
	Images = mkMsg(list_merge:imageList(X)),
	Res = 	?MODULE:spawnN( 0  , Nw  , msgt  , msgt  , iW, self()  ) ,
	?MODULE:roundRobin( msgt  , Images  ,  ( ?MODULE:convertChansRR( Res  )  )  ) ,
	Msgs = 	?MODULE:roundRobinRec(  ( length( Images  ) -1  )  ,  ( ?MODULE:inChans( Res  )  )  ) ,
	Msgs 
.

runFarm( Nw, X) -> 
	erlang:system_flag(schedulers_online, Nw), 
	io:format("Image Merge Farm ~p~n", [sk_profile:benchmark(fun ?MODULE:mergeFarm/2, [Nw, X], 1)]),
	io:format("Done on ~p cores ~n", [Nw]).

s1 ( PIn , POut )  -> 
	receive
		X -> case X of
	 ( {msg,M} )  ->
 %io:format("S1: ~p~n", [M]),
	M2 = list_merge:readImage(M),
	POut  !  ( {msg , ( M2 ) } ) ,
	Y = 	?MODULE:s1( PIn  , POut  ) ,
	{};
	( mend) -> 
		POut ! mend, 
		eos
end
	end
.
s2 ( PIn , POut )  -> 
	receive
		X -> case X of
	 ( {msg,{T1, T2, T3, T4, T5}} ) -> 
	%io:format("S2: ~p~n", [M]),
	M2 = list_merge:convertMerge({T1, T2, T3, T4, T5}),
	POut  !  ( {msg2 , ( M2 ) } ) ,
	Y = 	?MODULE:s2( PIn  , POut  ) ,
	{};
	( mend ) -> 
		eos
end
	end
.
mergePipeFarm ( NW1 , NW2 , X )  -> 
	erlang:system_flag(schedulers_online, 56),
	Images = mkMsg(list_merge:imageList(X)),
	ResS2 = 	?MODULE:spawnN( 0  , NW2	  , msgt  , msgt  , s2, self()  ) ,
	P = spawn(?MODULE,pipeMessages2, [ X, ?MODULE:outChans( ResS2)]) ,
	ResS1 = 	?MODULE:spawnN( 8  , NW1  , msgt  , msgt  , s1, P  ) ,
	?MODULE:roundRobin( msgt  , Images  ,  ( ?MODULE:convertChansRR( ResS1  )  )  ) ,
	Msgs = 	?MODULE:roundRobinRec(  X     ,  ( ?MODULE:inChans( ResS2  )  )  ) ,
	Msgs 
.

runPipe(Nw1, Nw2, X) ->
   	io:format("Image Merge Pipe on ~p ~p ~p ~n", [Nw1, Nw2, sk_profile:benchmark(fun ?MODULE:mergePipeFarm/3, [Nw1, Nw2, X], 1)]),
	io:format("Done on ~p and ~p cores ~n." , [Nw1, Nw2]).


t1 ( PIn , POut )  ->
        receive
                X -> case X of
         ( mend )  ->
        POut  ! mend ,
        eos ;
         ( {msg,M} )  ->
        % io:format("S1: ~p~n", [M]),
        POut  !  ( {msg , ( M+10) } ) ,
        Y =     ?MODULE:t1( PIn  , POut  ) ,
        {}
end
        end
.
t2 ( PIn , POut )  ->
        receive
                X -> case X of
         ( mend )  ->
        eos ;
         ( {msg,M} )  ->
        % io:format("S2: ~p~n", [M]),
        POut  !  ( {msg , ( M+20  ) } ) ,
        Y =     ?MODULE:t2( PIn  , POut  ) ,
        {}
end
        end
.
%testPipe ( NW1 , NW2 , Images )  ->
        % Images = mkMsg(list_merge:imageList(X)),
%        io:format("~p~n", [Images]),
%        ResS1 =         ?MODULE:spawnN( 0  , NW1  , msgt  , msgt  , t1, P  ) ,
%        ResS2 =         ?MODULE:spawnN( 8  , NW2          , msgt  , msgt  , t2, self()  ) ,
%        P = spawn (?MODULE, pipeMessages, [?MODULE:inChans( ResS1  ),?MODULE:outChans( ResS2  )]  )  ,
%        ?MODULE:roundRobin( msgt  , Images  ,  ( ?MODULE:convertChansRR( ResS1  )  )  ) ,
%        Msgs =  ?MODULE:roundRobinRec(  ( length( Images  )   )  ,  ( ?MODULE:inChans( ResS2  )  )  ) ,
%        Msgs
%.
