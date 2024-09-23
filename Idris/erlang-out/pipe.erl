-module(pipe).
-compile(export_all).
spawnN ( N , 0 , ToTy , FrmTy , P )  -> 
	[];
spawnN ( N , (Num) , ToTy , FrmTy , P )  -> 
	S = 	spawn( ?MODULE , P  , [ chan  , self()  ]  ) ,
	R = 	?MODULE:spawnN(  ( N  + 2  )  , Num-1  , ToTy  , FrmTy  , P  ) ,
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
	C  ! mend ,
	?MODULE:roundRobin( msgt  , [] , Chs  ) ,
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
		M1 -> 		Msgs = 		?MODULE:roundRobinRec( N-1  ,  ( lists:append(Chs  , [{M ,C }]) )  ) ,
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
	 ( mend )  -> 
	Oc  ! mend ,
	?MODULE:pipeMessages( Ics  , Ocs  ) ;
	 ( {msg,Msg} )  -> 
	Oc  !  ( {msg ,Msg } ) ,
	?MODULE:pipeMessages(  ( lists:append(Ics  , [{M ,Inc }]) )  ,  ( lists:append(Ocs  , [{M2 ,Oc }]) )  ) 
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
pRR ( PIn , POut )  -> 
	receive
		X -> case X of
	 ( mend )  -> 
	halt ;
	 ( {msg,M} )  -> 
	POut  !  ( {msg , ( M  + 100  ) } ) ,
	Y = 	?MODULE:pRR( PIn  , POut  ) ,
	{}
end
	end
.
farm4RR ( Nw , W , Input )  -> 
	Res = 	?MODULE:spawnN( 0  , 4  , msgt  , msgt  , pRR  ) ,
	?MODULE:roundRobin( msgt  , Input  ,  ( ?MODULE:convertChansRR( Res  )  )  ) ,
	Msgs = 	?MODULE:roundRobinRec(  ( length( Input  )  )  ,  ( ?MODULE:inChans( Res  )  )  ) ,
	Msgs 
.
s1 ( PIn , POut )  -> 
	receive
		X -> case X of
	 ( mend )  -> 
	POut  ! mend ,
	halt ;
	 ( {msg,M} )  -> 
	POut  !  ( {msg , ( M  + 10  ) } ) ,
	Y = 	?MODULE:s1( PIn  , POut  ) ,
	{}
end
	end
.
s2 ( PIn , POut )  -> 
	receive
		X -> case X of
	 ( mend )  -> 
	halt ;
	 ( {msg,M} )  -> 
	POut  !  ( {msg , ( M  + 10  ) } ) ,
	Y = 	?MODULE:s2( PIn  , POut  ) ,
	{}
end
	end
.
pipe ( NW1 , S1 , NW2 , S2 , Input )  -> 
	ResS1 = 	?MODULE:spawnN( 0  , 4  , msgt  , msgt  , s1  ) ,
	ResS2 = 	?MODULE:spawnN( 8  , 4  , msgt  , msgt  , s2  ) ,
	?MODULE:roundRobin( msgt  , Input  ,  ( ?MODULE:convertChansRR( ResS1  )  )  ) ,
	?MODULE:pipeMessages(  ( ?MODULE:inChans( ResS1  )  )  ,  ( ?MODULE:outChans( ResS2  )  )  ) ,
	Msgs = 	?MODULE:roundRobinRec(  ( length( Input  )  )  ,  ( ?MODULE:inChans( ResS2  )  )  ) ,
	Msgs 
.
