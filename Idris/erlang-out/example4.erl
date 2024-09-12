-module(example4).
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
	Res = 	?MODULE:spawnN( 4  , InTy  , OutTy  , W  ) ,
	?MODULE:sendN(  ( ?MODULE:convertChans( InTy  , Res  , Input  )  )  ) ,
	Msgs = 	?MODULE:recN( OutTy  ,  ( ?MODULE:inChans( Res  )  )  ) ,
	Msgs .

w ( PIn , POut )  -> 
	halt .

transpose1 ( ([[]|N]) )  -> 
	[];
transpose1 ( B )  -> 
	[	 ( 	lists:map(  ( fun ( X ) -> hd( X  )  end  )  , B  )  )  | 	?MODULE:transpose1(  ( lists:map(  ( fun ( X ) -> tl( X  )  end  )  , B  )  )  ) ].

red ( Pair , Sum )  -> 
		 ( 	utils:fst2( Pair  )  )  * 		 ( 	utils:snd2( Pair  )  )  + 	Sum .

dot_product ( A , B )  -> 
	lists:foldl(fun red/2  , 0  ,  ( lists:zip( A  , B  )  )  ) .

multiply_row_by_col ( Row , [] )  -> 
	[];
multiply_row_by_col ( Row , ([Col_head|Col_rest]) )  -> 
	[	 ( 	?MODULE:dot_product( Row  , Col_head  )  )  | 	 ( 	?MODULE:multiply_row_by_col( Row  , Col_rest  )  ) ].

multiply_internal ( [] , B )  -> 
	[];
multiply_internal ( ([Head|Rest]) , B )  -> 
	[	 ( 	?MODULE:multiply_row_by_col( Head  , B  )  )  | 	 ( 	?MODULE:multiply_internal( Rest  , B  )  ) ].


multiply_by_row(R, B) ->
	Element = multiply_row_by_col(R, B),

	Element. 

multiply ( A , B )  -> 
	?MODULE:multiply_internal( A  ,  ( ?MODULE:transpose1( B  )  )  ) .

eW (  PIn , POut )  -> 
    MatB =  lists:duplicate(1000, lists:seq(1,1000)), 
    MatBT = transpose1(MatB),
	receive
		X ->  POut  !  ( multiply_internal ( X , MatBT) )
		 
	end.

farmTest (  )  -> 
    MatA =  lists:duplicate(1000, lists:seq(1,1000)),
	Res = 	?MODULE:spawnN( 0  , 4  , nat  , nat  ,  eW ),
	?MODULE:sendN(  ( ?MODULE:convertChans( nat  , Res  ,  ( utils:n_length_chunks(  ( MatA  )  ,250  )  )  )  )  ) ,
	Msgs = 	?MODULE:recN( nat  ,  ( ?MODULE:inChans( Res  )  )  ) ,
	Msgs .


start(Size) ->
     MatA =  lists:duplicate(Size, lists:seq(1,Size)),
     MatB =  lists:duplicate(Size, lists:seq(1,Size)), 
     multiply(MatA, MatB).