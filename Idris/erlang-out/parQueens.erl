-module(parQueens).
-compile(export_all).
spawnN ( N , 0 , ToTy , FrmTy , P )  ->
        [];
spawnN ( N , (Num) , ToTy , FrmTy , P )  ->
        S =     spawn( ?MODULE , P  , [ chan  , self()  ]  ) ,
        R =     ?MODULE:spawnN(  ( N  + 2  )  , Num-1  , ToTy  , FrmTy  , P  ) ,
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
                M1 ->           Msgs =          ?MODULE:roundRobinRec( N-1  ,  ( lists:append(Chs  , [{M ,C }]) )  ) ,
                 ( [M1  | Msgs ] )
        end
.
recNChan ( Ty , [] )  ->
        [];
recNChan ( Ty , ([{M,C}|Chs]) )  ->
        receive
                M1 ->           Msgs =          ?MODULE:recNChan( Ty  , Chs  ) ,
                 ( [M1  | Msgs ] )
        end
.
p ( PIn , POut )  ->
        receive
                X ->            POut  ! 42 ,
                halt
        end
.
test (  )  ->
        C =     spawn( ?MODULE , p  , [ chan  , self()  ]  ) ,
         ( utils:fst( C  )  )  ! 42 ,
        receive
                V ->            halt
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
check ( {C,L} , {I,J} )  ->
         ( L  == J  )  or  (  ( C  + L  )  ==  ( I  + J  )  )  or  (  ( utils:minus( C  , L  )  )  ==  ( utils:minus( I  , J  )  )  )
.
safe ( P , N )  ->
        lists:foldr( fun(X,Y) -> X and Y end  , true  ,  ( [not(  ( ?MODULE:check( {I ,J } , {length( P  )  + 1 ,N } )  )  )  || {I,J} <-  ( lists:zip( lists:seq( 1  , length( P  )  )  , P  )  ) ] )  )
.
rainhas2 ( 0 , Linha , Numero )  ->
        [[]];
rainhas2 ( M , Linha , Numero )  ->
[lists:append( P  , [N ] )  || P <- ?MODULE:rainhas2(  ( utils:minus( M  , 1  )  )  , Linha  , Numero  ) ,N <-  ( lists:append(lists:seq( Linha  , Numero  )  , lists:seq( 1  , utils:minus( Linha  , 1  )  ) ) ) ,?MODULE:safe( P  , N  ) ]
.
prainhas ( Numero , Linha )  ->
        ?MODULE:rainhas2( Numero  , Linha  , Numero  )
.
search ( Numero , N )  ->
        lists:takewhile(  ( fun ( A ) -> hd( A  )  == N  end  )  ,  ( ?MODULE:prainhas( Numero  , N  )  )  )
.
rainhas ( N )  ->
        lists:map(  ( fun ( X ) -> ?MODULE:search( N  , X  )  end  )  , lists:seq( 1  , N  )  )
.

mkMsg (S, [] )  ->
        [mend ];
mkMsg (S,  ([X|Xs]) )  ->
        [{msg ,S, X } | ?MODULE:mkMsg( S, Xs  ) ].

pRR ( PIn , POut )  ->
        receive
                X -> case X of
         ( {msg,S,M} )  ->
        POut  !  ( ?MODULE:search( S, M  )  ) ,
        Y =     ?MODULE:pRR( PIn  , POut  ) ,
        {};
         ( mend )  ->
        eos
end
        end
.
farm4RR ( Nw , Size )  ->
        Res =   ?MODULE:spawnN( 0  , Nw  , msgt  , msgt  , pRR  ) ,
        ?MODULE:roundRobin( msgt  , mkMsg(Size, lists:seq(1,Size))  ,  ( ?MODULE:convertChansRR( Res  )  )  ) ,
        Msgs =  ?MODULE:roundRobinRec(  ( utils:minus(  Size    , 1  )  )  ,  ( ?MODULE:inChans( Res  )  )  ) ,
        Msgs
.

run(Nw, Size) ->
	erlang:system_flag(schedulers_online, Nw),
	io:format("Queens: ~p~n", [sk_profile:benchmark(fun ?MODULE:farm4RR/2, [Nw, Size], 1)]),
	io:format("Done with examples on ~p cores.~n--------~n", [Nw]).

