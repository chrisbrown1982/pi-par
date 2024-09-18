-module(rr).
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
roundRobin ( MsgT , [] , Y , [] )  ->
        {};
roundRobin ( MsgT , [] , Chs , ([{M,C}|Chs2]) )  ->
        C  ! mend ,
        ?MODULE:roundRobin( msgt  , [] , Chs  , Chs2  ) ,
        {};
roundRobin ( MsgT , ([Ms|Msgs]) , [] , Chs2 )  ->
        ?MODULE:roundRobin( msgt  ,  ( [Ms  | Msgs ] )  , Chs2  , Chs2  ) ;
roundRobin ( MsgT , ([Ms|Msgs]) , ([{M,C}|Chs]) , Chs2 )  ->
        C  ! Ms ,
        ?MODULE:roundRobin( msgt  , Msgs  , Chs  , Chs2  ) ,
        {}
.
roundRobinRec ( 0 , [] , Chs2 )  ->
        ?MODULE:roundRobinRec( 0  , Chs2  , Chs2  ) ;
roundRobinRec ( 0 , ([{M,C}|Chs]) , Chs2 )  ->
        receive
                M1 ->            ( [M1  | []] )
        end;
roundRobinRec ( (N) , [] , Chs2 )  ->
        ?MODULE:roundRobinRec( N-1  , Chs2  , Chs2  ) ;
roundRobinRec ( (N) , ([{M,C}|Chs]) , Chs2 )  ->
        receive
                M1 ->           Msgs =          ?MODULE:roundRobinRec( N-1  , Chs  , Chs2  ) ,
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
farm4 ( InTy , OutTy , Nw , W , Input )  ->
        Res =   ?MODULE:spawnN( 0  , 4  , InTy  , OutTy  , W  ) ,
        ?MODULE:sendN(  ( ?MODULE:convertChans( InTy  , Res  , Input  )  )  ) ,
        Msgs =  ?MODULE:recNChan( OutTy  ,  ( ?MODULE:inChans( Res  )  )  ) ,
        Msgs
.
pRR ( PIn , POut )  ->
        receive
                X -> case X of
         ( mend )  ->
         io:format("Halting~n"),
        halt ;
         ( {msg,M} )  ->
        POut  !  ( {msg , ( M  + 100  ) } ) ,
        Y =     ?MODULE:pRR( PIn  , POut  ) ,
        {}
end
        end
.
farm4RR ( Nw , W , Input )  ->
        Res =   ?MODULE:spawnN( 0  , 4  , msgt  , msgt  , pRR  ) ,
        ?MODULE:roundRobin( msgt  , Input  ,  ( ?MODULE:convertChansRR( Res  )  )  ,  ( ?MODULE:convertChansRR( Res  )  )  ) ,
        Msgs =  ?MODULE:roundRobinRec(  ( length( Input  )  )  ,  ( ?MODULE:inChans( Res  )  )  ,  ( ?MODULE:inChans( Res  )  )  ) ,
        Msgs
.
