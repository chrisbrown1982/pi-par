-module(parMatMul).
-compile(export_all).
spawnN ( M, N , 0 , ToTy , FrmTy , P )  ->
        [];
spawnN ( M, N , (Num) , ToTy , FrmTy , P )  ->
        S =     spawn( ?MODULE , P  , [ M, chan  , self()  ]  ) ,
        R =     ?MODULE:spawnN( M,  ( N  + 2  )  , Num-1  , ToTy  , FrmTy  , P  ) ,
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
transpose1 ( ([[]|N]) )  ->
        [];
transpose1 ( B )  ->
        [ ( lists:map(  ( fun ( X ) -> hd( X  )  end  )  , B  )  )  | ?MODULE:transpose1(  ( lists:map(  ( fun ( X ) -> tl( X  )  end  )  , B  )  )  ) ]
.
red ( Pair , Sum )  ->
         ( utils:fst2( Pair  )  )  *  ( utils:snd2( Pair  )  )  + Sum
.
dot_product ( A , B )  ->
        lists:foldl( fun red/2  , 0  ,  ( lists:zip( A  , B  )  )  )
.
multiply_row_by_col ( Row , [] )  ->
        [];
multiply_row_by_col ( Row , ([Col_head|Col_rest]) )  ->
        [ ( ?MODULE:dot_product( Row  , Col_head  )  )  |  ( ?MODULE:multiply_row_by_col( Row  , Col_rest  )  ) ]
.
multiply_internal ( [] , B )  ->
        [];
multiply_internal ( ([Head|Rest]) , B )  ->
        [ ( ?MODULE:multiply_row_by_col( Head  , B  )  )  |  ( ?MODULE:multiply_internal( Rest  , B  )  ) ]
.
multiply ( A , B )  ->
        ?MODULE:multiply_internal( A  ,  ( ?MODULE:transpose1( B  )  )  )
.
mkMsg ( [] )  ->
        [mend ];
mkMsg ( ([X|Xs]) )  ->
        [{msg ,X } | ?MODULE:mkMsg( Xs  ) ]
.
pRR ( MatB , PIn , POut )  ->
        receive
                X -> case X of
         ( {msg,M} )  ->
        POut  !  ( ?MODULE:multiply_row_by_col( M  , MatB  )  ) ,
        Y =     ?MODULE:pRR( MatB  , PIn  , POut  ) ,
        {};
         ( mend )  ->
        halt
end
        end
.
farm4RR ( Nw , Input , MatBT )  ->
        Res =   ?MODULE:spawnN( MatBT, 0  , Nw  , msgt  , msgt  , pRR  )    ,
        ?MODULE:roundRobin( msgt  , Input  ,  ( ?MODULE:convertChansRR( Res  )  )  ) ,
        Msgs =  ?MODULE:roundRobinRec(  ( utils:minus(  ( length( Input  )  )  , 1  )  )  ,  ( ?MODULE:inChans( Res  )  )  ) ,
        Msgs
.