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
roundRobin ( MsgT , [] , Y )  ->
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
gcd2 ( A , 0 )  ->
        A ;
gcd2 ( A , B )  ->
        ?MODULE:gcd2( B  ,  ( A  rem B  )  )
.
relPrime ( X , Y )  ->
         ( ?MODULE:gcd2( X  , Y  )  )  == 1
.
mkList ( N )  ->
        lists:seq(      1  ,    N  )
.
euler ( N )  ->
        length(  ( lists:filter(  ( fun ( X ) -> ?MODULE:relPrime( N  , X  )  end  )  ,  ( ?MODULE:mkList( N  )  )  )  )  )
.
sumEuler ( N )  ->
        lists:sum(  ( lists:map(  ( fun ( X ) -> ?MODULE:euler(  ( X  )  )  end  )  ,  ( ?MODULE:mkList( N  )  )  )  )  )
.
pRR ( PIn , POut )  ->
        receive
                X -> case X of
         ( M )  ->
        POut  !  ( ?MODULE:euler( M  )  ) ,
        Y =     ?MODULE:pRR( PIn  , POut  ) ,
        {}
end
        end
.
farm4RR ( Nw , Input )  ->
        Res =   ?MODULE:spawnN( 0  , Nw  , msgt  , msgt  , pRR  ) ,
        ?MODULE:roundRobin( msgt  , Input  ,  ( ?MODULE:convertChansRR( Res  )  )  ) ,
        Msgs =  ?MODULE:roundRobinRec(  ( length( Input  )  )  ,  ( ?MODULE:inChans( Res  )  )  ) ,
        Msgs
.