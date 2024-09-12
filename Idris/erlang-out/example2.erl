-module(example2).
-compile(export_all).
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

