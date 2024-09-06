-module(matmul).

-compile(export_all).
 
transpose([[]|_]) ->
	    [];
transpose(B) ->
	  [lists:map(fun hd/1, B) | transpose(lists:map(fun tl/1, B))].
 
 
red(Pair, Sum) ->
	    X = element(1, Pair),   %gets X
	        Y = element(2, Pair),   %gets Y
		    X * Y + Sum.
 
%% Mathematical dot product. A x B = d
%% A, B = 1-dimension vector
%% d    = scalar
dot_product(A, B) ->
     lists:foldl(fun red/2, 0, lists:zip(A, B)).
      
       
%% Exposed function. Expected result is C = A x B.
multiply(A, B) ->
    %% First transposes B, to facilitate the calculations (It's easier to fetch
    %% row than column wise).
    %multiply_internal(A, transpose(B)).
    % io:fwrite("~p~n",[A]),
    % io:fwrite("~p~n",[B]),


    % io:fwrite("~p~n",[multiply_internal(A, transpose(B))]). 
    multiply_internal(A, transpose(B)).

multiply_by_row(R, B) ->
	Element = multiply_row_by_col(R, B),

	Element. 

 
%% This function does the actual multiplication, but expects the second matrix
%% to be transposed.
multiply_internal([Head | Rest], B) ->
  % multiply each row by Y
  Element = multiply_row_by_col(Head, B),
                         
  % concatenate the result of this multiplication with the next ones
  [Element | multiply_internal(Rest, B)];
                                                  
multiply_internal([], B) ->
  % concatenating and empty list to the end of a list, changes nothing.
  [].
                                                           
                                                            
multiply_row_by_col(Row, [Col_Head | Col_Rest]) ->
  Scalar = dot_product(Row, Col_Head),
                                                   
  [Scalar | multiply_row_by_col(Row, Col_Rest)];
                                                                      
multiply_row_by_col(Row, []) ->
  [].

start(Size) ->
     MatA =  lists:duplicate(Size, lists:seq(1,Size)),
     MatB =  lists:duplicate(Size, lists:seq(1,Size)), 
     multiply(MatA, MatB).

parmatmul(NW, Size) ->
	MatA = lists:duplicate(Size, lists:seq(1,Size)),
	MatB = lists:duplicate(Size, lists:seq(1,Size)),
	MatBT = transpose(MatB),
	skel:do([{farm, [{seq, fun(A) -> multiply_by_row(A, MatBT) end}], NW}],MatA).

run_example(X, Size) ->
     erlang:system_flag(schedulers_online,X),
     % MatA = lists:duplicate(Size, lists:seq(1,Size)),
     % MatB = lists:duplicate(Size, lists:seq(1,Size)),
     io:format("MatMulPar : ~p~n", [sk_profile:benchmark(fun ?MODULE:parmatmul/2, [X, Size], 1)]),
     io:format("Done~n").



