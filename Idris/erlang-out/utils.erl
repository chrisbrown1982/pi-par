-module(utils).
-compile(export_all).

fst(A) -> A. % element(1, A).

snd(A) -> A. % element(2, A).

fst2 (A) -> element(1, A).

snd2 (A) -> element(2, A).

n_length_chunks([],_) -> [];
n_length_chunks(List,Len) when Len > length(List) ->
    [List];
n_length_chunks(List,Len) ->
    {Head,Tail} = lists:split(Len,List),
    [Head | n_length_chunks(Tail,Len)].