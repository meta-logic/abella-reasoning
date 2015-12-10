%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%				      %%
%%       MALL specification in        %%
%%       λProlog	      	      %%
%%				      %%
%%	 Leonardo Lima, 2015          %%
%%				      %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

sig mall.

%% List
kind    list_o                  type.

type    empty 			list_o.
type    list_o                  o -> list_o -> list_o.

type    is_list                 list_o -> o.

type 	split 			list_o -> list_o -> list_o -> o.
type 	memb_and_rest		o -> list_o -> list_o -> o.
type 	eq 			list_o -> list_o -> o.

%% MALL
kind	term, atm                type.

type	zero, one, bot, top	 o.
type	tensor, par, plus, with  o -> o -> o.
type    atom                     atm -> o.

type    prove		 	 list_o -> list_o -> o.
type	p			 term -> atm.
type 	a, b			 o.

