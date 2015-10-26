%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%				      %%
%%       MALL specification in        %%
%%       λProlog	      	      %%
%%				      %%
%%	 Leonardo Lima, 2015          %%
%%				      %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

module mall.

%% Treatment of equality
eq X X.

%% list_o is the data structure used to handle contexts (multisets of formulas)
%% list_o A (list_ B (list_ C empty)) is equivalent to (A::B::C::nil)
memb_and_rest X (list_o X L) L.
memb_and_rest X (list_o Y L1) (list_o Y L2) :- memb_and_rest X L1 L2.

%% Splitting contexts 
%% For computationally expensive cases use Dale's another solution
split empty empty empty.
split (list_o X L1) L2 (list_o Y L3) :- split L1 L2 L3.

%% example: prove (list_o (plus (p a) (p b)) empty) (list_o (with (p a) (p b)) (list_o (p a) (list_o (p b) empty))).

%% Identity rules
prove Gamma Delta :- memb_and_rest A Gamma _,
      	    	     memb_and_rest A Delta _.				% init

%% Multiplicative rules
prove Gamma Delta :- memb_and_rest one Gamma Gamma',
      	    	     prove Gamma' Delta.				% oneL

prove Gamma Delta :- memb_and_rest one Delta Delta',
      	    	     eq Gamma empty, eq Delta' empty.			% oneR

prove Gamma Delta :- memb_and_rest (tensor A B) Gamma Gamma',
      	    	     prove (list_o A (list_o B Gamma')) Delta.		% tensorL

prove Gamma Delta :- memb_and_rest (tensor A B) Delta Delta',
      	    	     split Delta' D1 D2, split Gamma G1 G2,
      	    	     prove G1 (list_o A D1), prove G2 (list_o B D2).	% tensorR

prove Gamma Delta :- memb_and_rest bot Gamma Gamma',
      	    	     eq Gamma' empty, eq Delta empty.			% botL

prove Gamma Delta :- memb_and_rest bot Delta Delta',
      	    	     prove Gamma Delta'.				% botR

prove Gamma Delta :- memb_and_rest (par A B) Gamma Gamma',
      	    	     split Gamma' G1 G2, split Delta D1 D2,
		     prove (list_o A G1) D1, prove (list_o B G2) D2.	% parL

prove Gamma Delta :- memb_and_rest (par A B) Delta Delta',
		     prove Gamma (list_o A (list_o B Delta')).		% parR

%% Additive rules
prove Gamma Delta :- memb_and_rest zero Gamma _.   			% zeroL

prove Gamma Delta :- memb_and_rest top Delta _. 			% topR

prove Gamma Delta :- memb_and_rest (with A B) Gamma Gamma',
      	    	     prove (list_o A Gamma') Delta.			% withL1

prove Gamma Delta :- memb_and_rest (with A B) Gamma Gamma',
      	    	     prove (list_o B Gamma') Delta.			% withL2

prove Gamma Delta :- memb_and_rest (with A B) Delta Delta',
      	    	     prove Gamma (list_o A Delta'),
		     prove Gamma (list_o B Delta').			% withR

prove Gamma Delta :- memb_and_rest (plus A B) Gamma Gamma',
      	    	     prove (list_o A Gamma') Delta,
		     prove (list_o B Gamma') Delta.			% plusL

prove Gamma Delta :- memb_and_rest (plus A B) Delta Delta',
      	    	     prove Gamma (list_o A Delta').			% plusR1

prove Gamma Delta :- memb_and_rest (plus A B) Delta Delta',
      	    	     prove Gamma (list_o B Delta').			% plusR2