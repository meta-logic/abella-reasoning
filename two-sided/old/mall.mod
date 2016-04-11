%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                    %%
%%       MALL specification in        %%
%%       λProlog (.mod)               %%
%%                                    %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

module mall.

%% Equality
eq X X.

is_list empty.
is_list (list_o X L) :- is_list L.

%% list_o is the data structure used to handle contexts (multisets of formulas)
%% list_o A (list_o B (list_o C empty)) is equivalent to (A::B::C::nil)
memb_and_rest X (list_o X L) L.
memb_and_rest X (list_o Y L1) (list_o Y L2) :- memb_and_rest X L1 L2.

%% Splitting contexts 
%% split L1 L2 L3 => L2 + L3 = L1.
%% For computationally expensive cases use Dale's solution
split empty empty empty.
split (list_o X L1) L2 (list_o X L3) :- split L1 L2 L3.
split (list_o X L1) (list_o X L2) L3 :- split L1 L2 L3.

%% Identity rules   
%:init:
prove Gamma Delta :- memb_and_rest (atom A) Gamma empty,
                     memb_and_rest (atom A) Delta empty.                % init

%% Multiplicative rules
prove Gamma Delta :- memb_and_rest one Delta empty,
                     eq Gamma empty.                                    % oneR

prove Gamma Delta :- is_list Gamma',
                     memb_and_rest one Gamma Gamma',
      	    	       prove Gamma' Delta.                                % oneL

%:tensorl:
prove Gamma Delta :- is_list Gamma',
                     memb_and_rest (tensor A B) Gamma Gamma',
      	    	       prove (list_o A (list_o B Gamma')) Delta.          % tensorL
%:tensorr:
prove Gamma Delta :- is_list Delta', is_list G1, is_list D1, 
                     is_list G2, is_list D2,
                     memb_and_rest (tensor A B) Delta Delta',
      	    	       split Delta' D1 D2, split Gamma G1 G2,
      	    	       prove G1 (list_o A D1), prove G2 (list_o B D2).    % tensorR

prove Gamma Delta :- memb_and_rest bot Gamma empty,
                     eq Delta empty.                                    % botL

prove Gamma Delta :- is_list Delta',
                     memb_and_rest bot Delta Delta',
      	    	       prove Gamma Delta'.                                % botR
%:parl:
prove Gamma Delta :- is_list Gamma', is_list G1, is_list D1,
                     is_list G2, is_list D2,
                     memb_and_rest (par A B) Gamma Gamma',
      	    	       split Gamma' G1 G2, split Delta D1 D2,
		                 prove (list_o A G1) D1, prove (list_o B G2) D2.    % parL
%:parr:
prove Gamma Delta :- is_list Delta',
                     memb_and_rest (par A B) Delta Delta',
		                 prove Gamma (list_o A (list_o B Delta')).          % parR

%% Additive rules
prove Gamma Delta :- memb_and_rest zero Gamma _.                        % zeroL

prove Gamma Delta :- memb_and_rest top Delta _.                         % topR

%:withl1:
prove Gamma Delta :- is_list Gamma',
                     memb_and_rest (with A B) Gamma Gamma',
      	    	       prove (list_o A Gamma') Delta.                     % withL1
%:withl2:
prove Gamma Delta :- is_list Gamma',
                     memb_and_rest (with A B) Gamma Gamma',
      	    	       prove (list_o B Gamma') Delta.                     % withL2
%:withr:
prove Gamma Delta :- is_list Delta',
                     memb_and_rest (with A B) Delta Delta',
      	    	       prove Gamma (list_o A Delta'),
		                 prove Gamma (list_o B Delta').                     % withR
%:plusl:
prove Gamma Delta :- is_list Gamma',
                     memb_and_rest (plus A B) Gamma Gamma',
      	    	       prove (list_o A Gamma') Delta,
		                 prove (list_o B Gamma') Delta.                     % plusL
%:plusr1:
prove Gamma Delta :- is_list Delta',
                     memb_and_rest (plus A B) Delta Delta',
      	    	       prove Gamma (list_o A Delta').                     % plusR1
%:plusr2:
prove Gamma Delta :- is_list Delta',
                     memb_and_rest (plus A B) Delta Delta',
      	    	       prove Gamma (list_o B Delta').                     % plusR2