module mallf.

dual (atom A) (natom A).
dual (tens P Q) (par M N) :- dual P M, dual Q N.
dual one bot.
dual (oplus P Q) (with M N) :- dual P M, dual Q N.
dual zero top.
dual (fex P) (fall N) :- pi x\ dual (P x) (N x).
dual (shp N) (shn P) :- dual P N.
