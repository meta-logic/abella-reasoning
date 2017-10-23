module llf.

dual (atom A) (natom A).
dual (tens P Q) (par M N) :- dual P M, dual Q N.
dual one bot.
dual (choice P Q) (with M N) :- dual P M, dual Q N.
dual zero top.
dual (fex P) (fall N) :- pi x\ dual (P x) (N x).
dual (bang N) (qm P) :- dual P N.
dual (shp N) (shn P) :- dual P N.

subf (fatom A) (atom A).
subf (fshift N) (shp N) :- dual P N.
subf (fbang N) (bang N) :- dual P N.
subf (fjoin F1 F2) (tens P Q) :- subf F1 P, subf F2 Q.
subf F (choice P Q) :- subf F P.
subf F (choice P Q) :- subf F Q.
subf F (fex P) :- subf F (P T).
subf femp one.
