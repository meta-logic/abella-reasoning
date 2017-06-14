module mallq.

% By defining this predicate on the specification logic
% we can instantiate its nominal constants and the abella
% can identify that the IH applies. \o/

dual (atom A) (natom A).
dual (tens A B) (par AA BB) :- dual A AA, dual B BB.
dual one bot.
dual (plus A B) (wth AA BB) :- dual A AA, dual B BB.
dual zero top.
dual (exs A) (all B) :- pi x\ dual (A x) (B x).

