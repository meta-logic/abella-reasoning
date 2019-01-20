module mllq.

$is (atom P).
$is (tens A B) :- $is A, $is B.
$is one.
$is (fex A) :- pi x\ $is (A x).

$is (natom P).
$is (par A B) :- $is A, $is B.
$is bot.
$is (fall A) :- pi x\ $is (A x).


dual (atom A) (natom A).
dual (tens A B) (par AA BB) :- dual A AA, dual B BB.
dual one bot.
dual (fex A) (fall B) :- pi x\ dual (A x) (B x).