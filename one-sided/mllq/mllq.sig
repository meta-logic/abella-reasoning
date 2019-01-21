sig mllq.

kind term, atm type.

type a, b, c, d, e, f atm.

kind fm type.

type atom    atm -> fm.
type tens    fm -> fm -> fm.
type one     fm.
type fex     (term -> fm) -> fm.

type natom   atm -> fm.
type par     fm -> fm -> fm.
type bot     fm.
type fall    (term -> fm) -> fm.

type $is     fm -> o.
type dual    fm -> fm -> o.
