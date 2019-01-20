sig mllq.

kind atm type.

type a, b, c, d, e, f atm.

kind fm type.

type atom    atm -> fm.
type tens    fm -> fm -> fm.
type one     fm.
type fex     (atm -> fm) -> fm.

type natom   atm -> fm.
type par     fm -> fm -> fm.
type bot     fm.
type fall    (atm -> fm) -> fm.

type $is     fm -> o.
type dual    fm -> fm -> o.