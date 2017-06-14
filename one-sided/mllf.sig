sig mllf.

kind atm type.

type a, b, c, d, e, f atm.

kind pf, nf  type.

type atom  atm -> pf.
type tens  pf -> pf -> pf.
type one   pf.
type plus  pf -> pf -> pf.
type zero  pf.
type fex   (atm -> pf) -> pf.
type shp   nf -> pf.

type natom atm -> nf.
type par   nf -> nf -> nf.
type bot   nf.
type with  nf -> nf -> nf.
type top   nf.
type fall  (atm -> nf) -> nf.
type shn   pf -> nf.

type dual  pf -> nf -> o.

kind foc type.
type fatom  atm -> foc.
type fshift nf -> foc.
type fjoin  foc -> foc -> foc.
type femp   foc.

type subf  foc -> pf -> o.