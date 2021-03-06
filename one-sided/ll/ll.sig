sig ll.

kind term, atm, fm type.

type a, b, c, d, e, f atm.

%% We reuse the o type to define LL formulas
type atom, natom   atm -> fm.
type tens, par     fm -> fm -> fm.
type one, bot      fm.
type wth, pls     fm -> fm -> fm.
type top, zero     fm.
type bang, qm      fm -> fm.
%% A quantifier on the object level is defined using the
%% HOAS (or lambda-parse trees) approach, i.e., a binder
%% on the object level is a binder on the meta-level
%% (hence the first function argument).
type all, exs      (term -> fm) -> fm.

type dual fm -> fm -> o.

