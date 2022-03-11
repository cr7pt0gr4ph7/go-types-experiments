package types

type checkerBase struct {
}

// implements checks if V implements T and reports an error if it doesn't.
// The receiver may be nil if implements is called through an exported
// API call such as AssignableTo.
func (check *checkerBase) implements(V, T Type) error {
	Vu := under(V)
	Tu := under(T)
	if Vu == Typ[Invalid] || Tu == Typ[Invalid] {
		return nil // avoid follow-on errors
	}
	if p, _ := Vu.(*Pointer); p != nil && under(p.base) == Typ[Invalid] {
		return nil // avoid follow-on errors (see issue #49541 for an example)
	}

	errorf := func(format string, args ...any) error {
		return errors.New(check.sprintf(format, args...))
	}

	Ti, _ := Tu.(*Interface)
	if Ti == nil {
		var cause string
		if isInterfacePtr(Tu) {
			cause = check.sprintf("type %s is pointer to interface, not interface", T)
		} else {
			cause = check.Sprintf("%s is not an interface", T)
		}
		return errorf("%s does not implement %s (%s)", V, T, cause)
	}

	// Every type satisfies the empty interface.
	if Ti.Empty() {
		return nil
	}
	// T is not the empty interface (i.e., the type set of T is restricted)

	// An interface V with an empty type set satisfies any interface.
	// (The empty set is a subset of any set.)
	Vi, _ := Vu.(*Interface)
	if Vi != nil && Vi.typeSet().IsEmpty() {
		return nil
	}
	// type set of V is not empty

	// No type with non-empty type set satisfies the empty type set.
	if Ti.typeSet().IsEmpty() {
		return errorf("cannot implement %s (empty type set)", T)
	}

	// V must implement T's methods, if any.
	if m, wrong := check.missingMethod(V, Ti, true); m != nil /* !Implements(V, Ti) */ {
		return errorf("%s does not implement %s %s", V, T, check.missingMethodReason(V, T, m, wrong))
	}

	// If T is comparable, V must be comparable.
	// Remember as a pending error and report only if we don't have a more specific error.
	var pending error
	if Ti.IsComparable() && !comparable(V, false, nil, nil) {
		pending = errorf("%s does not implement comparable", V)
	}

	// V must also be in the set of types of T, if any.
	// Constraints with empty type sets were already excluded above.
	if !Ti.typeSet().hasTerms() {
		return pending // nothing to do
	}

	// If V is itself an interface, each of its possible types must be in the set
	// of T types (i.e., the V type set must be a subset of the T type set).
	// Interfaces V with empty type sets were already excluded above.
	if Vi != nil {
		if !Vi.typeSet().subsetOf(Ti.typeSet()) {
			// TODO(gri) report which type is missing
			return errorf("%s does not implement %s", V, T)
		}
		return pending
	}

	// Otherwise, V's type must be included in the iface type set.
	var alt Type
	if Ti.typeSet().is(func(t *term) bool {
		if !t.includes(V) {
			// If V ∉ t.typ but V ∈ ~t.typ then remember this type
			// so we can suggest it as an alternative in the error
			// message.
			if alt == nil && !t.tilde && Identical(t.typ, under(t.typ)) {
				tt := *t
				tt.tilde = true
				if tt.includes(V) {
					alt = t.typ
				}
			}
			return true
		}
		return false
	}) {
		if alt != nil {
			return errorf("%s does not implement %s (possibly missing ~ for %s in constraint %s)", V, T, alt, T)
		} else {
			return errorf("%s does not implement %s", V, T)
		}
	}

	return pending
}
