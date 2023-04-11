from propositional import Or, And, Not, Implies

# https://en.wikipedia.org/wiki/Propositional_calculus#Basic_and_derived_argument_forms

def ExcludedMiddle(A):
	"""Given A: Prop, construct a proof of (A or not A)"""
	Not_A = Not(A)

	class A_or_not_A(Or):
		left_prop = A
		right_prop = Not_A

		def __new__(cls):
			return object.__new__(cls)
	return A_or_not_A()

def NonContradiction(A):
	"""Given A: Prop, construct a proof of not(A and not A)"""
	class A_and_not_A(And):
		left_prop = A
		right_prop = Not(A)


	return Not(A_and_not_A, is_true=True)()

def Trivial(A):
	"""Given A: Prop, construct the proof of (A -> A)"""
	class A_implies_A(Implies):
		antecedent = A
		consequent = A

		def __new__(cls):
			return object.__new__(cls)
	return A_implies_A()

	

