from propositional import (Implies, And, Conjunction, ModusPonens, HypSyll, _False, Prop,
	Contradiction, equal_type, Explosion, ImplicationToOr
	)

from tautologies import NonContradiction, Trivial

# user code

# A is a proposition
class A(Prop):
	def __new__(cls):
		return object.__new__(cls)

# B is a proposition that is true by axiom
class B(Prop):
	def __new__(cls):
		return object.__new__(cls)

# C is a proposition
class C(Prop):
	pass

class X(Prop):
	pass

class X_is_False(Implies):
	antecedent = X
	consequent = _False

	def __new__(cls):
		return object.__new__(cls)


# A -> B is a proposition which we have named as variable 'A_implies_B'
# A -> B is an 'element' if Implies, which is a subset of Prop
class A_implies_B(Implies):
	antecedent = A
	consequent = B

	def __new__(cls):
		return object.__new__(cls)


# Define an axiom/premise/hypothesis which is assumed to be True
# B -> C is a proposition which we have named as variable 'B_implies_C'
class B_implies_X(Implies):
	antecedent = B
	consequent = X

	# Changing __new__ to this means we can create an object of this class directly
	# So this class is an 'axiom'
	def __new__(cls):
		return object.__new__(cls)

class SorryProofA_is_False(Implies):
	antecedent = A
	consequent = _False

	def __new__(cls):
		return object.__new__(cls)

axiom_a_imp_b = A_implies_B()
axiom_b_imp_x = B_implies_X()
axiom_a = A()

# construct a proof that A is False
proof_that_a_is_false = (
	HypSyll(
		HypSyll(axiom_a_imp_b, axiom_b_imp_x),
		X_is_False()
	)
)
proof_of_a_and_not_a = Conjunction(axiom_a, proof_that_a_is_false)

print(proof_that_a_is_false)

# Check the proof
assert equal_type( proof_that_a_is_false, SorryProofA_is_False())

print(
	ModusPonens(NonContradiction(A), proof_of_a_and_not_a)
)

print(ImplicationToOr(proof_that_a_is_false))

