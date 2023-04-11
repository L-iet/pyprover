# https://en.wikipedia.org/wiki/Propositional_calculus#Basic_and_derived_argument_forms
# proofs are objects
# others (Propositions ie (A or B), (C and D) etc, Prop) are classes
"∈∃∀⊆×∧∨"
reprs = {
	"implies": (lambda cls: f"Implies({cls.antecedent}, {cls.consequent})"),
	"and": (lambda cls: f"And({cls.left_prop}, {cls.right_prop})"),
	"forall": (lambda cls: f"∀{cls.obj}, {cls.prop_about_obj}"),
	"exists": (lambda cls: f"∃{cls.obj}, {cls.prop_about_obj}"),
	"not": (lambda cls: f"Implies({cls.antecedent}, _False)"),
	"or": (lambda cls: f"Or({cls.left_prop}, {cls.right_prop})"),
}

class Meta(type):
	def __repr__(cls):
		for key in reprs:
			if key in cls.__name__.lower():
				return reprs[key](cls)
		return cls.__name__



def default_new(cls):
	raise Exception(f"Proposition '{cls}' is not an axiom. Try making this proposition True in the class definition.")


# (not X) is defined as (X -> _False)

class Prop(metaclass=Meta):
	obj = None
	predicate = None # If the proposition was from a predicate, this is the predicate
	def __new__(cls):
		default_new(cls)
	def __repr__(self):
		"""If an object is created, it will be a proof."""
		return f"Proof({self.__class__})"

def _produce_a_proof(cls):
	if issubclass(cls, Prop):
		# Need to copy the class, set andreset the new attr
		type_A = cls
		type_A.__new__ = lambda cls : object.__new__(cls)
		obj = type_A()
		cls.__new__ = default_new
		return obj
	else:
		pass
		# cls was a predicate instead

# The contradiction
class _False(Prop):
	"""Element of Prop. The contradiction."""
	pass

class Implies(Prop, metaclass=Meta):
	"""
	Subset of Prop.
	Given p1: Prop and p2: Prop, construct the proposition (p1 -> p2): Prop"""
	antecedent = None # will be set by subclass ie the proposition
	consequent = None # will be set by subclass ie the proposition

	def __repr__(self):
		"""If an object is created, it will be a proof."""
		return f"ProofOfImplies({self.antecedent}, {self.consequent})"

class And(Prop):
	"""
	Subset of Prop.
	Given p1: Prop and p2: Prop, construct the proposition (p1 ⋀ p2): Prop"""

	left_prop = None
	right_prop = None

	def __repr__(self):
		"""If an object is created, it will be a proof."""
		return f"ProofOfAnd({self.left_prop}, {self.right_prop})"

def Conjunction(ppa, ppb):
	""" Given ppa which is a proof of A, and ppb which is
	a proof of b, construct a proof of (A and B)
	"""
	class A_and_B(And):
		left_prop = ppa.__class__
		right_prop = ppb.__class__
		proof_left = ppa
		proof_right = ppb
	
		def __new__(cls):
			return object.__new__(cls)
	return A_and_B()

class Or(Prop):
	"""
	Subset of Prop.
	Given p1: Prop and p2: Prop, construct the proposition (p1 or p2): Prop"""

	left_prop = None
	right_prop = None

	def __repr__(self):
		"""If an object is created, it will be a proof."""
		return f"ProofOfOr({self.left_prop}, {self.right_prop})"


def Disjunction(ppa, B):
	""" Given ppa which is a proof of A, and B: Prop, construct a proof of (A or B).
	"""
	class A_or_B(Or):
		left_prop = ppa.__class__
		right_prop = B

		def __new__(cls):
			return object.__new__(cls)
	return A_or_B()


def Not(A, is_true=False):
	"""Subset of Implies. Given A: Prop, produce a proposition (A -> _False).
	For ease of defining (not A).
	If A is a negation, return the antecedent.

	If is_true, then axiom (not A) exists (ie A is False). Otherwise, simply returns the contingent proposition.
	"""
	if issubclass(A, Implies):
		if A.consequent == _False:
			return A.antecedent

	class Not_A(Implies):
		antecedent = A
		consequent = _False

		if is_true:
			def __new__(cls):
				return object.__new__(cls)
	return Not_A

class Equiv(Prop):
	"""Subset of Prop. Given two Props A and B, produce a prop of the form A <-> B."""
	left_prop = None
	right_prop = None

	# def __repr__(self):
	# 	"""If an object is created, it will be a proof."""
	# 	return f"ProofOfEquiv({self.left_prop}, {self.right_prop})"

def EquivIntro(ppa_imp_b, ppb_imp_a):
	"""Given a proof of (A -> B) and one of (B -> A), produce a proof of 
	A <-> B.
	left_imp is the proposition (B -> A), while right_imp is (A -> B).
	"""
	class A_is_B(Equiv):
		left_prop = ppa_imp_b.antecedent
		right_prop = ppa_imp_b.consequent
		left_imp = ppb_imp_a.__class__
		right_imp = ppa_imp_b.__class__

		proof_left_imp = ppb_imp_a
		proof_right_imp = ppa_imp_b
	
		def __new__(cls):
			return object.__new__(cls)
	return A_is_B()


def CommuteOr(ppa_or_b):
	"""Given a proof of (A or B), construct a proof of (B or A)."""
	assert isinstance(ppa_or_b, Or)

	class B_or_A(Or):
		left_prop = ppa_or_b.right_prop
		right_prop = ppa_or_b.left_prop

		def __new__(cls):
			return object.__new__(cls)
	return B_or_A()

def CommuteAnd(ppa_and_b):
	"""Given a proof of (A and B), construct a proof of (B and A)."""
	class B_and_A(Or):
		left_prop = ppa_and_b.right_prop
		right_prop = ppa_and_b.left_prop

		proof_left = ppa_and_b.proof_right
		proof_right = ppa_and_b.proof_left

		def __new__(cls):
			return object.__new__(cls)
	return B_and_A()


def ModusPonens(ppa_imp_b, ppa):
	"""Given ppa_imp_b which is a proof of (A -> B) and ppa which is
	a proof of A, generate a proof of B
	"""
	assert (f"ProofOfImplies({ppa_imp_b.antecedent}, {ppa_imp_b.consequent})" == str(ppa_imp_b)
		and
		str(ppa_imp_b.antecedent) == str(type(ppa))
		)
	return _produce_a_proof(ppa_imp_b.consequent)

def HypSyll(ppa_imp_b, ppb_imp_c):
	"""Given ppa_imp_b, a proof of (A -> B) and ppb_imp_c, a proof of
	(B -> C), construct a proof of (A -> C).
	"""
	assert str(ppa_imp_b.consequent) == str(ppb_imp_c.antecedent)

	class A_implies_C(Implies):
		antecedent = ppa_imp_b.antecedent
		consequent = ppb_imp_c.consequent
	
		def __new__(cls):
			return object.__new__(cls)
	return A_implies_C()

def ModusTollens(ppa_imp_b, pp_not_b):
	"""Given ppa_imp_b which is a proof of (A -> B) and pp_not_b which is
	a proof of (not B), generate a proof of (not A)
	"""
	return HypSyll(ppa_imp_b, ppb_not_b)

def Contradiction(ppa, pp_not_a):
	"""Given a proof of A and a proof of (not A)(which is the same as A -> _False),
	produce a proof of _False."""
	return ModusPonens(pp_not_a, ppa)

def ImplicationToOr(ppa_imp_b):
	"""Given a proof of (A -> B), construct a proof of (not A or B)"""
	Not_A = Not(ppa_imp_b.antecedent)
	class Not_A_or_B(Or):
		left_prop = Not_A
		right_prop = ppa_imp_b.consequent

		def __new__(cls):
			return object.__new__(cls)
	return Not_A_or_B()

def OrToImplication(ppa_or_b):
	"""Given a proof of (A or B), construct a proof of (not A -> B)."""
	Not_A = Not(ppa_or_b.left_prop)
	class Not_A_implies_B(Or):
		antecedent = Not_A
		consequent = ppa_or_b.right_prop

		def __new__(cls):
			return object.__new__(cls)
	return Not_A_implies_B()



def Explosion(ppfalse, A):
	"""Principle of explosion. Given a proof of _False, return a proof of A: Prop."""
	assert str(ppfalse) == "ProofOf_False"
	return _produce_a_proof(A)



# TODO: A or F = A, A and T = A, A or T = T, A and F = F... (Maybe principle of explosion instead)



def equal_type(pp1, pp2):
	return pp1.__repr__() == pp2.__repr__()


