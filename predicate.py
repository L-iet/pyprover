from propositional import Prop, default_new, _produce_a_proof, Implies, ModusPonens
from functools import partial
from typing import Union
import logging
import itertools
import fractions

debug = logging.debug
info = logging.info
warn = logging.warning
err = logging.error
crit = logging.critical

logging.basicConfig(level=logging.WARNING)
# Predicate takes an object and returns a Prop (a class)
# I believe we will not need to create a Python object of type Set,
# since we use predicates which give Props, and the obj attribute
# is just a value.

def remove_useless_keys(kwargs, required_kwargs):
	kwargs_ = {}
	for key in kwargs:
		if key in required_kwargs:
			kwargs_[key] = kwargs[key]
	return kwargs_


class Object:
	"""Represents an object in our universe."""
	_num_objects = 0
	def __init__(self, name='', set_=None):
		assert isinstance(name, str), "name must be str"
		if set_ is not None:
			assert type(set_) in [SetMeta, SetMetaMeta, ProdMeta]
		self.name = name
		Object._num_objects += 1
		self._id = Object._num_objects
		self.set_ = set_
	def __repr__(self):
		if self.name:
			return self.name
		else:
			return f"Obj(e_{self._id})"

	def __hash__(self):
		return hash(self._id)

	def __add__(self, other):
		if not self.set_:
			raise TypeError("No implementation for '+' known.")
		else:
			return self.set_.__add__(self, other)

	def __sub__(self, other):
		if not self.set_:
			raise TypeError("No implementation for '-' known.")
		else:
			return self.set_.__sub__(self, other)


class SetMetaMeta(type):
	def __repr__(cls):
		return cls.__name__

	def __contains__(cls, item):
		return cls.__contains__(item)

	def __iter__(cls):
		return cls.__iter__()


class SetMeta(SetMetaMeta):
	def add(cls, item):
		cls._items.add(item)

	def __contains__(cls, item):
		return item in cls._items

	def __iter__(cls):
		return (x for x in cls._items)


class ProdMeta(type):
	def __repr__(cls):
		st = ''
		for s in cls.sets:
			st += str(s) + '×'
		st = st[:-1]

		return f"{self.name}:{st}"

	def __contains__(cls, item):
		assert isinstance(item, tuple), "Product set contains only Python tuples."
		
		for i, obj in enumerate(items):
			if not obj in cls.sets[i]:
				return False
		return True

	def __iter__(cls):
		act_sets = [s._items for s in cls.sets]
		return itertools.product(*act_sets)

class FuncMeta(type):
	def __repr__(cls):
		return f"{cls.__name__}:{cls.domain}->{cls.range_}"

reprs = {
	
}

class Meta(type):
	def __repr__(cls):
		for key in reprs:
			if key in cls.__name__.lower():
				return reprs[key](cls)
		return cls.__name__

class Set(metaclass=SetMeta):
	def __new__(cls, name=''):
		obj = Object(name)
		cls._items.add(obj)
		return obj


class Prod(metaclass=ProdMeta):
	"""Implements Cartesian Product of sets.
	Cartesian product is associative but not commutative.
	Note that _items is always empty for this set, iterate over it instead.
	"""
	sets = [] # list of Set subclasses.
	def __new__(self):
		raise TypeError("Cannot create/assert new element of Product set.")



class Func(metaclass=FuncMeta):
	"""f(a) = b means that f._dict[a] = b.
	Represents an onto function.
	"""
	dict_ = {} # should be reset for each new subclass
	domain = None # subclass of Set. This is the set of ALL POSSIBLE inputs.
	range_ = None # Set of ALL POSSIBLE outputs. So the function is onto.
	definition = None


	def __new__(cls, obj):
		if not cls.definition:
			assert obj in cls.domain, f"Input {obj} is not an element of the domain '{cls.domain}'"

			if obj in cls.dict_:
				return cls.dict_[obj]

			image = Object(f"{cls.__name__}({obj})",set_=cls.range_)
			cls.dict_[obj] = image
			if hasattr(cls.range_, 'add'):
				cls.range_.add(image)
			return image
		else:
			return cls.definition(obj)


def createSet(name, superclass=Set,**kwargs):
	if superclass not in [Prod, Func]:
		kwargs.update({'_items': set()})
	cls = type(name, (superclass,), kwargs)
	if superclass == Func:
		cls.dict_ = {}
	return cls


class Predicate(metaclass=Meta):
	"""
	Returns a predicate. A predicate is a function that can take an object
	and return a proposition.
	Parameters:
	name: str
		Name of the Prop class to be created
	args:
		Dict of argument the predicate takes, and their types
	_completed_args:
		any already completed arguments and their values
	kwargs:
		other kwargs

	Return value: A predicate which is a Python function.
	When calling the function, can set the axiom keyword-only
	argument to true.
	"""
	def __init__(self, name: str, *, args: list|dict = None,
		_completed_args: dict=None,
		_superclass = Prop,
		prop_kwargs = {},
		**kwargs):
		self.name = name
		self._completed_args = _completed_args or {}
		self._superclass = _superclass
		self.prop_kwargs = prop_kwargs

		# if args is a list, every argument is an Object
		# else, can specify the type of arguments in a dictionary
		# eg args = {'a': Object, 'b': Set}
		if type(args) is dict:
			self.args = args
		else:
			self.args = {a: Object for a in self.args}
		self.arity = len(args)

	def __repr__(self):
		if not self._completed_args:
			return f"{self.name}(_)"

		s = ""
		for arg, val in self._completed_args.items():
			s += f"{arg}={val},"
		return f"{self.name}({s})"
	def _check_call_arguments(self,kwargs):
		if isinstance(self.args, dict):
			for arg in kwargs:
				if kwargs[arg] is not None:
					if self.args[arg] is Object:
						assert type(kwargs[arg]) == self.args[arg], f"Argument {arg} must be of type {self.args[arg]}."
					else:
						assert issubclass(kwargs[arg], self.args[arg]), f"Argument {arg} must be a {self.args[arg]}"
					

	def __call__(self, axiom=False,
		predicate=None,
		**kwargs):
		"""Returns a Prop.
		Parameters:
		kwargs: arguments to (partially) complete the predicate
		axiom: bool
			Whether to make the proposition true once created
		_class_name: str
			The name of the class to create.
		_superclass: type
			The Proposition class to inherit from
		prop_kwargs: Dict
			The attributes to set in the proposition class.
		"""
		kwargs = remove_useless_keys(kwargs, self.args)

		info("A "+str(self))
		info("B "+str(self.args))
		info("C "+str(self._completed_args))
		info("D "+str(kwargs))
		if self.arity == 0:
			cls = type(str(self), (self._superclass,), self.prop_kwargs)
			if axiom:
				cls.__new__ = lambda _cls: object.__new__(_cls)
			return cls # object of Prop
		else:
			# if you pass an already completed argument, remove it
			keys_to_pop = set()
			for key in kwargs:
				if key in self._completed_args or not(key in self.args):
					keys_to_pop.add(key)
			for k in keys_to_pop:
				kwargs.pop(k)


			if all((kwargs.get(k) is None) for k in kwargs):
				return self


			# get the 'first' key in kwargs, remove the key/value
			key = None
			for key2 in kwargs:
				if kwargs[key2] is not None:
					key = key2
					break
			val = kwargs.pop(key)


			if val is None:
				return self

			# add it to the completed args
			new_completed_args = self._completed_args.copy()
			new_completed_args[key] = val

			# remove it from the args for the new predicate
			new_args = self.args.copy()
			new_args.pop(key)

			# create a new prdicate with the same name, new completed args
			# and new args, and pass the rest of the arguments to the call

			info("E "+str(self))
			info("F "+str(self.args))
			info("G "+str(self._completed_args))
			info("H "+str(kwargs))
			next_pred = self.__class__(name=self.name,
				args=new_args,
				predicate=predicate,
				prop_kwargs=self.prop_kwargs, # shouldn't change, right?
				_completed_args=new_completed_args)
			# If the new pred does not take any more arguments, it must be a prop
			# or if there are still kwargs, we want to advance in the partial application
			if len(new_args) == 0 or len(kwargs) > 0:
				return next_pred(**kwargs,
				axiom=axiom,
				)
			else:
				return next_pred

class Membership(Predicate):
	"""Defines the predicate _ ∈ _, where the left argument is 'x' and
	right argument is the 'set_'."""
	def __init__(self, name, args=None, _completed_args=None, **kwargs):
		if args is None:
			args = {'x': Object, 'set_': Set}

		super().__init__(name, args=args, _completed_args=_completed_args)
	
	def __repr__(self):
		x = self._completed_args.get('x') or '_'
		set_ = self._completed_args.get('set_') or '_'
		return f"{x} ∈ {set_}"

	def __call__(self, x=None, set_=None, *, axiom=False,
		_class_name=None,**kwargs):
		if self.arity == 0:
			self.prop_kwargs = {'x': self._completed_args['x'],
			'set_': self._completed_args['set_']}

		return super().__call__(axiom=axiom, _class_name=_class_name, 
			x=x, set_=set_
			)

	@classmethod
	def natural_lang(cls):
		return f"{cls.obj} is in Set {cls.set_}"



class Quantified(Predicate):
	def __init__(self, name, predicate=None, quantifier=None,**kwargs):
		args = kwargs.get('args', {})
		if kwargs.get('args') is None:
			args = {'x': Object}

			if isinstance(predicate, Predicate):
				args.update(predicate.args)

		self.quantifier = quantifier

		self.predicate = predicate
		super().__init__(name, args=args, prop_kwargs={'quantifier': quantifier},
			_completed_args=kwargs.get('_completed_args'))

	def __repr__(self):
		symb = {"E": "∃", "A": "∀"}
		if 'x' in self._completed_args:
			return f"{symb[self.quantifier]}{self._completed_args['x']}({self.predicate})"
		else:
			return f"{symb[self.quantifier]}_({self.predicate})"

	def __call__(self, *, axiom=False,
		_class_name=None,
		x=None, **kwargs):

		kwargs = remove_useless_keys(kwargs, self.args)


		# If axiom is true for the "For all" prop, then its inner predicate will also be an axiom.
		# inner predicate may still be false even though entire "exists" Prop is an axiom.
		ax = False
		if self.quantifier == 'A':
			ax = axiom
		if isinstance(self.predicate, Predicate):
			self.predicate = self.predicate(axiom=ax,
				x=x,
				**kwargs)
		if x is not None:
			self._completed_args['x'] = x

		if not(isinstance(self.predicate, Predicate)):
			# has been completed
			self.prop_kwargs['inner_prop'] = self.predicate
			cls = type(self.__repr__(), (self._superclass,), self.prop_kwargs)
			if axiom:
				cls.__new__ = lambda _cls: object.__new__(_cls)
			return cls # subclass of Prop
		else:
			# still a predicate
			self.arity -= (len(kwargs) + (x is not None))
			return self

class Exists(Quantified):
	"""
	Defines the Predicate ∃_, Pred(_).
	Propositions returned from __call__ will have an inner part"""
	def __init__(self, name, predicate=None, **kwargs):
		super().__init__(name, args=kwargs.get('args'), predicate=predicate,
			quantifier='E', **kwargs)



class ForAll(Quantified):
	"""
	Defines the Predicate ∀_, Pred(_, ~).
	Propositions returned from __call__ will have an inner part"""
	def __init__(self, name, predicate=None, **kwargs):
		super().__init__(name, predicate=predicate,
			quantifier='A', **kwargs)


class P_Implies(Predicate):
	def __init__(self, name, antecedent=None, consequent=None, **kwargs):
		args = kwargs.get('args', {})
		if kwargs.get('args') is None:
			if isinstance(antecedent, Predicate):
				args.update(antecedent.args)
			if isinstance(consequent, Predicate):
				args.update(consequent.args)
		self.antecedent = antecedent # Predicate
		self.consequent = consequent
		super().__init__(name, args=args, _superclass = Implies,
			_completed_args=kwargs.get('_completed_args'))

	def __repr__(self):
		return f"[{self.antecedent}=>{self.consequent}]"

	def __call__(self, *, axiom=False,
		_class_name=None, **kwargs
		):
		# remove useless keys/values
		kwargs = remove_useless_keys(kwargs, self.args)

		if isinstance(self.antecedent, Predicate):
			self.antecedent = self.antecedent(axiom=False,**kwargs)
		if isinstance(self.consequent, Predicate):
			self.consequent = self.consequent(axiom=False, **kwargs)

		if (not(isinstance(self.antecedent, Predicate))
			and not(isinstance(self.consequent, Predicate))
		):
			cls = type(str(self), (Implies,),
						{'antecedent': self.antecedent, 'consequent': self.consequent}
			)
			if axiom:
				cls.__new__ = lambda _cls: object.__new__(_cls)
			return cls # subclass of Prop
		else:
			# at least one still a predicate
			self.arity -= len(kwargs)
			return self


class And_P(Predicate):
	def __init__(self, name, left_pred=None, right_pred=None, **kwargs):
		args = kwargs.get('args', {})
		if kwargs.get('args') is None:
			if isinstance(left_pred, Predicate):
				args.update(left_pred.args)
			if isinstance(right_pred, Predicate):
				args.update(right_pred.args)
		self.left_pred = left_pred # Predicate
		self.right_pred = right_pred
		super().__init__(name, args=args, _superclass = Implies,
			_completed_args=kwargs.get('_completed_args'))

	def __repr__(self):
		return f"{self.left_pred}∧{self.right_pred}"

	def __call__(self, *, axiom=False,
		_class_name=None, **kwargs
		):
		# remove useless keys/values
		kwargs = remove_useless_keys(kwargs, self.args)

		if isinstance(self.left_pred, Predicate):
			self.left_pred = self.left_pred(axiom=False,**kwargs)
		if isinstance(self.right_pred, Predicate):
			self.right_pred = self.right_pred(axiom=False, **kwargs)

		if (not(isinstance(self.left_pred, Predicate))
			and not(isinstance(self.right_pred, Predicate))
		):
			cls = type(str(self), (Implies,),
						{'left_prop': self.left_pred, 'right_prop': self.right_pred}
			)
			if axiom:
				cls.__new__ = lambda _cls: object.__new__(_cls)
			return cls # subclass of Prop
		else:
			# at least one still a predicate
			self.arity -= len(kwargs)
			return self

class Subset(ForAll):

	"""Defines the Predicate A ⊆ B where A and B are placeholders."""
	def __init__(self, name, args=None, _completed_args=None, **kwargs):
		if args is None:
			args = {'x': Object, 'A': Set, 'B': Set}

		super().__init__(name, args=args,
			predicate=P_Implies("xInAImpxInB",
						antecedent=Membership("xInA"),
						consequent=Membership("xInB")
					),
			_completed_args=_completed_args
		)
	
	def __repr__(self):
		if self.arity != 0:
			A = self._completed_args.get('A') or '_'
			B = self._completed_args.get('B') or '_'
			return f"{A} ⊆ {B}"
		else:
			return super().__repr__()

	def __call__(self, A=None, B=None, *, axiom=False,
		_class_name=None,**kwargs):
		kwargs = remove_useless_keys(kwargs, self.args)

		if kwargs.get('x') is not None:
			assert self.arity == 1, "Subset predicate cannot take x as argument unless it is the last remaining argument."
			self.arity = 0
			return super().__call__(axiom=axiom, _class_name=_class_name, **kwargs)
		else:

			if A is not None:
				self.predicate.antecedent = self.predicate.antecedent(set_=A)
				self._completed_args['A'] = A
				self.arity -= 1
			if B is not None:
				self.predicate.consequent = self.predicate.consequent(set_=B)
				self._completed_args['B'] = B
				self.arity -= 1
			return self


		if self.arity == 0:
			self.prop_kwargs = {'A': self._completed_args['A'],
			'B': self._completed_args['B']}
			return super().__call__(axiom=axiom, _class_name=_class_name, **kwargs) # not sure if needed

	def as_forall(self):
		"""Returns the predicate as a ForAll object with the x argument filled in."""
		x = Object('x')
		return ForAll(self.name, 
			predicate=self.predicate
			)(x=x)

class OrderingOfReals(Predicate):
	"""Defines one of the predicates x < y, x > y, x=y etc where x and y are
	placeholders and must be Objects."""
	def __init__(self, name, symbol=None,args=None, _completed_args=None, **kwargs):
		self.symbol = symbol
		if args is None:
			args = {'x': Object, 'y': Object}

		super().__init__(name, args=args, _completed_args=_completed_args)
	
	def __repr__(self):
		symbs = {'lt': '<', 'le': '≤', 'gt': '>', 'ge':'≥', 'eq': '='}
		x = self._completed_args.get('x') or '_'
		y = self._completed_args.get('y') or '_'
		return f"{x} {symbs[self.symbol]} {y}"

	def __call__(self, x=None, y=None, *, axiom=False,
		_class_name=None,**kwargs):
		if self.arity == 0:
			self.prop_kwargs = {'x': self._completed_args['x'],
			'y': self._completed_args['y'],
			'order_symbol': self.symbol
		}

		return super().__call__(axiom=axiom, _class_name=_class_name, 
			x=x, y=y
			)



class LessThan(OrderingOfReals):
	"""Defines the predicate x < y, x and y are placeholders and must be Objects."""
	def __init__(self, name, args=None, _completed_args=None, **kwargs):
		super().__init__(name, args=args, symbol='lt', _completed_args=_completed_args)

class GreaterThan(OrderingOfReals):
	"""Defines the predicate x < y, x and y are placeholders and must be Objects."""
	def __init__(self, name, args=None, _completed_args=None, **kwargs):
		super().__init__(name, args=args, symbol='gt', _completed_args=_completed_args)
class LessOrEq(OrderingOfReals):
	def __init__(self, name, args=None, _completed_args=None, **kwargs):
		super().__init__(name, args=args, symbol='le', _completed_args=_completed_args)
class GreaterOrEq(OrderingOfReals):
	def __init__(self, name, args=None, _completed_args=None, **kwargs):
		super().__init__(name, args=args, symbol='ge', _completed_args=_completed_args)
class Equal(OrderingOfReals):
	def __init__(self, name, args=None, _completed_args=None, **kwargs):
		super().__init__(name, args=args, symbol='eq', _completed_args=_completed_args)

def MembershipProof(xInA):
	"""Given a proposition (x in A), check that x is in A and if so, produce a proof, 
	else, throw an error.
	I should probably call this style of proof 'Observational proof' or 'By construction'.
	"""
	assert xInA.x in xInA.set_, f"Element {xInA.x} not found in Set '{xInA.set_}'."
	return _produce_a_proof(xInA)

def OrderingProof(x_lt_y):
	"""
	Given a proposition involving order such as (x < y) or (x > y), check that the
	equality/inequality is correct and produce a proof in that case.
	"""
	x = x_lt_y.obj1
	y = x_lt_y.obj2
	try:
		x_ = fractions.Fraction(x.name)
		y_ = fractions.Fraction(y.name)
	except ValueError:
		raise Exception(f'Either {x} or {y} is not a constant.')

	check_relation = lambda symb: (
		(symb == 'lt' and x_ < y_) or
		(symb == 'le' and x_ <= y) or
		(symb == 'gt' and x_ > y_) or
		(symb == 'ge' and x_ >= y) or
		(symb == 'eq' and x_ == y_)
	)
	if check_relation(x_lt_y.order_symbol):
		return _produce_a_proof(x_lt_y)
	else:
		raise Exception(f"Proposition {x_lt_y} cannot be proven True.")


####################
# TODO
def ForAllModusPonens(ppforallx_Ax_imp_Bx, ppforall_x_Ax):
	"""Given a proof of ∀x(Ax -> Bx) and a proof of ∀x(Ax) or ∃x(Ax),
	produce a proof of ∀x(Bx) or ∃x(Bx)."""
	A_imp_B = ppforallx_Ax_imp_Bx.inner_pred
	assert ppforallx_Ax_imp_Bx.quantifier == "A", "First argument must be a proof of the form ∀x(Ax -> Bx)"
	A = ppforall_x_Ax.inner_pred
	x = Object('x') # creating an 'arbitrary' object

	# checking that modus ponens works with the Props from the predicates
	Bx = ModusPonens(A_imp_B(x,axiom=True)(),
		A(x,axiom=True)())

	# getting the consequent
	B = A_imp_B.consequent

	# asserting that the consequent matches the result from Modus Ponens
	assert str(Bx) == str(B(x,axiom=True)())

	# return the consequent with the appropriate quantifier
	if ppforall_x_Ax.quantifier == "A":
		return ForAll(Bx.__class__, B)(x,axiom=True)()
	elif ppforall_x_Ax.quantifier == "E":
		return Exists(Bx.__class__, B)(x, axiom=True)()
	else:
		raise Exception("Did not recieve a quantified second argument.")




def UniversalResolve(ppforall_x_Ax, y: Object):
	"""Given a proof of the proposition ( ∀x, A(x) ) and
	a specific object y, produce a proof of the prop A(y).
	"""
	return _produce_a_proof(ppforall_x_Ax.predicate(y))

def ExistentialResolve(ppexists_x_Ax):
	"""Given a proof of (∃x, A(x)), return the object (e_n) and a proof
	of A(e_n).
	"""
	y = Object()
	return y, _produce_a_proof(ppexists_x_Ax.predicate(y))

def ExistentialProof(ppAy):
	"""Given a proof of A(y), produce a proof of (∃x, A(x))"""
	class ExistsxAx(Exists):
		obj = Object("x")
		predicate = ppAy.predicate
		prop_about_obj = predicate(_, obj)
		def __new__(cls):
			return object.__new__(cls)
	return ExistsxAx()

##############################

###

if __name__ == '__main__':
	Reals = createSet("Reals", Set)

	Naturals = createSet("Naturals", Set)

	NxR = createSet("NxR", Prod, sets=[Naturals, Reals])


	x = Object('x')
	y = Object('y')
	z = Object('z')
	a = Object('a')
	b = Object('b')
	c = Object('c')


	Naturals.add(x)
	Naturals.add(y)
	Naturals.add(a)
	Reals.add(z)
	Reals.add(b)
	Reals.add(c)
	print(Reals._items)


	f = createSet('f', Func, domain=Naturals, range_=Reals)


	xInNat = Membership('xInNat')(x=y,set_=Naturals)
	print(MembershipProof(xInNat))


