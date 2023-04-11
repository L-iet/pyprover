from predicate import SetMetaMeta
from predicate import Object
from itertools import count
from predicate import createSet, Func
import fractions
from predicate import Membership, MembershipProof
from predicate import Predicate


def _check_valid(name,symb):
	s = name.find(symb)
	if s != -1:
		rest = name[:s] + name[s+1:]
	else:
		rest = name
	return rest.isdigit()

class N(metaclass=SetMetaMeta):
	_items = set()
	def __new__(cls, name='0'):
		assert isinstance(name, int) or name.isdigit(), "Can only create natural number from integer"
		obj = Object(str(name))
		return obj

	@classmethod
	def __contains__(cls, item):
		return ((isinstance(item, Object) and item.name.isdigit())
			or item.set_ == cls
			or item in cls._items
			)

	@classmethod
	def __iter__(cls):
		for i in count(1):
			obj = Object(str(i))
			yield obj

	@classmethod
	def add(cls, item):
		assert isinstance(item, Object), "Item not an Object"
		cls._items.add(item)

	@classmethod
	def __add__(cls, obj1, obj2):
		return Q.__add__(obj1, obj2)

	@classmethod
	def __sub__(cls, obj1, obj2):
		return Q.__sub__(obj1, obj2)

class Q(metaclass=SetMetaMeta):
	_items = set()
	def __new__(cls, name='0'):
		assert _check_valid(name, '/'), 'name must contain only decimal digits and a single slash character'
		
		num, den = name.split('/')
		obj = Object(name,set_=cls)
		obj.numerator = num
		obj.denominator = den
		return obj

	@classmethod
	def __contains__(cls, item):
		return ((isinstance(item, Object) and _check_valid(item.name, '/'))
			or item.set_ == cls
			or item in cls._items
			or item in N)

	@classmethod
	def __iter__(cls):
		raise TypeError("Iteration not implemented for the set of Rationals.")

	@classmethod
	def add(cls, item):
		"""Add/assert that an element is in Q"""
		assert isinstance(item, Object), "Item not an Object"
		cls._items.add(item)

	@classmethod
	def __add__(cls, obj1, obj2):
		"""Implementation for +"""
		try:
			num1 = fractions.Fraction(obj1.name)
			num2 = fractions.Fraction(obj2.name)
		except ValueError:
			return Object(f"{obj1.name} + {obj2.name}",set_=Q)
		tup = (num1 + num2).as_integer_ratio()
		tup = map(str, tup)
		return Object('/'.join(
						tup	
			), set_=cls)

	@classmethod
	def __sub__(cls, obj1, obj2):
		"""Implementation for +"""
		try:
			num1 = fractions.Fraction(obj1.name)
			num2 = fractions.Fraction(obj2.name)
		except ValueError:
			return Object(f"{obj1.name} - {obj2.name}",set_=Q)
		tup = (num1 - num2).as_integer_ratio()
		tup = map(str, tup)
		return Object('/'.join(
						tup	
			), set_=cls)

	@classmethod
	def __lt__(cls, obj1, obj2):
		m = Predicate('LessThan',args={'obj1': Object, 'obj2': Object}, prop_kwargs={
				'left': obj1,
				'right': obj2
			})(obj1=obj1, obj2=obj2)
		return m

	def __gt__(cls, obj1, obj2):
		m = Predicate('GreaterThan',args={'obj1': Object, 'obj2': Object}, prop_kwargs={
				'left': obj1,
				'right': obj2
			})(obj1=obj1, obj2=obj2)
		return m

class R(metaclass=SetMetaMeta):	
	_items = set()
	def __new__(cls, name='0'):
		assert _check_valid(name, '.'), 'name must contain only decimal digits and a single decimal point'
		
		obj = Object(name)
		return obj

	@classmethod
	def __contains__(cls, item):
		return ((isinstance(item, Object) and _check_valid(item.name, '.'))
			or item.set_ == cls
			or item in cls._items
			or item in Q)

	@classmethod
	def __iter__(cls):
		raise TypeError("The set of Reals is not countable.")

	@classmethod
	def add(cls, item):
		assert isinstance(item, Object), "Item not an Object"
		cls._items.add(item)

	@classmethod
	def __add__(cls, obj1, obj2):
		return Q.__add__(obj1, obj2)

	@classmethod
	def __sub__(cls, obj1, obj2):
		return Q.__sub__(obj1, obj2)



if __name__ == '__main__':
	def f1(a):
		return a + Object('1/2',set_=Q)

	n1 = Object('1.56')
	n2 = Object('3/4',set_=Q)
	n3 = Object('1/2',set_=Q)

	f = createSet('f', Func, domain=Q, range_=Q, definition=f1)

	y = f(n3)
	p1 = Membership("_")(x=y,set_=Q)
	print(MembershipProof(p1))

