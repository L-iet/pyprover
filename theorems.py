from sets import N, Q, R
from predicate import (Subset, Object, ForAll, P_Implies, 
	GreaterThan, LessThan, createSet, Func, Exists, And_P
	)

x = Object('x')
y = Object('y')
z = Object('z')
ppQ_issubset_R = Subset('Q_isubset_R')(Q, R)(x=x,axiom=True)()
ppN_issubset_Q = Subset('N_issubset_Q')(N, Q)(x=y,axiom=True)()


zero = Object('0',set_=R)
eps = Object('eps',set_=R)
delta = Object('del',set_=R)
c = Object('c',set_=R)
x = Object('x',set_=R)

f = createSet('f',superclass=Func,domain=R,range_=R)

e_g_0 = GreaterThan('e>0')(y=zero)
d_g_0 = GreaterThan('d>0')(y=zero)

dis_xc_imp_dis_fxfc = P_Implies('Imp', antecedent=LessThan('Lt')(x=(x-c),y=delta),
	consequent=LessThan('Lt2')(x=(f(x) - f(c)), y=eps))

existsDelta = Exists('existsdel', predicate=And_P('d>0andDis',
									left_pred=GreaterThan('delGt0')(x=delta,y=zero),
									right_pred=dis_xc_imp_dis_fxfc
									)
)(x=delta)

eg0ImpExists = P_Implies('eg0ImpExists', antecedent=e_g_0, consequent=existsDelta)
forAllE = ForAll('ForAllE',predicate=eg0ImpExists)(x=eps)
forAllx = ForAll('ForAllX',predicate=forAllE)

continuity = forAllx(x=x)

print(continuity)


