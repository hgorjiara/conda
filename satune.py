from __future__ import absolute_import, division, print_function, unicode_literals

import pycsolver as ps
from enum import Enum
from ctypes import *
import sys

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

class Satune(object):
	
	def __init__(self):
		self.csolverlb = ps.loadCSolver();
        	self.csolver = self.csolverlb.createCCSolver()
		self.var_constr_map = {}
		self.orgelements = []
		self.orgboolVar = []
		#self.assignVars = []
		self.constraintmap = {}
		self.addToConstraintMap(self.getBooleanTrue(),  (Satune.getConstraint, (True,)) )
		self.addToConstraintMap(self.getBooleanFalse(), (Satune.getConstraint, (False,)) )
		self.constraints = []
		eprint("Initial constraintmap: " + str(self.constraintmap))
	
	def addToConstraintMap(self, key, value):
		if self.constrToString(key) not in self.constraintmap.keys():
			eprint("constraintmap1[" + str(self.constrToString(key)) + " ] = " + str(value) )
		else:
			eprint("constraintmap2[" + str(self.constrToString(key)) + " ] = " + str(self.constraintmap[self.constrToString(key)]) )
			eprint("value= " + str(value))
		
		def valueEqual(v1, v2):
			assert(type(v1) is tuple and type(v2) is tuple)
			if len(v1) != len(v2) and len(v1) != 2:
				return False
			if v1[0] != v2[0]:
				return False
			if len(v1[1]) != len(v2[1]):
				return False
			return True

		#assert(self.constrToString(key) not in self.constraintmap.keys() or (self.constrToString(key) in self.constraintmap.keys() and key != self.getBooleanTrue() and key != self.getBooleanFalse() and (valueEqual(value, self.constraintmap[self.constrToString(key)])) ) )
		if self.constrToString(key) not in self.constraintmap.keys():
			self.constraintmap[self.constrToString(key)] = value

	#def addAssignVars(self, var):
	#	assert(var not in self.assignVars)
	#	self.assignVars.append(var)

	def destroy(self):
		self.csolverlb.deleteCCSolver(self.csolver)
	
	def variableExist(self, var):
		return var in self.var_constr_map.keys()
	
	def cloneBooleanVar(self, myclone, boolean):
		func, params = self.constraintmap[ self.constrToString(boolean) ]
		eprint("cloneBooleanVar1: " + str(func) + " ( " + str(params) + " )")
		if func in (Satune.createNewBooleanVar,):
			func = Satune.getConstraint
		if func in (Satune.getConstraint, Satune.getBooleanFalse, Satune.getBooleanTrue):
			return func(myclone, *params)	
		newparam = ()
		def cloneparameter(p):
			eprint("cloneparameter: " + str(p))
			tx = type(p)
                	if tx is list:
				return tx(map(cloneparameter, p))
			return self.cloneBooleanVar(myclone, p)

		for param in params:
			eprint("param = " + str(param) )
			if "b" in str(param):
				newparam += (cloneparameter(param),)
		eprint("cloneBooleanVariable: " + str(func) + "( " + str(params) + " ) OR ( " + str(newparam) + " )")
		assert ( len(newparam) == 0 or len(newparam) == len(params) )	
		if len(newparam) == 0:
			return func(myclone, *params, conv=True)
		else:
			return func(myclone, *newparam, conv=False)

	def clone(self):
		myclone = Satune()
		for element in self.orgelements:
			myclone.createNewElement(element)
		for boolVar in self.orgboolVar:
			myclone.createNewBooleanVar(boolVar)
		eprint("clonefunction constraints: ", str(self.constraints))
		for var in self.var_constr_map.keys():
			if not myclone.variableExist(var):
				b = self.cloneBooleanVar(myclone, self.getConstraint(var))
				myclone.mapVarToConstraint(var, b)

		for constraint in self.constraints:
			eprint("New top level constraint: "+ str(constraint))
			b = self.cloneBooleanVar(myclone, constraint)
			eprint("adding constraint " + str(b) + " to myclone!")
			myclone.addConstraint(b)
		
		if 232 in self.var_constr_map.keys():
			myclone.getConstraint(232)
			eprint("232 exists in the clone")
		return myclone

	def getConstraint(self, var):
		if type(var) is bool:
			return self.getBooleanTrue() if var else self.getBooleanFalse()
		eprint("getConstraint: var=" + str(var))
		key=abs(var)
		assert(key in self.var_constr_map.keys())
		if var >= 0:
			return self.var_constr_map[key]
		else:
			return self.Not(self.var_constr_map[key], False)
	
	def mapVarToConstraint(self, var, constraint):
		key=abs(var)
		eprint("mapVarToConstraint: var=" + str(var) + " key=" + str(key)+" constraint=" + str(constraint))
		assert(key not in self.var_constr_map.keys())
		self.var_constr_map[key] = constraint
	
	def applyLogicalOperation(self, op, array):
		#eprint("Trace: applyLogicalOperation " + str(op) +" on " + str(array))
        	constrs = array
        	b = (c_void_p*len(constrs))(*constrs)
        	return self.csolverlb.applyLogicalOperation(self.csolver, op, b, c_uint(len(constrs)))

	def constrToString(self, b):
		tx = type(b)
        	if tx in (tuple, list):
            		return tx(map(self.constrToString, b))
		if "b" in str(b):
			return b
		return "b"+str(b)

	def Not(self, x, conv=True):
		eprint("Trace: Not => "+ str(x))
		constr=[self.getConstraint(x)] if conv else [x]
		b = self.applyLogicalOperation(ps.LogicOps.SATC_NOT, constr)
		if conv:
			self.addToConstraintMap(b, (Satune.Not, (x,)) )
		else:
			self.addToConstraintMap(b, (Satune.Not, (self.constrToString(x),)) )
		return b
	
	def And(self, f, g, conv=True):
		eprint("Trace: And => "+ str((f) + " , " + str(g)))
		constr=[self.getConstraint(f), self.getConstraint(g)] if conv else [f, g]
		b= self.applyLogicalOperation(ps.LogicOps.SATC_AND, constr)
		if conv:
                        self.addToConstraintMap(b, (Satune.And, (f,g)) )
                else:
                        self.addToConstraintMap(b, (Satune.And, (self.constrToString(f), self.constrToString(g))) )
                return b
	
	def Or(self , f, g, conv=True):
		eprint("Trace: Or => "+ str(f) + " , " + str(g))
		constr=[self.getConstraint(f), self.getConstraint(g)] if conv else [f,g]
		b = self.applyLogicalOperation(ps.LogicOps.SATC_OR, constr)
		if conv:
                        self.addToConstraintMap(b, (Satune.Or, (f,g)) )
                else:
                        self.addToConstraintMap(b, (Satune.Or, (self.constrToString(f), self.constrToString(g))) )
		return b

	def Xor(self , f, g, conv=True):
		eprint("Trace: Xor => "+ str((f) + " , " + str(g)))
		constr=[self.getConstraint(f), self.getConstraint(g)] if conv else [f, g]
		b= self.applyLogicalOperation(ps.LogicOps.SATC_XOR, constr)
		if conv:
                        self.addToConstraintMap(b, (Satune.Xor, (f,g)) )
                else:
                        self.addToConstraintMap(b, (Satune.Xor, (self.constrToString(f), self.constrToString(g))) )
 		return b
		
	def ITE(self , c, t, f, conv =True):
		eprint("Trace: ITE => "+ str(c) + " , " + str(t) + " , "+ str(f))
		constr=[self.getConstraint(c), self.getConstraint(t)] if conv else [c, t]
		CandT= self.applyLogicalOperation(ps.LogicOps.SATC_AND, constr)
		constr=[ self.Not(c) , self.getConstraint(f)] if conv else [ Not(c,conv), f]
		NotCandF= self.applyLogicalOperation(ps.LogicOps.SATC_AND, constr)
		constr=[CandT, NotCandF]
		b = self.applyLogicalOperation(ps.LogicOps.SATC_OR, constr)
		if conv:
                        self.addToConstraintMap(b, (Satune.ITE, (c,t,f)) )
                else:
                        self.addToConstraintMap(b, (Satune.ITE, (self.constrToString(c), self.constrToString(t), self.constrToString(f))) )
	
	def All(self, array, conv=True):
		eprint("Trace: All => "+ str(array))
		constr=[self.getConstraint(x) for x in array] if conv else array
		b= self.applyLogicalOperation(ps.LogicOps.SATC_AND, constr)
		if conv:
                        self.addToConstraintMap(b, (Satune.All, (array,)) )
                else:
			
                        self.addToConstraintMap(b, (Satune.All, (self.constrToString(array),)) )
		return b

	def Any(self, array, conv=True):
		eprint("Trace: Any => "+ str(array))
		constr=[self.getConstraint(x) for x in array] if conv else array
		b = self.applyLogicalOperation(ps.LogicOps.SATC_OR, constr)
		if conv:
                        self.addToConstraintMap(b, (Satune.Any, (array,)) )
                else:
                        self.addToConstraintMap(b, (Satune.Any, (self.constrToString(array),)) )
                return b

	def ExactlyOne(self, array, conv=True):
		eprint("Trace: ExactlyOne => "+ str(array))
		constrs=[self.getConstraint(x) for x in array] if conv else array
		b = (c_void_p*len(constrs))(*constrs)
		bb = self.csolverlb.applyExactlyOneConstraint(self.csolver, b, c_uint(len(constrs))) 
		if conv:
                        self.addToConstraintMap(bb, (Satune.ExactlyOne, (array,)) )
                else:

                        self.addToConstraintMap(bb, (Satune.ExactlyOne, (self.constrToString(array),)) )
                return bb
	
	def AtMostOne(self, array, conv=True):
		eprint("Trace: AtMostOne => "+ str(array))
		constrs=[self.getConstraint(x) for x in array] if conv else array
		b = (c_void_p*len(constrs))(*constrs)
		bb= self.csolverlb.applyExactlyOneConstraint(self.csolver, b, c_uint(len(constrs)))
		if conv:
                        self.addToConstraintMap(bb, (Satune.AtMostOne, (array,)) )
                else:
                        self.addToConstraintMap(bb, (Satune.AtMostOne, (self.constrToString(array),)) )
                return bb
	
	def createNewElement(self, array):
		self.orgelements.append(array)
		eprint("Trace: createNewElement => "+ str(array))
        	set1 = (c_long* len(array))(*array)
        	s1 = self.csolverlb.createSet(self.csolver, c_uint(1), set1, c_uint(len(array)))
        	e1 = self.csolverlb.getElementVar(self.csolver,s1)
        	self.csolverlb.mustHaveValue(self.csolver, e1)
		for n in array:
			assert(n>0)
			e2 = self.csolverlb.getElementConst(self.csolver, c_uint(1), n)
    			equals = self.csolverlb.createPredicateOperator(self.csolver, c_uint(ps.CompOp.SATC_EQUALS))
    			inp = [e1,e2]
    			inputs = (c_void_p*len(inp))(*inp)
    			b= self.csolverlb.applyPredicate(self.csolver,equals, inputs, c_uint(2))
			self.mapVarToConstraint(n, b)
			self.addToConstraintMap(b, (Satune.getConstraint, (n,)) )
	
	def createNewBooleanVar(self, m):
		eprint("Trace: createNewBooleanVar => " + str(m))
		b = self.csolverlb.getBooleanVar(self.csolver, c_uint(2))
		self.mapVarToConstraint(m, b)
		self.orgboolVar.append(m)
		self.addToConstraintMap(b, (Satune.createNewBooleanVar, (m,)) )

	def getBooleanTrue(self):
		eprint("BooleanTrue: " + str(self.csolverlb.getBooleanTrue(self.csolver)))
		return self.csolverlb.getBooleanTrue(self.csolver)

	def getBooleanFalse(self):
		eprint("BooleanFalse: " + str(self.csolverlb.getBooleanFalse(self.csolver)))
		return self.csolverlb.getBooleanFalse(self.csolver)

	def addConstraint(self, constr):
		eprint("Trace: addConstraint => "+ str(constr))
		if(constr not in self.constraints):
			self.constraints.append(constr)
		return self.csolverlb.addConstraint(self.csolver, constr)
	
	def solve(self):
		return self.csolverlb.solve(self.csolver)
	
	def printConstraints(self):
		self.csolverlb.printConstraints(self.csolver)
	
	
