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
	
	def getConstraint(self, var):
		if type(var) is bool:
			return self.getBooleanTrue() if var else self.getBooleanFalse()
		#eprint("getConstraint: var=" + str(var))
		key=abs(var)
		assert(key in self.var_constr_map.keys())
		if var >= 0:
			return self.var_constr_map[key]
		else:
			return self.Not(self.var_constr_map[key], False)
	
	def mapVarToConstraint(self, var, constraint):
		key=abs(var)
		#eprint("mapVarToConstraint: var=" + str(var) + " key=" + str(key)+" constraint=" + str(constraint))
		assert(key not in self.var_constr_map.keys())
		self.var_constr_map[key] = constraint
	
	def applyLogicalOperation(self, op, array):
		#eprint("Trace: applyLogicalOperation " + str(op) +" on " + str(array))
        	constrs = array
        	b = (c_void_p*len(constrs))(*constrs)
        	return self.csolverlb.applyLogicalOperation(self.csolver, op, b, c_uint(len(constrs)))

	def Not(self, x, conv=True):
		#eprint("Trace: Not => "+ str(x))
		constr=[self.getConstraint(x)] if conv else [x]
		return self.applyLogicalOperation(ps.LogicOps.SATC_NOT, constr)
	
	def And(self, f, g, conv=True):
		#eprint("Trace: And => "+ str((f) + " , " + str(g)))
		constr=[self.getConstraint(f), self.getConstraint(g)] if conv else [f, g]
		return self.applyLogicalOperation(ps.LogicOps.SATC_AND, constr)
	
	def Or(self , f, g, conv=True):
		eprint("Trace: Or => "+ str(f) + " , " + str(g))
		constr=[self.getConstraint(f), self.getConstraint(g)] if conv else [f,g]
		return self.applyLogicalOperation(ps.LogicOps.SATC_OR, constr)
	
	def Xor(self , f, g, conv=True):
		#eprint("Trace: Xor => "+ str((f) + " , " + str(g)))
		constr=[self.getConstraint(f), self.getConstraint(g)] if conv else [f, g]
		return self.applyLogicalOperation(ps.LogicOps.SATC_OR, constr)
 
	def ITE(self , c, t, f, conv =True):
		#eprint("Trace: ITE => "+ str(c) + " , " + str(t) + " , "+ str(f))
		constr=[self.getConstraint(c), self.getConstraint(t)] if conv else [c, t]
		CandT= self.applyLogicalOperation(ps.LogicOps.SATC_AND, constr)
		constr=[ self.Not(c) , self.getConstraint(f)] if conv else [ Not(c,conv), f]
		NotCandF= self.applyLogicalOperation(ps.LogicOps.SATC_AND, constr)
		constr=[CandT, NotCandF]
		return self.applyLogicalOperation(ps.LogicOps.SATC_OR, constr)
	
	def All(self, array, conv=True):
		#eprint("Trace: All => "+ str(array))
		constr=[self.getConstraint(x) for x in array] if conv else array
		return self.applyLogicalOperation(ps.LogicOps.SATC_AND, constr)

	def Any(self, array, conv=True):
		#eprint("Trace: Any => "+ str(array))
		constr=[self.getConstraint(x) for x in array] if conv else array
		return self.applyLogicalOperation(ps.LogicOps.SATC_OR, constr)

	def ExactlyOne(self, array, conv=True):
		#eprint("Trace: ExactlyOne => "+ str(array))
		constrs=[self.getConstraint(x) for x in array] if conv else array
		b = (c_void_p*len(constrs))(*constrs)
		return self.csolverlb.applyExactlyOneConstraint(self.csolver, b, c_uint(len(constrs))) 
	
	def AtMostOne(self, array, conv=True):
		#eprint("Trace: AtMostOne => "+ str(array))
		constrs=[self.getConstraint(x) for x in array] if conv else array
		b = (c_void_p*len(constrs))(*constrs)
		return self.csolverlb.applyExactlyOneConstraint(self.csolver, b, c_uint(len(constrs))) 
	
	def createNewElement(self, array):
		#eprint("Trace: createNewElement => "+ str(array))
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
	
	def createNewBooleanVar(self, m):
		b = self.csolverlb.getBooleanVar(self.csolver, c_uint(2))
		self.mapVarToConstraint(m, b)

	def getBooleanTrue(self):
		return self.csolverlb.getBooleanTrue(self.csolver)

	def getBooleanFalse(self):
		return self.csolverlb.getBooleanFalse(self.csolver)

	def addConstraint(self, constr):
		eprint("Trace: addConstraint => "+ str(constr))
		return self.csolverlb.addConstraint(self.csolver, constr)
	
	def solve(self):
		return self.csolverlb.solve(self.csolver)
	
	def printConstraints(self):
		self.csolverlb.printConstraints(self.csolver)
