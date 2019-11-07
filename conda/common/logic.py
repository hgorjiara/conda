# -*- coding: utf-8 -*-
"""
The basic idea to nest logical expressions is instead of trying to denest
things via distribution, we add new variables. So if we have some logical
expression expr, we replace it with x and add expr <-> x to the clauses,
where x is a new variable, and expr <-> x is recursively evaluated in the
same way, so that the final clauses are ORs of atoms.

To use this, create a new Clauses object with the max var, for instance, if you
already have [[1, 2, -3]], you would use C = Clause(3).  All functions return
a new literal, which represents that function, or True or False if the expression
can be resolved fully. They may also add new clauses to C.clauses, which
will then be delivered to the SAT solver.

All functions take atoms as arguments (an atom is an integer, representing a
literal or a negated literal, or boolean constants True or False; that is,
it is the callers' responsibility to do the conversion of expressions
recursively. This is done because we do not have data structures
representing the various logical classes, only atoms.

The polarity argument can be set to True or False if you know that the literal
being used will only be used in the positive or the negative, respectively
(e.g., you will only use x, not -x).  This will generate fewer clauses. It
is probably best if you do not take advantage of this directly, but rather
through the Require and Prevent functions.

"""
from __future__ import absolute_import, division, print_function, unicode_literals

from itertools import chain, combinations
from logging import getLogger
import pycosat
import sys
import time
from satune import Satune
from .compat import iteritems

log = getLogger(__name__)

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

# Code that uses special cases (generates no clauses) is in ADTs/FEnv.h in
# minisatp. Code that generates clauses is in Hardware_clausify.cc (and are
# also described in the paper, "Translating Pseudo-Boolean Constraints into
# SAT," Eén and Sörensson).
class Clauses(object):
    def __init__(self, m=0):
        self.clauses = []
        self.names = {}
        self.indices = {}
        self.unsat = False
        self.m = m
	self.satune = Satune()

    def name_var(self, m, name):
        nname = '!' + name
        self.names[name] = m
        self.names[nname] = -m
        if type(m) is not bool and m not in self.indices:
            self.indices[m] = name
            self.indices[-m] = nname
        return m

    def new_var(self, name=None):
        m = self.m + 1
        self.m = m
        if name:
            self.name_var(m, name)
        return m

    def create_element(self, myset):
    	self.satune.createNewElement(myset);

    def create_booleanvar(self, m):
    	self.satune.createNewBooleanVar(m)

    def from_name(self, name):
        return self.names.get(name)

    def from_index(self, m):
        return self.indices.get(m)

        
    def Assign_(self, vals, name=None):
        tvals = type(vals)
        if tvals is tuple:
            x = self.new_var()
	    eprint("1.new var in Assign_ " + str(x))
	    eprint("vals[0] = " + str(vals[0]))
	    eprint("vals[1] = " + str(vals[1]))
            self.clauses.extend((-x,) + y for y in vals[0])
            self.clauses.extend((x,) + y for y in vals[1])
	    def AssertNegate(constr, negconstr):
	        if len(negconstr) == 0:
		    return
		def negate(constr):
		    t = type(constr)
		    if t is list:
		        mylist = map(negate,constr)
			tmpor = ()
			for l in mylist:
			    tmpor += l
			return [tmpor]
		    if t is tuple:
		    	return tuple(map(negate,constr))
		    return constr * -1
	        eprint("negate var[1] = " + str(negate(negconstr) ) )
	        assert(constr == negate(negconstr))
	    AssertNegate(vals[0], vals[1])
	    assert(len(vals[0]) >0)
	    andlist = []
	    for y in vals[0]:
	    	andlist.append(self.satune.Any(list(y)) )
	    self.satune.mapVarToConstraint(x, self.satune.All(andlist, False))
        elif tvals is bool and name:
            x = self.new_var()
	    self.satune.mapVarToConstraint(x, self.satune.getBooleanTrue())
	    eprint("2.new var in Assign_ name " + str(x))
            self.clauses.append((x,) if vals else (-x,))
        else:
	    eprint("Not creating new var! Using vals " + str(vals))
            x = vals
        return self.name_var(x, name) if name else x

    def Convert_(self, x):
        tx = type(x)
        if tx in (tuple, list):
            return tx(map(self.Convert_, x))
        return self.names.get(x, x)

    def Eval_(self, func, args, polarity, name, conv=True):
        if conv:
            args = self.Convert_(args)
        nz = len(self.clauses)
        vals = func(*args, polarity=polarity)
        if name is not False:
            return self.Assign_(vals, name)
        tvals = type(vals)
        if tvals is tuple:
	    eprint("tvals are tuples: " + str(vals))
            self.clauses.extend(vals[0])
            self.clauses.extend(vals[1])
        elif tvals is not bool:
	    eprint("tvals are not Bool:" + str(vals))
            self.clauses.append((vals if polarity else -vals,))
        else:
	    assert(nz == len(self.clauses))
            self.clauses = self.clauses[:nz]
            self.unsat = self.unsat or polarity != vals

    def Combine_(self, args, polarity):
        if any(v is False for v in args):
            return False
        args = [v for v in args if v is not True]
        nv = len(args)
        if nv == 0:
            return True
        if nv == 1:
            return args[0]
        if all(type(v) is tuple for v in args):
            return (sum((v[0] for v in args), []), sum((v[1] for v in args), []))
        else:
            return self.All_(map(self.Assign_, args), polarity)

    def Prevent(self, what, *args):
    	eprint("Prevent: Running " + str(what) + " arg:")
	eprint(self.Convert_(args))
        ret, satval = what.__get__(self, Clauses)(*args, polarity=False, name=False)
	eprint("Conda addConstraint: " + str(ret))
	self.satune.addConstraint( self.satune.Not(satval, False))
	return ret

    def Require(self, addConstr, what, *args):
    	eprint("Require: Running " + str(what) +" arg:")
	eprint(self.Convert_(args))
        ret, satval = what.__get__(self, Clauses)(*args, polarity=True, name=False)
        if addConstr:
	    self.satune.addConstraint(satval)
	return ret

    def Not_(self, x, polarity=None):
        eprint("Not_ x=" + str(x))
        return (not x) if type(x) is bool else -x

    def Not(self, x, polarity=None, name=None):
    	convX = self.Convert_(x)
        return self.Eval_(self.Not_, (x,), polarity, name), self.satune.Not(convX) if polarity in (True, None) else self.satune.getConstraint(convX)

    def And_(self, f, g, polarity=None):
        if f is False or g is False:
            return False
        if f is True:
            return g
        if g is True or f is g:
            return f
        if f is -g:
            return False
        if g < f:
            f, g = g, f
        pval = [(f,), (g,)] if polarity in (True, None) else []
        nval = [(-f, -g)] if polarity in (False, None) else []
        return pval, nval

    def And(self, f, g, polarity=None, name=None):
    	convF = self.Convert_(f)
	convG = self.Convert_(g)
        return self.Eval_(self.And_, (f, g), polarity, name), self.satune.And(convF,convG ) if polarity in (True, None) else self.satune.Not(self.satune.And(convF,convG ), False)

    def Or_(self, f, g, polarity):
        if f is True or g is True:
            return True
        if f is False:
            return g
        if g is False or f is g:
            return f
        if f is -g:
            return True
        if g < f:
            f, g = g, f
        pval = [(f, g)] if polarity in (True, None) else []
        nval = [(-f,), (-g,)] if polarity in (False, None) else []
        return pval, nval

    def Or(self, f, g, polarity=None, name=None):
    	convF = self.Convert_(f)
	convG = self.Convert_(g)
	eprint("f:Conv( " + str(f) + " )= "+ str(convF))
	eprint("g:Conv( " + str(g) + " )= "+ str(convG))
	return self.Eval_(self.Or_, (f, g), polarity, name), self.satune.Or(convF,convG ) if polarity in (True,None) else self.satune.Not(self.satune.Or(convF,convG), False)

    def Xor_(self, f, g, polarity):
        if f is False:
            return g
        if f is True:
            return self.Not_(g, polarity)
        if g is False:
            return f
        if g is True:
            return -f
        if f is g:
            return False
        if f is -g:
            return True
        if g < f:
            f, g = g, f
        pval = [(f, g), (-f, -g)] if polarity in (True, None) else []
        nval = [(-f, g), (f, -g)] if polarity in (False, None) else []
        return pval, nval

    def Xor(self, f, g, polarity=None, name=None):
    	convF = self.Convert_(f)
	convG = self.Convert_(g)
        return self.Eval_(self.Xor_, (f, g), polarity, name), self.satune.Xor(convF,convG) if polarity in (True, None) else self.satune.Not(self.satune.Xor(convF, convG), False)

    def ITE_(self, c, t, f, polarity):
        if c is True:
            return t
        if c is False:
            return f
        if t is True or t is c:
            return self.Or_(c, f, polarity)
        if t is False or t is -c:
            return self.And_(-c, f, polarity)
        if f is False or f is c:
            return self.And_(c, t, polarity)
        if f is True or f is -c:
            return self.Or_(t, -c, polarity)
        if t is f:
            return t
        if t is -f:
            return self.Xor_(c, f, polarity)
        if t < f:
            t, f, c = f, t, -c
        # Basically, c ? t : f is equivalent to (c AND t) OR (NOT c AND f)
        # The third clause in each group is redundant but assists the unit
        # propagation in the SAT solver.
        pval = [(-c, t), (c, f), (t, f)] if polarity in (True, None) else []
        nval = [(-c, -t), (c, -f), (-t, -f)] if polarity in (False, None) else []
        return pval, nval

    def ITE(self, c, t, f, polarity=None, name=None, satune=True):
        """
        if c then t else f

        In this function, if any of c, t, or f are True and False the resulting
        expression is resolved.
        """
	satuneConstr = None
	if satune:
    	    convC = self.Convert_(c)
	    convT = self.Convert_(t)
	    convF = self.Convert_(f)
	    satuneConstr = self.satune.ITE(convC,convT,convF) if polarity in (True, None) else self.satune.Not(self.satune.ITE(convC,convT,convF), False)
        return self.Eval_(self.ITE_, (c, t, f), polarity, name), satuneConstr

    def All_(self, iter, polarity=None):
        vals = set()
        for v in iter:
            if v is True:
                continue
            if v is False or -v in vals:
                return False
            vals.add(v)
        nv = len(vals)
        if nv == 0:
            return True
        elif nv == 1:
            return next(v for v in vals)
        pval = [(v,) for v in vals] if polarity in (True, None) else []
        nval = [tuple(-v for v in vals)] if polarity in (False, None) else []
        return pval, nval

    def All(self, iter, polarity=None, name=None):
        vals = [x for x in iter]
	convVals = self.Convert_(vals)
        return self.Eval_(self.All_, (iter,), polarity, name), self.satune.All(convVals) if polarity in (True, None) else self.satune.Not(self.satune.All(convVals), False)

    def Any_(self, iter, polarity):
        vals = set()
        for v in iter:
            if v is False:
                continue
            elif v is True or -v in vals:
                return True
            vals.add(v)
        nv = len(vals)
        if nv == 0:
            return False
        elif nv == 1:
            return next(v for v in vals)
        pval = [tuple(vals)] if polarity in (True, None) else []
        nval = [(-v,) for v in vals] if polarity in (False, None) else []
        return pval, nval

    def Any(self, vals, polarity=None, name=None):
        convVals = self.Convert_(vals)
        return self.Eval_(self.Any_, (list(vals),), polarity, name) , self.satune.Any(convVals) if polarity in (True, None) else self.satune.Not(self.satune.Any(convVals), False)

    def AtMostOne_NSQ_(self, vals, polarity):
        combos = []
        for v1, v2 in combinations(map(self.Not_, vals), 2):
            combos.append(self.Or_(v1, v2, polarity))
        return self.Combine_(combos, polarity)

    def AtMostOne_NSQ(self, vals, polarity=None, name=None):
        return self.Eval_(self.AtMostOne_NSQ_, (list(vals),), polarity, name)

    def AtMostOne_BDD_(self, vals, polarity=None, name=None):
        vals = [(1, v) for v in vals]
        return self.LinearBound_(vals, 0, 1, True, polarity)

    def AtMostOne_BDD(self, vals, polarity=None, name=None):
        return self.Eval_(self.AtMostOne_BDD_, (list(vals),), polarity, name)

    def AtMostOne(self, vals, polarity=None, name=None):
        vals = list(vals)
        nv = len(vals)
        if nv < 5 - (polarity is not True):
            what = self.AtMostOne_NSQ
        else:
            what = self.AtMostOne_BDD
	convVals = self.Convert_(vals)
        return self.Eval_(what, (vals,), polarity, name), self.satune.AtMostOne(convVals) if polarity in (True, None) else self.satune.Not(self.satune.AtMostOne(convVals), False)

    def ExactlyOne_NSQ_(self, vals, polarity):
        vals = list(vals)
        v1 = self.AtMostOne_NSQ_(vals, polarity)
        v2 = self.Any_(vals, polarity)
        return self.Combine_((v1, v2), polarity)

    def ExactlyOne_NSQ(self, vals, polarity=None, name=None):
        return self.Eval_(self.ExactlyOne_NSQ_, (list(vals),), polarity, name)

    def ExactlyOne_BDD_(self, vals, polarity):
        vals = [(1, v) for v in vals]
        return self.LinearBound_(vals, 1, 1, True, polarity)

    def ExactlyOne_BDD(self, vals, polarity=None, name=None):
        return self.Eval_(self.ExactlyOne_BDD_, (list(vals),), polarity, name)

    def ExactlyOne(self, vals, polarity=None, name=None):
        vals = list(vals)
        nv = len(vals)
        if nv < 2:
            what = self.ExactlyOne_NSQ
        else:
            what = self.ExactlyOne_BDD
	convVals = self.Convert_(vals)
        return self.Eval_(what, (vals,), polarity, name), self.satune.ExactlyOne(convVals) if polarity in (True, None) else self.satune.Not(self.satune.ExactlyOne(convVals), False)

    def LB_Preprocess_(self, equation):
        if type(equation) is dict:
            equation = [(c, self.names.get(a, a)) for a, c in iteritems(equation)]
        if any(c <= 0 or type(a) is bool for c, a in equation):
            offset = sum(c for c, a in equation if a is True or a is not False and c <= 0)
            equation = [(c, a) if c > 0 else (-c, -a) for c, a in equation
                        if type(a) is not bool and c]
        else:
            offset = 0
        equation = sorted(equation)
        return equation, offset

    def BDD_(self, equation, nterms, lo, hi, polarity):
        # The equation is sorted in order of increasing coefficients.
        # Then we take advantage of the following recurrence:
        #                l      <= S + cN xN <= u
        #  => IF xN THEN l - cN <= S         <= u - cN
        #           ELSE l      <= S         <= u
        # we use memoization to prune common subexpressions
        total = sum(c for c, _ in equation[:nterms])
        target = (nterms-1, 0, total)
        call_stack = [target]
        ret = {}
        csum = 0
        while call_stack:
            ndx, csum, total = call_stack[-1]
            lower_limit = lo - csum
            upper_limit = hi - csum
            if lower_limit <= 0 and upper_limit >= total:
                ret[call_stack.pop()] = True
                continue
            if lower_limit > total or upper_limit < 0: 
		ret[call_stack.pop()] = False
                continue
            LC, LA = equation[ndx]
            ndx -= 1
            total -= LC
            hi_key = (ndx, csum if LA < 0 else csum + LC, total)
            thi = ret.get(hi_key)
            if thi is None:
                call_stack.append(hi_key)
                continue
            lo_key = (ndx, csum + LC if LA < 0 else csum, total)
            tlo = ret.get(lo_key)
            if tlo is None:
                call_stack.append(lo_key)
                continue
	    #eprint("BDD_.self.ITE (" + str(abs(LA)) + ", " + str(thi) + ", " + str(tlo) +" )")
            ret[call_stack.pop()], _ = self.ITE(abs(LA), thi, tlo, polarity, None, False)
        return ret[target]


    def BDD_Satune(self, equation, nterms, lo, hi, polarity):
        # The equation is sorted in order of increasing coefficients.
        # Then we take advantage of the following recurrence:
        #                l      <= S + cN xN <= u
        #  => IF xN THEN l - cN <= S         <= u - cN
        #           ELSE l      <= S         <= u
        # we use memoization to prune common subexpressions
        total = sum(c for c, _ in equation[:nterms])
        target = (nterms-1, 0, total)
        call_stack = [target]
        ret = {}
        csum = 0
        while call_stack:
            ndx, csum, total = call_stack[-1]
            lower_limit = lo - csum
            upper_limit = hi - csum
            if lower_limit <= 0 and upper_limit >= total:
                ret[call_stack.pop()] = True
                continue
            if lower_limit > total or upper_limit < 0:
                ret[call_stack.pop()] = False
                continue
            LC, LA = equation[ndx]
            ndx -= 1
            total -= LC
            hi_key = (ndx, csum if LA < 0 else csum + LC, total)
            thi = ret.get(hi_key)
            if thi is None:
                call_stack.append(hi_key)
                continue
            lo_key = (ndx, csum + LC if LA < 0 else csum, total)
            tlo = ret.get(lo_key)
            if tlo is None:
                call_stack.append(lo_key)
                continue
            #eprint("BDD_.self.ITE (" + str(abs(LA)) + ", " + str(thi) + ", " + str(tlo) +" )")
            ret[call_stack.pop()], _ = self.ITE(abs(LA), thi, tlo, polarity, None, False)
        assert(type(ret[target]) not in (list, tuple) or len(ret[target]) == 1)
	return self.satune.getConstraint(ret[target])

    def LinearBound_(self, equation, lo, hi, preprocess, polarity):
        if preprocess:
            equation, offset = self.LB_Preprocess_(equation)
            lo -= offset
            hi -= offset
        nterms = len(equation)
        if nterms and equation[-1][0] > hi:
            nprune = sum(c > hi for c, a in equation)
            log.trace('Eliminating %d/%d terms for bound violation' % (nprune, nterms))
            nterms -= nprune
        else:
            nprune = 0
        # Tighten bounds
        total = sum(c for c, _ in equation[:nterms])
        if preprocess:
            lo = max([lo, 0])
            hi = min([hi, total])
        if lo > hi:
            return False
        if nterms == 0:
            res = lo == 0
        else:
            res = self.BDD_(equation, nterms, lo, hi, polarity)
        if nprune:
            prune= self.All_([-a for c, a in equation[nterms:]], polarity)
            res = self.Combine_((res, prune), polarity)
	eprint("LinearBound_ returned: " + str(res) )
        return res


    def LinearBound_Satune(self, equation, lo, hi, preprocess, polarity):
	if preprocess:
            equation, offset = self.LB_Preprocess_(equation)
            lo -= offset
            hi -= offset
        nterms = len(equation)
        if nterms and equation[-1][0] > hi:
            nprune = sum(c > hi for c, a in equation)
            log.trace('Eliminating %d/%d terms for bound violation' % (nprune, nterms))
            nterms -= nprune
        else:
            nprune = 0
        # Tighten bounds
        total = sum(c for c, _ in equation[:nterms])
        if preprocess:
            lo = max([lo, 0])
            hi = min([hi, total])
        if lo > hi:
            #return False
	    return self.satune.getBooleanFalse()
        if nterms == 0:
            res = lo == 0
	    resSAT = self.satune.getBooleanTrue() if lo ==0 else self.satune.getBooleanFalse()
        else:
            res = self.BDD_(equation, nterms, lo, hi, polarity)
            resSAT = self.BDD_Satune(equation, nterms, lo, hi, polarity)
	    eprint("BDD_Satune returned: " + str(resSAT))
        if nprune:
	    values=[-a for c, a in equation[nterms:]]
            prune = self.All_(values, polarity)
	    pruneSAT= self.satune.All(values) if polarity in (True, None) else self.satune.Not(self.satune.All(values) , False)
	    eprint("PruneSAAT got the value: " + str(pruneSAT) )
            res = self.Combine_((res, prune), polarity)
	    resSAT = self.satune.All([resSAT,pruneSAT], False) if polarity in (True, None) else self.satune.Not(self.satune.All([resSAT,pruneSAT], False), False)
        eprint("LinearBound_Satune returned: " + str(resSAT))
	return resSAT

    def LinearBound(self, equation, lo, hi, preprocess=True, polarity=None, name=None):
        return self.Eval_(self.LinearBound_, (equation, lo, hi, preprocess),
                          polarity, name, conv=False), self.LinearBound_Satune(equation, lo, hi, preprocess, polarity)

    def replaceSatune(self, newSatune):
    	eprint("Destroying the old SATTune and replace it with new one!!!")
    	self.satune.destroy()
	self.satune = newSatune
    
    def sat(self, additional=None, includeIf=False, names=False, limit=0):
        """
        Calculate a SAT solution for the current clause set.

        Returned is the list of those solutions.  When the clauses are
        unsatisfiable, an empty list is returned.

        """
        if self.unsat:
            return None
        if not self.m:
            return set() if names else []
        clauses = self.clauses
	cloneSatune = None
        if additional:
            def preproc(eqs):
                def preproc_(cc):
                    for c in cc:
                        c = self.names.get(c, c)
                        if c is False:
                            continue
                        yield c
                        if c is True:
                            break
                for cc in eqs:
                    cc = tuple(preproc_(cc))
                    if not cc:
                        yield cc
                        break
                    if cc[-1] is not True:
                        yield cc
            additional = list(preproc(additional))
            if additional:
                if not additional[-1]:
                    return None
                clauses = tuple(chain(clauses, additional))
		def addAdditionalToSatune():
			vals = [list(x) for x in additional]
			eprint("vals = "+ str(vals))
			valsConstr =[]
			for v in vals:
				valsConstr.append(self.satune.Any(v))
			self.satune.addConstraint(self.satune.All( valsConstr, False))
		if not includeIf: #When there are additionals but we don't include them
			cloneSatune = self.satune.clone()
		addAdditionalToSatune()
		if includeIf: # When there are additionals and we include them
			cloneSatune = self.satune.clone()
	#self.satune.printConstraints()
	if not cloneSatune: # When there are no additionals
		cloneSatune = self.satune.clone()
	eprint("Invoking SAT with clause count: " + str(len(clauses)))
	eprint("Clauses= " + str(clauses))
	start = time.time()
        solution = pycosat.solve(clauses, vars=self.m, prop_limit=limit)
	end = time.time()
	satsolution = self.satune.solve()
	satend = time.time()
        eprint("PycoSAT SOLVING TIME:")
        eprint(end - start)
	eprint("SATTune SOLVING TIME:")
	eprint(satend - end)
	eprint("satsolution=" + str(satsolution))
	eprint("solution=" + str(solution))
	assert((satsolution ==0 and solution == "UNSAT") or (satsolution ==1 and len(solution) > 0)  )
        assert( cloneSatune)
	self.replaceSatune(cloneSatune)
	if solution in ("UNSAT", "UNKNOWN"):
            return None
        if additional and includeIf:
            self.clauses.extend(additional)
        if names:
            return set(nm for nm in (self.indices.get(s) for s in solution) if nm and nm[0] != '!')
        return solution

    #def itersolve(self, constraints=None, m=None):
    #    exclude = []
    #    if m is None:
    #        m = self.m
    #    while True:
            # We don't use pycosat.itersolve because it is more
            # important to limit the number of terms added to the
            # exclusion list, in our experience. Once we update
            # pycosat to do this, this can use it.
    #        sol = self.sat(chain(constraints, exclude))
    #        if sol is None:
    #            return
    #        yield sol
    #        exclude.append([-k for k in sol if -m <= k <= m])

    def minimize(self, objective, bestsol=None, trymax=False):
        """
        Minimize the objective function given either by (coeff, integer)
        tuple pairs, or a dictionary of varname: coeff values. The actual
        minimization is multiobjective: first, we minimize the largest
        active coefficient value, then we minimize the sum.
        """
	eprint("Minimizing objective = " + str(objective) +" |||| best solution= " + str(bestsol))
        if bestsol is None or len(bestsol) < self.m:
            log.debug('Clauses added, recomputing solution')
	    assert(False)
            bestsol = self.sat()

        if bestsol is None or self.unsat:
            log.debug('Constraints are unsatisfiable')
            return bestsol, sum(abs(c) for c, a in objective) + 1 if objective else 1
        if not objective:
            log.debug('Empty objective, trivial solution')
            return bestsol, 0

        if type(objective) is dict:
            objective = [(v, self.names.get(k, k)) for k, v in iteritems(objective)]

        objective, offset = self.LB_Preprocess_(objective)
        maxval = max(c for c, a in objective)

        def peak_val(sol, odict):
            return max(odict.get(s, 0) for s in sol)

        def sum_val(sol, odict):
            return sum(odict.get(s, 0) for s in sol)

        lo = 0
        try0 = 0
        for peak in ((True, False) if maxval > 1 else (False,)):
            if peak:
                log.trace('Beginning peak minimization')
                objval = peak_val
            else:
                log.trace('Beginning sum minimization')
                objval = sum_val

            odict = {a: c for c, a in objective}
            bestval = objval(bestsol, odict)

            # If we got lucky and the initial solution is optimal, we still
            # need to generate the constraints at least once
            hi = bestval
            m_orig = self.m
            nz = len(self.clauses)
	    nzClone = self.satune.clone()
            if trymax and not peak:
                try0 = hi - 1

            log.trace("Initial range (%d,%d)" % (lo, hi))
            while True:
	    	eprint("Starting the loop ...")
                if try0 is None:
                    mid = (lo+hi) // 2
                else:
                    mid = try0
                if peak:
                    self.Prevent(self.Any, tuple(a for c, a in objective if c > mid))
                    temp = tuple(a for c, a in objective if lo <= c <= mid)
                    if temp:
                        self.Require(True, self.Any, temp)
                else:
                    self.Require(True, self.LinearBound, objective, lo, mid, False)
                log.trace('Bisection attempt: (%d,%d), (%d+%d) clauses' %
                          (lo, mid, nz, len(self.clauses)-nz))
		newsol = self.sat()
                if newsol is None:
                    lo = mid + 1
                    log.trace("Bisection failure, new range=(%d,%d)" % (lo, hi))
                    # If this was a failure of the first test after peak minimization,
                    # then it means that the peak minimizer is "tight" and we don't need
                    # any further constraints.
                else:
                    done = lo == mid
                    bestsol = newsol
                    bestval = objval(newsol, odict)
                    hi = bestval
                    log.trace("Bisection success, new range=(%d,%d)" % (lo, hi))
                    if done:
                        break
                self.m = m_orig
                if len(self.clauses) > nz:
		    eprint("New Constraints are added, we should replace it to the old one ...")
		    self.replaceSatune(nzClone.clone())
                    self.clauses = self.clauses[:nz]
                self.unsat = False
                try0 = None

            log.debug('Final %s objective: %d' % ('peak' if peak else 'sum', bestval))
            if bestval == 0:
                break
            elif peak:
                # Now that we've minimized the peak value, we can drop any terms
                # with coefficients larger than this. Furthermore, since we know
                # at least one peak will be active, our lower bound for the sum
                # equals the peak.
                objective = [(c, a) for c, a in objective if c <= bestval]
                try0 = sum_val(bestsol, odict)
                lo = bestval
            else:
                log.debug('New peak objective: %d' % peak_val(bestsol, odict))

        return bestsol, bestval


def evaluate_eq(eq, sol):
    if type(eq) is not dict:
        eq = {c: v for v, c in eq if type(c) is not bool}
    return sum(eq.get(s, 0) for s in sol if type(s) is not bool)


def minimal_unsatisfiable_subset(clauses, sat):
    """
    Given a set of clauses, find a minimal unsatisfiable subset (an
    unsatisfiable core)

    A set is a minimal unsatisfiable subset if no proper subset is
    unsatisfiable.  A set of clauses may have many minimal unsatisfiable
    subsets of different sizes.

    sat should be a function that takes a tuple of clauses and returns True if
    the clauses are satisfiable and False if they are not.  The algorithm will
    work with any order-reversing function (reversing the order of subset and
    the order False < True), that is, any function where (A <= B) iff (sat(B)
    <= sat(A)), where A <= B means A is a subset of B and False < True).

    Algorithm
    =========

    Algorithm suggested from
    http://www.slideshare.net/pvcpvc9/lecture17-31382688. We do a binary
    search on the clauses by splitting them in halves A and B. If A or B is
    UNSAT, we use that and repeat. Otherwise, we recursively check A, but each
    time we do a sat query, we include B, until we have a minimal subset A* of
    A such that A* U B is UNSAT. Then we find a minimal subset B* of B such
    that A* U B* is UNSAT. Then A* U B* will be a minimal unsatisfiable subset
    of the original set of clauses.

    Proof: If some proper subset C of A* U B* is UNSAT, then there is some
    clause c in A* U B* not in C. If c is in A*, then that means (A* - {c}) U
    B* is UNSAT, and hence (A* - {c}) U B is UNSAT, since it is a superset,
    which contradicts A* being the minimal subset of A with such
    property. Similarly, if c is in B, then A* U (B* - {c}) is UNSAT, but B* -
    {c} is a strict subset of B*, contradicting B* being the minimal subset of
    B with this property.

    """
    clauses = tuple(clauses)
    assert(False)
    if sat(clauses):
        raise ValueError("Clauses are not unsatisfiable")

    def split(S):
        """
        Split S into two equal parts
        """
        S = tuple(S)
        L = len(S)
        return S[:L//2], S[L//2:]

    def minimal_unsat(clauses, include=()):
        """
        Return a minimal subset A of clauses such that A + include is
        unsatisfiable.

        Implicitly assumes that clauses + include is unsatisfiable.
        """
        global L, d

        # assert not sat(clauses + include), (len(clauses), len(include))

        # Base case: Since clauses + include is implicitly assumed to be
        # unsatisfiable, if clauses has only one element, it must be its own
        # minimal subset
        if len(clauses) == 1:
            return clauses

        A, B = split(clauses)

        # If one half is unsatisfiable (with include), we can discard the
        # other half.

        # To display progress, every time we discard clauses, we update the
        # progress by that much.
        assert(False)
	if not sat(A + include):
            d += len(B)
            return minimal_unsat(A, include)
	assert(False)
        if not sat(B + include):
            d += len(A)
            return minimal_unsat(B, include)

        Astar = minimal_unsat(A, B + include)
        Bstar = minimal_unsat(B, Astar + include)
        return Astar + Bstar

    global L, d
    L = len(clauses)
    d = 0
    ret = minimal_unsat(clauses)
    return ret
