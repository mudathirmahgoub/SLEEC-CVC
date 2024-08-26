import time

import cvc5
from cvc5 import Kind, Term

from CVC5_wrapper.utility import _polymorph_args_to_tuple

# for writing SMT-LIB
Decls = []
Options = []

tm = cvc5.TermManager()
integer = tm.getIntegerSort()
boolean = tm.getBooleanSort()
tuple_counter = 0


def get_new_tuple_counter():
    global tuple_counter
    tuple_counter += 1
    return tuple_counter


'''
For Sorts
'''

# a dictionary for sorts, and the bounded variable namespace (by id)
sorts_v_index = {integer: 0}
name_to_sort = {"int": integer, "bool": boolean}


def new_free_sort(name: str):
    new_sort = declareUninterpretedSort(name)
    name_to_sort[name] = (new_sort)
    return new_sort


def new_bounded_var(sort_name, prefix=''):
    if isinstance(sort_name, str):
        if sort_name in name_to_sort:
            sort = name_to_sort[sort_name]
        else:
            print("unavailable sort")
            assert False
    else:
        sort = sort_name
    index = sorts_v_index.get(sort, 0)
    if not prefix:
        var = tm.mkVar(sort, "b_{}_{}".format(sort, index))
    else:
        var = tm.mkVar(sort, "{}_{}_{}".format(prefix, sort, index))
    sorts_v_index[sort] = index + 1
    if sort == integer:
        return CVC5_INT(var)
    else:
        return CVC5_FreeSort(var)


'''
For relations
'''
Relations = {}


def declareConst(sort, name):
    Decls.append("(declare-const " + name + " " + str(sort) + ")")
    return tm.mkConst(sort, name)


def declareUninterpretedSort(name):
    Decls.append("(declare-sort " + name + " 0)")
    return tm.mkUninterpretedSort(name)


def setOption(solver, option, value):
    Options.append("(set-option :" + option + " " + value + ")")
    solver.setOption(option, value)


class Relation:
    def __init__(self, name, args, relation=None):
        self.cardinal = None
        self.name = name
        self.args = args
        Relations[name] = self
        self.relational_class = None

        if relation is not None:
            self.relation = relation
        else:
            tuple_sort = tm.mkTupleSort(*(self.get_relation_types()))
            relationSort = tm.mkSetSort(tuple_sort)
            self.relation = declareConst(relationSort, self.name)

        self.nat_cons = None

    def get_relation_types(self):
        return [type for _, type in self.args]

    def apply(self, function):
        relation_args_types = self.get_relation_types()
        tuple_sort = tm.mkTupleSort(*relation_args_types)
        new_tuple = tm.mkVar(tuple_sort, "tuple_{}".format(get_new_tuple_counter()))
        instance = self.new_relational_object(
            tuple=[cast(tuple_select(new_tuple, i)) for i in range(len(relation_args_types))])
        term = function(instance)
        lambda_func = tm.mkTerm(Kind.LAMBDA, tm.mkTerm(Kind.VARIABLE_LIST, new_tuple), val(term))
        return lambda_func

    def filter(self, filter_function, name):
        lambda_func = self.apply(filter_function)
        result_relation = val(
            tm.mkTerm(Kind.SET_FILTER, lambda_func,
                      self.relation))
        return Relation("{}".format(str(name)), args=self.args, relation=result_relation)

    def map(self, map_function, name, args):
        lambda_func = self.apply(map_function)
        result_relation = val(
            tm.mkTerm(Kind.SET_MAP, lambda_func,
                      self.relation))
        return Relation("{}".format(str(name)), args=args, relation=result_relation)

    def product(self, other, name, args):
        # product
        result_relation = tm.mkTerm(Kind.RELATION_PRODUCT, self.relation, val(other))
        return Relation(name, args=args, relation=result_relation)

    def contains(self, item):
        return CVC5_Bool(tm.mkTerm(Kind.SET_MEMBER, item, self.relation))

    def join(self, other, name, args):
        result_relation = tm.mkTerm(Kind.RELATION_TABLE_JOIN, self.relation, other.relation)
        return Relation(name, args=args, relation=result_relation)

    def project(self, indexes, name, args):
        keys = [key for key, _ in self.args]
        indexes = [index if isinstance(index, int) else keys.index(index) for index in indexes]
        relation_project_op = tm.mkOp(Kind.RELATION_PROJECT, *indexes)
        result_relation = tm.mkTerm(relation_project_op, self.relation)
        # result_relation = tm.mkTerm(Kind.RELATION_PROJECT, *indexes, self.relation)
        return Relation(name, args=args, relation=result_relation)

    def __le__(self, other):
        return CVC5_Bool(tm.mkTerm(Kind.SET_SUBSET, self.relation, val(other)))

    def __ge__(self, other):
        return CVC5_Bool(tm.mkTerm(Kind.SET_SUBSET, val(other), self.relation))

    def __eq__(self, other):
        return CVC5_Bool(tm.mkTerm(Kind.EQUAL, val(other), self.relation))

    def __add__(self, other):
        # concat
        result_relation = tm.mkTerm(Kind.SET_UNION, self.relation, val(other))
        return Relation(name="{}+{}".format(self.name, str(val(other))), args=self.args, relation=result_relation)

    def split(self, tight=False):
        rel1 = Relation(name="split1_{}".format(self.name), args=self.args)
        rel2 = Relation(name="split2_{}".format(self.name), args=self.args)
        if tight:
            union_version = rel1 + rel2

            return rel1, rel2, (union_version >= self) & (union_version <= self)
        else:
            return rel1, rel2, (rel1 + rel2) >= self

    def get_relational_class(self):
        if self.relational_class is None:
            def __init__(self, reference=self, tuple=None):
                self.relation = reference.relation
                if tuple is None:
                    for arg_name, arg_type in reference.args:
                        setattr(self, arg_name,
                                new_bounded_var(arg_type, prefix="{}_{}".format(reference.name, arg_name)))
                else:
                    for i in range(len(reference.args)):
                        arg_name, arg_type = reference.args[i]
                        setattr(self, arg_name, tuple[i])

                self.relation = reference
                self.tuple = tm.mkTuple([val(getattr(self, name)) for name, _ in reference.args])

            def member(self):
                return CVC5_Bool(tm.mkTerm(Kind.SET_MEMBER, self.tuple, self.relation.relation))

            def get_args(self):
                return [val(getattr(self, name)) for name, _ in self.relation.args]

            def __eq__(self, other):
                if self is other:
                    return TRUE()
                if type(self) == type(other):
                    return AND([getattr(self, name) == getattr(other, name) for name, _ in self.relation.args])
                else:
                    return FALSE()

            action_class = type(self.name, (),
                                {"__init__": __init__, "member": member, "get_args": get_args, "__eq__": __eq__})
            self.relational_class = action_class
        return self.relational_class

    def new_relational_object(self, tuple=None):
        constructor = self.get_relational_class()
        if tuple is None:
            return constructor()
        else:
            return constructor(tuple=tuple)

    def card(self):
        if self.cardinal is None:
            self.cardinal = CVC5_INT(tm.mkTerm(Kind.SET_CARD, self.relation))
        return self.cardinal

    def subset(self, other):
        return CVC5_Bool(tm.mkTerm(Kind.SET_SUBSET, self.relation, other.relation))

    def nat_constraints(self):
        def inner_constraints(a, relation=self):
            constraints = []
            for arg_name, arg_type in relation.args:
                if arg_type == integer:
                    constraints.append(getattr(a, arg_name) >= 0)

            return AND(constraints)

        if self.nat_cons is None:
            self.nat_cons = forall(self, lambda a, relaton=self: inner_constraints(a, relaton))
        # print(val(self.nat_cons))
        return self.nat_cons


def create_relations(name, args):
    new_Relation = Relation(name, args)
    return new_Relation


def get_relations_types(rel_name):
    relation = Relations.get(rel_name, None)
    return relation.get_relation_types()


'''
For terms
'''


def new_var(name):
    return CVC5_INT(tm.mkVar(integer, name))


def EQ(lhs, rhs):
    return lhs == rhs


def AND(*args):
    c_args = _polymorph_args_to_tuple(args)
    if c_args == [] or args is None:
        return TRUE()
    elif len(c_args) == 1:
        return c_args[0]
    else:
        head = c_args.pop()
        return bool_compare(head, AND(c_args), Kind.AND)


def OR(*args):
    c_args = _polymorph_args_to_tuple(args)
    if c_args == [] or args is None:
        return FALSE()
    elif len(c_args) == 1:
        return c_args[0]
    else:
        head = c_args.pop()
        return bool_compare(head, AND(c_args), Kind.OR)


def NOT(term):
    return CVC5_Bool(tm.mkTerm(Kind.NOT, val(term)))


def IMPLIES(lhs, rhs):
    return bool_compare(lhs, rhs, Kind.IMPLIES)


def ITE(cond, if_true, if_false):
    return cast(tm.mkTerm(Kind.ITE, val(cond), val(if_true), val(if_false)))


def IFF(lhs, rhs):
    return bool_compare(lhs, rhs, Kind.EQUAL)


def XOR(lhs, rhs):
    return bool_compare(lhs, rhs, Kind.XOR)


def int_const(value):
    return tm.mkInteger(value)


def bool_const(value):
    return tm.mkBoolean(value)


def val(term):
    if isinstance(term, CVC_term):
        return term.get_val()
    elif isinstance(term, int):
        return int_const(term)
    elif term is True:
        return TRUE()
    elif term is False:
        return FALSE()
    elif isinstance(term, Relation):
        return term.relation
    else:
        return term


def objectify(lhs, rhs):
    if isinstance(rhs, int):
        rhs = int_const(rhs)
    if isinstance(lhs, int):
        lhs = int_const(lhs)
    return lhs, rhs


def bool_objectify(lhs, rhs):
    if isinstance(rhs, int) or isinstance(rhs, bool):
        rhs = tm.mkTrue() if rhs else tm.mkFalse()
    if isinstance(lhs, int) or isinstance(lhs, bool):
        lhs = tm.mkTrue() if rhs else tm.mkFalse()
    return lhs, rhs


def compare(lhs, rhs, compare):
    lhs, rhs = objectify(lhs, rhs)
    return CVC5_Bool(tm.mkTerm(compare, val(lhs), val(rhs)))


def bool_compare(lhs, rhs, compare):
    lhs, rhs = bool_objectify(lhs, rhs)
    return CVC5_Bool(tm.mkTerm(compare, val(lhs), val(rhs)))


def arithmetic(lhs, rhs, op):
    lhs, rhs = objectify(lhs, rhs)
    return CVC5_INT(tm.mkTerm(op, val(lhs), val(rhs)))


# def tuple_select(tuple_sort, tuple, index):
#     dt = tuple_sort.getDatatype()[index]
#     c = dt.getSelector("__cvc5_tuple_Int_stor_{}").getTerm()

def tuple_select(tuple, index):
    datatype = tuple.getSort().getDatatype()
    constructor = datatype[0]
    selector_term = constructor[index].getTerm()
    element = tm.mkTerm(Kind.APPLY_SELECTOR, selector_term, tuple)
    return element


def LAMBDA(kinds, term_func, make_tuple=False):
    if make_tuple:
        # TODO, this functionality is still being worked on
        tuple_sort = tm.mkTupleSort(*([name_to_sort[k] if isinstance(k, str) else k for k in kinds]))
        new_tuple = tm.mkVar(tuple_sort, "tuple_{}".format(get_new_tuple_counter()))
        vars = [cast(tuple_select(new_tuple, i)) for i in range(len(kinds))]
        term = term_func(*vars)
        return tm.mkTerm(Kind.LAMBDA, tm.mkTerm(Kind.VARIABLE_LIST, new_tuple), val(term))
    else:
        vars = [new_bounded_var(kind) for kind in kinds]
        term = term_func(*vars)
        return tm.mkTerm(Kind.LAMBDA, tm.mkTerm(Kind.VARIABLE_LIST, *([val(v) for v in vars])), val(term))


def _exists(variables, terms):
    return CVC_term(tm.mkTerm(Kind.EXISTS, tm.mkTerm(Kind.VARIABLE_LIST, *([val(v) for v in variables])), val(terms)))


def _forall(variables, terms):
    return CVC_term(tm.mkTerm(Kind.FORALL, tm.mkTerm(Kind.VARIABLE_LIST, *([val(v) for v in variables])), val(terms)))


def cast(term):
    if isinstance(term, int):
        return CVC5_INT(int_const(term))
    elif isinstance(term, bool):
        return term
    elif isinstance(term, Term):
        if term.getSort() == integer:
            return CVC5_INT(term)
        elif term.getSort() == boolean:
            return CVC5_Bool(term)

    print(Term.getSort(term))
    return term


def exists_quantifier(kinds, term_func):
    # in case kinds is a Relation
    if isinstance(kinds, Relation) or \
            (isinstance(kinds, list) and kinds and isinstance(kinds[0], Relation)):
        if isinstance(kinds, Relation):
            instance = kinds.new_relational_object()
            term = term_func(instance)
            return _exists(instance.get_args(), AND(instance.member(), term))
        else:
            instances = [kind.new_relational_object() for kind in kinds]
            term = term_func(*instances)
            args = []
            for instance in instances:
                args.extend(instance.get_args())
            return _exists(args, AND(AND([instance.member() for instance in instances]), term))
    else:
        # in case kinds is a data type
        vars = [new_bounded_var(kind) for kind in kinds]
        term = term_func(*vars)
        return _exists(vars, term)


def exists_relation(kinds, term_func):
    return NOT(forall_relation(kinds, term_func, neg=True))


def forall_quantifier(kinds, term_func):
    if isinstance(kinds, Relation) or \
            (isinstance(kinds, list) and kinds and isinstance(kinds[0], Relation)):
        if isinstance(kinds, Relation):

            instance = kinds.new_relational_object()
            term = term_func(instance)
            return _forall(instance.get_args(), IMPLIES(instance.member(), term))
        else:
            instances = [kind.new_relational_object() for kind in kinds]
            term = term_func(*instances)
            args = []
            for instance in instances:
                args.extend(instance.get_args())
            return _forall(args, IMPLIES(AND([instance.member() for instance in instances]), term))
    else:
        vars = [new_bounded_var(kind) for kind in kinds]
        term = term_func(*vars)
        return _forall(vars, term)


def forall_relation(kinds, term_func, neg=False):
    if isinstance(kinds, Relation) or \
            (isinstance(kinds, list) and kinds and isinstance(kinds[0], Relation)):
        if isinstance(kinds, Relation):
            arguments = kinds.get_relation_types()
            tuple_sort = tm.mkTupleSort(*arguments)
            new_tuple = tm.mkVar(tuple_sort, "tuple_{}".format(get_new_tuple_counter()))
            instance = kinds.new_relational_object(
                tuple=[cast(tuple_select(new_tuple, i)) for i in range(len(arguments))])
            term = term_func(instance)
            if neg:
                lambda_func = tm.mkTerm(Kind.LAMBDA, tm.mkTerm(Kind.VARIABLE_LIST, new_tuple), val(term))
            else:
                lambda_func = tm.mkTerm(Kind.LAMBDA, tm.mkTerm(Kind.VARIABLE_LIST, new_tuple), val(NOT(term)))

            filtered_set = val(
                tm.mkTerm(Kind.SET_FILTER, lambda_func,
                          kinds.relation))
            return is_empty(filtered_set)
        else:
            instances = []
            merged_relation = tm.mkTerm(Kind.RELATION_PRODUCT, *([kind.relation for kind in kinds]))
            new_argument_type = []

            for kind in kinds:
                assert isinstance(kind, Relation)
                argument_types = kind.get_relation_types()
                new_argument_type.extend(argument_types)

            tuple_sort = tm.mkTupleSort(*new_argument_type)
            new_tuple = tm.mkVar(tuple_sort, "tuple_{}".format(get_new_tuple_counter()))
            arguments = [cast(tuple_select(new_tuple, i)) for i in range(len(new_argument_type))]

            current_start = 0
            for kind in kinds:
                current_end = current_start + len(kind.get_relation_types())
                instance = kind.new_relational_object(tuple=arguments[current_start:current_end])
                instances.append(instance)
                current_start = current_end

            term = term_func(*instances)
            if neg:
                lambda_func = tm.mkTerm(Kind.LAMBDA, tm.mkTerm(Kind.VARIABLE_LIST, new_tuple), val(term))
            else:
                lambda_func = tm.mkTerm(Kind.LAMBDA, tm.mkTerm(Kind.VARIABLE_LIST, new_tuple), val(NOT(term)))
            filtered_set = val(
                tm.mkTerm(Kind.SET_FILTER, lambda_func,
                          merged_relation))

            return is_empty(filtered_set)

    assert False


def set_all(kinds, term_func, neg=False):
    if isinstance(kinds, Relation) or \
            (isinstance(kinds, list) and kinds and isinstance(kinds[0], Relation)):
        if isinstance(kinds, Relation):
            arguments = kinds.get_relation_types()
            tuple_sort = tm.mkTupleSort(*arguments)
            new_tuple = tm.mkVar(tuple_sort, "tuple_{}".format(get_new_tuple_counter()))
            instance = kinds.new_relational_object(
                tuple=[cast(tuple_select(new_tuple, i)) for i in range(len(arguments))])
            term = term_func(instance)
            if neg:                
                lambda_func = tm.mkTerm(Kind.LAMBDA, tm.mkTerm(Kind.VARIABLE_LIST, new_tuple), val(NOT(term)))
            else:                
                lambda_func = tm.mkTerm(Kind.LAMBDA, tm.mkTerm(Kind.VARIABLE_LIST, new_tuple), val(term))

            all = val(
                tm.mkTerm(Kind.SET_ALL, lambda_func,
                          kinds.relation))
            return all
        else:
            instances = []
            merged_relation = tm.mkTerm(Kind.RELATION_PRODUCT, *([kind.relation for kind in kinds]))
            new_argument_type = []

            for kind in kinds:
                assert isinstance(kind, Relation)
                argument_types = kind.get_relation_types()
                new_argument_type.extend(argument_types)

            tuple_sort = tm.mkTupleSort(*new_argument_type)
            new_tuple = tm.mkVar(tuple_sort, "tuple_{}".format(get_new_tuple_counter()))
            arguments = [cast(tuple_select(new_tuple, i)) for i in range(len(new_argument_type))]

            current_start = 0
            for kind in kinds:
                current_end = current_start + len(kind.get_relation_types())
                instance = kind.new_relational_object(tuple=arguments[current_start:current_end])
                instances.append(instance)
                current_start = current_end

            term = term_func(*instances)
            if neg:
                lambda_func = tm.mkTerm(Kind.LAMBDA, tm.mkTerm(Kind.VARIABLE_LIST, new_tuple), val(NOT(term)))
            else:                
                lambda_func = tm.mkTerm(Kind.LAMBDA, tm.mkTerm(Kind.VARIABLE_LIST, new_tuple), val(term))
            all = val(
                tm.mkTerm(Kind.SET_ALL, lambda_func,
                          merged_relation))

            return all

    assert False

def set_some(kinds, term_func, neg=False):
    if isinstance(kinds, Relation) or \
            (isinstance(kinds, list) and kinds and isinstance(kinds[0], Relation)):
        if isinstance(kinds, Relation):
            arguments = kinds.get_relation_types()
            tuple_sort = tm.mkTupleSort(*arguments)
            new_tuple = tm.mkVar(tuple_sort, "tuple_{}".format(get_new_tuple_counter()))
            instance = kinds.new_relational_object(
                tuple=[cast(tuple_select(new_tuple, i)) for i in range(len(arguments))])
            term = term_func(instance)
            if neg:                
                lambda_func = tm.mkTerm(Kind.LAMBDA, tm.mkTerm(Kind.VARIABLE_LIST, new_tuple), val(NOT(term)))
            else:                
                lambda_func = tm.mkTerm(Kind.LAMBDA, tm.mkTerm(Kind.VARIABLE_LIST, new_tuple), val(term))

            some = val(
                tm.mkTerm(Kind.SET_SOME, lambda_func,
                          kinds.relation))
            return some
        else:
            instances = []
            merged_relation = tm.mkTerm(Kind.RELATION_PRODUCT, *([kind.relation for kind in kinds]))
            new_argument_type = []

            for kind in kinds:
                assert isinstance(kind, Relation)
                argument_types = kind.get_relation_types()
                new_argument_type.extend(argument_types)

            tuple_sort = tm.mkTupleSort(*new_argument_type)
            new_tuple = tm.mkVar(tuple_sort, "tuple_{}".format(get_new_tuple_counter()))
            arguments = [cast(tuple_select(new_tuple, i)) for i in range(len(new_argument_type))]

            current_start = 0
            for kind in kinds:
                current_end = current_start + len(kind.get_relation_types())
                instance = kind.new_relational_object(tuple=arguments[current_start:current_end])
                instances.append(instance)
                current_start = current_end

            term = term_func(*instances)
            if neg:
                lambda_func = tm.mkTerm(Kind.LAMBDA, tm.mkTerm(Kind.VARIABLE_LIST, new_tuple), val(NOT(term)))
            else:                
                lambda_func = tm.mkTerm(Kind.LAMBDA, tm.mkTerm(Kind.VARIABLE_LIST, new_tuple), val(term))
            some = val(
                tm.mkTerm(Kind.SET_SOME, lambda_func,
                          merged_relation))

            return some

    assert False



class CVC_term:
    def __init__(self, val):
        assert not isinstance(val, CVC_term)
        self.val = val

    def get_val(self):
        return self.val


class CVC5_Bool(CVC_term):

    def __and__(self, other):
        return AND(self, other)

    def __or__(self, other):
        return OR(self, other)

    def __ne__(self, other):
        return XOR(self, other)

    def __eq__(self, other):
        return IFF(self, other)


class CVC5_FreeSort(CVC_term):
    def __eq__(self, other):
        return compare(self, other, Kind.EQUAL)

    def __ne__(self, other):
        return not (self == other)


class CVC5_INT(CVC5_FreeSort):
    def __gt__(self, other):
        return compare(self, other, Kind.GT)

    def __ge__(self, other):
        return compare(self, other, Kind.GEQ)

    def __lt__(self, other):
        return compare(self, other, Kind.LT)

    def __le__(self, other):
        return compare(self, other, Kind.LEQ)

    def __add__(self, other):
        return arithmetic(self, other, Kind.ADD)

    def __radd__(self, other):
        return self.__add__(other)

    def __sub__(self, other):
        return arithmetic(self, other, Kind.SUB)

    def __rsub__(self, other):
        return arithmetic(other, self, Kind.SUB)

    def __mul__(self, other):
        return arithmetic(self, other, Kind.MULT)

    def __rmul__(self, other):
        return arithmetic(self, other, Kind.MULT)

    def __neg__(self):
        return CVC5_INT(tm.mkTerm(Kind.NEG, val(self)))


'''
Helper functions
'''


def TRUE():
    return tm.mkTrue()


def FALSE():
    return tm.mkFalse()


def solve(constraints, output_file=""):
    solver = cvc5.Solver(tm)
    solver.setLogic("HO_ALL")
    setOption(solver, "produce-models", "true")
    setOption(solver, "finite-model-find", "true")
    setOption(solver, "check-models", "true")
    setOption(solver, "sets-ext", "true")
    setOption(solver, "dag-thresh", "0")
    setOption(solver, "uf-lazy-ll", "true")
    setOption(solver, "fmf-bound", "true")
    setOption(solver, "tlimit-per", "100000")

    if output_file:
        out = open(output_file, 'w')
        out.write("(set-logic HO_ALL)\n")
        for o in Options:
            out.write(o + '\n')
        for decl in Decls:
            out.write(decl + '\n')

    for c in constraints:
        solver.assertFormula(val(c))
        if output_file:
            out.write("(assert " + str(val(c)) + ")\n")
        # print(val(c))

    if output_file:
        out.write("(check-sat)\n")

    start = time.time()
    result = solver.checkSat()
    print("trail {}".format(time.time() - start))

    # solver.dump("test.smt2)
    # output
    print("Result     = {}".format(result))
    if result.isSat():
        if output_file:
            out.write("(get-model)\n")
        for r in Relations.values():
            print("{}     = {}".format(r.name, solver.getValue(r.relation)))

    if output_file:
        out.close()

    return result


def find_nat_constraints():
    constraints = []
    for r in Relations.values():
        constraints.append(r.nat_constraints())
    return constraints


# const short cut
def is_empty(r):
    if isinstance(r, Relation):
        relation = r.relation
    else:
        relation = r
    target_sort = Term.getSort(relation)
    return CVC5_Bool(tm.mkTerm(Kind.EQUAL, tm.mkEmptySet(target_sort), relation))


#
# def r_all(r: Relation, func, is_relational_object=False):
#     if is_relational_object:
#         relation_args_types = r.get_relation_types()
#         tuple_sort = tm.mkTupleSort(*relation_args_types)
#         new_tuple = tm.mkVar(tuple_sort, "tuple_{}".format(get_new_tuple_counter()))
#         instance = r.new_relational_object(tuple=new_tuple)
#         term = func(instance)
#         lambda_func = tm.mkTerm(Kind.LAMBDA, tm.mkTerm(Kind.VARIABLE_LIST, new_tuple), val(term))
#         filtered_set = val(
#             tm.mkTerm(Kind.SET_FILTER, lambda_func,
#                       r.relation))
#     else:
#         filtered_set = val(
#             tm.mkTerm(Kind.SET_FILTER, LAMBDA(r.get_relation_types(), func, make_tuple=True),
#                       r.relation))
#     return CVC5_Bool(tm.mkTerm(Kind.EQUAL, r.relation, filtered_set))

def make_tuple(*arg):
    proper_arg = _polymorph_args_to_tuple(arg)
    if len(proper_arg) == 1 and Term.isTupleValue(val(proper_arg[0])):
        return val(proper_arg[0])
    else:
        return tm.mkTuple([val(arg) for arg in proper_arg])


forall = set_all
exists = set_some


def test_relation_map():
    birth = Relation("FATHER", [("parent", integer), ("child", integer)])
    male = Relation("Male", [("person", integer)])
    people = Relation("People", [("person", integer)])
    constrints = []
    constrints.append(exists(male, lambda m: m.person > 5))
    guardian = male.map(lambda m: ITE(m.person > 5,
                                      make_tuple(m.person, 5 + m.person),
                                      make_tuple(m.person, 0)
                                      ),
                        name="guardian",
                        args=[("target", integer), ("guardian", integer)]
                        )
    l1, l2, split_constraints = guardian.split(tight=True)

    constrints.append(split_constraints)
    solve(constrints)


def test_conditional_map():
    male = Relation("Male", [("person", integer)])
    constraints = []
    gurandian = male.filter(lambda m: m.person < 20, name="teen").map(lambda m: make_tuple(2 * m.person),
                                                                      name="guardian", args=male.args)
    constraints.append(gurandian.contains(make_tuple(38)))
    solve(constraints)


def test_join():
    parent = Relation("Parent", [("parent", integer), ("child", integer), ("witness", integer)])
    male = Relation("Male", [("person", integer)])
    male_parent = parent.join(male, "male_parent", [("parent", integer), ("child", integer)])
    constraints = []
    # constraints.append(male_parent.contains(make_tuple(6)))
    constraints.append(parent.contains(make_tuple(1, 5, 2)))
    constraints.append(parent.contains(make_tuple(2, 6, 3)))
    constraints.append(male.contains(make_tuple(2)))
    solve(constraints)

def test_project():
    parent = Relation("Parent", [("parent", integer), ("child", integer)])
    constraints = []
    constraints.append(parent.contains(make_tuple(1, 5)))
    constraints.append(parent.contains(make_tuple(2, 6)))
    father = parent.project(["child"], "p", [("father", integer)])
    solve(constraints)
if __name__ == "__main__":
    test_join()
    C = Relation("C", [("parent", integer), ("child", integer)])
    forall(C, lambda p: p.parent > 0)
    # test_conditional_map()
    # test_relation_map()
    # test_join()
    # t = exists(["int", "int"], lambda a, b: a > b)
    # k = forall(["int"], lambda a: exists(["int"], lambda b: b > a))
    # solver = cvc5.Solver(tm)
    # solver.assertFormula(val(k))
    # result = solver.checkSat()
    # print(result)
    #
    # print(val(k))
    # var1 = new_var("int1")
    # var2 = new_var("int2")
    # print(val((var1 > 5) != (var2 < 3)))
    # birth = Relation("FATHER", [("parent", integer), ("child", integer)])
    # male = Relation("Male", [("person", integer)])
    # people = Relation("People", [("person", integer)])
    # print(val(birth.card() > 5))
    # father_child_pair = birth.new_relational_object()
    # print(val(father_child_pair.member()))
    # print(val(exists(birth, lambda b: forall(birth, lambda c: b.parent > c.child))))
    # print(val(forall(birth, lambda b: b.parent > b.child)))
    # print(val(male.subset(people)))
    #
    # print(val(LAMBDA(["int"], lambda a: a > 5)))
    # print(people.relation)
    #
    # set_filtering = val(
    #     tm.mkTerm(Kind.SET_FILTER, LAMBDA(["int", "int"], lambda a, b: (a > 5) & (b < 3), make_tuple=True),
    #               birth.relation))
    # print(val(is_empty(set_filtering)))
    # filtering_constraint = forall_relation(birth, lambda b: (b.parent > 5) & (b.child < 3))
    #
    # new_map_filter = forall_relation([birth, people], lambda b, p: IMPLIES(b.parent > 5, p.person > (b.child + 3)))
    #
    # print(val(filtering_constraint))
    # b_m = tm.mkTerm(Kind.RELATION_PRODUCT, birth.relation, male.relation)
    # print(Term.getSort(b_m))
    # solver.assertFormula(val(filtering_constraint))
    #
    # # check map
    # new_tuple = make_tuple([1, 2, 4])
    # print(new_tuple)
    # new_relation =birth.map(lambda b: b.parent + b.child, args=[("sum", int)])
    # print(new_relation.relation)
