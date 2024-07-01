from CVC5_wrapper.cvc_wrapper import *
from utility import _polymorph_args_to_tuple


def op_str_sleec(op):
    if op == ">":
        return lambda a, b: a > b
    elif op == ">=":
        return lambda a, b: a >= b
    elif op == "<=":
        return lambda a, b: a <= b
    elif op == "<":
        return lambda a, b: a < b
    elif op == "+":
        return lambda a, b: a + b
    elif op == "-":
        return lambda a, b: a - b
    elif op == "*":
        return lambda a, b: a * b
    elif op == "=":
        return lambda a, b: a == b
    elif op == "<>":
        return lambda a, b: a != b
    else:
        assert False


def op_str_sleec_bool(op):
    if op == "and":
        return AND
    elif op == "or":
        return OR
    elif op == "=>":
        return IMPLIES
    else:
        assert False


def unless(*args, reference=None):
    # if no consequence, then the defeater is on the condition
    cum_condition = True
    constraints = []
    processed = _polymorph_args_to_tuple(args)
    for i in range(len(processed) - 1, -1, -1):
        condition, action = processed[i]
        if reference:
            if i == 0:
                pass
            else:
                d = reference.defeater[i - 1]
                condition = condition
                action = action

        constraints.append(IMPLIES(AND(cum_condition, condition), action))
        cum_condition = AND(cum_condition, NOT(condition))
    return AND(constraints)


# TODO, convert to xor
def otherwise(cond, primary, alt):
    return IMPLIES(cond, OR(primary, alt))


M = None


def complie_measure(MEASURE):
    global M
    M = MEASURE


def when_assert(trigger, action, rule_condition=None, reference=None):
    t_trigger = t_condition = None

    if rule_condition is None:
        return exists(trigger, lambda t, t_trigger=t_trigger: exists(M, lambda m: AND(t.time == m.time,
                                                                                      NOT(action(t, m))
                                                                                      )))
    else:
        return exists(trigger,
                      lambda t, t_trigger=t_trigger, t_condition=t_condition: exists(M, lambda m: AND(t.time == m.time,
                                                                                                      AND(
                                                                                                          rule_condition(
                                                                                                              t, m),
                                                                                                          NOT(action(t,
                                                                                                                     m)))
                                                                                                      )))


def when(trigger, action, rule_condition=None,  reference=None):
    t_trigger = t_condition = None

    if rule_condition is None:
        return forall(trigger, lambda t, t_trigger=t_trigger: exists(M, lambda m: AND(t.time == m.time,
                                                                                      action(t, m)
                                                                                      )))
    else:
        return forall(trigger,
                      lambda t, t_trigger=t_trigger, t_condition=t_condition: exists(M, lambda m: AND(t.time == m.time,
                                                                                                      OR(
                                                                                                          NOT(rule_condition(
                                                                                                              t, m)),
                                                                                                          action(t, m))
                                                                                                      )))


def when_concern(trigger, action, rule_condition=None, reference=None):
    if reference:
        t_trigger = reference.trigger
        t_condition = reference.condition
    else:
        t_trigger = t_condition = None

    if rule_condition is None:
        return exists(trigger, lambda t, t_trigger=t_trigger: exists(M, lambda m: AND(EQ(t.time, m.time),
                                                                                      action(t, m)
                                                                                      )))
    else:
        return exists(trigger,
                      lambda t, t_trigger=t_trigger, t_condition=t_condition: exists(M,
                                                                                     lambda m: AND(EQ(t.time, m.time),
                                                                                                   AND(
                                                                                                       rule_condition(
                                                                                                           t, m),
                                                                                                       action(t, m))
                                                                                                   )))


def when_premise(trigger, rule_condition,  reference=None):

    if rule_condition is None:
        return exists([trigger, M], lambda t, m: EQ(t.time, m.time))
    else:
        return exists([trigger, M],
                      lambda t, m: AND(EQ(t.time, m.time), rule_condition(t, m)))


def valid(t, rule_condition):
    if rule_condition is None:
        return TRUE()
    else:
        return exists(M, lambda m, t=t, cond=rule_condition: AND(EQ(m.time, t.time), cond(t, m)))


def last(last_t, trigger, rule_condition):
    return forall(trigger, lambda t, last_t=last_t, cond=rule_condition:
    IMPLIES(valid(t, cond), last_t.time >= t.time))


def when_last_trigger(trigger, rule_condition, reference=None):
    return IMPLIES(exists(trigger,
                          lambda t, trigger=trigger, rule_condition=rule_condition: valid(t, rule_condition)),
                   exists(trigger, lambda t_last,
                                          trigger=trigger,
                                          rule_condition=rule_condition:
                   AND(valid(t_last,
                             rule_condition),
                       last(t_last, trigger,
                            rule_condition)
                       )
                          )
                   )


def happen_within(target_class, reference, start, end, constraints=None, ref=None):
    def make_constraint(t, reference=reference, start=start, end=end, ref=ref):
        lower_limit = t.time >= reference.time + start
        upper_limit = t.time <= reference.time + end

        if ref and ref.limit:
            lower_limit = t.time >= reference.time + start
            upper_limit = t.time <= reference.time + end
            lower_limit = lower_limit
            upper_limit = upper_limit

            res = AND(upper_limit, lower_limit)
        else:
            res = AND(upper_limit, lower_limit)
        return res

    def make_constraint_unlimited(t, reference=reference, ref=ref):
        term = t.time >= reference.time
        res = term
        return res

    if ref is not None:
        event = ref.event
    else:
        event = None

    if end >= 0:
        if constraints is None:
            return exists(target_class, lambda t: make_constraint(t, reference, start, end, ref))
        else:
            return exists(target_class,
                          lambda t: AND(make_constraint(t, reference, start, end, ref), constraints(t, reference)))
    else:
        if constraints is None:
            return exists(target_class, lambda t: make_constraint_unlimited(t, reference, ref))
        else:
            return exists(target_class,
                          lambda t: AND(make_constraint_unlimited(t, reference, ref), constraints(t, reference)))


class Concern():
    def __init__(self, trigger, action, rule_condition=None, reference=None, next=None):
        self.concern = when_concern(trigger, action, rule_condition=rule_condition, reference=reference)
        self.next = next

    def get_concern(self):
        if not self.next:
            return self.concern
        else:
            return AND(self.next.get_concern(), self.concern)


def em_until(start_trigger, end_trigger, start_condition, end_condition, inv, reference):
    if reference:
        t_start_trigger = reference.start_trigger
        t_start_condition = reference.start_condition
        t_end_trigger = reference.end_trigger
        t_end_condition = reference.end_condition
    else:
        t_start_trigger = t_start_condition = t_end_condition = t_end_condition = None

    if end_trigger is not None:
        if t_start_condition is None and t_end_condition is None:
            # cond 1, end cond never happens
            cond1 = forall(start_trigger, lambda st, end_trigger=end_trigger,
                                                 t_start_trigger=t_start_trigger, t_end_trigger=t_end_condition,
                                                 inv=inv:
            OR(
                AND(forall(end_trigger, lambda et, t_start_trigger=t_start_trigger, t_end_trigger=t_end_condition:
                et.time < st.time),
                    forall(M, lambda m, inv=inv: IMPLIES(m.time >= st.time, inv(m))
                           )),
                exists(end_trigger, lambda eet, end_trigger=end_trigger, inv=inv:
                AND(eet.time >= st.time, AND(forall(end_trigger, lambda net:
                NOT(AND(net.time >= st.time, net.time < eet.time))),
                                             forall(M, lambda m, inv=inv, reference=reference:
                                             IMPLIES(AND(
                                                 m.time >= st.time,
                                                 m.time < eet.time),
                                                 inv(m)
                                             )))
                    )
                       )))
            return cond1
        else:
            print("unsupported yet")
            assert False
    else:
        print("unsupported yet")
        assert False


def em_timed(start_trigger, end_duration, inv, reference):
    return forall(start_trigger, lambda st, end_durantion=end_duration, inv=inv, reference=reference:
    exists(M, lambda cur_m: AND(EQ(cur_m.time, st.time),
                                exists(M, lambda m, cur_m=cur_m, st=st, end_durantion=end_durantion, inv=inv,
                                                 reference=reference:
                                AND(EQ(m.time, st.time + end_duration(cur_m)),
                                    forall(M, lambda m_prime, m=m, st=st, inv=inv, reference=reference:
                                    IMPLIES(
                                        AND(m_prime.time >= st.time, m_prime.time < m.time), inv(m_prime)
                                    )
                                           ))
                                       )))
                  )


class TimedEMRelation:

    def __init__(self, start_trigger, end_duration, inv, reference):
        self.start_trigger = start_trigger
        self.end_duration = end_duration
        self.inv = inv
        self.reference = reference

        self.encoded = em_timed(self.start_trigger, self.end_duration, self.inv, self.reference)

    def clear(self):
        if self.encoded:
            self.encoded.clear()

    def encode(self, refresh=False):
        if self.encoded and not refresh:
            return self.encoded
        else:
            self.encoded = em_timed(self.start_trigger, self.end_duration, self.inv, self.reference)

            return self.encoded


class UntilEMRelation:

    def __init__(self, start_trigger, end_trigger, start_condition, end_condition, inv, reference):
        self.start_trigger = start_trigger
        self.end_trigger = end_trigger
        self.start_condition = start_condition
        self.end_condition = end_condition
        self.inv = inv
        self.reference = reference
        self.encoded = em_until(start_trigger, end_trigger, start_condition, end_condition, inv, reference)

    def clear(self):
        if self.encoded:
            self.encoded.clear()

    def encode(self, refresh=False):
        if self.encoded and not refresh:
            return self.encoded
        else:
            self.encoded = em_until(self.start_trigger, self.end_trigger,
                                    self.start_condition, self.end_condition, self.inv, self.reference)
            return self.encoded


class WhenRule:

    def __init__(self, trigger, action, neg_action, rule_condition=None, reference=None):
        self.rule = when(trigger, action, rule_condition=rule_condition, reference=reference)
        self.neg_rule = when_assert(trigger, neg_action, rule_condition=rule_condition, reference=reference)
        self.premise = when_premise(trigger, rule_condition=rule_condition, reference=reference)
        self.last_trigger = when_last_trigger(trigger, rule_condition, reference)

    def get_rule(self):
        return self.rule

    def get_neg_rule(self):
        return self.neg_rule

    def get_premise(self):
        return self.premise

    def encode(self):
        return val(self.get_rule())


def process_event(op_str, lhs, rhs, reference):
    if op_str == "witness":
        return forall(lhs, lambda l, rhs=rhs: exists(rhs, lambda r, l=l, reference=reference: EQ(r.time, l.time)))
    # elif op_str == "exclusion":
    #     return forall(lhs, lambda l, rhs=rhs: NOT(exist(rhs, lambda r: EQ(r.time, l.time))), reference=reference)
    elif op_str == "equal":
        return AND(forall(lhs, lambda l, rhs=rhs, reference=reference: exists(rhs,
                                                                              lambda r, l=l, reference=reference: EQ(
                                                                                  r.time, l.time))),
                   forall(rhs, lambda r, lhs=lhs: exists(lhs, lambda l, r=r, reference=reference: EQ(r.time, l.time))))
    elif op_str == "mutualExclusive":
        return AND(forall(lhs, lambda l, rhs=rhs, reference=reference: NOT(
            exists(rhs, lambda r, l=l, reference=reference: EQ(r.time, l.time)))),
                   forall(rhs,
                          lambda r, lhs=lhs: NOT(exists(lhs, lambda l, r=r, reference=reference: EQ(r.time, l.time)))))
    elif op_str == "happenBefore":
        return forall(rhs, lambda r, lhs=lhs, reference=reference:
        exists(lhs, lambda l, r=r, reference=reference: l.time < r.time))
    else:
        print("unsupport rel: {}".format(op_str))
        assert False


class EventRelation:
    def __init__(self, op, lhs, rhs, reference=None):
        self.op = op
        self.lhs = lhs
        self.rhs = rhs
        self.reference = reference
        self.encoded = None
        # self.encoded = process_event(self.op, self.lhs, self.rhs, self.reference)

    def clear(self):
        if self.encoded:
            self.encoded.clear()

    def encode(self, refresh=False):
        if self.encoded and not refresh:
            return self.encoded
        else:
            self.encoded = process_event(self.op, self.lhs, self.rhs, self.reference)
            return self.encoded


class MeasureRelation:
    def __init__(self, expr, reference=None):
        self.expr = expr
        self.reference = reference
        self.encoded = None

    def clear(self):
        if self.encoded:
            self.encoded.clear()

    def encode(self, refresh=False):
        if self.encoded and not refresh:
            return self.encoded
        else:
            self.encoded = forall(M,
                                  lambda m, self=self:
                                  self.expr(m))
            return self.encoded


class Causation:

    def __init__(self, cause, effect, reference=None):
        self.cause = cause
        self.effect = effect
        self.reference = reference
        self.encoded = None

    def clear(self):
        if self.encoded:
            self.encoded.clear()

    def encode(self, refresh=False):
        if self.encoded and not refresh:
            return self.encoded
        else:
            self.encoded = forall(M,
                                  lambda m, self=self:
                                  IMPLIES(self.effect(m),
                                          exists(self.cause, lambda c, m=m, self=self:
                                          EQ(c.time, m.time)))
                                  )
            return self.encoded


class Effect:

    def __init__(self, cause, effect, reference=None):
        self.cause = cause
        self.effect = effect
        self.reference = reference
        self.encoded = None

    def clear(self):
        if self.encoded:
            self.encoded.clear()

    def encode(self, refresh=False):
        if self.encoded and not refresh:
            return self.encoded
        else:
            self.encoded = forall(self.cause,
                                  lambda c, self=self:
                                  exists(M, lambda m, c=c, self=self:
                                  AND(EQ(c.time, m.time),
                                      self.effect(m)
                                      )
                                         ))
            return self.encoded
