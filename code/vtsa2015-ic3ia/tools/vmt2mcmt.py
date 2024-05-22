import sys, re
from mathsat import *
import vmt


def main():
    env = msat_create_env()
    model = vmt.read(env, sys.stdin)

    def is_var(t):
        return msat_term_arity(t) == 0 and \
               msat_decl_get_tag(env, msat_term_get_decl(t)) == \
               MSAT_TAG_UNKNOWN and not msat_term_is_number(env, t)

    subst = {}
    curidx = [1]
    def visit(e, t, pre):
        if t in subst:
            return MSAT_VISIT_SKIP
        if not pre:
            if is_var(t):
                idx = curidx[0]
                curidx[0] += 1
                d = msat_declare_function(env, 'x!%d' % idx,
                                          msat_term_get_type(t))
                tt = msat_make_constant(env, d)
                subst[t] = tt
            else:
                d = msat_term_get_decl(t)
                args = [subst[msat_term_get_arg(t, i)]
                        for i in range(msat_term_arity(t))]
                tt = msat_make_term(e, d, args)
                subst[t] = tt
        return MSAT_VISIT_PROCESS
    msat_visit_term(env, model.init, visit)
    msat_visit_term(env, model.trans, visit)
    for p in model.props:
        msat_visit_term(env, p, visit)
    for (c, n) in model.statevars:
        msat_visit_term(env, c, visit)
        msat_visit_term(env, n, visit)

    nextmap = dict((subst[k], subst[v]) for (k, v) in model.statevars)
    curmap = dict((subst[n], subst[c]) for (c, n) in model.statevars)
    statevars = [p[0] for p in model.statevars]
    
    def visit(e, t, pre):
        if pre and is_var(t) and t not in curmap and t not in nextmap:
            nextmap[t] = None
            statevars.append(t)
        return MSAT_VISIT_PROCESS
    msat_visit_term(env, subst[model.trans], visit)
    
    def pr(s): sys.stdout.write(s.replace('.def_', 'def!'))
    
    pr('(define-state-type state (\n')
    def tpstr(t):
        if msat_is_bool_type(env, t): return 'Bool'
        elif msat_is_rational_type(env, t): return 'Real'
        elif msat_is_integer_type(env, t): return 'Int'
        else: assert False
    for c in statevars:
        name = str(c)
        orig = ""
        if c in subst:
            orig = name
            name = str(subst[c])
        pr('(%s %s) ;; %s\n' % (name, tpstr(msat_term_get_type(c)), orig))
    pr('))\n\n')

    pr('(define-states init state\n')
    pr(msat_to_smtlib2_term(env, subst[model.init]))
    pr(')\n\n')

    pr('(define-transition trans state\n')
    cache = {}
    def visit(e, t, pre):
        if not pre:
            if t in nextmap:
                tt = msat_make_constant(
                    e, msat_declare_function(
                    e, 'state.' + str(t), msat_term_get_type(t)))
            elif t in curmap:
                tt = msat_make_constant(
                    e, msat_declare_function(
                    e, 'next.' + str(curmap[t]), msat_term_get_type(t)))
            else:
                d = msat_term_get_decl(t)
                args = [cache[msat_term_get_arg(t, i)]
                        for i in range(msat_term_arity(t))]
                tt = msat_make_term(e, d, args)
            cache[t] = tt
        return MSAT_VISIT_PROCESS
    msat_visit_term(env, subst[model.trans], visit)
    trans = cache[subst[model.trans]]
    pr(msat_to_smtlib2_term(env, trans))
    pr(')\n\n')

    pr('(define-transition-system T state init trans)\n\n')

    for p in model.props:
        pr('(query T %s)\n\n' % msat_to_smtlib2_term(env, subst[p]))

    msat_destroy_env(env)


if __name__ == '__main__':
    main()
