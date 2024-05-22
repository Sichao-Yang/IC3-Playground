from mathsat import *
import copy


class VmtModel(object):
    def __init__(self, statevars, init, trans, props, params=None, preds=None):
        self.init = init
        self.trans = trans
        self.props = props
        self.params = set(params) if params else set()
        self.preds = set(preds) if preds else set()
        self.statevars = statevars
        self.nextvars = set(p[1] for p in statevars)
        self.nextmap = dict(statevars)

    def add_state_var(self, v, vn):
        self.nextmap[v] = vn
        self.statevars.append((v, vn))
        self.nextvars.add(vn)

    def next(self, env, v):
        cache = copy.copy(self.nextmap)
        def visit(e, t, pre):
            if t in cache:
                return MSAT_VISIT_SKIP
            if not pre:
                d = msat_term_get_decl(t)
                args = [cache[msat_term_get_arg(t, i)]
                        for i in range(msat_term_arity(t))]
                tt = msat_make_term(e, d, args)
                cache[t] = tt
            return MSAT_VISIT_PROCESS
        msat_visit_term(env, v, visit)
        return cache[v]

# end of class VmtModel


def parse(env, src):
    val = msat_annotated_list_from_smtlib2(env, src.read())
    assert val is not None
    terms, annots = val

    def unquote(n):
        if n.startswith('|'):
            n = n[1:-1]
        return n

    init = msat_make_true(env)
    trans = msat_make_true(env)
    props = []
    statevars = []
    for i, t in enumerate(terms):
        key = annots[2*i]
        if key == "init":
            init = msat_make_and(env, init, t)
        elif key == "trans":
            trans = msat_make_and(env, trans, t)
        elif key == "invar-property":
            props.append((int(annots[2*i+1]), t))
        elif key == "next":
            name = unquote(annots[2*i+1])
            d = msat_find_decl(env, name)
            if MSAT_ERROR_DECL(d):
                d = msat_declare_function(env, name, msat_term_get_type(t))
            n = msat_make_constant(env, d)
            statevars.append((t, n))
    props.sort()
    if not props:
        props = [(0, msat_make_true(env))]
    return VmtModel(statevars, init, trans, [p[1] for p in props])

read = parse


def write(env, model, out):
    terms = [model.init, model.trans] + model.props + \
            [s[0] for s in model.statevars]
    annots = ['init', 'true', 'trans', 'true']
    for i, p in enumerate(model.props):
        annots.append('invar-property')
        annots.append(str(i))
    for (c, n) in model.statevars:
        annots.append('next')
        d = msat_term_get_decl(n)
        annots.append('|%s|' % msat_decl_get_name(d))
    for p in model.preds:
        annots.append('predicate')
        annots.append('true')
        terms.append(p)
    out.write(msat_annotated_list_to_smtlib2(env, terms, annots))
