/** -*- C++ -*-
 * 
 * entry point of ic3ia
 * author: Alberto Griggio <griggio@fbk.eu>
 * 
 * This file is part of ic3ia.
 * Copyright (C) 2015 Fondazione Bruno Kessler.
 *
 * ic3ia is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * ic3ia is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with ic3ia.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "ic3.h"
#include <iostream>
#include <stdlib.h>
#include <signal.h>


using namespace vtsa2015;


IC3 *the_ic3 = NULL;

void handle_interrupt(int signo)
{
    if (the_ic3) {
        the_ic3->print_stats();
    }
    std::cout << "interrupted by signal " << signo << "\nunknown" << std::endl;
    //_Exit(signo);
    exit(signo);
}


/**
 * read a transition system from a file in VMT format. VMT is an extension of
 * the SMT-LIBv2 format for specifying fair symbolic transition systems, and
 * for specifying properties over the transition system.
 *
 * VMT exploits the capability offered by the SMT2 language of attaching
 * annotations to terms and formulas in order to specify the components of the
 * transition system and the properties to verify.  More specifically, the
 * following annotations are used:
 * 
 * - ":next name" is used to represent state variables. For each variable x in
 *   the model, the VMT file contains a pair of variables, x^c and x^n,
 *   representing respectively the current and next version of x.  The two
 *   variables are linked by annotating x^c with the attribute ":next x^n".
 *   All the variables that are not in relation with another by means of
 *   a ":next" attribute are considered inputs.
 * 
 * - ":init true" is used to specify the formula for the initial states of the
 *   model.  This formula should contain neither next-state variables nor
 *   input variables. (The dummy value "true" in the annotation is needed
 *   because the current SMT2 standard requires annotations to always have an
 *   associated value.)
 * 
 * - ":trans true" is used to specify the formula for the transition relation.
 * 
 * - ":invar-property idx" is used to specify invariant properties.  The
 *   non-negative integer "idx" is a unique identifier for the property. Only
 *   single-property files are supported by this function.
 *
 * - ":predicate true" is used to annotate a predicate used for computing the
 *   initial abstraction.
 * 
 * In a VMT file, only annotated terms and their sub-terms are
 * meaningful. Any other term is ignored.  Moreover, only the following
 * commands are allowed to occur in VMT files:
 * 
 *   set-logic set-option declare-sort define-sort declare-fun define-fun
 *   
 * (For convenience, an additional "(assert true)" command is
 * allowed to appear at the end of the file.)
 */
bool read_ts(const Options &opts, TransitionSystem &ts, TermList &preds)
{
    msat_term *terms;
    char **annots;
    size_t n;

    struct File {
        File(): file(stdin) {}
        ~File()
        {
            if (file && file != stdin) {
                fclose(file);
            }
        }

        FILE *file;
    };
    File f;
    
    if (!opts.filename.empty()) {
        f.file = fopen(opts.filename.c_str(), "r");
    }
    if (!f.file) {
        return false;
    }
    
    int err = msat_annotated_list_from_smtlib2_file(ts.get_env(), f.file, &n,
                                                    &terms, &annots);

    if (err) {
        return false;
    }

    TermMap statevars;
    msat_term init, trans, prop;
    preds.clear();

    for (size_t i = 0; i < n; ++i) {
        std::string key(annots[2*i]);
        msat_term t = terms[i];
        if (key == "init") {
            init = t;
        } else if (key == "trans") {
            trans = t;
        } else if (key == "invar-property") {
            prop = t;
        } else if (key == "next") {
            std::string val(annots[2*i+1]);
            if (val.length() && val[0] == '|') {
                val = val.substr(1, val.length()-2);
            }
            msat_decl d = msat_find_decl(ts.get_env(), val.c_str());
            if (MSAT_ERROR_DECL(d)) {
                d = msat_declare_function(ts.get_env(), val.c_str(),
                                          msat_term_get_type(terms[i]));
            }
            msat_term n = msat_make_constant(ts.get_env(), d);
            statevars[t] = n;
        } else if (key == "predicate" &&
                   msat_is_bool_type(ts.get_env(), msat_term_get_type(t)) &&
                   !msat_term_is_boolean_constant(ts.get_env(), t)) {
            preds.push_back(t);
        }
    }

    ts.initialize(statevars, init, trans, prop);

    msat_free(terms);
    for (size_t i = 0; i < n; ++i) {
        msat_free(annots[2*i]);
        msat_free(annots[2*i+1]);
    }
    msat_free(annots);

    if (opts.nopreds) {
        preds.clear();
    }

    logger(1) << "parsed system with " << statevars.size() << " state variables"
              << endlog;

    return true;
}


Options get_options(int argc, const char **argv)
{
    Options ret;
    
    bool ok = true;
    for (int i = 1; i < argc; ++i) {
        std::string a(argv[i]);
        if (a == "-v") {
            if (i+1 < argc) {
                std::istringstream buf(argv[i+1]);
                int val;
                if (buf >> val) {
                    ret.verbosity = val;
                    set_verbosity(val);
                } else {
                    ok = false;
                    break;
                }
                ++i;
            } else {
                ok = false;
                break;
            }
        } else if (a == "-w") {
            ret.witness = true;
        } else if (a == "-p") {
            ret.nopreds = true;
        } else if (a == "-t") {
            if (i+1 < argc) {
                ret.trace = argv[i+1];
                ++i;
            } else {
                ok = false;
                break;
            }
        } else if (a == "-r") {
            if (i+1 < argc) {
                std::istringstream buf(argv[i+1]);
                int val;
                if (buf >> val) {
                    ret.seed = val;
                } else {
                    ok = false;
                    break;
                }
                ++i;
            } else {
                ok = false;
                break;
            }
        } else if (a == "-s") {
            ret.stack = true;
        } else if (a == "-h" || a == "-help" || a == "--help") {
            std::cout << "USAGE: " << argv[0] << " [OPTIONS] FILENAME.vmt"
                      << "\n\n   -v N : set verbosity level"
                      << "\n   -w : print witness"
                      << "\n   -p : do not use initial predicates (if any)"
                      << "\n   -t NAME : dump SMT queries into NAME.main.smt2 "
                      << "and NAME.itp.smt2"
                      << "\n   -r VAL : set random seed to VAL "
                      << "(0 to disable [default])"
                      << "\n   -s : stack-based proof obligation management"
                      << std::endl;
            exit(0);
            break;
        } else if (a[0] != '-' && ret.filename.empty()) {
            ret.filename = a;
        } else {
            ok = false;
            break;
        }
    }
    if (!ok) {
        std::cout << "Error in parsing command-line options (use -h for help)"
                  << std::endl;
        exit(1);
    }

    return ret;
}


int main(int argc, const char **argv)
{
    Options opts = get_options(argc, argv);
    
    msat_config cfg = msat_create_config();
    msat_env env = msat_create_env(cfg);
    EnvDeleter del_env(env);
    msat_destroy_config(cfg);

    TransitionSystem ts(env);
    TermList preds;
    
    if (!read_ts(opts, ts, preds)) {
        std::cout << "ERROR reading input" << std::endl;
        return 1;
    }

    if (!opts.trace.empty()) {
        logger(1) << "dumping SMT traces to " << opts.trace << ".main.smt2"
                  << " and " << opts.trace << ".itp.smt2" << endlog;
    }

    IC3 ic3ia(ts, opts);

    signal(SIGINT, handle_interrupt);
    the_ic3 = &ic3ia;

    ic3ia.set_initial_predicates(preds);
    bool safe = ic3ia.prove();

    if (opts.witness) {
        std::vector<TermList> wit;
        if (!ic3ia.witness(wit)) {
            std::cout << "ERROR computing witness" << std::endl;
        } else {
            std::cout << (safe ? "invariant" : "counterexample") << "\n";
            for (size_t i = 0; i < wit.size(); ++i) {
                TermList &w = wit[i];
                std::cout << ";; " << (safe ? "clause " : "step ") << i
                          << "\n" << (safe ? "(or" : "(and") << "\n";
                for (msat_term t : w) {
                    std::cout << "  " << logterm(env, t) << "\n";
                }
                std::cout << ")\n";
            }
            std::cout.flush();
        }
    }

    ic3ia.print_stats();

    std::cout << (safe ? "safe" : "unsafe") << std::endl;
    return 0;
}