/****************************************************************************************[Solver.C]
MiniSat -- Copyright (c) 2003-2005, Niklas Een, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include "SMTSubsumption/minisat/Solver.h"
#include "SMTSubsumption/minisat/Sort.h"
#include <cmath>
#include <limits>

using namespace SMTSubsumption::Minisat;

#define TRACE_SOLVER 0
#define DEBUG_STREAM_ENABLED TRACE_SOLVER
#include "SMTSubsumption/cdebug.hpp"


//=================================================================================================
// Helper functions:


bool removeWatch(vec<GClause>& ws, GClause elem)    // Pre-condition: 'elem' must exists in 'ws' OR 'ws' must be empty.
{
    if (ws.size() == 0) return false;     // (skip lists that are already cleared)
    int j = 0;
    for (; ws[j] != elem  ; j++) assert(j < ws.size());
    assert(ws[j] == elem);
    for (; j < ws.size()-1; j++) ws[j] = ws[j+1];
    ws.pop();
    return true;
}


//=================================================================================================
// Operations on clauses:


/*_________________________________________________________________________________________________
|
|  newClause : (ps : const vec<Lit>&) (learnt : bool)  ->  [void]
|
|  Description:
|    Allocate and add a new clause to the SAT solvers clause database. If a conflict is detected,
|    the 'ok' flag is cleared and the solver is in an unusable state (must be disposed).
|
|  Input:
|    ps     - The new clause as a vector of literals.
|    learnt - Is the clause a learnt clause? For learnt clauses, 'ps[0]' is assumed to be the
|             asserting literal. An appropriate 'enqueue()' operation will be performed on this
|             literal. One of the watches will always be on this literal, the other will be set to
|             the literal with the highest decision level.
|
|  Effect:
|    Activity heuristics are updated.
|________________________________________________________________________________________________@*/
void Solver::newClause(const vec<Lit>& ps_, bool learnt)
{
    if (!ok) return;

#if TRACE_SOLVER
    std::cerr << "newClause:";
    for (Lit l : ps_) {
      std::cerr << " " << l;
    }
    std::cerr << std::endl;
#endif

    vec<Lit>& qs = newClause_qs;
    if (!learnt) {
        assert(decisionLevel() == 0);
        ps_.copyTo(qs);             // Make a copy of the input vector.

        // Remove duplicates:
        sortUnique(qs);

        // Check if clause is satisfied:
        for (int i = 0; i < qs.size()-1; i++) {
            if (qs[i] == ~qs[i+1])
                return;
        }
        for (int i = 0; i < qs.size(); i++) {
            if (value(qs[i]) == l_True)
                return;
        }

        // Remove false literals:
        // TODO: in our use case this will never happen! (no, it can happen due to theory propagation)
        int i, j;
        for (i = j = 0; i < qs.size(); i++)
            if (value(qs[i]) != l_False)
                qs[j++] = qs[i];
        qs.shrink(i - j);
    }
    const vec<Lit>& ps = learnt ? ps_ : qs; // 'ps' is now the (possibly) reduced vector of literals.

    if (ps.size() == 0) {
        ok = false;
    }
    else if (ps.size() == 1) {
        CDEBUG("NEW UNIT: " << ps[0]);
        // NOTE: If enqueue takes place at root level, the assignment will be lost in incremental use (it doesn't seem to hurt much though).
        if (!enqueue(ps[0])) {
            ok = false;
            CDEBUG("\t=> ROOT CONFLICT");
        } else {
            CDEBUG("\t=> OK");
        }
    }
    else if (ps.size() == 2) {
        // Create special binary clause watch:
        watches[index(~ps[0])].push(GClause_new(ps[1]));
        watches[index(~ps[1])].push(GClause_new(ps[0]));

        if (learnt) {
            check(enqueue(ps[0], GClause_new(~ps[1])));   // TODO why? because learnt clause is unit under current assignment; and the remaining literal is always the first in learned clauses. see also doc comment on this method...
            IF_MINISAT_STATS(stats.learnts_literals += ps.size());
        } else {
            IF_MINISAT_STATS(stats.clauses_literals += ps.size());
        }
        n_bin_clauses++;
    }
    else {
        // Allocate clause:
        Clause* c = Clause_new(learnt, ps);

        if (learnt) {
            // Put the second watch on the literal with highest decision level:
            int     max   = level[var(ps[1])];
            int     max_i = 1;
            for (int i = 2; i < ps.size(); i++) {
                if (level[var(ps[i])] > max) {
                    max   = level[var(ps[i])];
                    max_i = i;
                }
            }
            (*c)[1]     = ps[max_i];
            (*c)[max_i] = ps[1];

            // Bump, enqueue, store clause:
            IF_ENABLE_CLAUSE_DELETION(claBumpActivity(c));         // (newly learnt clauses should be considered active)
            check(enqueue((*c)[0], GClause_new(c)));
            learnts.push(c);
            IF_MINISAT_STATS(stats.learnts_literals += c->size());
        } else {
            // Store clause:
            clauses.push(c);
            IF_MINISAT_STATS(stats.clauses_literals += c->size());
        }
        // Watch clause:
        watches[index(~(*c)[0])].push(GClause_new(c));
        watches[index(~(*c)[1])].push(GClause_new(c));
    }
}

void Solver::addClause_unchecked(const vec<Lit>& ps)
{
    assert(decisionLevel() == 0);

    if (!ok) return;

#if TRACE_SOLVER
    std::cerr << "addClause_unchecked:";
    for (Lit l : ps_) {
      std::cerr << " " << l;
    }
    std::cerr << std::endl;
#endif

#if VDEBUG
    // Even if this is called "unchecked", we still do the checks in debug mode.
    // ps is sorted without duplicates
    for (int i = 0; i < ps.size()-1; ++i) {
        assert(ps[i] < ps[i+1]);
    }
    // clause is not yet satisfied
    // and there are no false literals in the clause
    for (int i = 0; i < ps.size()-1; ++i) {
        assert(ps[i] != ~ps[i+1]);
    }
    for (int i = 0; i < ps.size(); ++i) {
        assert(value(ps[i]) != l_True);
        assert(value(ps[i]) != l_False);
        assert(value(ps[i]) == l_Undef);
    }
#endif

    if (ps.size() == 0) {
        ok = false;
    }
    else if (ps.size() == 1) {
        CDEBUG("NEW UNIT: " << ps[0]);
        // NOTE: If enqueue takes place at root level, the assignment will be lost in incremental use (it doesn't seem to hurt much though).
        if (!enqueue(ps[0])) {
            ok = false;
            CDEBUG("\t=> ROOT CONFLICT");
        } else {
            CDEBUG("\t=> OK");
        }
    }
    else if (ps.size() == 2) {
        // Create special binary clause watch:
        watches[index(~ps[0])].push(GClause_new(ps[1]));
        watches[index(~ps[1])].push(GClause_new(ps[0]));

        IF_MINISAT_STATS(stats.clauses_literals += ps.size());
        n_bin_clauses++;
    }
    else {
        // Allocate clause:
        Clause* c = Clause_new(false, ps);

        // Store clause:
        clauses.push(c);
        IF_MINISAT_STATS(stats.clauses_literals += c->size());

        // Watch clause:
        watches[index(~(*c)[0])].push(GClause_new(c));
        watches[index(~(*c)[1])].push(GClause_new(c));
    }
}

void Solver::addConstraint_AtMostOne(const vec<Lit>& ps_)
{
    if (!ok) return;

#if TRACE_SOLVER
    std::cerr << "addConstraint_AtMostOne:";
    for (Lit l : ps_) {
      std::cerr << " " << l;
    }
    std::cerr << std::endl;
#endif

    assert(decisionLevel() == 0);

    // Make a copy of the input vector.
    vec<Lit>& ps = addConstraint_AtMostOne_ps;
    ps_.copyTo(ps);

    // Remove duplicates
    sortUnique(ps);  // TODO: we can move this to precondition and convert this check into an assertion

    // Check if constraint is already violated:
    int num_true = 0;
    for (Lit p : ps) {
      // std::cerr << "value(" << p << ") = " << value(p) << std::endl;
      if (value(p) == l_True) {
        num_true += 1;
        if (num_true > 1) {
          // std::cerr << "AtMostOne constraint already violated" << std::endl;
          ok = false;
          return;
        }
      }
    }
    assert(num_true == 0 || num_true == 1);
    // If one is already true, we can already set all other literals to false.
    if (num_true == 1) {
        CDEBUG("Can propagate AtMostOne constraint already during creation");
        // std::cerr << "Can propagate AtMostOne constraint already during creation" << std::endl;;
        for (Lit p : ps) {
            if (value(p) == l_Undef) {
                check(enqueue(~p));
            }
        }
    }

    // Remove false literals
    int i, j;
    for (i = j = 0; i < ps.size(); i++) {
      if (value(ps[i]) != l_False)
        ps[j++] = ps[i];
    }
    ps.shrink(i - j);

    // 'ps' is now the (possibly) reduced vector of literals.

    if (ps.size() <= 1) {
      // nothing to do
    }
    else if (ps.size() == 2) {
      // In this case, we create a binary clause instead,
      // because AtMostOne(p, q) == ~p \/ ~q

      // Create special binary clause watch
      watches[index(ps[0])].push(GClause(~ps[1]));
      watches[index(ps[1])].push(GClause(~ps[0]));

      IF_MINISAT_STATS(stats.clauses_literals += 2);
      n_bin_clauses++;
    }
    else {
      // Allocate and store constraint
      AtMostOne* c = AtMostOne::new_from_literals(ps);
      at_most_one_constraints.push(c);
      IF_MINISAT_STATS(stats.clauses_literals += c->size());  // TODO

      // Set up watches for the constraint
      // AtMostOne is equivalent to a set of binary clauses
      // (~p \/ ~q for all p,q in ps)
      // When any one of the literals in ps becomes true, the others will be propagated to false.
      // so we need to watch all literals in ps.
      for (Lit l : ps) {
        watches[index(l)].push(GClause(c));
      }
    }
}

void Solver::addConstraint_AtMostOne_unchecked(const vec<Lit>& ps)
{
    if (!ok) return;

#if TRACE_SOLVER
    std::cerr << "addConstraint_AtMostOne_unchecked:";
    for (Lit l : ps_) {
      std::cerr << " " << l;
    }
    std::cerr << std::endl;
#endif

    assert(decisionLevel() == 0);

#if VDEBUG
    // Even if this is called "unchecked", we still do the checks in debug mode.
    // ps is sorted without duplicates
    for (int i = 0; i < ps.size()-1; ++i) {
        assert(ps[i] < ps[i+1]);
    }
    // All literals are undefined
    for (int i = 0; i < ps.size(); ++i) {
        assert(value(ps[i]) == l_Undef);
    }
#endif

    if (ps.size() <= 1) {
      // nothing to do
    }
    else if (ps.size() == 2) {
      // In this case, we create a binary clause instead,
      // because AtMostOne(p, q) == ~p \/ ~q

      // Create special binary clause watch
      watches[index(ps[0])].push(GClause(~ps[1]));
      watches[index(ps[1])].push(GClause(~ps[0]));

      IF_MINISAT_STATS(stats.clauses_literals += 2);
      n_bin_clauses++;
    }
    else {
      // Allocate and store constraint
      AtMostOne* c = AtMostOne::new_from_literals(ps);
      at_most_one_constraints.push(c);
      IF_MINISAT_STATS(stats.clauses_literals += c->size());  // TODO

      // Set up watches for the constraint
      // AtMostOne is equivalent to a set of binary clauses
      // (~p \/ ~q for all p,q in ps)
      // When any one of the literals in ps becomes true, the others will be propagated to false.
      // so we need to watch all literals in ps.
      for (Lit l : ps) {
        watches[index(l)].push(GClause(c));
      }
    }
}


// Disposes a clauses and removes it from watcher lists.
// NOTE! Low-level; does NOT change the 'clauses' and 'learnts' vector.
//
void Solver::remove(Clause* c, bool just_dealloc)
{
    if (!just_dealloc) {
        if (c->size() == 2) {
            removeWatch(watches[index(~(*c)[0])], GClause_new((*c)[1]));
            removeWatch(watches[index(~(*c)[1])], GClause_new((*c)[0]));
        } else {
            removeWatch(watches[index(~(*c)[0])], GClause_new(c));
            removeWatch(watches[index(~(*c)[1])], GClause_new(c));
        }
    }

#if MINISAT_STATS
    if (c->learnt()) stats.learnts_literals -= c->size();
    else             stats.clauses_literals -= c->size();
#endif

    xfree(c);
}


// Can assume everything has been propagated! (esp. the first two literals are != l_False, unless
// the clause is binary and satisfied, in which case the first literal is true)
// Returns True if clause is satisfied (will be removed), False otherwise.
//
bool Solver::simplify(Clause* c) const
{
    assert(decisionLevel() == 0);
    for (int i = 0; i < c->size(); i++) {
        if (value((*c)[i]) == l_True)
            return true;
    }
    return false;
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision_var' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar()
{
    int     index;
    index = nVars();
    watches     .push();          // (list for positive literal)
    watches     .push();          // (list for negative literal)
    reason      .push(GClause_NULL);
    assigns     .push(toInt(l_Undef));
    level       .push(-1);
    activity    .push(0);
    order       .newVar();
    analyze_seen.push(0);
    return index;
}

// Create n new SAT variables in the solver.
void Solver::newVars(int n)
{
    // int new_nVars = nVars() + n;
    // watches.growTo(2*new_nVars);
    // reason.growTo(new_nVars, GClause_NULL);
    // assigns.growTo(new_nVars, toInt(l_Undef));
    // level.growTo(new_nVars, -1);
    // activity.growTo(new_nVars, 0);
    //   order.newVar();  // needs to be called only once
    // analyze_seen.growTo(new_nVars, 0);
    // assert(new_nVars == nVars());

    // TODO: there's a bug in the above bulk addition code
    for (int i = 0; i < n; ++i) {
        newVar();
    }
}

// Returns FALSE if immediate conflict.
bool Solver::assume(Lit p)
{
    trail_lim.push(trail.size());
    return enqueue(p);
}


// Revert to the state at given level.
void Solver::cancelUntil(int level)
{
    if (decisionLevel() > level) {
        for (int c = trail.size()-1; c >= trail_lim[level]; c--) {
            Var     x  = var(trail[c]);
            assigns[x] = toInt(l_Undef);
            reason [x] = GClause_NULL;
            order.undo(x);
        }
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);
        tqhead = trail.size();
        qhead = trail.size();
        subst_theory.backjump(level);
    }
}


//=================================================================================================
// Major methods:


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|
|  Description:
|    Analyze conflict and produce a reason clause.
|
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|
|  Effect:
|    Will undo part of the trail, upto but not beyond the assumption of the current decision level.
|________________________________________________________________________________________________@*/
void Solver::analyze(Clause* _confl, vec<Lit>& out_learnt, int& out_btlevel)
{
#if TRACE_SOLVER
    std::cerr << "ANALYZE: _confl = ";
    if (_confl) { std::cerr << *_confl; } else { std::cerr << "NULL"; }
    std::cerr << std::endl;
#endif
    assert(out_learnt.size() == 0);
    assert(decisionLevel() > root_level);
    for (int i = 0; i < analyze_seen.size(); ++i) {
      assert(analyze_seen[i] == 0);
    }
    assert(std::all_of(analyze_seen.begin(), analyze_seen.end(), [](char c){ return c == 0; }));

    GClause confl = GClause_new(_confl);
    vec<char>&     seen  = analyze_seen;
    int            pathC = 0;
    Lit            p     = lit_Undef;  // undefined in the first iteration

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    out_btlevel = 0;
    int index = trail.size()-1;
    do {
        assert(confl != GClause_NULL);          // (otherwise should be UIP)

        Clause& c = *[&]() {
            if (confl.isLit()) {
                assert(p != lit_Undef);  // otherwise, we would access analyze_tmpbin[0] in the loop below
                (*analyze_tmpbin)[1] = confl.lit();
                return analyze_tmpbin;
            } else {
                assert(confl.isClause());
                return confl.clause();
            }
        }();

#if ENABLE_CLAUSE_DELETION
        if (c.learnt())
            claBumpActivity(&c);
#endif

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++) {
            Lit q = c[j];
            if (!seen[var(q)] && level[var(q)] > 0) {
                varBumpActivity(q);
                seen[var(q)] = 1;
                if (level[var(q)] == decisionLevel()) {
                    pathC++;
                } else {
                    out_learnt.push(q);
                    out_btlevel = max(out_btlevel, level[var(q)]);
                }
            }
        }

        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason[var(p)];
        // NOTE: first literal of reason is ignored (it's the one that has been propagated)
        if (confl.isClause() && !confl.isNull()) { assert( (*confl.clause())[0] == p ); }
        seen[var(p)] = 0;
        pathC--;
    } while (pathC > 0);
    out_learnt[0] = ~p;

    int i, j;
    if (expensive_ccmin) {  // TODO decide if we want to keep this
        // Simplify conflict clause (a lot):
        //
        uint min_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            min_level |= 1 << (level[var(out_learnt[i])] & 31);         // (maintain an abstraction of levels involved in conflict)

        out_learnt.copyTo(analyze_toclear);
        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason[var(out_learnt[i])] == GClause_NULL || !analyze_removable(out_learnt[i], min_level))
                out_learnt[j++] = out_learnt[i];
        // TODO: check if we get any reduced clauses from this (caveat: may be help with harder instances)
    } else {

        // Simplify conflict clause (a little):
        //
        out_learnt.copyTo(analyze_toclear);
        for (i = j = 1; i < out_learnt.size(); i++){
            GClause r = reason[var(out_learnt[i])];
            if (r == GClause_NULL) {
                out_learnt[j++] = out_learnt[i];
            } else if (r.isLit()) {
                Lit q = r.lit();
                if (!seen[var(q)] && level[var(q)] != 0)
                    out_learnt[j++] = out_learnt[i];
            } else {
                Clause& c = *r.clause();
                for (int k = 1; k < c.size(); k++) {
                    if (!seen[var(c[k])] && level[var(c[k])] != 0) {
                        out_learnt[j++] = out_learnt[i];
                        break;
                    }
                }
            }
        }
    }

    IF_MINISAT_STATS(stats.max_literals += out_learnt.size());
    out_learnt.shrink(i - j);
    IF_MINISAT_STATS(stats.tot_literals += out_learnt.size());

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)
}


// Check if 'p' can be removed. 'min_level' is used to abort early if visiting literals at a level that cannot be removed.
//
bool Solver::analyze_removable(Lit p, uint min_level)
{
    assert(reason[var(p)] != GClause_NULL);
    analyze_stack.clear(); analyze_stack.push(p);
    int top = analyze_toclear.size();
    while (analyze_stack.size() > 0){
        assert(reason[var(analyze_stack.last())] != GClause_NULL);
        GClause r = reason[var(analyze_stack.last())]; analyze_stack.pop();
        Clause& c = r.isLit() ? ((*analyze_tmpbin)[1] = r.lit(), *analyze_tmpbin)
                              : *r.clause();
        for (int i = 1; i < c.size(); i++){
            Lit p = c[i];
            if (!analyze_seen[var(p)] && level[var(p)] != 0){
                if (reason[var(p)] != GClause_NULL && ((1 << (level[var(p)] & 31)) & min_level) != 0){
                    analyze_seen[var(p)] = 1;
                    analyze_stack.push(p);
                    analyze_toclear.push(p);
                }else{
                    for (int j = top; j < analyze_toclear.size(); j++)
                        analyze_seen[var(analyze_toclear[j])] = 0;
                    analyze_toclear.shrink(analyze_toclear.size() - top);
                    return false;
                }
            }
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (confl : Clause*) (skip_first : bool)  ->  [void]
|
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    'root_level' is allowed to point beyond end of trace (useful if called after conflict while
|    making assumptions). If 'skip_first' is TRUE, the first literal of 'confl' is  ignored (needed
|    if conflict arose before search even started).
|________________________________________________________________________________________________@*/
// TODO remove this method?
void Solver::analyzeFinal(Clause* confl, bool skip_first)
{
    // -- NOTE! This code is relatively untested. Please report bugs!
    conflict.clear();
    if (root_level == 0) return;

    vec<char>&     seen  = analyze_seen;
    for (int i = skip_first ? 1 : 0; i < confl->size(); i++){
        Var     x = var((*confl)[i]);
        if (level[x] > 0)
            seen[x] = 1;
    }

    int     start = (root_level >= trail_lim.size()) ? trail.size()-1 : trail_lim[root_level];
    for (int i = start; i >= trail_lim[0]; i--){
        Var     x = var(trail[i]);
        if (seen[x]){
            GClause r = reason[x];
            if (r == GClause_NULL){
                assert(level[x] > 0);
                conflict.push(~trail[i]);
            }else{
                if (r.isLit()){
                    Lit p = r.lit();
                    if (level[var(p)] > 0)
                        seen[var(p)] = 1;
                }else{
                    Clause& c = *r.clause();
                    for (int j = 1; j < c.size(); j++)
                        if (level[var(c[j])] > 0)
                            seen[var(c[j])] = 1;
                }
            }
            seen[x] = 0;
        }
    }
}


/*_________________________________________________________________________________________________
|
|  basicEnqueue : (p : Lit) (from : Clause*)  ->  [bool]
|
|  Description:
|    Puts a new fact on the propagation queue as well as immediately updating the variable's value.
|    Should a conflict arise, FALSE is returned.
|    Should not be called directly, use 'enqueue' instead.
|
|  Input:
|    p    - The fact to enqueue
|    from - [Optional] Fact propagated from this (currently) unit clause. Stored in 'reason[]'.
|           Default value is NULL (no reason).
|
|  Output:
|    TRUE if fact was enqueued without conflict, FALSE otherwise.
|________________________________________________________________________________________________@*/
bool Solver::basicEnqueue(Lit p, GClause from)
{
    CDEBUG("ENQUEUE: " << p << " (current value: " << value(p) << ")");
    if (value(p) != l_Undef) {
        return (value(p) != l_False);
    } else {
        assigns[var(p)] = toInt(lbool(!sign(p)));
        level  [var(p)] = decisionLevel();
        reason [var(p)] = from;
        trail.push(p);
        return true;
    }
}

// enqueue = basicEnqueue + theoryPropagate
bool Solver::enqueue(Lit p, GClause from)
{
    bool no_conflict = basicEnqueue(p, from);
    if (no_conflict) {
        // NOTE on why we do theory propagation as part of enqueue and not in the propagate() loop:
        // - we don't want to iterate through watchlists multiple times
        // - but if we handle the watch completely, we may get multiple enqueues, and these may already contain a theory conflict
        //   (unless our specific problem structure somehow prevents this -- but I don't see how it would; and relying on that seems fragile anyways)
        // - so we cannot simply choose in each iteration what we do,
        //   we need to theory-propagate after *each* call to enqueue
        // - Also note that we may already get a conflict on decision level 0 if we add two theory-conflicting unit clauses.
        theoryPropagate();
    }
    return no_conflict;
}


void Solver::theoryPropagate()
{
    CDEBUG("PROPAGATE THEORY");

    assert(!subst_theory.empty());
    assert(qhead <= tqhead);

    // Do all outstanding theory propagations
    while (tqhead < trail.size())
    {
        Lit q = trail[tqhead++];  // 'q' is enqueued fact to theory-propagate

        CDEBUG("PROPAGATE THEORY for q = " << q);

        if (q.isPositive())
        {
            bool enabled =
                subst_theory.enable(var(q), decisionLevel(), [this, q](Lit propagated_lit, GClause reason) {
                    CDEBUG("tpropagated: " << propagated_lit);
                    bool no_conflict = basicEnqueue(propagated_lit, reason);
                    assert(no_conflict);
                    return true;
                });
            assert(enabled);
        }
    }
}

/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise NULL.
|
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
Clause* Solver::propagate()
{
    CDEBUG("PROPAGATE");

    assert(tqhead == trail.size());  // theory is always fully propagated before regular propagation

    Clause *confl = nullptr;
    while (qhead < trail.size()) {
        assert(confl == nullptr);
        assert(tqhead == trail.size());  // theory is always fully propagated before regular propagation
        IF_MINISAT_STATS(stats.propagations++);
        IF_MINISAT_STATS(simpDB_props--);

        ASS_EQ(tqhead, trail.size());  // all theory stuff is propagated, now we turn to the watch lists
        Lit p = trail[qhead++]; // 'p' is enqueued fact to propagate.

        CDEBUG("PROPAGATE p = " << p);

        // TODO:
        // note additional invariant:
        // - Reasons are still only lits/clauses
        // - Only watches can be an AtMostOne constraint
        // Should probably split GClause into two classes?
        // - class Reason ... can hold literal or clause
        // - class Watcher ... can hold literal, clause, or AtMostOne constraint

        vec<GClause>& ws = watches[index(p)];
        GClause* i = ws.begin();
        GClause* j = ws.begin();
        GClause* end = ws.end();
        while (i != end) {
            CDEBUG("PROPAGATE WATCHER: " << *i);
            if (i->isLit()) {
                if (!enqueue(i->lit(), GClause_new(p))) {
                    if (decisionLevel() == 0) {   // TODO: is that right? should we compare to root_level instead?  (probably not. If we're not at the root level, we stay "ok")
                        ok = false;
                    }
                    confl = propagate_tmpbin;
                    (*confl)[1] = ~p;
                    (*confl)[0] = i->lit();

                    qhead = trail.size();
                    // Copy the remaining watches:
                    while (i != end)  // TODO: can skip loop if i==j. (should check if that helps though)
                        *(j++) = *(i++);
                    assert(i == end);
                } else {
                    // Watcher is a literal, meaning it comes from a binary clause which is not stored anywhere else
                    // => keep it in the watchlist.
                    *(j++) = *(i++);
                }
            } else if (i->isClause()) {
                Clause& c = *i->clause(); i++;
                assert(c.size() > 2);
                // Make sure the false literal is data[1]:
                Lit false_lit = ~p;
                if (c[0] == false_lit) {
                    c[0] = c[1];
                    c[1] = false_lit;
                }

                assert(c[1] == false_lit);

                // If 0th watch is true, then clause is already satisfied.
                Lit   first = c[0];
                lbool val   = value(first);
                if (val == l_True) {
                    *(j++) = GClause_new(&c);
                } else {
                    // Look for new watch:
                    for (int k = 2; k < c.size(); k++) {
                        if (value(c[k]) != l_False) {
                            c[1] = c[k]; c[k] = false_lit;
                            watches[index(~c[1])].push(GClause_new(&c));
                            goto FoundWatch;
                        }
                    }

                    // Did not find watch -- clause is unit under assignment:
                    *j++ = GClause_new(&c);
                    if (!enqueue(first, GClause_new(&c))) {
                        if (decisionLevel() == 0)
                            ok = false;
                        confl = &c;
                        qhead = trail.size();
                        // Copy the remaining watches:
                        while (i != end) {
                            *(j++) = *(i++);
                        }
                        assert(i == end);
                    }
                  FoundWatch:;
                }
            } else {
              assert(i->isAtMostOne());
              AtMostOne& c = *i->atMostOne();
              // propagate all other literals to false
              bool got_conflict = false;
              for (int k = 0; k < c.size(); ++k) {
                if (c[k] != p) {
                  got_conflict = !enqueue(~c[k], GClause(p));
                  if (got_conflict) {
                    if (decisionLevel() == 0) {
                        ok = false;
                    }
                    confl = propagate_tmpbin;
                    (*confl)[1] = ~p;
                    (*confl)[0] = ~c[k];
                    qhead = trail.size();
                    break;
                  }
                }
              }
              if (got_conflict) {
                // Copy the remaining watches
                while (i != end)  // TODO: can skip loop if i==j. (should check if that helps though)
                  *(j++) = *(i++);
                assert(i == end);
              } else {
                // Copy the current AtMostOne constraint
                *(j++) = *(i++);
              }
            }
        }  // while (i != end)
        ws.shrink(i - j);
    }  // while (qhead < trail.size())

#if TRACE_SOLVER
    std::cerr << "PROPAGATE DONE: confl = ";
    if (confl) { std::cerr << *confl; } else { std::cerr << "NULL"; }
    std::cerr << std::endl;
#endif

    return confl;
}


#if ENABLE_CLAUSE_DELETION
/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt
{
    bool operator()(Clause *x, Clause *y) { return x->size() > 2 && (y->size() == 2 || x->activity() < y->activity()); }
};
void Solver::reduceDB()
{
    int     i, j;
    double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

    sort(learnts, reduceDB_lt());
    for (i = j = 0; i < learnts.size() / 2; i++){
        if (learnts[i]->size() > 2 && !locked(learnts[i]))
            remove(learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    for (; i < learnts.size(); i++){
        if (learnts[i]->size() > 2 && !locked(learnts[i]) && learnts[i]->activity() < extra_lim)
            remove(learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    learnts.shrink(i - j);
}
#endif


/*_________________________________________________________________________________________________
|
|  simplifyDB : [void]  ->  [bool]
|
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
void Solver::simplifyDB()
{
    if (!ok) return;    // GUARD (public method)
    assert(decisionLevel() == 0);

    if (propagate() != NULL){
        ok = false;
        return; }

#if MINISAT_STATS
    if (nAssigns() == simpDB_assigns || simpDB_props > 0)   // (nothing has changed or performed a simplification too recently)
        return;
#else
    if (nAssigns() == simpDB_assigns)   // (nothing has changed or performed a simplification too recently)
        return;
#endif

    // Clear watcher lists:
    for (int i = simpDB_assigns; i < nAssigns(); i++){
        Lit           p  = trail[i];
        vec<GClause>& ws = watches[index(~p)];
        for (int j = 0; j < ws.size(); j++)
            if (ws[j].isLit())
                if (removeWatch(watches[index(~ws[j].lit())], GClause_new(p)))  // (remove binary GClause from "other" watcher list)
                    n_bin_clauses--;
        watches[index( p)].clear(true);
        watches[index(~p)].clear(true);
    }

    // Remove satisfied clauses:
    for (int type = 0; type < 2; type++){
        vec<Clause*>& cs = type ? learnts : clauses;
        int     j  = 0;
        for (int i = 0; i < cs.size(); i++){
            if (!locked(cs[i]) && simplify(cs[i]))  // (the test for 'locked()' is currently superfluous, but without it the reason-graph is not correctly maintained for decision level 0)
                remove(cs[i]);
            else
                cs[j++] = cs[i];
        }
        cs.shrink(cs.size()-j);
    }

    simpDB_assigns = nAssigns();
    IF_MINISAT_STATS(simpDB_props = stats.clauses_literals + stats.learnts_literals);   // (shouldn't depend on 'stats' really, but it will do for now)
}


/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (nof_learnts : int) (params : const SearchParams&)  ->  [lbool]
|
|  Description:
|    Search for a model the specified number of conflicts, keeping the number of learnt clauses
|    below the provided limit. NOTE! Use negative value for 'nof_conflicts' or 'nof_learnts' to
|    indicate infinity.
|
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int nof_conflicts, int nof_learnts, const SearchParams& params)
{
    if (!ok) return l_False;    // GUARD (public method)
    assert(root_level == decisionLevel());

    IF_MINISAT_STATS(stats.starts++);
    int     conflictC = 0;
    var_decay = 1 / params.var_decay;
    cla_decay = 1 / params.clause_decay;
    model.clear();

    for (;;) {
        Clause* confl = propagate();
        if (confl != NULL){
            // CONFLICT

            IF_MINISAT_STATS(stats.conflicts++);
            conflictC++;
            vec<Lit>    learnt_clause;
            int         backtrack_level;
            if (decisionLevel() == root_level){
                // Contradiction found:
                analyzeFinal(confl);
                return l_False; }
            analyze(confl, learnt_clause, backtrack_level);
            cancelUntil(max(backtrack_level, root_level));
            newClause(learnt_clause, true);
            if (learnt_clause.size() == 1) level[var(learnt_clause[0])] = 0;    // (this is ugly (but needed for 'analyzeFinal()') -- in future versions, we will backtrack past the 'root_level' and redo the assumptions)
            varDecayActivity();
            IF_ENABLE_CLAUSE_DELETION(claDecayActivity());

        }else{
            // NO CONFLICT

            // TODO: in the 300-million pigeonhole-like example, we're faster without restarts
            // if (nof_conflicts >= 0 && conflictC >= nof_conflicts){
            //     // Reached bound on number of conflicts:
            //     progress_estimate = progressEstimate();
            //     cancelUntil(root_level);
            //     return l_Undef; }

            if (decisionLevel() == 0) {
                // Simplify the set of problem clauses:
                simplifyDB();
                assert(ok);
            }

#if ENABLE_CLAUSE_DELETION
            if (nof_learnts >= 0 && learnts.size()-nAssigns() >= nof_learnts)
                // Reduce the set of learnt clauses:
                reduceDB();
#endif

            // New variable decision:
            IF_MINISAT_STATS(stats.decisions++);
            Var next = order.select(params.random_var_freq);

            if (next == var_Undef) {
                // Model found:
                model.growTo(nVars());
                for (int i = 0; i < nVars(); i++) model[i] = value(i);
                cancelUntil(root_level);
                return l_True;
            }

            // NOTE: decisions should always do the positive choice first, because this triggers lots of propagations
            check(assume(Lit(next)));
        }
    }
}


// Return search-space coverage. Not extremely reliable.
//
double Solver::progressEstimate()
{
    double  progress = 0;
    double  F = 1.0 / nVars();
    for (int i = 0; i < nVars(); i++)
        if (value(i) != l_Undef)
            progress += pow(F, level[i]);
    return progress / nVars();
}


// Divide all variable activities by 1e100.
//
void Solver::varRescaleActivity()
{
    for (int i = 0; i < nVars(); i++)
        activity[i] *= 1e-100;
    var_inc *= 1e-100;
}


#if ENABLE_CLAUSE_DELETION
// Divide all constraint activities by 1e100.
//
void Solver::claRescaleActivity()
{
    for (int i = 0; i < learnts.size(); i++)
        learnts[i]->activity() *= 1e-20;
    cla_inc *= 1e-20;
}
#endif


/*_________________________________________________________________________________________________
|
|  solve : (assumps : const vec<Lit>&)  ->  [bool]
|
|  Description:
|    Top-level solve. If using assumptions (non-empty 'assumps' vector), you must call
|    'simplifyDB()' first to see that no top-level conflict is present (which would put the solver
|    in an undefined state).
|________________________________________________________________________________________________@*/
bool Solver::solve(const vec<Lit>& assumps)
{
    if (!ok) return false;

    simplifyDB();

    SearchParams    params(default_params);
    double  nof_conflicts = 100;
    double  nof_learnts   = nClauses() / 3;
    lbool   status        = l_Undef;

    // Perform assumptions:
    root_level = assumps.size();
    for (int i = 0; i < assumps.size(); i++){
        Lit p = assumps[i];
        assert(var(p) < nVars());
        if (!assume(p)){
            GClause r = reason[var(p)];
            if (r != GClause_NULL){
                Clause* confl;
                if (r.isLit()){
                    confl = propagate_tmpbin;
                    (*confl)[1] = ~p;
                    (*confl)[0] = r.lit();
                }else
                    confl = r.clause();
                analyzeFinal(confl, true);
                conflict.push(~p);
            }else
                conflict.clear(),
                conflict.push(~p);
            cancelUntil(0);
            return false; }
        Clause* confl = propagate();
        if (confl != NULL){
            analyzeFinal(confl), assert(conflict.size() > 0);
            cancelUntil(0);
            return false; }
    }
    assert(root_level == decisionLevel());

    // Search:
    if (verbosity >= 1){
        reportf("==================================[MINISAT]===================================\n");
        reportf("| Conflicts |     ORIGINAL     |              LEARNT              | Progress |\n");
        reportf("|           | Clauses Literals |   Limit Clauses Literals  Lit/Cl |          |\n");
        reportf("==============================================================================\n");
    }

    while (status == l_Undef){
        if (verbosity >= 1) {
            #if MINISAT_STATS
            reportf("| %9d | %7d %8d | %7d %7d %8d %7.1f | %6.3f %% |\n", (int)stats.conflicts, nClauses(), (int)stats.clauses_literals, (int)nof_learnts, nLearnts(), (int)stats.learnts_literals, (double)stats.learnts_literals/nLearnts(), progress_estimate*100);
            #else
            reportf("| --------- | %7d -------- | %7d %7d -------- ------- | %6.3f %% |\n", nClauses(), (int)nof_learnts, nLearnts(), progress_estimate*100);
            #endif
        }
        status = search((int)nof_conflicts, (int)nof_learnts, params);
        nof_conflicts *= 1.5;
        nof_learnts   *= 1.1;
    }
    if (verbosity >= 1) {
        reportf("------------------------------------------------------------------------------\n");
        #if MINISAT_STATS
        reportf("| %9d | %7d %8d | %7d %7d %8d %7.1f | %6.3f %% |\n", (int)stats.conflicts, nClauses(), (int)stats.clauses_literals, (int)nof_learnts, nLearnts(), (int)stats.learnts_literals, (double)stats.learnts_literals/nLearnts(), progress_estimate * 100);
        #else
        reportf("| --------- | %7d -------- | %7d %7d -------- ------- | %6.3f %% |\n", nClauses(), (int)nof_learnts, nLearnts(), progress_estimate*100);
        #endif
        reportf("==============================================================================\n");
    }

    cancelUntil(0);
    return status == l_True;
}
