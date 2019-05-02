#include "ForwardSubsumptionDemodulation.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/LiteralMiniIndex.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/MLMatcher.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Sorts.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"
#include "Lib/ScopeGuard.hpp"
#include "Lib/STL.hpp"
#include "Lib/STLAllocator.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include <array>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using namespace Kernel;
using namespace Lib;
using namespace Inferences;
using namespace Saturation;


void ForwardSubsumptionDemodulation::attach(SaturationAlgorithm* salg)
{
  CALL("ForwardSubsumptionDemodulation::attach");
  ForwardSimplificationEngine::attach(salg);

  auto index_type = getOptions().forwardSubsumptionDemodulationUseSeparateIndex() ? FSD_SUBST_TREE : FW_SUBSUMPTION_SUBST_TREE;
  _index.request(salg->getIndexManager(), index_type);

  _preorderedOnly = false;  // TODO: might add an option for this like in forward demodulation
  _performRedundancyCheck = getOptions().demodulationRedundancyCheck();

  testSomeStuff();  // TODO: for debugging, to be removed later
}

void ForwardSubsumptionDemodulation::detach()
{
  CALL("ForwardSubsumptionDemodulation::detach");
  _index.release();
  ForwardSimplificationEngine::detach();
}



namespace TermBuilder
{

class TermBuilder
{
  public:
    TermBuilder(Term* t)
      : t{t}
    { }

    TermBuilder(TermList t)
      : t{t}
    { }

    operator TermList() const
    {
      return t;
    }

  private:
    TermList t;
};

class LiteralBuilder
{
  public:
    LiteralBuilder(Literal* lit)
      : lit{lit}
    { }

    operator Literal*() const
    {
      return lit;
    }

  private:
    Literal* lit;
};

TermBuilder var(unsigned i)
{
  return {TermList(i, false)};
}

TermList term(TermBuilder tb)
{
  return tb;
}

TermList term(Term* t)
{
  return TermList(t);
}

TermList term(TermList t)
{
  return t;
}

TermBuilder operator+(TermBuilder const& t1, TermBuilder const& t2)
{
  unsigned const fn = env.signature->getInterpretingSymbol(Theory::INT_PLUS);
  return {Term::create2(fn, t1, t2)};
}

// problematic! (type is too general)
template <typename T1, typename T2>
LiteralBuilder operator<(T1 t1, T2 t2)
{
  unsigned const pred = env.signature->getInterpretingSymbol(Theory::INT_LESS);
  return {Literal::create2(pred, true, term(t1), term(t2))};
}

LiteralBuilder operator!(LiteralBuilder const& l)
{
  return {Literal::complementaryLiteral(l)};
}

template <unsigned Arity>
class FnBuilder
{
  public:
    FnBuilder(unsigned fn)
      : fn{fn}
    { }

    // Args may contain values of types TermBuilder, Term*, and TermList (also mixed)
    template <typename...Args, typename std::enable_if<sizeof...(Args) == Arity>::type* = nullptr>
    TermBuilder operator()(Args... args) const
    {
      std::array<TermList, Arity> const ts{term(args)...};
      return {Term::create(fn, Arity, ts.data())};
    }

    static FnBuilder fresh(char const* prefix, char const* suffix = nullptr)
    {
      unsigned fn = env.signature->addFreshFunction(Arity, prefix, suffix);
      return {fn};
    }

  private:
    unsigned fn;
};

static TermBuilder const x = var(0);
static TermBuilder const y = var(1);
static TermBuilder const z = var(2);
}

void ForwardSubsumptionDemodulation::testSomeStuff()
{
  CALL("ForwardSubsumptionDemodulation::testSomeStuff");

  return;

  {
    using namespace TermBuilder;
    TermList xpx = x + x;
    TermList xpxpy = x + (x + y);

    // auto h = FnBuilder<1>(env.signature->addFreshFunction(1, "h"));
    // auto g = FnBuilder<2>(env.signature->addFreshFunction(2, "g"));
    auto h = FnBuilder<1>::fresh("h");
    auto g = FnBuilder<2>::fresh("g");

    auto hx = h(x);
    auto hhx = h(h(x));
    auto hhx2 = h(hx);

    TermList gx = g(x, x);
    TermList ggh = g(gx, h(hx));

    Literal* blup = hx < ggh;
  }

  unsigned csym = env.signature->addFreshFunction(0, "c");
  unsigned f = env.signature->addFreshFunction(1, "f");
  unsigned g = env.signature->addFreshFunction(2, "g");
  unsigned P = env.signature->addFreshPredicate(1, "P");
  unsigned Q = env.signature->addFreshPredicate(1, "Q");
  unsigned R = env.signature->addFreshPredicate(1, "R");

  TermList x(0, false);
  TermList y(1, false);
  TermList fx(Term::create1(f, x));
  TermList ffx(Term::create1(f, fx));
  TermList fffx(Term::create1(f, ffx));
  TermList gx(Term::create2(g, x, x));
  TermList g2x(Term::create2(g, gx, gx));
  TermList g3x(Term::create2(g, g2x, g2x));
  TermList g4x(Term::create2(g, g3x, g3x));

  TermList c(Term::create(csym, 0, nullptr));
  TermList fc(Term::create1(f, c));
  TermList ffc(Term::create1(f, fc));
  TermList fffc(Term::create1(f, ffc));
  TermList gc(Term::create2(g, c, c));
  TermList g2c(Term::create2(g, gc, gc));
  TermList g3c(Term::create2(g, g2c, g2c));
  TermList g4c(Term::create2(g, g3c, g3c));

  Literal* fffxEQfx = Literal::createEquality(true, fffx, fx, Sorts::SRT_DEFAULT);
  Literal* Pgx = Literal::create1(P, true, gx);
  Literal* Pg2x = Literal::create1(P, true, g2x);
  Literal* Qfffc = Literal::create1(Q, true, fffc);
  Literal* Pgc = Literal::create1(P, true, gc);
  Literal* Pg2c = Literal::create1(P, true, g2c);
  Literal* Pg4c = Literal::create1(P, true, g4c);
  Literal* Ry = Literal::create1(R, true, y);

  Clause* mcl = [&]() {
    LiteralStack lits;
    lits.push(fffxEQfx);
    // This literal needs to be large, otherwise it won't be indexed by the subsumption index.
    // NOTE: Maybe we should make a new index which skips equality literals when selecting the "best" literal
    // (however, we could have the case that one equality is used for demodulation but another equality subsumes part of the given clause)
    lits.push(Pg2x);
    return Clause::fromStack(lits, Unit::AXIOM, new Inference(Inference::THEORY));
  }();

  Clause* cl = [&]() {
    LiteralStack lits;
    lits.push(Qfffc);
    lits.push(Pg2c);
    lits.push(Pg4c);  // (!)
    lits.push(Ry);
    return Clause::fromStack(lits, Unit::AXIOM, new Inference(Inference::THEORY));
  }();

  std::cerr << "Clause mcl:\t" << mcl->toNiceString() << std::endl;
  std::cerr << "Clause cl:\t" << cl->toNiceString() << std::endl;

  // _index->handleClause(mcl, true);


  Clause* replacement = nullptr;
  ClauseIterator premises;
  if (perform(cl, replacement, premises)) {
    std::cerr << "testSomeStuff: success!" << std::endl;
  } else {
    std::cerr << "testSomeStuff: fail!" << std::endl;
  }


  std::cerr << "exiting" << std::endl;
  std::exit(27);
}



class AccumulatingBinder
{
  public:

    using Var = unsigned int;
    using BindingsMap = v_unordered_map<Var, TermList>;

    AccumulatingBinder() { }

    /// Initializes the current bindings (uncommitted) with the given argument
    explicit
    AccumulatingBinder(BindingsMap&& initialBindings)
      : m_checkpoint()
      , m_current(std::move(initialBindings))
    { }

    /// Set the current bindings (uncommitted) without changing the committed bindings
    AccumulatingBinder& operator=(BindingsMap&& bindings)
    {
      m_current = std::move(bindings);
      return *this;
    }

    bool bind(Var var, TermList term)
    {
      // If the variable is already bound, it must be bound to the same term.
      auto res = m_current.insert({var, term});
      auto it = res.first;
      bool inserted = res.second;
      return inserted || (it->second == term);
    }

    void specVar(Var var, TermList term)
    {
      ASSERTION_VIOLATION;
    }

    /// Resets to last checkpoint
    void reset() {
      m_current = m_checkpoint;
    }

    /// Commits the current state to a checkpoint
    void commit() {
      m_checkpoint = m_current;
    }

    /// Deletes all bindings and checkpoints
    void clear() {
      m_current.clear();
      m_checkpoint.clear();
    }

    BindingsMap const& bindings() const {
      return m_current;
    }

    // Makes objects of this class work as applicator for substitution
    // (as defined in Kernel/SubstHelper.hpp)
    TermList apply(Var var) const {
      auto it = m_current.find(var);
      if (it != m_current.end()) {
        return it->second;
      } else {
        // If var is not bound, return the variable itself (as TermList)
        return TermList(var, false);
      }
    }

    TermList applyTo(TermList t, bool noSharing = false) const {
      return SubstHelper::apply(t, *this, noSharing);
    }

    Literal* applyTo(Literal* l) const {
      return SubstHelper::apply(l, *this);
    }

  private:
    BindingsMap m_checkpoint;
    BindingsMap m_current;
};


class OverlayBinder
{
  public:
    using Var = unsigned int;
    using BindingsMap = v_unordered_map<Var, TermList>;

    OverlayBinder()
      : m_base(16)
      , m_overlay(16)
    { }

    /// Initializes the base bindings with the given argument
    explicit
    OverlayBinder(BindingsMap&& initialBindings)
      : m_base(std::move(initialBindings))
      , m_overlay(16)
    { }

    bool bind(Var var, TermList term)
    {
      // If the variable is already bound, it must be bound to the same term.
      auto base_it = m_base.find(var);
      if (base_it != m_base.end()) {
        return base_it->second == term;
      }
      else {
        auto res = m_overlay.insert({var, term});
        auto it = res.first;
        bool inserted = res.second;
        return inserted || (it->second == term);
      }
    }

    void specVar(Var var, TermList term)
    {
      ASSERTION_VIOLATION;
    }

    /// Clear all bindings
    void clear()
    {
      m_base.clear();
      m_overlay.clear();
    }

    /// Direct access to base bindings
    BindingsMap& base()
    {
      ASS(m_overlay.empty());
      return m_base;
    }

    /// Resets to base bindings
    void reset() {
      m_overlay.clear();
    }

    // /// Resets to the given base bindings
    // void resetToBase(BindingsMap&& newBase)
    // {
    //   m_base = std::move(newBase);
    //   m_overlay.clear();
    // }

    // Makes objects of this class work as applicator for substitution
    // (as defined in Kernel/SubstHelper.hpp)
    TermList apply(Var var) const {
      auto b_it = m_base.find(var);
      if (b_it != m_base.end()) {
        return b_it->second;
      } else {
        auto o_it = m_overlay.find(var);
        if (o_it != m_overlay.end()) {
          return o_it->second;
        } else {
          // If var is not bound, return the variable itself (as TermList)
          return TermList(var, false);
        }
      }
    }

    TermList applyTo(TermList t, bool noSharing = false) const {
      return SubstHelper::apply(t, *this, noSharing);
    }

    Literal* applyTo(Literal* l) const {
      return SubstHelper::apply(l, *this);
    }

  private:
    BindingsMap m_base;
    BindingsMap m_overlay;
};


#define CHECK_FOR_MULTIPLE_RESULTS 0

bool ForwardSubsumptionDemodulation::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  CALL("ForwardSubsumptionDemodulation::perform");

  //     mcl                cl
  // vvvvvvvvvv      vvvvvvvvvvvvvvvv
  // eqLit         matched      /-- only look for a term to demodulate in this part!
  // vvvvv           vv    vvvvvvvvvv
  // l = r \/ C      CΘ \/ L[lΘ] \/ D
  // --------------------------------
  //       CΘ \/ L[rΘ] \/ D
  //
  // whenever lΘ > rΘ.
  // also   l = r \/ C   <   CΘ \/ L[lΘ] \/ D    (to preserve completeness (redundancy))
  //
  //
  // if l > r then lΘ > rΘ
  //
  // Pseudocode:
  //
  // Input: cl
  //
  // for each literal sqlit in cl:
  //    for each clause mcl such that sqlit \in mclσ for some substitution σ:
  //        for each equality literal eqLit in mcl:
  //            for each substitution Θ such that (mcl \ {eqLit})Θ \subset cl:
  //                for each lhs in DemodulationLHS(eqLit):
  //                    for each term t in (cl \ mclΘ):
  //                        if there is τ s.t. lhsΘτ == t
  //                        then replace t in cl by rhsΘτ and return the modified clause.     // NOTE: all occurrences of t in the first literal of (cl\...) where t is found are replaced.

  TimeCounter tc(TC_FORWARD_SUBSUMPTION_DEMODULATION);

  Ordering& ordering = _salg->getOrdering();

  // Discards all previous aux values (so after this, hasAux() returns false for any clause).
  Clause::requestAux();
  ON_SCOPE_EXIT( Clause::releaseAux(); );

  // Initialize miniIndex with literals in the clause cl
  LiteralMiniIndex miniIndex(cl);

  for (unsigned sqli = 0; sqli < cl->length(); ++sqli) {
    Literal* subsQueryLit = (*cl)[sqli];  // this literal is only used to query the subsumption index

#if CHECK_FOR_MULTIPLE_RESULTS
    int fsd_result_count = 0;
    Clause* fsd_first_mcl = nullptr;
    Clause* fsd_first_result = nullptr;
    v_set<v_set<Literal*>> fsd_results;
#endif

    SLQueryResultIterator rit = _index->getGeneralizations(subsQueryLit, false, false);
    while (rit.hasNext()) {
      SLQueryResult res = rit.next();
      Clause* mcl = res.clause;

      ASS_NEQ(cl, mcl);  // this can't happen because cl isn't in the index yet, right?
      ASS_GE(mcl->length(), 2);  // property of the index we use

      if (mcl->hasAux()) {
        // we've already checked this clause
        continue;
      }
      mcl->setAux(nullptr);  // we only need existence and don't care about the actual value

      if (!ColorHelper::compatible(cl->color(), mcl->color())) {
        continue;
      }

      // No multiset match possible if base is longer than instance
      if (mcl->length() > cl->length()) {
        // static int mpc = 0;
        // std::cerr << "prevented impossible matching " << ++mpc << std::endl;
        continue;
      }

      // Find a positive equality in mcl to use for demodulation
      for (unsigned eqi = 0; eqi < mcl->length(); ++eqi) {
        Literal* eqLit = (*mcl)[eqi];  // Equality literal for demodulation
        if (!eqLit->isEquality()) {
          continue;
        }
        if (eqLit->isNegative()) {
          continue;
        }
        ASS(eqLit->isEquality());
        ASS(eqLit->isPositive());

        unsigned const eqSort = SortHelper::getEqualityArgumentSort(eqLit);

        Ordering::Result argOrder = ordering.getEqualityArgumentOrder(eqLit);
        bool preordered = (argOrder == Ordering::LESS) || (argOrder == Ordering::GREATER);
        if (_preorderedOnly && !preordered) {
          continue;
        }

        // Now we have to check if (mcl without eqLit) can be instantiated to some subset of cl
        static v_vector<Literal*> baseLits;
        static v_vector<LiteralList*> alts;
        baseLits.clear();
        alts.clear();
        baseLits.reserve(mcl->length() - 1);
        alts.reserve(mcl->length() - 1);
        ASS_EQ(baseLits.size(), 0);
        ASS_EQ(alts.size(), 0);
        for (unsigned mi = 0; mi < mcl->length(); ++mi) {
          if (mi != eqi) {
            Literal* base = (*mcl)[mi];
            baseLits.push_back(base);

            LiteralList* l = nullptr;

            // TODO: order alternatives, either smaller to larger or larger to smaller, or unordered
            // to do this, can we simply order the literals inside the miniIndex? (in each equivalence class w.r.t. literal header)
            LiteralMiniIndex::InstanceIterator instIt(miniIndex, base, false);
            while (instIt.hasNext()) {
              Literal* matched = instIt.next();
              LiteralList::push(matched, l);
            }

            alts.push_back(l);
          }
        }
        ASS_GE(baseLits.size(), 1);
        ASS_EQ(baseLits.size(), alts.size());

        // Ensure cleanup of LiteralLists
        ON_SCOPE_EXIT({
          for (LiteralList* ll : alts) {
              LiteralList::destroy(ll);
          }
        });

        static MLMatcher matcher;
        matcher.init(baseLits.data(), baseLits.size(), cl, alts.data(), true);

        static unsigned const maxMatches =
          getOptions().forwardSubsumptionDemodulationMaxMatches() == 0
          ? std::numeric_limits<decltype(maxMatches)>::max()
          : getOptions().forwardSubsumptionDemodulationMaxMatches();

        for (unsigned numMatches = 0; numMatches < maxMatches; ++numMatches) {
          if (!matcher.nextMatch()) {
            break;
          }
          // std::cerr << "Subsumption (modulo eqLit) discovered! Now try to demodulate some term of cl in the unmatched literals." << std::endl;

          static v_unordered_set<Literal*> matchedAlts(16);
          matchedAlts.clear();
          matcher.getMatchedAlts(matchedAlts);

          static OverlayBinder binder;
          binder.clear();
          matcher.getBindings(binder.base());

          // Now we try to demodulate some term in an unmatched literal with eqLit.
          // IMPORTANT: only look at literals that are not being matched to mcl (the rule is unsound otherwise)!
          //
          //     mcl                cl
          // vvvvvvvvvv      vvvvvvvvvvvvvvvv
          // eqLit         matched      /-- only look for a term to demodulate in this part!
          // vvvvv           vv    vvvvvvvvvv
          // l = r \/ C      CΘ \/ L[lΘ] \/ D
          // --------------------------------
          //       CΘ \/ L[rΘ] \/ D

          bool postMLMatchOrdered = preordered;
          if (!preordered) {
            Literal* eqLitS = binder.applyTo(eqLit);
            auto argOrder = ordering.getEqualityArgumentOrder(eqLitS);
            postMLMatchOrdered = (argOrder == Ordering::LESS) || (argOrder == Ordering::GREATER);
          }

          auto lhsIt = EqHelper::getDemodulationLHSIterator(eqLit, true, ordering, getOptions());
          while (lhsIt.hasNext()) {
            TermList lhs = lhsIt.next();
            TermList rhs = EqHelper::getOtherEqualitySide(eqLit, lhs);

#if VDEBUG
            if (preordered) {
              if (argOrder == Ordering::LESS) {
                ASS_EQ(rhs, *eqLit->nthArgument(0));
              } else {
                ASS_EQ(rhs, *eqLit->nthArgument(1));
              }
            }
#endif

            static DHSet<TermList> attempted;  // Terms we already attempted to demodulate
            attempted.reset();

            for (unsigned dli = 0; dli < cl->length(); ++dli) {
              Literal* dlit = (*cl)[dli];  // literal to be demodulated
              // std::cerr << "Try to demodulate dlit = cl[" << dli << "]: " << dlit->toString() << std::endl;

              // TODO: discuss
              if (dlit == eqLit) {
                // Only possible match would lead to an equality tautology => skip this literal
                // static int eqcnt = 0;
                // ++eqcnt;
                // std::cerr << "eqcnt = " << eqcnt << std::endl;
                continue;
              }

              if (matchedAlts.find(dlit) != matchedAlts.end()) {
                continue;
              }

              NonVariableIterator nvi(dlit);
              while (nvi.hasNext()) {
                TermList lhsS = nvi.next();  // named 'lhsS' because it will be matched against 'lhs'

                if (!attempted.insert(lhsS)) {
                  // We have already tried to demodulate the term lhsS and did not
                  // succeed (otherwise we would have returned from the function).
                  // If we have tried the term lhsS, we must have tried to
                  // demodulate also its subterms, so we can skip them too.
                  nvi.right();
                  continue;
                }

                if (SortHelper::getTermSort(lhsS, dlit) != eqSort) {
                  continue;
                }

                binder.reset();  // reset binder to state after subsumption check
                if (MatchingUtils::matchTerms(lhs, lhsS, binder)) {
                  TermList rhsS = binder.applyTo(rhs);
                  ASS_EQ(lhsS, binder.applyTo(lhs));

                  if (!postMLMatchOrdered && ordering.compare(lhsS, rhsS) != Ordering::GREATER) {
                    continue;
                  }

                  bool performToplevelCheck = _performRedundancyCheck && dlit->isEquality() && (lhsS == *dlit->nthArgument(0) || lhsS == *dlit->nthArgument(1));
                  if (performToplevelCheck) {
                    //   lhsS=rhsS
                    //    eqLitS          dlit
                    //    vvvvv          vvvvv
                    //    l = r \/ C     l = t \/ D
                    //   ---------------------------
                    //        r = t \/ D
                    TermList other = EqHelper::getOtherEqualitySide(dlit, lhsS);   // t
                    Ordering::Result tord = ordering.compare(rhsS, other);
                    if (tord != Ordering::LESS && tord != Ordering::LESS_EQ) {  // TODO: why is LESS_EQ ok?   tord == LESS_EQ  ==>  r ≤ t  ==>  l=r ≤ l=t  ==>  ??? (Don't we need strictly less here?)
                      Literal* eqLitS = binder.applyTo(eqLit);
                      // TODO: check this again with the writeup of FSD
                      bool isMax = true;
                      for (unsigned li2 = 0; li2 < cl->length(); li2++) {
                        if (dli == li2) {
                          continue;
                        }
                        Literal* lit2 = (*cl)[li2];
                        if (ordering.compare(eqLitS, (*cl)[li2]) == Ordering::LESS) {
                          isMax = false;
                          break;
                        }
                      }
                      if (isMax) {
                        // std::cerr << "toplevel check prevented something" << std::endl;
                        // We have the following case which doesn't preserve completeness:
                        //    l = r \/ C     l = t \/ D
                        //   ---------------------------
                        //        r = t \/ D
                        // where r > t and l = r > D.
                        //
                        // Reason:
                        // the right premise should become redundant after application of FSD (since it is a simplification rule).
                        // It is redundant, if it is a logical consequence of smaller clauses in the search space.
                        // * It is easy to see that the right premise is a logical consequence of the conclusion and the left premise.
                        // * Also, the right premise is larger than the conclusion, because l > r.
                        // * However, we also need that the left premise is smaller than the right premise.
                        //   Three cases for dlit (the literal in the right premise to be demodulated):
                        //   1. L[l] in the right premise is not an equality literal. Then L[l] > l = r because equalities are smallest in the ordering.
                        //   2. s[l] = t with s[l] ≠ l. Then s[l] > l (subterm property of simplification orderings).
                        //                              Thus s[l] = t > l = r.  (multiset extension of ordering: { s[l], t } > { s[l] } > { l, r }, because s[l] > l > r)
                        //   3. l = t in the right premise.
                        //   3a. If r ≤ t, then l = r ≤ l = t.
                        //   3b. Otherwise we have to perform the toplevel check. isMax iff l = r > D.
                        //
                        //   Now we have a literal L in the right premise such that L > l = r.
                        //   We know that Cσ is a sub-multiset of D, thus C ≤ Cσ ≤ D.
                        //
                        //   What if
                        //   l = r \/ L \/ P  ;  l = t \/ L \/ P \/ Q   and r > t ???
                        continue;
                      }
                    }
                  }  // if (performToplevelCheck)

                  Literal* newLit = EqHelper::replace(dlit, lhsS, rhsS);
                  ASS_EQ(ordering.compare(lhsS, rhsS), Ordering::GREATER);
                  ASS_EQ(ordering.compare(dlit, newLit), Ordering::GREATER);

                  if (EqHelper::isEqTautology(newLit)) {
                    env.statistics->forwardSubsumptionDemodulationsToEqTaut++;

                    // TODO: discuss this;
                    // we might find another useful match after encountering an equality tautology,
                    // so maybe we should continue here.
                    // (After the other optimizations, this is no issue anymore for our oxford-fsd example.
                    //  "FSD after FS" eliminated most of the equality tautologies.;
                    //  the "dlit == eqLit" check eliminated the rest.)
                    // NOTE:
                    // Actually, when we get an equality tautology, it means the given clause can be deleted.
                    // So it's actually good if we end up in this case.

                    premises = pvi(getSingletonIterator(mcl));
                    replacement = nullptr;
                    // Clause reduction was successful (=> return true),
                    // but we don't set the replacement (because the result is a tautology and should be discarded)
                    return true;
                  }

                  Inference* inference = new Inference2(Inference::FORWARD_SUBSUMPTION_DEMODULATION, cl, mcl);
                  Unit::InputType inputType = std::max(cl->inputType(), mcl->inputType());

                  Clause* newCl = new(cl->length()) Clause(cl->length(), inputType, inference);

                  for (unsigned i = 0; i < cl->length(); ++i) {
                    if (i == dli) {
                      (*newCl)[i] = newLit;
                    } else {
                      (*newCl)[i] = (*cl)[i];
                    }
                  }

                  newCl->setAge(cl->age());
                  env.statistics->forwardSubsumptionDemodulations++;

#if CHECK_FOR_MULTIPLE_RESULTS
                  v_set<Literal*> newClSet;
                  for (unsigned i = 0; i < newCl->length(); ++i) {
                    newClSet.insert((*newCl)[i]);
                  }
                  auto ins_res = fsd_results.insert(newClSet);
                  bool result_is_new = ins_res.second;
                  fsd_result_count += 1;
                  if (fsd_result_count == 1) {
                    ASS(!fsd_first_mcl);
                    ASS(!fsd_first_result);
                    fsd_first_mcl = mcl;
                    fsd_first_result = newCl;
                  }
                  if (fsd_result_count >= 2 && result_is_new) {
                    if (fsd_result_count == 2) {
                      std::cerr << "\n\n";
                      std::cerr << "fsd_count = 1" << std::endl;
                      std::cerr << "   mcl = " << fsd_first_mcl->toNiceString() << std::endl;
                      std::cerr << "   cl  = " << cl->toNiceString() << std::endl;
                      std::cerr << "   res = " << fsd_first_result->toNiceString() << std::endl;
                    }
                    std::cerr << "fsd_count = " << fsd_result_count << std::endl;
                    std::cerr << "   mcl = " << mcl->toNiceString() << std::endl;
                    std::cerr << "   cl  = " << cl->toNiceString() << std::endl;
                    std::cerr << "   res = " << newCl->toNiceString() << std::endl;
                  }
#endif

                  // TODO:
                  // If we continue here, we find a lot more inferences (but takes a long time; factor 2);
                  // continue;

                  // Return early to measure the impact of computation without affecting the search space
                  // return false;

                  premises = pvi(getSingletonIterator(mcl));
                  replacement = newCl;
                  // std::cerr << "\t FwSubsDem replacement: " << replacement->toNiceString() << std::endl;
                  // std::cerr << "\t          for input cl: " << cl->toNiceString() << std::endl;
                  // std::cerr << "\t               via mcl: " << mcl->toNiceString() << std::endl;
                  return true;
                } // if (lhs matches lhsS)
              } // while (nvi.hasNext())
            } // for dli
          } // while (lhsIt.hasNext())
        } // for (numMatches)
      } // for eqi
    } // while (rit.hasNext)
  } // for (li)

  return false;
}
