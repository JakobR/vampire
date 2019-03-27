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
  _fwIndex.attach(salg);

  testSomeStuff();  // TODO: for debugging, to be removed later
}

void ForwardSubsumptionDemodulation::detach()
{
  CALL("ForwardSubsumptionDemodulation::detach");
  _fwIndex.detach();
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

    TermList term() const
    {
      return t;
    }

  private:
    TermList t;
};

TermBuilder operator+(TermBuilder const& t1, TermBuilder const& t2)
{
  unsigned const pred_int_plus = env.signature->getInterpretingSymbol(Theory::INT_PLUS);
  return {Term::create2(pred_int_plus, t1.term(), t2.term())};
}

TermList term(TermBuilder tb)
{
  return tb.term();
}

TermList term(Term* t)
{
  return TermList(t);
}

TermList term(TermList t)
{
  return t;
}
template <unsigned Arity>
class FnBuilder
{
  public:
    FnBuilder(unsigned fn)
      : fn{fn}
    { }

    // Args may contain values of types TermBuilder, Term*, and TermList (also mixed)
    template <typename...Args, typename std::enable_if_t<sizeof...(Args) == Arity>* = nullptr>
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

static TermBuilder const x = TermBuilder(TermList(0, false));
static TermBuilder const y = TermBuilder(TermList(1, false));
static TermBuilder const z = TermBuilder(TermList(2, false));
}

void ForwardSubsumptionDemodulation::testSomeStuff()
{
  CALL("ForwardSubsumptionDemodulation::testSomeStuff");

  std::cerr << "testSomeStuff" << std::endl;
  // return;

  {
    using namespace TermBuilder;
    TermList xpx = ( x + x ).term();
    TermList xpxpy = term( x + (x + y) );

    // auto h = FnBuilder<1>(env.signature->addFreshFunction(1, "h"));
    // auto g = FnBuilder<2>(env.signature->addFreshFunction(2, "g"));
    auto h = FnBuilder<1>::fresh("h");
    auto g = FnBuilder<2>::fresh("g");

    auto hx = term( h(x) );
    auto hhx = term( h(h(x)) );
    auto hhx2 = term( h(hx) );

    auto gx = term( g(x, x) );
    auto ggh = term( g(gx, h(x)) );
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

  _fwIndex->handleClause(mcl, true);


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

    bool bind(Var var, TermList term)
    {
      // If the variable is already bound, it must be bound to the same term.
      auto [ it, inserted ] = m_current.insert({var, term});
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
  // for each literal lit in cl:
  //    for each clause mcl such that lit \in mclσ for some substitution σ:
  //        for each equality literal eqLit in mcl:
  //            for each substitution Θ such that (mcl \ {eqLit})Θ \subset cl:
  //                for each lhs in DemodulationLHS(eqLit):
  //                    for each term t in (cl \ mclΘ):
  //                        if there is τ s.t. lhsΘτ == t
  //                        then replace t in cl by rhsΘτ and return the modified clause.     // NOTE: all occurrences of t in the first literal of (cl\...) where t is found are replaced.

  std::cerr << "\n\nEntering ForwardSubsumptionDemodulation::perform with\n\tcl = " << cl->toNiceString() << std::endl;
  // The subsumption check in ForwardSubsumptionAndResolution has two stages:
  // 1. Check subsumption by unit clauses (with UnitClauseLiteralIndex)
  // 2. Check subsumption by longer clauses (with FwSubsSimplifyingLiteralIndex)
  //
  // In the case of ForwardSubsumptionDemodulation we do not need to check unit
  // clauses, because these would be unit equalities which are already handled
  // by the regular ForwardDemodulation rule.

  TimeCounter tc(TC_FORWARD_SUBSUMPTION_DEMODULATION);

  Ordering& ordering = _salg->getOrdering();

  // Discards all previous aux values (so after this, hasAux() returns false for any clause).
  Clause::requestAux();
  ON_SCOPE_EXIT( Clause::releaseAux(); );

  // Initialize miniIndex with literals in the clause cl
  LiteralMiniIndex miniIndex(cl);


  for (unsigned li = 0; li < cl->length(); ++li) {
    Literal* lit = (*cl)[li];

    std::cerr << "Literal cl[" << li << "]: " << lit->toString() << std::endl;

    SLQueryResultIterator rit = _fwIndex->getGeneralizations(lit, false, false);
    while (rit.hasNext()) {
      SLQueryResult res = rit.next();
      Clause* mcl = res.clause;

      std::cerr << "Found generalization: " << res.literal->toString() << "\t which is part of: " << mcl->toNiceString() << std::endl;

      if (mcl->hasAux()) {
        // we've already checked this clause
        std::cerr << "Skipping mcl due to aux" << std::endl;
        continue;
      }
      mcl->setAux(nullptr);  // we only need existence and don't care about the actual value

      ASS_GE(mcl->length(), 2);  // property of the index we use

      if (!ColorHelper::compatible(cl->color(), mcl->color())) {
        continue;
      }

      // Find an equality in mcl
      for (unsigned eqi = 0; eqi < mcl->length(); ++eqi) {
        Literal* eqLit = (*mcl)[eqi];  // Equality literal for demodulation
        if (!eqLit->isEquality()) {
          continue;
        }
        if (eqLit->isNegative()) {
          continue;
        }

        std::cerr << "Found equality in mcl: " << eqLit->toString() << std::endl;


        // TODO:
        // We can do a pre-check of the ordering like in FwDem (see "preordered")


        // Now we have to check if (mcl without eqLit) can be instantiated to some subset of cl
        v_vector<Literal*> baseLits;
        v_vector<LiteralList*> alts;
        baseLits.reserve(mcl->length() - 1);
        alts.reserve(mcl->length() - 1);
        for (unsigned mi = 0; mi < mcl->length(); ++mi) {
          if (mi != eqi) {
            baseLits.push_back((*mcl)[mi]);

            LiteralList* l = nullptr;

            // TODO: order alternatives, either smaller to larger or larger to smaller, or unordered
            LiteralMiniIndex::InstanceIterator instIt(miniIndex, (*mcl)[mi], false);
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
          std::cerr << "destroying LiteralLists" << std::endl;
          for (LiteralList* ll : alts) {
              LiteralList::destroy(ll);
          }
        });

        static MLMatcher matcher;

        // TODO: Do we need multiset matching here or can we get away without it? I think we don't need it.
        matcher.init(baseLits.data(), baseLits.size(), cl, alts.data(), false);

        while (matcher.nextMatch()) {  // TODO limit max number of matches
          std::cerr << "Subsumption (modulo eqLit) discovered! Now try to demodulate some term of cl in the unmatched literals." << std::endl;

          auto matchedAlts = matcher.getMatchedAlts();

          AccumulatingBinder binder{matcher.getBindings()};
          binder.commit();

          std::cerr << "Literals in CΘ:\n";
          for (Literal* ctl : matchedAlts) {
            std::cerr << "\t" << ctl->toString() << std::endl;
          }

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

          ASS_EQ(eqLit->arity(), 2);
          TermList t0 = *eqLit->nthArgument(0);
          TermList t1 = *eqLit->nthArgument(1);
          std::cerr << "eqLit:        t0 = " << t0.toString() << std::endl;
          std::cerr << "              t1 = " << t1.toString() << std::endl;

          // Apply current substitution to t0 and t1
          // TermList s0 = SubstHelper::apply(t0, std::as_const(binder));
          // TermList s1 = SubstHelper::apply(t1, std::as_const(binder));
          TermList s0 = binder.applyTo(t0);
          TermList s1 = binder.applyTo(t1);
          std::cerr << "substituted:  s0 = " << s0.toString() << std::endl;
          std::cerr << "              s1 = " << s1.toString() << std::endl;

          Literal* eqLitS = binder.applyTo(eqLit);

          TermList r0 = t0;
          TermList r1 = t1;
          // TODO Assertion violation when KBOForEPR is used as ordering
          // It says:
          //    Condition in file /Users/jakob/code/vampire/Kernel/KBOForEPR.cpp, line 103 violated:
          //    !tl1.isTerm() || tl1.term()->arity()==0
          // Maybe use ordering.getEqualityArgumentOrder instead (like in FwDem)
          auto order = ordering.getEqualityArgumentOrder(eqLitS);
          // auto order = ordering.compare(s0, s1);
          if (order == Ordering::GREATER) {
            // do nothing
          } else if (order == Ordering::LESS) {
            std::swap(r0, r1);
          } else {
            std::cerr << "No clear ordering between s0 and s1 (order = " << order << "); skipping demodulation." << std::endl;
            ASS(order == Ordering::GREATER_EQ
                || order == Ordering::LESS_EQ
                || order == Ordering::EQUAL
                || order == Ordering::INCOMPARABLE)
            continue;
          }
          std::cerr << "ordered:      r0 = " << r0.toString() << std::endl;
          std::cerr << "              r1 = " << r1.toString() << std::endl;
          ASS_EQ(ordering.compare(binder.applyTo(r0), binder.applyTo(r1)), Ordering::GREATER);
          // TODO: Is this check useless? But how do we know in which direction to demodulate?
          // Maybe use EqHelper::getDemodulationLHSIterator(eqLit, true, ordering, options)

          auto lhsIt = EqHelper::getDemodulationLHSIterator(eqLit, true, ordering, *env.options);
          while (lhsIt.hasNext()) {
            TermList lhs = lhsIt.next();
            TermList rhs = EqHelper::getOtherEqualitySide(eqLit, lhs);


            DHSet<TermList> attempted;  // Terms we already attempted to demodulate

            for (unsigned dli = 0; dli < cl->length(); ++dli) {
              Literal* dlit = (*cl)[dli];  // literal to be demodulated
              std::cerr << "Try to demodulate dlit = cl[" << dli << "]: " << dlit->toString() << std::endl;

              if (matchedAlts.find(dlit) != matchedAlts.end()) {
                std::cerr << "\t(skipped because part of CΘ)" << std::endl;
                continue;
              }

              NonVariableIterator nvi(dlit);
              while (nvi.hasNext()) {
                TermList trm = nvi.next();
                std::cerr << "Term: " << trm.toString();
                if (!attempted.insert(trm)) {
                  //We have already tried to demodulate the term @b trm and did not
                  //succeed (otherwise we would have returned from the function).
                  //If we have tried the term @b trm, we must have tried to
                  //demodulate also its subterms, so we can skip them too.
                  nvi.right();
                  std::cerr << "\t(skipped because already checked)" << std::endl;
                  continue;
                }
                std::cerr << std::endl;

                // TODO: Demodulation has a lot more checks which I don't understand yet. We probably need some of them here too
                // TODO: do at least the sort-check like this:
                // unsigned eqSort = SortHelper::getEqualityArgumentSort(eqLit);
                // if(querySort!=eqSort) {
                //   continue;
                // }

                // TermList rhs=EqHelper::getOtherEqualitySide(qr.literal,qr.term);

                binder.reset();  // resets to last checkpoint (here: to state after subsumption check)
                if (MatchingUtils::matchTerms(r0, trm, binder)) {
                  TermList newTrm = binder.applyTo(r1);    // TODO consider naming it rhsS like in demodulation (equality is lhs = rhs, substituted is lhsS = rhsS)

                  auto trmOrder = ordering.compare(trm, newTrm);
                  if (trmOrder != Ordering::GREATER) {
                    std::cerr << "\t Match prevented by ordering: " << newTrm.toString() << "     (trmOrder = " << trmOrder << ")" << std::endl;
                    continue;
                  }
                  std::cerr << "\t Match! replacing term with: " << newTrm.toString() << std::endl;

                  Literal* newLit = EqHelper::replace(dlit, trm, newTrm);
                  std::cerr << "\t newLit: " << newLit->toString() << std::endl;

                  if (EqHelper::isEqTautology(newLit)) {
                    std::cerr << "\t TAUTOLOGY (discard result)" << std::endl;
                    env.statistics->forwardSubsumptionDemodulationsToEqTaut++;
                    premises = pvi(getSingletonIterator(mcl));
                    replacement = nullptr;
                    // Clause reduction was successful but we don't set the replacement (because it is a tautology)
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

                  premises = pvi(getSingletonIterator(mcl));
                  replacement = newCl;
                  std::cerr << "\t FwSubsDem replacement: " << replacement->toNiceString() << std::endl;
                  return true;
                }

              } // while (nvi.hasNext())
            } // for dli
          } // while (lhsIt.hasNext())
          std::cerr <<"end matching"<<std::endl;
        } // while (nextMatch)
      } // for eqi
    } // while (rit.hasNext)
  } // for (li)

  return false;
}
