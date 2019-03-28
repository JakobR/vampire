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

  _preorderedOnly = false;  // TODO: might add an option for this like in forward demodulation
  _performRedundancyCheck = getOptions().demodulationRedundancyCheck();

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
  // for each literal sqlit in cl:
  //    for each clause mcl such that sqlit \in mclσ for some substitution σ:
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


  for (unsigned sqli = 0; sqli < cl->length(); ++sqli) {
    Literal* subsQueryLit = (*cl)[sqli];  // this literal is only used to query the subsumption index

    std::cerr << "Literal cl[" << sqli << "]: " << subsQueryLit->toString() << std::endl;

    SLQueryResultIterator rit = _fwIndex->getGeneralizations(subsQueryLit, false, false);
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
        ASS(eqLit->isEquality());
        ASS(eqLit->isPositive());

        unsigned const eqSort = SortHelper::getEqualityArgumentSort(eqLit);

        std::cerr << "Found equality in mcl: " << eqLit->toString() << std::endl;

        Ordering::Result argOrder = ordering.getEqualityArgumentOrder(eqLit);
        bool preordered = (argOrder == Ordering::LESS) || (argOrder == Ordering::GREATER);
        std::cerr << "\t preordered = " << preordered << std::endl;
        if (_preorderedOnly && !preordered) {
          continue;
        }

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
            // to do this, can we simply order the literals inside the miniIndex? (in each equivalence class w.r.t. literal header)
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
        matcher.init(baseLits.data(), baseLits.size(), cl, alts.data());

        static unsigned const maxMatches =
          getOptions().forwardSubsumptionDemodulationMaxMatches() == 0
          ? std::numeric_limits<decltype(maxMatches)>::max()
          : getOptions().forwardSubsumptionDemodulationMaxMatches();

        for (unsigned numMatches = 0; numMatches < maxMatches; ++numMatches) {
          if (!matcher.nextMatch()) {
            break;
          }
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

          bool postMLMatchOrdered = preordered;
          if (!preordered) {
            Literal* eqLitS = binder.applyTo(eqLit);
            auto argOrder = ordering.getEqualityArgumentOrder(eqLitS);
            postMLMatchOrdered = (argOrder == Ordering::LESS) || (argOrder == Ordering::GREATER);
          }
          std::cerr << "\t postMLMatchOrdered = " << postMLMatchOrdered << std::endl;

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
              std::cerr << "Try to demodulate dlit = cl[" << dli << "]: " << dlit->toString() << std::endl;

              if (matchedAlts.find(dlit) != matchedAlts.end()) {
                std::cerr << "\t(skipped because part of CΘ)" << std::endl;
                continue;
              }

              NonVariableIterator nvi(dlit);
              while (nvi.hasNext()) {
                TermList lhsS = nvi.next();  // lhsS because it will be matched against lhs
                std::cerr << "Term: " << lhsS.toString();
                if (!attempted.insert(lhsS)) {
                  // We have already tried to demodulate the term lhsS and did not
                  // succeed (otherwise we would have returned from the function).
                  // If we have tried the term lhsS, we must have tried to
                  // demodulate also its subterms, so we can skip them too.
                  nvi.right();
                  std::cerr << "\t(skipped because already checked)" << std::endl;
                  continue;
                }
                std::cerr << std::endl;

                // TODO: Demodulation has a lot more checks which I don't understand yet. We probably need some of them here too
                // TODO: do at least the sort-check like this:
                // if(querySort!=eqSort) {
                //   continue;
                // }

                binder.reset();  // resets to last checkpoint (here: to state after subsumption check)
                if (MatchingUtils::matchTerms(lhs, lhsS, binder)) {
                  TermList rhsS = binder.applyTo(rhs);
                  ASS_EQ(lhsS, binder.applyTo(lhs));

                  auto trmOrder = ordering.compare(lhsS, rhsS);
                  if (!postMLMatchOrdered && trmOrder != Ordering::GREATER) {
                    std::cerr << "\t Match prevented by ordering: " << rhsS.toString() << "     (trmOrder = " << trmOrder << ")" << std::endl;
                    continue;
                  }

                  bool performToplevelCheck = _performRedundancyCheck && dlit->isEquality() && (lhsS == *dlit->nthArgument(0) || lhsS == *dlit->nthArgument(1));
                  if (performToplevelCheck) {
                    TermList other = EqHelper::getOtherEqualitySide(dlit, lhsS);
                    Ordering::Result tord = ordering.compare(rhsS, other);
                    if (tord != Ordering::LESS && tord != Ordering::LESS_EQ) {
                      Literal* eqLitS = binder.applyTo(eqLit);
                      /** TODO: what literals do I have to include in the check here exactly?
                      bool isMax = true;
                      for (unsigned li2 = 0; li2 < cl->length(); li2++) {
                        if (dli == li2) {
                          continue;
                        }
                        Literal* lit2 = (*cl)[li2];
                        if(ordering.compare(eqLitS, (*cl)[li2]) == Ordering::LESS) {
                          isMax=false;
                          break;
                        }
                      }
                      if(isMax) {
                        //The demodulation is this case which doesn't preserve completeness:
                        //s = t     s = t1 \/ C
                        //---------------------
                        //     t = t1 \/ C
                        //where t > t1 and s = t > C
                        continue;
                      }
                      */
                    }
                  }  // if (performToplevelCheck)

                  std::cerr << "\t Match! replacing term with: " << rhsS.toString() << std::endl;

                  Literal* newLit = EqHelper::replace(dlit, lhsS, rhsS);
                  std::cerr << "\t newLit: " << newLit->toString() << std::endl;
                  ASS_EQ(ordering.compare(lhsS, rhsS), Ordering::GREATER);
                  ASS_EQ(ordering.compare(dlit, newLit), Ordering::GREATER);

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
        } // for (numMatches)
      } // for eqi
    } // while (rit.hasNext)
  } // for (li)

  return false;
}
