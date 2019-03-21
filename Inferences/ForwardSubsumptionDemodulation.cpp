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
#include "Lib/STLAllocator.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include <optional>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using namespace Kernel;
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



void ForwardSubsumptionDemodulation::testSomeStuff()
{
  CALL("ForwardSubsumptionDemodulation::testSomeStuff");

  std::cerr << "testSomeStuff" << std::endl;
  return;

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
    // lits.push(Pg4c);  // (!)
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


/*
class scope_guard
{
  public:
    template <typename Callable>
    scope_guard(Callable&& f)
      : f(std::forward<Callable>(f))
    { }

    ~scope_guard()
    {
      try {
        f();
      }
      catch(...) {
        // Destructor must not throw
        // (actually, it just must not throw during stack unwinding, i.e., if another exception was thrown.
        //  We could check that with std::uncaught_exceptions)
        std::terminate();  // ???
      }
    }

  private:
    // better use a class template instead of std::function to avoid memory allocation,
    // and add some helper function make_scope_guard<...>(...) to help with type inference
    std::function<void()> f;
}; // */


class RequestClauseAux
{
  public:
    RequestClauseAux() {
      std::cerr << "RequestClauseAux" << std::endl;
      Clause::requestAux();
    }

    ~RequestClauseAux() {
      std::cerr << "~RequestClauseAux" << std::endl;
      Clause::releaseAux();
    }
};



template< typename Key = unsigned int
        , typename T = TermList
        , typename Hash = std::hash<Key>
        , typename KeyEqual = std::equal_to<Key>
        , typename Allocator = STLAllocator<std::pair<const Key, T>>
        >
class AccumulatingBinder
{
  public:

    using BindingMap = std::unordered_map<Key, T, Hash, KeyEqual, Allocator>;

    AccumulatingBinder() { }

    // Initialize the current bindings (uncommitted) with the given argument
    AccumulatingBinder(BindingMap&& initialBindings)
      : m_checkpoint()
      , m_current(std::move(initialBindings))
    { }

    bool bind(Key var, T term)
    {
      // If the variable is already bound, it must be bound to the same term.
      auto [ it, inserted ] = m_current.insert({var, term});
      return inserted || (it->second == term);
    }

    void specVar(Key var, T term)
    {
      ASSERTION_VIOLATION;
    }

    // Reset to last checkpoint
    void reset() {
      m_current = m_checkpoint;
    }

    // Commit the current state to a checkpoint
    void commit() {
      m_checkpoint = m_current;
    }

    // Delete all bindings and checkpoints
    void clear() {
      m_current.clear();
      m_checkpoint.clear();
    }

    BindingMap const& bindings() const {
      return m_current;
    }

    // Makes objects of this class work as applicator for substitution
    // (as defined in Kernel/SubstHelper.hpp)
    TermList apply(unsigned int var) const {
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

  private:
    BindingMap m_checkpoint;
    BindingMap m_current;
};


class AccumulatingBinder2
{
  public:
    using Generation = unsigned int;
    using Var = unsigned int;

    bool bind(Var var, TermList term)
    {
      // If the variable is already bound, it must be bound to the same term.
      auto [ it, inserted ] = m_bindings.insert({var, {term, m_current_generation}});
      if (inserted) {
        m_dirty = true;
        return true;
      } else {
        auto [storedTerm, storedGen] = it->second;
        ASS_LE(storedGen, m_current_generation);
        return storedTerm == term;
      }
    }

    void specVar(Var var, TermList term)
    {
      ASSERTION_VIOLATION;
    }

    // Reset to last checkpoint
    void reset() {
      if (m_dirty) {
        for (auto it = m_bindings.begin(); it != m_bindings.end(); ) {
          auto gen = it->second.second;
          if (gen >= m_current_generation) {
            it = m_bindings.erase(it);
          } else {
            ++it;
          }
        }
        m_dirty = false;
      }
    }

    // Commit the current state to a checkpoint
    void commit() {
      m_current_generation += 1;
    }

    // Delete all bindings and checkpoints
    void clear() {
      m_bindings.clear();
      m_current_generation = 0;
      m_dirty = false;
    }

    std::optional<TermList> operator[] (Var var) const {
      auto it = m_bindings.find(var);
      if (it != m_bindings.end()) {
        auto [t, gen] = it->second;
        ASS_LE(gen, m_current_generation);
        return {t};
      } else {
        return {};
      }
    }

    // Makes objects of this class work as applicator for substitution
    // (as defined in Kernel/SubstHelper.hpp)
    TermList apply(Var var) const {
      auto ot = operator[](var);
      if (ot) {
        return *ot;
      } else {
        // If var is not bound, return the variable itself (as TermList)
        return TermList(var, false);
      }
    }

    TermList applyTo(TermList t, bool noSharing = false) const {
      return SubstHelper::apply(t, *this, noSharing);
    }

  private:
    using Hash = std::hash<Var>;
    using KeyEqual = std::equal_to<Var>;
    using Record = std::pair<TermList, Generation>;
    using Allocator = STLAllocator<std::pair<const Var, Record>>;
    using BindingsMap = std::unordered_map<Var, Record, Hash, KeyEqual, Allocator>;

    BindingsMap m_bindings;
    Generation m_current_generation = 0;
    bool m_dirty = false;
};


template <typename T> using vvector = std::vector<T, STLAllocator<T>>;

bool ForwardSubsumptionDemodulation::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  CALL("ForwardSubsumptionDemodulation::perform");

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

  // discard all previous aux values (so after this, hasAux() returns false for any clause).
  // Clause::requestAux();
  // scope_guard on_exit([]() {
  //   std::cerr << "on_exit" << std::endl;
  //   Clause::releaseAux();
  // });
  RequestClauseAux aux;

  // Initialize miniIndex with literals in the clause cl
  LiteralMiniIndex miniIndex(cl);


  for (unsigned li = 0; li < cl->length(); ++li) {
    Literal* lit = (*cl)[li];

    std::cerr << "Literal cl[" << li << "]: " << lit->toString() << std::endl;

    SLQueryResultIterator rit = _fwIndex->getGeneralizations(lit, false, false);
    while(rit.hasNext()) {
      SLQueryResult res = rit.next();
      Clause* mcl = res.clause;

      std::cerr << "Found generalization: " << res.literal->toString() << "\t which is part of: " << mcl->toNiceString() << std::endl;

      if (mcl->hasAux()) {
        // we've already checked this clause
        std::cerr << "Skipping mcl due to aux" << std::endl;
        continue;
      }
      mcl->setAux(nullptr);  // we only need existence and don't care about the actual value

      ASS_GE(mcl->length(), 2);

      if (!ColorHelper::compatible(cl->color(), mcl->color())) {
        continue;
      }

      // Find an equality in mcl
      for (unsigned eqi = 0; eqi < mcl->length(); ++eqi) {
        Literal* eqlit = (*mcl)[eqi];
        if (!eqlit->isEquality()) {
          continue;
        }

        std::cerr << "Found equality in mcl: " << eqlit->toString() << std::endl;

        // Now we have to check if (mcl without eqlit) can be instantiated to some subset of cl
        vvector<Literal*> baseLits;
        vvector<LiteralList*> alts;
        baseLits.reserve(mcl->length() - 1);
        alts.reserve(mcl->length() - 1);
        for (unsigned mi = 0; mi < mcl->length(); ++mi) {
          if (mi != eqi) {
            baseLits.push_back((*mcl)[mi]);

            LiteralList* l = nullptr;

            LiteralMiniIndex::InstanceIterator instIt(miniIndex, (*mcl)[mi], false);
            while(instIt.hasNext()) {
              Literal* matched = instIt.next();
              LiteralList::push(matched, l);
            }

            alts.push_back(l);
          }
        }
        ASS_GE(baseLits.size(), 1);
        ASS_EQ(baseLits.size(), alts.size());

        MLMatcher::LiteralVector matchedAlts; //(alts.size(), nullptr);
        MLMatcher::BindingsMap bindings;

        // std::cerr << "Calling MLMatcher::match with:\n";
        // for (unsigned j = 0; j < baseLits.size(); ++j) {
        //   std::cerr << "\tbase = " << baseLits[j]->toString() << std::endl;

        //   LiteralList* a = alts[j];
        //   while (LiteralList::isNonEmpty(a)) {
        //     std::cerr << "\t alt = " << a->head()->toString() << std::endl;
        //     a = a->tail();
        //   }
        // }

        // If yes, we try to demodulate some of the *other* literals of cl with eqlit
        if (MLMatcher::canBeMatched(baseLits.data(), baseLits.size(), cl, alts.data(), false, &matchedAlts, &bindings)) {
          // TODO: Do we need multiset matching here or can we get away without it? I think we don't need it.

          // TODO:
          // We have to look at *all* possible matchings if we want to ensure that we find possible applications!
          // (Just enable Pg4c in the example above, marked with "(!)" to see why.)
          // Because the substitution will be different and thus different demodulations are available.
          std::cerr << "Subsumption (modulo eqlit) discovered! Now try to demodulate some term of cl in the unmatched literals." << std::endl;
          ASS_EQ(matchedAlts.size(), baseLits.size());
          std::cerr << "MLMatcher result:\n";
          for (unsigned i = 0; i < baseLits.size(); ++i) {
            std::cerr << "Matching:   base = " << baseLits[i]->toString() << std::endl;
            std::cerr << "            inst = " << matchedAlts[i]->toString() << std::endl;
          }

          // TODO: We need the substitution from this match. Can we extract this more cheaply from the match data?
          AccumulatingBinder<> binder;
          std::cerr << "Recovering bindings... ";
          for (unsigned i = 0; i < baseLits.size(); ++i) {
            std::cerr << i << "... ";
            ALWAYS(MatchingUtils::match(baseLits[i], matchedAlts[i], false, binder));
            binder.commit();  // MatchingUtils::match calls reset() on the binder, but we want to keep the previous matches
          }
          std::cerr << "OK\n";
          std::cerr << "Recovered Bindings:\n";
          for (auto [ v, t ] : binder.bindings()) {
            std::cerr << "\t" << TermList(v, false) << " -> " << t << std::endl;
          }
          std::cerr << "Bindings from MLMatcher:\n";
          for (auto [ v, t ] : bindings) {
            std::cerr << "\t" << TermList(v, false) << " -> " << t << std::endl;
          }

          ASS(bindings == binder.bindings());

          // TODO: initialize like this instead
          AccumulatingBinder<> bbb(std::move(bindings));
          bbb.commit();

          std::cerr << "Literals in CΘ:\n";
          // TODO for small size, a linear scan is probably faster than building a set
          std::unordered_set<Literal*,std::hash<Literal*>,std::equal_to<Literal*>,STLAllocator<Literal*>> blup;
          for (Literal* ctl : matchedAlts) {
            std::cerr << "\t" << ctl->toString() << std::endl;
            blup.insert(ctl);
          }

          // Now we try to demodulate some term by using eqlit
          // IMPORTANT: only look at literals that are not being matched to mcl (the rule is unsound otherwise)!
          //
          //     mcl                cl
          // vvvvvvvvvv      vvvvvvvvvvvvvvvv
          // eqlit         matched      /-- only look for a term to demodulate in this part!
          // vvvvv           vv    vvvvvvvvvv
          // l = r \/ C      CΘ \/ L[lΘ] \/ D
          // --------------------------------
          //       CΘ \/ L[rΘ] \/ D

          ASS_EQ(eqlit->arity(), 2);
          TermList t0 = *eqlit->nthArgument(0);
          TermList t1 = *eqlit->nthArgument(1);
          std::cerr << "eqlit:        t0 = " << t0.toString() << std::endl;
          std::cerr << "              t1 = " << t1.toString() << std::endl;

          // Apply current substitution to t0 and t1
          // TermList s0 = SubstHelper::apply(t0, std::as_const(binder));
          // TermList s1 = SubstHelper::apply(t1, std::as_const(binder));
          TermList s0 = binder.applyTo(t0);
          TermList s1 = binder.applyTo(t1);
          std::cerr << "substituted:  s0 = " << s0.toString() << std::endl;
          std::cerr << "              s1 = " << s1.toString() << std::endl;

          TermList r0 = t0;
          TermList r1 = t1;
          // TODO Assertion violation when KBOForEPR is used as ordering
          // It says:
          //    Condition in file /Users/jakob/code/vampire/Kernel/KBOForEPR.cpp, line 103 violated:
          //    !tl1.isTerm() || tl1.term()->arity()==0
          // Maybe use ordering.getEqualityArgumentOrder instead (like in FwDem)
          auto order = ordering.compare(s0, s1);
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

          DHSet<TermList> attempted;  // Terms we already attempted to demodulate

          for (unsigned dli = 0; dli < cl->length(); ++dli) {
            Literal* dlit = (*cl)[dli];
            std::cerr << "Try to demodulate dlit = cl[" << dli << "]: " << dlit->toString() << std::endl;

            if (blup.find(dlit) != blup.end()) {
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

              // auto applicator = [&binder = std::as_const(binder)](unsigned int var) {
              // };

              binder.reset();  // resets to last checkpoint (here: to state after subsumption check)
              if (MatchingUtils::matchTerms(r0, trm, binder)) {
                TermList newTrm = binder.applyTo(r1);
                std::cerr << "\t Match! replace with: " << newTrm.toString() << std::endl;

                Literal* newLit = EqHelper::replace(dlit, trm, newTrm);
                std::cerr << "\t newLit: " << newLit->toString() << std::endl;

                if (EqHelper::isEqTautology(newLit)) {
                  std::cerr << "\t TAUTOLOGY (discard result)" << std::endl;
                  env.statistics->forwardSubsumptionDemodulationsToEqTaut++;
                  premises = pvi(getSingletonIterator(mcl));
                  // Clause reduction was successful but we don't set the replacement (because it is a tautology)
                  return true;
                }

                Inference* inf = new Inference2(Inference::FORWARD_SUBSUMPTION_DEMODULATION, cl, mcl);
                Unit::InputType inpType = (Unit::InputType)Int::max(cl->inputType(), mcl->inputType());

                Clause* res = new(cl->length()) Clause(cl->length(), inpType, inf);

                for (unsigned i = 0; i < cl->length(); ++i) {
                  if (i == dli) {
                    (*res)[i] = newLit;
                  } else {
                    (*res)[i] = (*cl)[i];
                  }
                }

                res->setAge(cl->age());
                env.statistics->forwardSubsumptionDemodulations++;

                premises = pvi(getSingletonIterator(mcl));
                replacement = res;
                std::cerr << "\t FwSubsDem replacement: " << replacement->toNiceString() << std::endl;
                return true;
              }

            } // while (nvi.hasNext())
          } // for dli

        } // if (canBeMatched)

        for (LiteralList* ll : alts) {
          LiteralList::destroy(ll);
        }

      } // for eqi

    } // while (rit.hasNext)

  } // for (li)

  return false;
}
