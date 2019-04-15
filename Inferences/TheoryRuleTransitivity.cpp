#include "TheoryRuleTransitivity.hpp"

#include "Indexing/LiteralIndex.hpp"
// #include "Indexing/LiteralMiniIndex.hpp"
// #include "Kernel/ColorHelper.hpp"
// #include "Kernel/EqHelper.hpp"
#include "Kernel/FormulaVarIterator.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
// #include "Lib/ScopeGuard.hpp"
// #include "Lib/STL.hpp"
// #include "Lib/STLAllocator.hpp"
// #include "Saturation/SaturationAlgorithm.hpp"
// #include <array>
// #include <unordered_map>
// #include <unordered_set>
// #include <vector>

using namespace Kernel;
using namespace Lib;
using namespace Inferences;
using namespace Saturation;


void TheoryRuleTransitivity::attach(SaturationAlgorithm* salg)
{
  CALL("TheoryRuleTransitivity::attach");
  GeneratingInferenceEngine::attach(salg);
  _index.attach(salg);

  pred_int_less = env.signature->getInterpretingSymbol(Theory::INT_LESS);
}

void TheoryRuleTransitivity::detach()
{
  CALL("TheoryRuleTransitivity::detach");
  _index.detach();
  GeneratingInferenceEngine::detach();
}



namespace {

enum class term_source {
  // The selected literal 'lit' from 'premise'
  selected_left,
  selected_right,
  // The literal returned from the query
  result_left,
  result_right
};

class ChainedClauseBuilder
{
  public:
    ChainedClauseBuilder(Clause* premise, Literal* lit, bool polarity, term_source left_term, term_source right_term)
      : premise(premise)
      , lit(lit)
      , polarity(polarity)
      , left_term(left_term)
      , right_term(right_term)
    {
      ASS(premise->contains(lit));
    }

    Clause* operator()(SLQueryResult qr) const;

  private:
    Clause* premise;
    Literal* lit;
    bool polarity;
    term_source left_term;
    term_source right_term;
};

Clause* ChainedClauseBuilder::operator()(SLQueryResult qr) const {
  CALL("ChainedClauseBuilder::operator()");

  ASS_EQ(lit->functor(), qr.literal->functor());
  ASS_EQ(lit->arity(), 2);
  ASS_EQ(qr.literal->arity(), 2);
  ASS(qr.substitution);

  auto const get_term = [this,qr](term_source src) -> TermList {
    switch (src) {
      case term_source::selected_left:
        return qr.substitution->applyToQuery(*lit->nthArgument(0));
      case term_source::selected_right:
        return qr.substitution->applyToQuery(*lit->nthArgument(1));
      case term_source::result_left:
        return qr.substitution->applyToResult(*qr.literal->nthArgument(0));
      case term_source::result_right:
        return qr.substitution->applyToResult(*qr.literal->nthArgument(1));
      default:
        ASSERTION_VIOLATION;
    }
  };

  Literal* newLit = Literal::create2(lit->functor(), polarity, get_term(left_term), get_term(right_term));

  // TODO: assumption: no duplicated literals in premise and rCl [but this assumption seems to be pervasive in vampire]
  // also, there is a DuplicateLiteralRemovalISE that is added in MainLoop. So we probably don't have to worry about that.
  int const nlen = premise->length() + qr.clause->length() - 1;
  ASS_GE(nlen, 1);

  Inference* inf = new Inference2(Inference::THEORY_INFERENCE_RULE_TRANSITIVITY, premise, qr.clause);
  Unit::InputType inputType = std::max(premise->inputType(), qr.clause->inputType());
  Clause* res = new(nlen) Clause(nlen, inputType, inf);

  (*res)[0] = newLit;

  int next = 1;
  for (int i = 0; i < premise->length(); ++i) {
    Literal* curr = (*premise)[i];
    if (curr != lit) {
      (*res)[next] = qr.substitution->applyToQuery(curr);
      next += 1;
    }
  }

  // we should have skipped exactly one literal (namely lit)
  ASS(next == 1 + (premise->length() - 1));

  for (int i = 0; i < qr.clause->length(); ++i) {
    Literal* curr = (*qr.clause)[i];
    if (curr != qr.literal) {
      (*res)[next] = qr.substitution->applyToResult(curr);
      next += 1;
    }
  }
  ASS(next == 1 + (premise->length() - 1) + (qr.clause->length() - 1));
  ASS(next == nlen);

  res->setAge(std::max(premise->age(), qr.clause->age()) + 1);
  // res->setPenalty(premise->penalty() + qr.clause->penalty() + 5);

  return res;
}

}  // namespace



/**
 *     r < s \/ C     t < u \/ D     θ = mgu(s, t)
 *    ---------------------------------------------
 *               rθ < uθ \/ Cθ \/ Dθ
 *
 *
 *     r < s \/ C     ~(t < u) \/ D     θ = mgu(r, t)
 *    ------------------------------------------------
 *               ~(sθ < uθ) \/ Cθ \/ Dθ
 *
 *  where the leftmost literal in each premise is selected.
 */
ClauseIterator TheoryRuleTransitivity::generateClauses(Clause* premise)
{
  CALL("TheoryRuleTransitivity::generateClauses");
  // We implement both rules at once.
  //
  // NOTE: the activated clause (argument "premise") can be the left or the right clause in the rule above (or both).


  // Uncomment this in case I want to show the broken version.
  // return generateClausesBroken(premise);


  // We need a new variable relative to the whole premise
  // so we can later apply the substitution without messing up the other term and C/D.
  unsigned const maxVar = premise->maxVar();
  ASS_L(maxVar, std::numeric_limits<decltype(maxVar)>::max());
  TermList newVar(maxVar + 1, false);
#if VDEBUG
  for (unsigned i = 0; i < premise->length(); ++i) {
    Literal* l = (*premise)[i];
    ASS(!l->containsSubterm(newVar));
  }
#endif

  auto it1 = premise->getSelectedLiteralIterator();

  // Any selected literal of the form:
  //    t < u
  // (positive or negative).
  auto it2 = getFilteredIterator(it1, [this](Literal* lit) -> bool {
    CALL("TheoryRuleTransitivity::generateClauses::it2");
    return lit->functor() == pred_int_less;
  });

  GeneratingLiteralIndex* index = _index.get();

  // Iterator<Iterator<Clause*>>
  auto it3 = getMappingIterator(it2, [index, premise, newVar](Literal* lit) {
    CALL("TheoryRuleTransitivity::generateClauses::it3");
    // Rule 1:
    //    1a, premise is right:
    //      lit = t < u
    //      find r < s with mgu(t,s)
    //      => query: x < t                       x < lit[0]
    //      => result: r < u                      qr[0] < lit[1]
    //    1b, premise is left:
    //      lit = r < s
    //      find t < u with mgu(t,s)
    //      => query: s < x                       lit[1] < x
    //      => result: r < u                      lit[0] < qr[1]
    // Rule 2:
    //    2a, premise is right:
    //      lit = ~(t < u)
    //      find r < s with mgu(t,r)
    //      => query: t < x                       lit[0] < x
    //      => result: ~(s < u)                   ~(qr[1] < lit[1])
    //    2b, premise is left:
    //      lit = r < s
    //      find ~(t < u) with mgu(t,r)
    //      => query: ~(r < x)                    ~(lit[0] < x)
    //      => result: ~(s < u)                   ~(lit[1] < qr[1])

    if (lit->isPositive()) {
      // Case 1a
      Literal* query1a = Literal::create2(lit->functor(), true, newVar, *lit->nthArgument(0));  // x < t   (unify with: r < s)
      auto unif1a = index->getUnifications(query1a, false, true);
      auto res1a = getMappingIterator(unif1a, ChainedClauseBuilder(premise, lit, true, term_source::result_left, term_source::selected_right));  // r < u
      // Case 1b
      Literal* query1b = Literal::create2(lit->functor(), true, *lit->nthArgument(1), newVar);  // s < x   (unify with: t < u)
      auto unif1b = index->getUnifications(query1b, false, true);
      auto res1b = getMappingIterator(unif1b, ChainedClauseBuilder(premise, lit, true, term_source::selected_left, term_source::result_right));  // r < u
      // Case 2b
      Literal* query2b = Literal::create2(lit->functor(), false, *lit->nthArgument(0), newVar);  // ~(r < x)   (unify with: ~(t < u))
      auto unif2b = index->getUnifications(query2b, false, true);
      auto res2b = getMappingIterator(unif2b, ChainedClauseBuilder(premise, lit, false, term_source::selected_right, term_source::result_right));  // ~(s < u)
      return pvi(getConcatenatedIterator(res1a, getConcatenatedIterator(res1b, res2b)));
    } else {
      ASS(lit->isNegative());
      // Case 2a
      Literal* query2a = Literal::create2(lit->functor(), true, *lit->nthArgument(0), newVar);  // t < x   (unify with: r < s)
      auto unif2a = index->getUnifications(query2a, false, true);
      auto res2a = getMappingIterator(unif2a, ChainedClauseBuilder(premise, lit, false, term_source::result_right, term_source::selected_right));  // ~(s < u)
      return pvi(res2a);
    }
  });
  static_assert(std::is_same<ELEMENT_TYPE(ELEMENT_TYPE(decltype(it3))), Clause*>::value, "");

  // Use a VirtualIterator here because only the specialization of getFlattenedIterator for VirtualIterator<VirtualIterator<T>> is lazy
  // (actually this is only necessary if we use output in the intermediate stages)
  auto it4 = getFlattenedIterator(pvi(it3));

  // TODO: Count the time used for this rule
  // // The outer iterator ensures we update the time counter for superposition
  auto it5 = getTimeCountedIterator(it4, TC_THEORY_TRANSITIVITY);

  return pvi(it5);
}





/**
 *     r < s \/ C     t < u \/ D     θ = mgu(s, t)
 *    ---------------------------------------------
 *               rθ < uθ \/ Cθ \/ Dθ
 *
 *
 *     r < s \/ C     ~(t < u) \/ D     θ = mgu(r, t)
 *    ------------------------------------------------
 *               ~(sθ < uθ) \/ Cθ \/ Dθ
 *
 *  where the leftmost literal in each premise is selected.
 */
ClauseIterator TheoryRuleTransitivity::generateClausesBroken(Clause* premise)
{
  CALL("TheoryRuleTransitivity::generateClausesBroken");
  // We implement both rules at once.
  //
  // NOTE:
  // Selected clause (the argument "premise") must be the right one,
  // because otherwise it could happen that r<s is added first,
  // then ~(t<u) and no match is found,
  // while in the other direction we would have found it.
  //
  // So we can use the polarity of the selected literal to decide
  // whether we are in the first or in the second rule.

  // TODO
  // The above note is wrong.
  // With this version, the example transitivity_rule_disjunctive finally works.
  // But the other two examples, transitivity_rule and transitivity_rule_subst are now broken!
  // Because of this, I suspect that the relevant inference is never applied.
  // I'm pretty sure this depends on the order the clauses are selected.
  // => change the rule so we don't lose potential application

  // We need a new variable relative to the premise
  // so we can later apply the substitution without messing up u and D.
  unsigned const maxVar = premise->maxVar();
  ASS_L(maxVar, std::numeric_limits<decltype(maxVar)>::max());
  TermList newVar(maxVar + 1, false);
#if VDEBUG
  for (unsigned i = 0; i < premise->length(); ++i) {
    Literal* l = (*premise)[i];
    ASS(!l->containsSubterm(newVar));
  }
#endif

  auto it1 = premise->getSelectedLiteralIterator();

  // Any selected literal of the form:
  //    t < u
  // (positive or negative).
  auto it2 = getFilteredIterator(it1, [this](Literal* lit) -> bool {
    CALL("TheoryRuleTransitivity::generateClauses::it2");
    return lit->functor() == pred_int_less;
  });

  // Iterator<Iterator<std::pair<Literal*,SLQueryResult>>>
  auto it3 = getMappingIterator(it2, [this, newVar](Literal* lit) {
    CALL("TheoryRuleTransitivity::generateClauses::it3");
    // Case 1, lit is positive:
    //    lit = t < u
    //    find r < s with mgu(t,s)
    // Case 2, lit is negative:
    //    lit = ~(t < u)
    //    find r < s with mgu(t,r)

    TermList const t = *lit->nthArgument(0);

    Literal* queryLit = nullptr;
    if (lit->isPositive()) {
      // template literal: x < t
      queryLit = Literal::create2(lit->functor(), true, newVar, t);
    } else {
      ASS(lit->isNegative());
      // template literal: t < x
      queryLit = Literal::create2(lit->functor(), true, t, newVar);
    }
    ASS(queryLit);

    // GeneratingLiteralIndex matches selected literals
    // TODO This rule can probably be improved by using a TermIndex instead (that only indexes on arguments of "<"). The question is if the tradeoff with index maintenance is worth it.
    auto unifIt1 = _index->getUnifications(queryLit, false, true);

    // Annotate each result with the currently selected literal
    auto unifIt2 = pushPairIntoRightIterator(lit, unifIt1);

    return pvi(unifIt2);  // need pvi here, otherwise getFlattenedIterator complains
  });
  static_assert(std::is_same<ELEMENT_TYPE(ELEMENT_TYPE(decltype(it3))), std::pair<Literal*, SLQueryResult>>::value, "");

  // Use a VirtualIterator here because only the specialization of getFlattenedIterator for VirtualIterator<VirtualIterator<T>> is lazy
  // (actually this is only necessary if we use output in the intermediate stages)
  auto it4 = getFlattenedIterator(pvi(it3));

  // Build the result clauses
  auto it5 = getMappingIterator(it4, [premise](std::pair<Literal*, SLQueryResult> arg) {
    CALL("TheoryRuleTransitivity::generateClauses::it5");
    Literal* lit = arg.first;             // t < u  or  ~(t < u)

    Clause* rCl = arg.second.clause;
    Literal* rLit = arg.second.literal;   // r < s  with either mgu(t,s) or mgu(t,r)

    // TODO: assumption: no duplicated literals in premise and rCl [but this assumption seems to be pervasive in vampire]
    // also, there is a DuplicateLiteralRemovalISE that is added in MainLoop. So we probably don't have to worry about that.
    int const nlen = premise->length() + rCl->length() - 1;
    ASS_GE(nlen, 1);

    Inference* inf = new Inference2(Inference::THEORY_INFERENCE_RULE_TRANSITIVITY, premise, rCl);
    Unit::InputType inpType = std::max(premise->inputType(), rCl->inputType());
    Clause* res = new(nlen) Clause(nlen, inpType, inf);

    auto theta = arg.second.substitution;
    Literal* newLit = nullptr;
    if (lit->isPositive()) {
      // rθ < uθ
      TermList r = *rLit->nthArgument(0);
      TermList u = *lit->nthArgument(1);
      newLit = Literal::create2(lit->functor(), true, theta->applyToResult(r), theta->applyToQuery(u));
    } else {
      ASS(lit->isNegative());
      // ~(sθ < uθ)
      TermList s = *rLit->nthArgument(1);
      TermList u = *lit->nthArgument(1);
      newLit = Literal::create2(lit->functor(), false, theta->applyToResult(s), theta->applyToQuery(u));
    }
    ASS(newLit);

    (*res)[0] = newLit;

    int next = 1;
    for (int i = 0; i < premise->length(); ++i) {
      Literal* curr = (*premise)[i];
      if (curr != lit) {
        (*res)[next] = theta->applyToQuery(curr);
        next += 1;
      }
    }
    // we should have skipped exactly one literal (namely lit)
    ASS(next == 1 + (premise->length() - 1));
    for (int i = 0; i < rCl->length(); ++i) {
      Literal* curr = (*rCl)[i];
      if (curr != rLit) {
        (*res)[next] = theta->applyToResult(curr);
        next += 1;
      }
    }
    ASS(next == 1 + (premise->length() - 1) + (rCl->length() - 1));
    ASS(next == nlen);

    res->setAge(std::max(premise->age(), rCl->age()) + 1);
    // res->setPenalty(premise->penalty() + rCl->penalty() + 5);

    return res;
  });

  return pvi(it5);
}
