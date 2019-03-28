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
  // NOTE:
  // Selected clause (the argument "premise") must be the right one,
  // because otherwise it could happen that r<s is added first,
  // then ~(t<u) and no match is found,
  // while in the other direction we would have found it.
  //
  // So we can use the polarity of the selected literal to decide
  // whether we are in the first or in the second rule.

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
      queryLit = Literal::create2(pred_int_less, true, newVar, t);
    } else {
      ASS(lit->isNegative());
      // template literal: t < x
      queryLit = Literal::create2(pred_int_less, true, t, newVar);
    }
    ASS(queryLit);

    // GeneratingLiteralIndex matches selected literals
    // TODO This rule can probably be improved by using a TermIndex instead (that only indexes on arguments of "<"). The question is if the tradeoff with index maintenance is worth it.
    auto unifIt1 = _index->getUnifications(queryLit, false, true);

    // Annotate each result with the currently selected literal
    auto unifIt2 = pushPairIntoRightIterator(lit, unifIt1);

    return pvi(unifIt2);  // need pvi here, otherwise getFlattenedIterator complains
  });
  static_assert(std::is_same_v<ELEMENT_TYPE(ELEMENT_TYPE(decltype(it3))), std::pair<Literal*, SLQueryResult>>);

  // Use a VirtualIterator here because only the specialization of getFlattenedIterator for VirtualIterator<VirtualIterator<T>> is lazy
  // (actually this is only necessary if we use output in the intermediate stages)
  auto it4 = getFlattenedIterator(pvi(it3));

  // Build the result clauses
  auto it5 = getMappingIterator(it4, [this, premise](std::pair<Literal*, SLQueryResult> arg) {
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
      newLit = Literal::create2(pred_int_less, true, theta->applyToResult(r), theta->applyToQuery(u));
    } else {
      ASS(lit->isNegative());
      // ~(sθ < uθ)
      TermList s = *rLit->nthArgument(1);
      TermList u = *lit->nthArgument(1);
      newLit = Literal::create2(pred_int_less, false, theta->applyToResult(s), theta->applyToQuery(u));
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
