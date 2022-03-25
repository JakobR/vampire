/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Induction.cpp
 * Implements class Induction.
 */

#include <utility>

#include "Debug/RuntimeStatistics.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Indexing/ResultSubstitution.hpp"

#include "Inferences/BinaryResolution.hpp"

#include "Lib/DHSet.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/IntUnionFind.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Set.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Connective.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InterpretedLiteralEvaluator.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/OperatorType.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/NewCNF.hpp"
#include "Shell/NNF.hpp"
#include "Shell/Rectify.hpp"

#include "Induction.hpp"

using std::pair;
using std::make_pair;

namespace Inferences
{
using namespace Kernel;
using namespace Lib; 

namespace {

void addToMapFromIterator(DHMap<Term*, TermQueryResult>& map, TermQueryResultIterator it) {
  while (it.hasNext()) {
    TermQueryResult tqr = it.next();
    ASS(tqr.term.isTerm());
    map.insert(tqr.term.term(), tqr);
  }
}

InferenceRule getGeneralizedRule(InferenceRule rule) {
  switch (rule) {
    case InferenceRule::INDUCTION_AXIOM:
    case InferenceRule::GEN_INDUCTION_AXIOM:
      return InferenceRule::GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM;
    default:
      ASSERTION_VIOLATION;
  }
}

InferenceRule getNonGeneralizedRule(InferenceRule rule) {
  switch (rule) {
    case InferenceRule::INDUCTION_AXIOM:
    case InferenceRule::GEN_INDUCTION_AXIOM:
      return InferenceRule::INDUCTION_AXIOM;
    case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_INF_UP_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM;
    case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_FIN_UP_INDUCTION_AXIOM;
    case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM;
    case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_DB_UP_INDUCTION_AXIOM;
    case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM;
    default:
      ASSERTION_VIOLATION;
  }
}

InferenceRule getInfRule(InferenceRule rule) {
  switch (rule) {
    case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
      return InferenceRule::INT_INF_UP_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
      return InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM;
    default:
      ASSERTION_VIOLATION;
  }
}

InferenceRule getFinRule(InferenceRule rule) {
  switch (rule) {
    case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
      return InferenceRule::INT_FIN_UP_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
      return InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM;
    default:
      ASSERTION_VIOLATION;
  }
}

InferenceRule getDBRule(InferenceRule rule) {
  switch (rule) {
    case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
      return InferenceRule::INT_DB_UP_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
      return InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM;
    default:
      ASSERTION_VIOLATION;
  }
}

Term* getPlaceholderForTerm(Term* t)
{
  CALL("getPlaceholderForTerm");
  static DHMap<TermList,Term*> placeholders;
  TermList srt = env.signature->getFunction(t->functor())->fnType()->result();
  if(!placeholders.find(srt)){
    unsigned fresh = env.signature->addFreshFunction(0,(srt.toString() + "_placeholder").c_str());
    env.signature->getFunction(fresh)->setType(OperatorType::getConstantsType(srt));
    placeholders.insert(srt,Term::createConstant(fresh));
  }
  return placeholders.get(srt);
}

};  // namespace

TermList TermReplacement::transformSubterm(TermList trm)
{
  CALL("TermReplacement::transformSubterm");

  if(trm.isTerm() && trm.term()==_o){
    return _r;
  }
  return trm;
}

TermList SkolemSquashingTermReplacement::transformSubterm(TermList trm)
{
  CALL("SkolemSquashingTermReplacement::transformSubterm");

  if(trm.isTerm()) {
    auto t = trm.term();
    if (t==_o){
      return _r;
    }
    unsigned f = t->functor();
    if (env.signature->getFunction(f)->skolem()) {
      unsigned v;
      if (!_tv.find(t,v)) {
        v = _v++;
        _tv.insert(t,v);
      }
      return TermList(v,false);
    }
  }
  return trm;
}

Literal* replaceTermInLiteral(Literal* lit, Term* o, TermList r) {
  TermReplacement tr(o,r);
  return tr.transform(lit);
}

Formula* InductionContext::getFormula(TermReplacement& tr, bool opposite)
{
  CALL("InductionContext::getFormula/1");

  ASS(!_cls.empty());
  auto argLists = FormulaList::empty();
  for (const auto& kv : _cls) {
    auto argList = FormulaList::empty();
    for (const auto& lit : kv.second) {
      auto tlit = tr.transform(lit);
      FormulaList::push(new AtomicFormula(opposite ? Literal::complementaryLiteral(tlit) : tlit), argList);
    }
    FormulaList::push(JunctionFormula::generalJunction(opposite ? Connective::AND : Connective::OR, argList), argLists);
  }
  return JunctionFormula::generalJunction(opposite ? Connective::OR : Connective::AND, argLists);
}

Formula* InductionContext::getFormula(TermList r, bool opposite, Substitution* subst)
{
  CALL("InductionContext::getFormula/2");

  TermReplacement tr(getPlaceholderForTerm(_indTerm), r);
  if (subst) {
    ASS(r.isVar());
    subst->bind(r.var(), getPlaceholderForTerm(_indTerm));
  }
  return getFormula(tr, opposite);
}

Formula* InductionContext::getFormulaWithSquashedSkolems(TermList r, bool opposite,
  unsigned& var, VList** varList, Substitution* subst)
{
  CALL("InductionContext::getFormulaWithSquashedSkolems");

  const bool strengthenHyp = env.options->inductionStrengthenHypothesis();
  if (!strengthenHyp) {
    return getFormula(r, opposite, subst);
  }
  SkolemSquashingTermReplacement tr(getPlaceholderForTerm(_indTerm), r, var);
  unsigned temp = var;
  auto res = getFormula(tr, opposite);
  if (subst) {
    ASS(r.isVar());
    subst->bind(r.var(), getPlaceholderForTerm(_indTerm));
    DHMap<Term*,unsigned>::Iterator it(tr._tv);
    while (it.hasNext()) {
      unsigned v;
      Term* t;
      it.next(t, v);
      subst->bind(v,t);
    }
  }
  if (varList) {
    // The variables replacing the Skolems after calling transform
    // are needed for quantification if varList is non-null, collect them
    for (unsigned i = temp; i < var; i++) {
      VList::push(i,*varList);
    }
  }
  return res;
}

TermList LiteralSubsetReplacement::transformSubterm(TermList trm)
{
  CALL("LiteralSubsetReplacement::transformSubterm");

  if(trm.isTerm() && trm.term() == _o){
    // Replace either if there are too many occurrences to try all possibilities,
    // or if the bit in _iteration corresponding to this match is set to 1.
    if ((_occurrences > _maxOccurrences) || (1 & (_iteration >> _matchCount++))) {
      return _r;
    }
  }
  return trm;
}

Literal* LiteralSubsetReplacement::transformSubset(InferenceRule& rule) {
  CALL("LiteralSubsetReplacement::transformSubset");
  // Increment _iteration, since it either is 0, or was already used.
  _iteration++;
  // Note: __builtin_popcount() is a GCC built-in function.
  unsigned setBits = __builtin_popcount(_iteration);
  // Skip this iteration if not all bits are set, but more than maxSubset are set.
  while ((_iteration <= _maxIterations) &&
         ((_maxSubsetSize > 0) && (setBits < _occurrences) && (setBits > _maxSubsetSize))) {
    _iteration++;
    setBits = __builtin_popcount(_iteration);
  }
  if ((_iteration >= _maxIterations) ||
      ((_occurrences > _maxOccurrences) && (_iteration > 1))) {
    // All combinations were already returned.
    return nullptr;
  }
  if (setBits == _occurrences) {
    rule = getNonGeneralizedRule(rule);
  } else {
    rule = getGeneralizedRule(rule);
  }
  _matchCount = 0;
  return transform(_lit);
}

List<pair<Literal*, InferenceRule>>* LiteralSubsetReplacement::getListOfTransformedLiterals(InferenceRule rule) {
  CALL("LiteralSubsetReplacement::getListOfTransformedLiterals");

  Literal* l;
  List<pair<Literal*, InferenceRule>>* res = List<pair<Literal*, InferenceRule>>::empty();
  while ((l = transformSubset(rule))) {
    res = List<pair<Literal*, InferenceRule>>::cons(make_pair(l, rule), res);
  }
  return res;
}

ContextSubsetReplacement::ContextSubsetReplacement(InductionContext context, bool noGen)
  : _context(context), _r(getPlaceholderForTerm(context._indTerm))
{
  unsigned occurrences = 0;
  for (const auto& kv : _context._cls) {
    for (const auto& lit : kv.second) {
      occurrences += lit->countSubtermOccurrences(TermList(_context._indTerm));
    }
  }
  _maxIterations = pow(2, occurrences);
  if (noGen) {
    _iteration = _maxIterations - 2;
  }
}

TermList ContextSubsetReplacement::transformSubterm(TermList trm)
{
  CALL("ContextSubsetReplacement::transformSubterm");
  if (trm.isTerm() && trm.term() == _context._indTerm){
    // Replace if the bit in _iteration corresponding to this match is set to 1.
    if (1 & (_iteration >> _matchCount++)) {
      return _r;
    }
  }
  return trm;
}

InductionContext ContextSubsetReplacement::next() {
  CALL("ContextSubsetReplacement::transformSubset");
  ASS(hasNext());
  InductionContext context;
  context._indTerm = _context._indTerm;
  _iteration++;
  _matchCount = 0;
  for (const auto& kv : _context._cls) {
    for (const auto& lit : kv.second) {
      auto tlit = transform(lit);
      if (tlit != lit) {
        context.insert(kv.first, tlit);
      }
    }
  }
  return context;
}

void Induction::attach(SaturationAlgorithm* salg) {
  CALL("Induction::attach");

  GeneratingInferenceEngine::attach(salg);
  if (InductionHelper::isIntInductionOn()) {
    _comparisonIndex = static_cast<LiteralIndex*>(_salg->getIndexManager()->request(UNIT_INT_COMPARISON_INDEX));
  }
  if (InductionHelper::isIntInductionTwoOn()) {
    _inductionTermIndex = static_cast<TermIndex*>(_salg->getIndexManager()->request(INDUCTION_TERM_INDEX));
  }
  _structInductionTermIndex = static_cast<TermIndex*>(
    _salg->getIndexManager()->request(STRUCT_INDUCTION_TERM_INDEX));
}

void Induction::detach() {
  CALL("Induction::detach");

  _structInductionTermIndex = nullptr;
  _salg->getIndexManager()->release(STRUCT_INDUCTION_TERM_INDEX);
  if (InductionHelper::isIntInductionOn()) {
    _comparisonIndex = nullptr;
    _salg->getIndexManager()->release(UNIT_INT_COMPARISON_INDEX);
  }
  if (InductionHelper::isIntInductionTwoOn()) {
    _inductionTermIndex = nullptr;
    _salg->getIndexManager()->release(INDUCTION_TERM_INDEX);
  }
  GeneratingInferenceEngine::detach();
}

ClauseIterator Induction::generateClauses(Clause* premise)
{
  CALL("Induction::generateClauses");

  return pvi(InductionClauseIterator(premise, InductionHelper(_comparisonIndex, _inductionTermIndex), getOptions(),
    _structInductionTermIndex, _formulaIndex));
}

void InductionClauseIterator::processClause(Clause* premise)
{
  CALL("InductionClauseIterator::processClause");

  // The premise should either contain a literal on which we want to apply induction,
  // or it should be an integer constant comparison we use as a bound.
  if (InductionHelper::isInductionClause(premise)) {
    for (unsigned i=0;i<premise->length();i++) {
      processLiteral(premise,(*premise)[i]);
    }
  }
  if (InductionHelper::isIntInductionTwoOn() && InductionHelper::isIntegerComparison(premise)) {
    processIntegerComparison(premise, (*premise)[0]);
  }
}

struct InductionContextFn
{
  InductionContextFn(Clause* premise, Literal* lit) : _premise(premise), _lit(lit) {}

  InductionContext operator()(pair<Term*, VirtualIterator<TermQueryResult>> arg) {
    Set<Literal*> lits;
    lits.insert(_lit);
    InductionContext ctx(arg.first, _lit, _premise);
    auto indDepth = _premise->inference().inductionDepth();
    if (indDepth && !env.signature->getFunction(arg.first->functor())->arity()) {
      return ctx;
    }
    while (arg.second.hasNext()) {
      auto tqr = arg.second.next();
      // TODO: having the same literal multiple times has unwanted effects
      // in the clausification/resolution part, so avoid it for now
      if (lits.contains(tqr.literal)) {
        continue;
      }
      lits.insert(tqr.literal);
      if (_premise == tqr.clause && _lit == tqr.literal) {
        continue;
      }
      if (indDepth != tqr.clause->inference().inductionDepth()) {
        continue;
      }
      // if induction depth is >0, we need further check
      if (indDepth) {
        if (tqr.clause == _premise) {
          continue;
        }
        if (_lit->functor() != tqr.literal->functor()) {
          continue;
        }
        bool match = false;
        SubtermIterator sti1(_lit);
        SubtermIterator sti2(tqr.literal);
        while (sti1.hasNext()) {
          ALWAYS(sti2.hasNext());
          auto st1 = sti1.next();
          auto st2 = sti2.next();
          if (st1 != st2) {
            if (match || !st1.containsSubterm(st2) || st2.term() != arg.first) {
              match = false;
              break;
            }
            sti1.right();
            sti2.right();
            match = true;
          }
        }
        if (!match) {
          continue;
        }
      }
      ctx.insert(tqr.clause, tqr.literal);
    }
    return ctx;
  }
private:
  Clause* _premise;
  Literal* _lit;
};

void InductionClauseIterator::processLiteral(Clause* premise, Literal* lit)
{
  CALL("Induction::ClauseIterator::processLiteral");

  if(_opt.showInduction()){
    env.beginOutput();
    env.out() << "[Induction] process " << lit->toString() << " in " << premise->toString() << endl;
    env.endOutput();
  }

  if (lit->ground()) {
      Set<Term*> ta_terms;
      Set<Term*> int_terms;
      //TODO this should be a non-variable non-type iterator it seems
      SubtermIterator it(lit);
      while(it.hasNext()){
        TermList ts = it.next();
        if(!ts.isTerm()){ continue; }
        unsigned f = ts.term()->functor(); 
        if(InductionHelper::isInductionTermFunctor(f)){
          if(InductionHelper::isStructInductionOn() && InductionHelper::isStructInductionFunctor(f)){
            ta_terms.insert(ts.term());
          }
          if(InductionHelper::isIntInductionOneOn() && InductionHelper::isIntInductionTermListInLiteral(ts, lit)){
            int_terms.insert(ts.term());
          }
        }
      }

    if (InductionHelper::isInductionLiteral(lit)) {
      Set<Term*>::Iterator citer1(int_terms);
      while(citer1.hasNext()){
        Term* t = citer1.next();
        List<pair<Literal*, InferenceRule>>* indLits = List<pair<Literal*, InferenceRule>>::empty();
        DHMap<Term*, TermQueryResult> grBound;
        addToMapFromIterator(grBound, _helper.getGreaterEqual(t));
        addToMapFromIterator(grBound, _helper.getGreater(t));
        DHMap<Term*, TermQueryResult> leBound;
        addToMapFromIterator(leBound, _helper.getLessEqual(t));
        addToMapFromIterator(leBound, _helper.getLess(t));
        performIntInductionForEligibleBounds(premise, lit, t, indLits, /*increasing=*/true, leBound, grBound);
        performIntInductionForEligibleBounds(premise, lit, t, indLits, /*increasing=*/false, grBound, leBound);
        List<pair<Literal*, InferenceRule>>::destroy(indLits);
      }
    }
    // collect term queries for each induction term
    auto sideLitsIt = iterTraits(Set<Term*>::Iterator(ta_terms))
      .map([this](Term* arg) {
        return make_pair(arg, _structInductionTermIndex->getGeneralizations(TermList(arg), true));
      });
    // put clauses from queries into contexts alongside with the given clause and induction term
    auto sideLitsIt2 = iterTraits(getMappingIterator(sideLitsIt, InductionContextFn(premise, lit)))
      // filter out that have no "induction literal" or not multi-clause
      .filter([](const InductionContext& arg) {
        return !arg.isSingleLiteral() && arg.hasInductionLiteral();
      });
    // collect contexts for single-literal induction with given clause
    auto indCtxSingle = iterTraits(Set<Term*>::Iterator(ta_terms))
      .map([&lit,&premise](Term* arg) {
        return InductionContext(arg, lit, premise);
      })
      .filter([](const InductionContext& arg) {
        return arg.hasInductionLiteral();
      });
    // generalize all contexts if needed
    auto indCtxIt = iterTraits(getConcatenatedIterator(sideLitsIt2, indCtxSingle))
      .flatMap([](const InductionContext& arg) {
        return vi(new ContextSubsetReplacement(arg, !env.options->inductionGen()));
      });
    while (indCtxIt.hasNext()) {
      auto ctx = indCtxIt.next();
      static bool one = _opt.structInduction() == Options::StructuralInductionKind::ONE ||
                        _opt.structInduction() == Options::StructuralInductionKind::ALL;
      static bool two = _opt.structInduction() == Options::StructuralInductionKind::TWO ||
                        _opt.structInduction() == Options::StructuralInductionKind::ALL;
      static bool three = _opt.structInduction() == Options::StructuralInductionKind::THREE ||
                        _opt.structInduction() == Options::StructuralInductionKind::ALL;
      InferenceRule rule = InferenceRule::INDUCTION_AXIOM;
      InductionFormulaVariantIndex::Entry* e;
      if (_formulaIndex.findOrInsert(ctx, e)) {
        if(one){
          performStructInductionOne(ctx,e,rule);
        }
        if(two){
          performStructInductionTwo(ctx,e,rule);
        }
        if(three){
          performStructInductionThree(ctx,e,rule);
        }
      }
      for (auto& kv : e->get()) {
        resolveClauses(kv.first, ctx, kv.second);
      }
    }
  }
}

void InductionClauseIterator::performIntInductionForEligibleBounds(Clause* premise, Literal* origLit, Term* origTerm, List<pair<Literal*, InferenceRule>>*& indLits, bool increasing, DHMap<Term*, TermQueryResult>& bounds1, DHMap<Term*, TermQueryResult>& bounds2) {
  DHMap<Term*, TermQueryResult>::Iterator it1(bounds1);
  while (it1.hasNext()) {
    TermQueryResult b1 = it1.next();
    // Skip if the premise equals the bound (that would add tautologies to the search space).
    if (b1.clause != premise) {
      if (_helper.isInductionForFiniteIntervalsOn()) {
        DHMap<Term*, TermQueryResult>::Iterator it2(bounds2);
        while (it2.hasNext()) {
          TermQueryResult b2 = it2.next();
          if (notDoneInt(origLit, origTerm, increasing, b1.term.term(), b2.term.term(), /*bool fromComparison=*/b1.literal != nullptr)) {
            generalizeAndPerformIntInduction(premise, origLit, origTerm, indLits, increasing, b1, &b2);
          }
        }
      }
      if (_helper.isInductionForInfiniteIntervalsOn() &&
          notDoneInt(origLit, origTerm, increasing, b1.term.term(), /*optionalBound2=*/nullptr, /*bool fromComparison=*/b1.literal != nullptr)) {
        generalizeAndPerformIntInduction(premise, origLit, origTerm, indLits, increasing, b1, nullptr);
      }
    }
  }
  static bool useDefaultBound = _opt.integerInductionDefaultBound();
  if (useDefaultBound && _helper.isInductionForInfiniteIntervalsOn()) {
    static TermQueryResult defaultBound(TermList(theory->representConstant(IntegerConstantType(0))), nullptr, nullptr);
    if (notDoneInt(origLit, origTerm, increasing, defaultBound.term.term(), /*optionalBound2=*/nullptr, /*fromComparison=*/false)) {
      generalizeAndPerformIntInduction(premise, origLit, origTerm, indLits, increasing, defaultBound, nullptr);
    }
  }
}

void InductionClauseIterator::generalizeAndPerformIntInduction(Clause* premise, Literal* origLit, Term* origTerm, List<pair<Literal*, InferenceRule>>*& indLits, bool increasing, TermQueryResult& bound1, TermQueryResult* optionalBound2) {
  static bool generalize = _opt.inductionGen();
  auto indTerm = getPlaceholderForTerm(origTerm);
  // If induction literals were not computed yet, compute them now.
  if (List<pair<Literal*, InferenceRule>>::isEmpty(indLits)) {
    bool finite = ((optionalBound2 != nullptr) && (optionalBound2->literal != nullptr));
    InferenceRule rule =
        (bound1.literal == nullptr)
            ? (increasing ? InferenceRule::INT_DB_UP_INDUCTION_AXIOM : InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM)
            : (increasing ? (finite ? InferenceRule::INT_FIN_UP_INDUCTION_AXIOM : InferenceRule::INT_INF_UP_INDUCTION_AXIOM)
                          : (finite ? InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM : InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM));
    if (generalize) {
      Kernel::LiteralSubsetReplacement subsetReplacement(origLit, origTerm, TermList(indTerm), _opt.maxInductionGenSubsetSize());
      indLits = subsetReplacement.getListOfTransformedLiterals(rule);
    } else {
      TermReplacement tr(origTerm, TermList(indTerm));
      indLits = new List<pair<Literal*, InferenceRule>>(make_pair(tr.transform(origLit), rule));
    }
  }
  List<pair<Literal*, InferenceRule>>::RefIterator it(indLits);
  while (it.hasNext()) {
    auto& litAndRule = it.next();
    ASS(litAndRule.first != nullptr);
    InductionContext context;
    context._indTerm = origTerm;
    context.insert(premise, litAndRule.first);
    performIntInduction(context, litAndRule.second, increasing, bound1, optionalBound2);
  }
}

void InductionClauseIterator::processIntegerComparison(Clause* premise, Literal* lit)
{
  CALL("Induction::ClauseIterator::processIntegerComparison");

  ASS((theory->interpretPredicate(lit) == Theory::INT_LESS) && lit->ground());

  bool positive = lit->isPositive();
  TermList* lesserTL = lit->nthArgument(positive ? 0 : 1);
  TermList* greaterTL = lit->nthArgument(positive ? 1 : 0);
  ASS(lesserTL != nullptr);
  ASS(greaterTL != nullptr);
  Term* lt = lesserTL->term();
  Term* gt = greaterTL->term();
  DHMap<Term*, TermQueryResult> grBound;
  addToMapFromIterator(grBound, _helper.getGreaterEqual(gt));
  addToMapFromIterator(grBound, _helper.getGreater(gt));
  performIntInductionOnEligibleLiterals(
    gt, _helper.getTQRsForInductionTerm(*greaterTL), /*increasing=*/true, TermQueryResult(*lesserTL, lit, premise), grBound);
  DHMap<Term*, TermQueryResult> leBound;
  addToMapFromIterator(leBound, _helper.getLessEqual(lt));
  addToMapFromIterator(leBound, _helper.getLess(lt));
  performIntInductionOnEligibleLiterals(
    lt, _helper.getTQRsForInductionTerm(*lesserTL), /*increasing=*/false, TermQueryResult(*greaterTL, lit, premise), leBound);
}

void InductionClauseIterator::performIntInductionOnEligibleLiterals(Term* origTerm, TermQueryResultIterator inductionTQRsIt, bool increasing, TermQueryResult bound1, DHMap<Term*, TermQueryResult>& bounds2) {
  while (inductionTQRsIt.hasNext()) {
    TermQueryResult tqr = inductionTQRsIt.next();
    // Skip if the TQR clause is equal to the bound clause (that would add tautologies to the search space).
    if (bound1.clause != tqr.clause) {
      // We need to pass an empty list, which will get populated when performing induction.
      // Then we need to destroy it.
      List<pair<Literal*, InferenceRule>>* indLits = List<pair<Literal*, InferenceRule>>::empty();
      if (_helper.isInductionForFiniteIntervalsOn()) {
        DHMap<Term*, TermQueryResult>::Iterator it(bounds2);
        while (it.hasNext()) {
          TermQueryResult bound2 = it.next();
          if (notDoneInt(tqr.literal, origTerm, increasing, bound1.term.term(), bound2.term.term(), /*bool fromComparison=*/bound1.literal != nullptr)) {
            generalizeAndPerformIntInduction(tqr.clause, tqr.literal, origTerm, indLits, increasing, bound1, &bound2);
          }
        }
      }
      if (_helper.isInductionForInfiniteIntervalsOn() &&
          notDoneInt(tqr.literal, origTerm, increasing, bound1.term.term(), /*optionalBound2=*/nullptr, /*bool fromComparison=*/bound1.literal != nullptr)) {
        generalizeAndPerformIntInduction(tqr.clause, tqr.literal, origTerm, indLits, increasing, bound1, nullptr);
      }
      List<pair<Literal*, InferenceRule>>::destroy(indLits);
    }
  }
}

ClauseStack InductionClauseIterator::produceClauses(Formula* hypothesis, InferenceRule rule, InductionContext& context)
{
  CALL("InductionClauseIterator::produceClauses");
  NewCNF cnf(0);
  cnf.setForInduction();
  Stack<Clause*> hyp_clauses;
  Inference inf = NonspecificInference0(UnitInputType::AXIOM,rule);
  unsigned maxInductionDepth = 0;
  for (const auto& kv : context._cls) {
    maxInductionDepth = max(maxInductionDepth,kv.first->inference().inductionDepth());
  }
  inf.setInductionDepth(maxInductionDepth+1);
  FormulaUnit* fu = new FormulaUnit(hypothesis,inf);
  if(_opt.showInduction()){
    env.beginOutput();
    env.out() << "[Induction] formula " << fu->toString() << endl;
    env.endOutput();
  }
  cnf.clausify(NNF::ennf(fu), hyp_clauses);
  return hyp_clauses;
}

bool contains(Literal* clit, Term* indTerm, const ClauseToLiteralMap& toResolve) {
  CALL("contains");
  for (const auto& kv : toResolve) {
    for (const auto& lit : kv.second) {
      if (lit == clit) {
        return true;
      }
    }
  }
  return false;
}

IntUnionFind findDistributedVariants(const Stack<Clause*>& clauses, Substitution& subst, InductionContext& context)
{
  CALL("findDistributedVariants");
  auto toResolve = context._cls;
  IntUnionFind uf(clauses.size());
  for (unsigned i = 0; i < clauses.size(); i++) {
    auto cl = clauses[i];
    Stack<Literal*> conclusionLits(toResolve.size());
#if VDEBUG
    Stack<unsigned> variantCounts(toResolve.size());
#endif
    // we first find the conclusion literals in cl, exactly 1 from
    // each of toResolve and save how many variants it should have
    for (unsigned k = 0; k < cl->length(); k++) {
      auto clit = Literal::complementaryLiteral((*cl)[k]);
      for (const auto& kv : toResolve) {
#if VDEBUG
        bool found = false;
#endif
        for (const auto& lit : kv.second) {
          if (lit == SubstHelper::apply<Substitution>(clit, subst)) {
            conclusionLits.push((*cl)[k]);
#if VDEBUG
            variantCounts.push(kv.second.size()-1);
            ASS(!found);
            found = true;
#else
            break;
#endif
          }
        }
      }
    }
    // cl should have the same number of conclusion
    // literals as the size of toResolve
    ASS_EQ(conclusionLits.size(), toResolve.size());
    // now we look for the variants
    for (unsigned k = 0; k < conclusionLits.size(); k++) {
#if VDEBUG
      for (unsigned j = 0; j < clauses.size(); j++) {
#else
      for (unsigned j = i+1; j < clauses.size(); j++) {
#endif
        auto other = clauses[j];
        if (i == j || cl->length() != other->length()) {
          continue;
        }
        if (other->contains(conclusionLits[k])) {
          continue;
        }
        unsigned mismatchCnt = 0;
        for (unsigned l = 0; l < cl->length(); l++) {
          if (!cl->contains((*other)[l])) {
            mismatchCnt++;
          }
        }
        if (mismatchCnt == 1) {
#if VDEBUG
          variantCounts[k]--;
#endif
          uf.doUnion(i,j);
        }
      }
      ASS_EQ(variantCounts[k],0);
    }
  }
  uf.evalComponents();
  return uf;
}

Clause* resolveClausesHelper(InductionContext& context, const Stack<Clause*>& cls, IntUnionFind::ElementIterator eIt, Substitution& subst, RobSubstitution* rsubst)
{
  CALL("resolveClauses");
  ASS(eIt.hasNext());
  auto cl = cls[eIt.next()];
  unsigned newLength = cl->length();
  auto premises = UnitList::singleton(cl);
  auto toResolve = context._cls;
  while (eIt.hasNext()) {
    auto other = cls[eIt.next()];
    ASS_EQ(other->length(),newLength);
    UnitList::push(other,premises);
  }

  for (const auto& kv : toResolve) {
    newLength += kv.first->length() - kv.second.size() - 1;
    UnitList::push(kv.first, premises);
  }

  Inference inf(GeneratingInferenceMany(InferenceRule::RESOLUTION, premises));
  Clause* res = new(newLength) Clause(newLength, inf);

  unsigned next = 0;
  for (unsigned i = 0; i < cl->length(); i++) {
    Literal* curr=(*cl)[i];
    auto clit = SubstHelper::apply<Substitution>(Literal::complementaryLiteral(curr), subst);
    if (!contains(clit, context._indTerm, toResolve)) {
      ASS(next < newLength);
      (*res)[next] = rsubst ? rsubst->apply(curr, 0) : curr;
      next++;
    }
  }

  for (const auto& kv : toResolve) {
    for (unsigned i = 0; i < kv.first->length(); i++) {
      bool copyCurr = true;
      for (const auto& lit : kv.second) {
        auto rlit = replaceTermInLiteral(lit, getPlaceholderForTerm(context._indTerm), TermList(context._indTerm));
        if (rlit == (*kv.first)[i]) {
          copyCurr = false;
          break;
        }
      }
      if (copyCurr) {
        (*res)[next] = (*kv.first)[i];
        next++;
      }
    }
  }
  ASS_EQ(next,newLength);

  env.statistics->resolution++;
  return res;
}

void InductionClauseIterator::resolveClauses(const ClauseStack& cls, InductionContext& context, Substitution& subst, RobSubstitution* rsubst)
{
  // It might happen that NewCNF finds all generated clauses tautological
  if (cls.isEmpty()) {
    return;
  }

  auto uf = findDistributedVariants(cls, subst, context);
  IntUnionFind::ComponentIterator cit(uf);
  while(cit.hasNext()){
    IntUnionFind::ElementIterator eIt = cit.next();
    _clauses.push(resolveClausesHelper(context, cls, eIt, subst, rsubst));
    if(_opt.showInduction()){
      env.beginOutput();
      env.out() << "[Induction] generate " << _clauses.top()->toString() << endl;
      env.endOutput();
    }
  }
  auto rule = cls[0]->inference().rule();
  env.statistics->induction++;
  if (rule == InferenceRule::GEN_INDUCTION_AXIOM ||
      rule == InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM ||
      rule == InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM ||
      rule == InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM ||
      rule == InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM ||
      rule == InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM ||
      rule == InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM) {
    env.statistics->generalizedInduction++;
  }
  switch (rule) {
    case InferenceRule::INDUCTION_AXIOM:
    case InferenceRule::GEN_INDUCTION_AXIOM:
      env.statistics->structInduction++;
      break;
    case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM:
      env.statistics->intInfInduction++;
      break;
    case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM:
      env.statistics->intFinInduction++;
      break;
    case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM:
      env.statistics->intDBInduction++;
      break;
    default:
      ;
  }
  switch (rule) {
    case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM:
      env.statistics->intInfUpInduction++;
      break;
    case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM:
      env.statistics->intInfDownInduction++;
      break;
    case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM:
      env.statistics->intFinUpInduction++;
      break;
    case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM:
      env.statistics->intFinDownInduction++;
      break;
    case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM:
      env.statistics->intDBUpInduction++;
      break;
    case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM:
      env.statistics->intDBDownInduction++;
      break;
    default:
      ;
  }
}

// Given a literal ~L[term], where 'term' is of the integer sort,
// introduce and induction hypothesis for integers, for example:
//   (L[b1] & (![X] : (b1 <= X & X < b2 & L[X]) -> L[x+1])) -> (![Y] : (b1 <= Y & Y <= b2) -> L[Y])
// In general, the hypothesis is an instance of one of the following
// hypotheses (depending on the value of 'increasing'):
//   (L[b1] & (![X] : (interval_x(X)) -> L[x+1])) -> (![Y] : interval_y(Y) -> L[Y])
//   (L[b1] & (![X] : (interval_x(X)) -> L[x-1])) -> (![Y] : interval_y(Y) -> L[Y])
// where 'b1' is bound1.term, and the predicates inteval_x(X) and interval_y(Y)
// capture the property "X (or Y) belongs to the interval [b1, b2] or [b1, b2)",
// where 'b2' is either optionalBound2->term (if present) or depending on 'increasing'
// either infinity or -infinity. (The intervals are set such that the hypothesis
// is valid: if interval_y(Y) holds for some Y, then either interval_x(Y) holds,
// or depending on 'increasing' either interval_x(Y-1) or interval_x(Y+1) holds.)
void InductionClauseIterator::performIntInduction(InductionContext& context, InferenceRule rule, bool increasing, const TermQueryResult& bound1, TermQueryResult* optionalBound2)
{
  CALL("InductionClauseIterator::performIntInduction");

  TermList b1(bound1.term);
  TermList one(theory->representConstant(IntegerConstantType(increasing ? 1 : -1)));

  TermList x(0,false);
  TermList y(1,false);

  // create L[b1]
  Formula* Lb1 = context.getFormula(b1,true);

  // create L[X]
  Formula* Lx = context.getFormula(x,true);

  // create L[Y]
  Substitution subst;
  Formula* Ly = context.getFormula(y,true,&subst);

  // create L[X+1] or L[X-1]
  TermList fpo(Term::create2(env.signature->getInterpretingSymbol(Theory::INT_PLUS),x,one));
  Formula* Lxpo = context.getFormula(fpo,true);

  static unsigned less = env.signature->getInterpretingSymbol(Theory::INT_LESS);
  // create X>=b1 (which is ~X<b1) or X<=b1 (which is ~b1<X)
  Formula* Lxcompb1 = new AtomicFormula(Literal::create2(less,false,(increasing ? x : b1),(increasing ? b1 : x)));
  // create Y>=b1 (which is ~Y<b1), or Y>b1, or Y<=b1 (which is ~b1<Y), or Y<b1
  // This comparison is mirroring the structure of bound1.literal, which is "b1 <comparison> inductionTerm".
  // If bound1.literal is nullptr, we are using the default bound with the comparison sign >= or <=.
  const bool isBound1Equal = (!bound1.literal || (bound1.literal->functor() == less && bound1.literal->isNegative()));
  const bool isBound1FirstArg = (increasing != isBound1Equal);
  Formula* Lycompb1 = new AtomicFormula(Literal::create2(
        less, !isBound1Equal, (isBound1FirstArg ? b1 : y), (isBound1FirstArg ? y : b1)));

  Formula* FxInterval;
  Formula* FyInterval;
  const bool isDefaultBound = ((bound1.clause == nullptr) || (bound1.literal == nullptr));
  const bool hasBound2 = ((optionalBound2 != nullptr) && (optionalBound2->literal != nullptr));
  // Also resolve the hypothesis with comparisons with bound(s) (if the bound(s) are present/not default).
  if (!isDefaultBound) {
    context.insert(bound1.clause, replaceTermInLiteral(bound1.literal, context._indTerm, TermList(getPlaceholderForTerm(context._indTerm))));
  }
  if (hasBound2) {
    // Finite interval induction, use two bounds on both x and y.
    rule = getFinRule(rule);
    TermList b2(optionalBound2->term);
    // create X<b2 or X>b2 (which is b2<X)
    Formula* Lxcompb2 = new AtomicFormula(Literal::create2(less, true, (increasing ? x : b2), (increasing ? b2 : x)));
    const bool isBound2Equal = (optionalBound2->literal->functor() == less && optionalBound2->literal->isNegative());
    const bool isBound2FirstArg = (increasing == isBound2Equal);
    // create Y<b2, or Y<=b2 (which is ~b2<Y) or Y>b2, or Y>=b2 (which is ~Y<b2)
    Formula* Lycompb2 = new AtomicFormula(Literal::create2(
          less, !isBound2Equal, (isBound2FirstArg ? b2 : y), (isBound2FirstArg ? y : b2)));
    FxInterval = new JunctionFormula(Connective::AND, FormulaList::cons(Lxcompb1, FormulaList::singleton(Lxcompb2)));
    FyInterval = new JunctionFormula(Connective::AND, FormulaList::cons(Lycompb1, FormulaList::singleton(Lycompb2)));
    if (!isDefaultBound) {
      // If there is also a second bound, add that to the list as well.
      context.insert(optionalBound2->clause, replaceTermInLiteral(optionalBound2->literal, context._indTerm, TermList(getPlaceholderForTerm(context._indTerm))));
    }
  } else {
    // Infinite interval induction (either with default bound or not), use only one bound on both x and y.
    if (isDefaultBound) rule = getDBRule(rule);
    else rule = getInfRule(rule);
    FxInterval = Lxcompb1;
    FyInterval = Lycompb1;
  }

  // Create the hypothesis, with FxInterval and FyInterval being as described
  // in the comment above this function.
  Formula* hyp = new BinaryFormula(Connective::IMP,
                   new JunctionFormula(Connective::AND,FormulaList::cons(Lb1,FormulaList::singleton(
                     Formula::quantify(new BinaryFormula(Connective::IMP,
                       new JunctionFormula(Connective::AND, FormulaList::cons(FxInterval,FormulaList::singleton(Lx))),
                       Lxpo))))),
                   Formula::quantify(new BinaryFormula(Connective::IMP,FyInterval,Ly)));

  RobSubstitution rsubst;
  if (isDefaultBound) {
    ALWAYS(rsubst.match(y,0,TermList(context._indTerm),1));
  }

  auto cls = produceClauses(hyp, rule, context);
  resolveClauses(cls, context, subst, isDefaultBound ? &rsubst : nullptr);
}

/**
 * Introduce the Induction Hypothesis
 * ( L[base1] & ... & L[basen] & (L[x] => L[c1(x)]) & ... (L[x] => L[cm(x)]) ) => L[x]
 * for some lit ~L[a]
 * and then force binary resolution on L for each resultant clause
 */

void InductionClauseIterator::performStructInductionOne(InductionContext& context, InductionFormulaVariantIndex::Entry* e, InferenceRule rule)
{
  CALL("InductionClauseIterator::performStructInductionOne"); 

  TermAlgebra* ta = env.signature->getTermAlgebraOfSort(env.signature->getFunction(context._indTerm->functor())->fnType()->result());
  TermList ta_sort = ta->sort();

  FormulaList* formulas = FormulaList::empty();

  unsigned var = 0;

  // first produce the formula
  for(unsigned i=0;i<ta->nConstructors();i++){
    TermAlgebraConstructor* con = ta->constructor(i);
    unsigned arity = con->arity();
      Stack<TermList> argTerms;
      Stack<TermList> ta_vars;
      for(unsigned j=0;j<arity;j++){
        TermList x(var,false);
        var++;
        if(con->argSort(j) == ta_sort){
          ta_vars.push(x);
        }
        argTerms.push(x);
      }
      // if hypothesis strengthening is on, this replaces the Skolems with fresh variables
      auto right = context.getFormulaWithSquashedSkolems(
        TermList(Term::create(con->functor(),(unsigned)argTerms.size(), argTerms.begin())), true, var);
      FormulaList* args = FormulaList::empty();
      Stack<TermList>::Iterator tvit(ta_vars);
      while(tvit.hasNext()){
        auto hypVars = VList::empty();
        auto hyp = context.getFormulaWithSquashedSkolems(tvit.next(),true,var,&hypVars);
        // quantify each hypotheses with variables replacing Skolems explicitly
        if (hypVars) {
          hyp = new QuantifiedFormula(Connective::FORALL, hypVars, SList::empty(), hyp);
        }
        FormulaList::push(hyp,args);
      }

      FormulaList::push(args ?
        new BinaryFormula(Connective::IMP,JunctionFormula::generalJunction(Connective::AND,args),right) : right, formulas);
  }
  ASS(formulas);
  Formula* indPremise = JunctionFormula::generalJunction(Connective::AND,formulas);
  Substitution subst;
  auto conclusion = context.getFormulaWithSquashedSkolems(TermList(var++,false), true, var, nullptr, &subst);
  Formula* hypothesis = new BinaryFormula(Connective::IMP,
                            Formula::quantify(indPremise),
                            Formula::quantify(conclusion));

  auto cls = produceClauses(hypothesis, rule, context);
  e->add(std::move(cls), std::move(subst));
  // resolveClauses(cls, context, subst);
}

/**
 * This idea (taken from the CVC4 paper) is that there exists some smallest k that makes lit true
 * We produce the clause ~L[x] \/ ?y : L[y] & !z (z subterm y -> ~L[z])
 * and perform resolution with lit L[c]
 */
void InductionClauseIterator::performStructInductionTwo(InductionContext& context, InductionFormulaVariantIndex::Entry* e, InferenceRule rule)
{
  CALL("InductionClauseIterator::performStructInductionTwo"); 

  TermAlgebra* ta = env.signature->getTermAlgebraOfSort(env.signature->getFunction(context._indTerm->functor())->fnType()->result());
  TermList ta_sort = ta->sort();

  // make L[y]
  TermList y(0,false); 
  unsigned var = 1;
  // if hypothesis strengthening is on, this replaces the Skolems with fresh variables
  auto mainVars = VList::singleton(y.var());
  auto Ly = context.getFormulaWithSquashedSkolems(y,false,var,&mainVars);

  // for each constructor and destructor make
  // ![Z] : y = cons(Z,dec(y)) -> ( ~L[dec1(y)] & ~L[dec2(y)]
  FormulaList* formulas = FormulaList::empty();

  for(unsigned i=0;i<ta->nConstructors();i++){
    TermAlgebraConstructor* con = ta->constructor(i);
    unsigned arity = con->arity();

    if(con->recursive()){
  
      // First generate all argTerms and remember those that are of sort ta_sort 
      Stack<TermList> argTerms;
      Stack<TermList> taTerms; 
      for(unsigned j=0;j<arity;j++){
        unsigned dj = con->destructorFunctor(j);
        TermList djy(Term::create1(dj,y));
        argTerms.push(djy);
        if(con->argSort(j) == ta_sort){
          taTerms.push(djy);
        }
      }
      ASS(taTerms.isNonEmpty());
      // create y = con1(...d1(y)...d2(y)...)
      TermList coni(Term::create(con->functor(),(unsigned)argTerms.size(), argTerms.begin()));
      Literal* kneq = Literal::createEquality(true,y,coni,ta_sort);
      FormulaList* And = FormulaList::empty(); 
      Stack<TermList>::Iterator tit(taTerms);
      while(tit.hasNext()){
        TermList djy = tit.next();
        auto hypVars = VList::empty();
        auto f = context.getFormulaWithSquashedSkolems(djy,true,var,&hypVars);
        if (hypVars) {
          f = new QuantifiedFormula(Connective::FORALL, hypVars, SList::empty(), f);
        }
        FormulaList::push(f,And);
      }
      ASS(And);
      Formula* imp = new BinaryFormula(Connective::IMP,
                            new AtomicFormula(kneq),
                            JunctionFormula::generalJunction(Connective::AND,And));
      FormulaList::push(imp,formulas);
    }
  }
  // quantify with mainVars explicitly
  Formula* exists = new QuantifiedFormula(Connective::EXISTS, mainVars,SList::empty(),
                        formulas ? new JunctionFormula(Connective::AND,FormulaList::cons(Ly,formulas))
                                 : Ly);

  Substitution subst;
  auto conclusion = context.getFormulaWithSquashedSkolems(TermList(var++, false), true, var, nullptr, &subst);
  FormulaList* orf = FormulaList::cons(exists,FormulaList::singleton(Formula::quantify(conclusion)));
  Formula* hypothesis = new JunctionFormula(Connective::OR,orf);

  auto cls = produceClauses(hypothesis, rule, context);
  e->add(std::move(cls), std::move(subst));
  // resolveClauses(cls, context, subst);
}

/*
 * A variant of Two where we are stronger with respect to all subterms. here the existential part is
 *
 * ?y : L[y] &_{con_i} ( y = con_i(..dec(y)..) -> smaller(dec(y))) 
             & (!x : smallerThanY(x) -> smallerThanY(destructor(x))) 
             & !z : smallerThanY(z) => ~L[z]
 *
 * i.e. we add a new special predicat that is true when its argument is smaller than Y
 *
 */
void InductionClauseIterator::performStructInductionThree(InductionContext& context, InductionFormulaVariantIndex::Entry* e, InferenceRule rule)
{
  CALL("InductionClauseIterator::performStructInductionThree");

  TermAlgebra* ta = env.signature->getTermAlgebraOfSort(env.signature->getFunction(context._indTerm->functor())->fnType()->result());
  TermList ta_sort = ta->sort();

  // make L[y]
  TermList x(0,false); 
  TermList y(1,false); 
  TermList z(2,false); 
  unsigned vars = 3;
  // if hypothesis strengthening is on, this replaces the Skolems with fresh variables
  auto mainVars = VList::singleton(y.var());
  auto Ly = context.getFormulaWithSquashedSkolems(y,false,vars,&mainVars);

  // make smallerThanY
  unsigned sty = env.signature->addFreshPredicate(1,"smallerThan");
  env.signature->getPredicate(sty)->setType(OperatorType::getPredicateType({ta_sort}));

  // make ( y = con_i(..dec(y)..) -> smaller(dec(y)))  for each constructor 
  FormulaList* conjunction = FormulaList::singleton(Ly);
  for(unsigned i=0;i<ta->nConstructors();i++){
    TermAlgebraConstructor* con = ta->constructor(i);
    unsigned arity = con->arity();

    if(con->recursive()){
      // First generate all argTerms and remember those that are of sort ta_sort 
      Stack<TermList> argTerms;
      Stack<TermList> taTerms; 
      Stack<unsigned> ta_vars;
      Stack<TermList> varTerms;
      for(unsigned j=0;j<arity;j++){
        unsigned dj = con->destructorFunctor(j);
        TermList djy(Term::create1(dj,y));
        argTerms.push(djy);
        TermList xj(vars,false);
        varTerms.push(xj);
        if(con->argSort(j) == ta_sort){
          taTerms.push(djy);
          ta_vars.push(vars);
        }
        vars++;
      }
      // create y = con1(...d1(y)...d2(y)...)
      TermList coni(Term::create(con->functor(),(unsigned)argTerms.size(), argTerms.begin()));
      Literal* kneq = Literal::createEquality(true,y,coni,ta_sort);

      // create smaller(cons(x1,..,xn))
      Formula* smaller_coni = new AtomicFormula(Literal::create1(sty,true,
                                TermList(Term::create(con->functor(),(unsigned)varTerms.size(),varTerms.begin()))));

      FormulaList* smallers = FormulaList::empty();
      Stack<unsigned>::Iterator vtit(ta_vars);
      while(vtit.hasNext()){
        FormulaList::push(new AtomicFormula(Literal::create1(sty,true,TermList(vtit.next(),false))),smallers);
      }
      ASS(smallers);
      Formula* ax = Formula::quantify(new BinaryFormula(Connective::IMP,smaller_coni,
                      JunctionFormula::generalJunction(Connective::AND,smallers)));

      // now create a conjunction of smaller(d(y)) for each d
      FormulaList* And = FormulaList::empty(); 
      Stack<TermList>::Iterator tit(taTerms);
      while(tit.hasNext()){
        Formula* f = new AtomicFormula(Literal::create1(sty,true,tit.next()));
        FormulaList::push(f,And);
      }
      ASS(And);
      Formula* imp = new BinaryFormula(Connective::IMP,
                            new AtomicFormula(kneq),
                            JunctionFormula::generalJunction(Connective::AND,And));

      FormulaList::push(imp,conjunction);
      FormulaList::push(ax,conjunction);
    } 
  }
  // now !z : smallerThanY(z) => ~L[z]
  Formula* smallerImpNL = Formula::quantify(new BinaryFormula(Connective::IMP, 
                            new AtomicFormula(Literal::create1(sty,true,z)),
                            context.getFormulaWithSquashedSkolems(z,true,vars)));

  FormulaList::push(smallerImpNL,conjunction);
  // quantify with mainVars explicitly
  Formula* exists = new QuantifiedFormula(Connective::EXISTS, mainVars,SList::empty(),
                       new JunctionFormula(Connective::AND,conjunction));

  Substitution subst;
  auto conclusion = context.getFormulaWithSquashedSkolems(x,true,vars,nullptr,&subst);
  FormulaList* orf = FormulaList::cons(exists,FormulaList::singleton(Formula::quantify(conclusion)));
  Formula* hypothesis = new JunctionFormula(Connective::OR,orf);

  auto cls = produceClauses(hypothesis, rule, context);
  e->add(std::move(cls), std::move(subst));
  // resolveClauses(cls, context, subst);
}
// Note: only works for unit clauses.
// TODO: encapsulate the 'done' map in a helper class to have it deallocate correctly.
bool InductionClauseIterator::notDoneInt(Literal* lit, Term* t, bool increasing, Term* bound1, Term* optionalBound2, bool fromComparison)
{
  CALL("InductionClauseIterator::notDoneInt");

  // Map structure:
  // (induction lit/t representation, increasing) -> ((bound1, optionalBound2) -> (existsFromComparisonTrue, {(induction term, fromComparison)}))
  static DHMap<pair<Literal*, bool>, DHMap<pair<Term*, Term*>, pair<bool, DHMap<Term*, bool>*>>*> done;

  // Create representation of lit/t combination
  static Term* blank;
  static unsigned freshInt = env.signature->addFreshFunction(0, "blank");
  if (!blank) {
    env.signature->getFunction(freshInt)->setType(OperatorType::getConstantsType(AtomicSort::intSort()));
    blank = Term::createConstant(freshInt);
  }
  Literal* rep = replaceTermInLiteral(lit,t,TermList(blank));

  auto key = make_pair(rep, increasing);
  DHMap<pair<Term*, Term*>, pair<bool, DHMap<Term*, bool>*>>* val;
  pair<bool, DHMap<Term*, bool>*>* p;
  auto bounds = make_pair(bound1, optionalBound2);
  if (done.find(key, val)) {
    // Check two conditions under which we can skip this induction literal/term/bounds combination:
    p = val->findPtr(bounds);
    if (p != nullptr) {
      // 1. either induction was applied on the same induction literal representation with the same bound(s),
      //    and the bound(s) came from comparison (i.e., its comparison with induction term was resolved away).
      if (p->first) return false;
      // 2. or induction was applied on the same induction literal & induction term with the same bound(s),
      //    and either now the bound did not come from comparison, or then it did.
      bool previousFromComparison = false;
      if (p->second->find(t, previousFromComparison) && (!fromComparison || previousFromComparison)) return false;
    }
    // There is a 3rd possibility: the bound now is an interpreted constant, and induction was applied
    // on the same induction lit and some other interpreted constant bound, which came from comparison,
    // and the bound then was <= this bound (if increasing) or >= this bound (if not increasing).
    // TODO: explore if it is worth it to implement this condition.
  }
  else {
    val = new DHMap<pair<Term*, Term*>, pair<bool, DHMap<Term*, bool>*>>();
    done.insert(key, val);
  }
  p = val->findPtr(bounds);
  DHMap<Term*, bool>* insideMap;
  if (p != nullptr) {
    insideMap = p->second;
    p->first |= fromComparison;
  } else {
    insideMap = new DHMap<Term*, bool>();
    val->insert(bounds, make_pair(fromComparison, insideMap));
  }
  bool previousFromComparison = false;
  if (!insideMap->find(t, previousFromComparison) || (!previousFromComparison && fromComparison)) {
    insideMap->set(t, fromComparison);
  }

  return true;
}

}
