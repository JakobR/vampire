#include "TheoryRuleAttempt.hpp"

#include "Kernel/FormulaVarIterator.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Lib/PairUtils.hpp"
#include "Indexing/IndexManager.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

using namespace Kernel;
using namespace Inferences;
using namespace Saturation;

void TransitivityRuleExperiment::attach(SaturationAlgorithm* salg)
{
    CALL("TransitivityRuleExperiment::attach");

    GeneratingInferenceEngine::attach(salg);

    // TermIndex
    _supSubtermIndex = static_cast<SuperpositionSubtermIndex*>(
        _salg->getIndexManager()->request(SUPERPOSITION_SUBTERM_SUBST_TREE));
    _supLHSIndex = static_cast<SuperpositionLHSIndex*>(
        _salg->getIndexManager()->request(SUPERPOSITION_LHS_SUBST_TREE));
    _demSubtermIndex = static_cast<DemodulationSubtermIndex*>(
        _salg->getIndexManager()->request(DEMODULATION_SUBTERM_SUBST_TREE));
    _demLHSIndex = static_cast<DemodulationLHSIndex*>(
        _salg->getIndexManager()->request(DEMODULATION_LHS_SUBST_TREE));

    // LiteralIndex
    _glIndex = static_cast<GeneratingLiteralIndex*>(
        _salg->getIndexManager()->request(GENERATING_SUBST_TREE));
    _slIndex = static_cast<SimplifyingLiteralIndex*>(
        _salg->getIndexManager()->request(SIMPLIFYING_SUBST_TREE));
    _fwsslIndex = static_cast<FwSubsSimplifyingLiteralIndex*>(
        _salg->getIndexManager()->request(FW_SUBSUMPTION_SUBST_TREE));
    _suclIndex = static_cast<UnitClauseLiteralIndex*>(
        _salg->getIndexManager()->request(SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE));
    _guclIndex = static_cast<UnitClauseLiteralIndex*>(
        _salg->getIndexManager()->request(GENERATING_UNIT_CLAUSE_SUBST_TREE));
    _nuclIndex = static_cast<NonUnitClauseLiteralIndex*>(
        _salg->getIndexManager()->request(GENERATING_NON_UNIT_CLAUSE_SUBST_TREE));
    _rrIndex = static_cast<RewriteRuleIndex*>(
        _salg->getIndexManager()->request(REWRITE_RULE_SUBST_TREE));
}

void TransitivityRuleExperiment::detach()
{
    CALL("TransitivityRuleExperiment::detach");

    _demLHSIndex = nullptr;
    _salg->getIndexManager()->release(DEMODULATION_LHS_SUBST_TREE);
    _demSubtermIndex = nullptr;
    _salg->getIndexManager()->release(DEMODULATION_SUBTERM_SUBST_TREE);
    _supLHSIndex = nullptr;
    _salg->getIndexManager()->release(SUPERPOSITION_LHS_SUBST_TREE);
    _supSubtermIndex = nullptr;
    _salg->getIndexManager()->release(SUPERPOSITION_SUBTERM_SUBST_TREE);

    _glIndex = nullptr;
    _salg->getIndexManager()->release(GENERATING_SUBST_TREE);
    _slIndex = nullptr;
    _salg->getIndexManager()->release(SIMPLIFYING_SUBST_TREE);
    _fwsslIndex = nullptr;
    _salg->getIndexManager()->release(FW_SUBSUMPTION_SUBST_TREE);
    _suclIndex = nullptr;
    _salg->getIndexManager()->release(SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE);
    _guclIndex = nullptr;
    _salg->getIndexManager()->release(GENERATING_UNIT_CLAUSE_SUBST_TREE);
    _nuclIndex = nullptr;
    _salg->getIndexManager()->release(GENERATING_NON_UNIT_CLAUSE_SUBST_TREE);
    _rrIndex = nullptr;
    _salg->getIndexManager()->release(REWRITE_RULE_SUBST_TREE);

    GeneratingInferenceEngine::detach();
}

/** Returns an iterator that contains the same elements as the given iterator it,
 * but calls the function f on each element before returning the element.
 */
template <typename Inner, typename ElementType=ELEMENT_TYPE(Inner), typename Function>
MappingIterator<Inner,std::function<ElementType(ElementType)>,ElementType>
getSideEffectIterator(Inner it, Function f) {
    auto fn = std::function<ElementType(ElementType)>([f] (ElementType el) {
        f(el);
        return el;
    });
    return getMappingIteratorKnownRes<ElementType>(it, fn);
}

ClauseIterator TransitivityRuleExperiment::generateClauses(Clause* premise)
{
    CALL("TransitivityRuleExperiment::generateClauses");

    // Plan:
    // 1. Match given clause against "x < y".
    // 2. Search active clause set for a clause of form "y < z".
    // 3. Return clause: "x < z".

    // std::cerr << "\nTransitivityRuleExperiment::generateClauses:\n";
    // std::cerr << "Given: " << premise->toString() << std::endl;

    static unsigned const pred_int_less = env.signature->getInterpretingSymbol(Theory::INT_LESS);

    auto it1 = premise->getSelectedLiteralIterator();

    auto it2 = getSideEffectIterator(it1, [](Literal* lit) -> void {
        std::cerr << "Selected literal: " << lit->toString() << std::endl;
        // std::cerr << "\tFunctor: " << lit->functor() << std::endl;
        // std::cerr << "\tPredicate name: " << lit->predicateName() << std::endl;
        // std::cerr << "\tsecond argument: " << lit->nthArgument(1)->toString() << std::endl;
    });

    // Filter iterator to positive literals of form "x < y"
    // NOTE:
    // This is easy here, since we just need to compare the outermost predicate symbol.
    // The question is how we can properly generalize this matching for other theory rules.
    // TODO: Check how the instance check of LiteralIndex->getInstances() works. We can probably reuse that.
    auto it3 = getFilteredIterator(it2, [](Literal* lit) -> bool {

        // TermList x(0, false);
        // TermList y(1, false);
        // Literal* query = Literal::create2(pred_int_less, true, x, y);

        // It probably does not make sense to create a new substitution tree just for matching here.
        // We could either use lambdas with ad-hoc checks as here, or implement our own function for instance checking.

        return lit->isPositive()
            && (lit->functor() == pred_int_less);
    });


    // it3: selected literals of premise of the form "t1 < t2"
    // it4 looks for matches "t2 < t3"
    auto it4 = getMappingIteratorKnownRes<VirtualIterator<std::pair<Literal*,SLQueryResult>>>(it3, [this](Literal* lit) {
        // Here: lit = $less(t1, t2).
        // Goal: match against $less(t3, t4) such that there is a unification of t2 and t3.
        TermList const t2 = *lit->nthArgument(1);

        /*
        auto printTermQueryResults = [](VirtualIterator<TermQueryResult> it) -> void {
            while (it.hasNext()) {
                auto unif = it.next();
                std::cerr << "\t\tTermQueryResult:" << std::endl;
                std::cerr << "\t\t\tClause: " << unif.clause->toString() << std::endl;
                std::cerr << "\t\t\tLiteral: " << unif.literal->toString() << std::endl;
                std::cerr << "\t\t\tTerm: " << unif.term.toString() << std::endl;
            }
        };

        std::cerr << "\tSuperpositionSubtermIndex::getUnifications(...) for term: " << t2.toString() << std::endl;
        printTermQueryResults(_supSubtermIndex->getUnifications(t2));

        std::cerr << "\tSuperpositionLHSIndex::getUnifications(...) for term: " << t2.toString() << std::endl;
        printTermQueryResults(_supLHSIndex->getUnifications(t2));

        std::cerr << "\tDemodulationSubtermIndex::getUnifications(...) for term: " << t2.toString() << std::endl;
        printTermQueryResults(_demSubtermIndex->getUnifications(t2));

        std::cerr << "\tDemodulationLHSIndex::getUnifications(...) for term: " << t2->toString() << std::endl;
        printTermQueryResults(_demLHSIndex->getUnifications(*t2));
        */


        // Find a variable that does not appear in t2
        std::cerr << "\tFormulaVarIterator on " << t2.toString() << ": [";
        FormulaVarIterator fvi(&t2);
        int maxVar = -1;
        while (fvi.hasNext()) {
            auto fv = fvi.next();
            std::cerr << " " << fv;
            if (fv > maxVar) {
                maxVar = fv;
            }
        }
        std::cerr << " ]" << std::endl;

        // Create "template" literal for matching
        TermList x(maxVar + 1, false);
        ASS(!t2.containsSubterm(x));
        Literal* lQuery = Literal::create2(pred_int_less, true, t2, x);  // TODO: is this shared or not? and what exactly does that mean?
        std::cerr << "\tQuery literal: " << lQuery->toString() << std::endl;

        // Compare different LiteralIndexes
        auto printSLQueryResults = [](VirtualIterator<SLQueryResult> it) -> void {
            while (it.hasNext()) {
                auto unif = it.next();
                std::cerr << "\t\tSLQueryResult:" << std::endl;
                std::cerr << "\t\t\tClause: " << unif.clause->toString() << std::endl;
                std::cerr << "\t\t\tLiteral: " << unif.literal->toString() << std::endl;
            }
        };
        std::cerr << "\tGeneratingLiteralIndex::getUnifications(...) for literal: " << lQuery->toString() << std::endl;
        printSLQueryResults(_glIndex->getUnifications(lQuery, false, true));
        std::cerr << "\tGeneratingLiteralIndex::getUnifications(...) for literal: " << lQuery->toString() << std::endl;
        printSLQueryResults(_glIndex->getUnifications(lQuery, false, true));
        std::cerr << "\tSimplifyingLiteralIndex::getUnifications(...) for literal: " << lQuery->toString() << std::endl;
        printSLQueryResults(_slIndex->getUnifications(lQuery, false, true));
        std::cerr << "\tFwSubsSimplifyingLiteralIndex::getUnifications(...) for literal: " << lQuery->toString() << std::endl;
        printSLQueryResults(_fwsslIndex->getUnifications(lQuery, false, true));
        std::cerr << "\tSimplifying UnitClauseLiteralIndex::getUnifications(...) for literal: " << lQuery->toString() << std::endl;
        printSLQueryResults(_suclIndex->getUnifications(lQuery, false, true));
        std::cerr << "\tGenerating UnitClauseLiteralIndex::getUnifications(...) for literal: " << lQuery->toString() << std::endl;
        printSLQueryResults(_guclIndex->getUnifications(lQuery, false, true));
        std::cerr << "\tNonUnitClauseLiteralIndex::getUnifications(...) for literal: " << lQuery->toString() << std::endl;
        printSLQueryResults(_nuclIndex->getUnifications(lQuery, false, true));
        std::cerr << "\tRewriteRuleIndex::getUnifications(...) for literal: " << lQuery->toString() << std::endl;
        printSLQueryResults(_rrIndex->getUnifications(lQuery, false, true));

        auto unifIt1 = _glIndex->getUnifications(lQuery, false, true);
        // lQuery->destroyNonShared();  // TODO: Can/should we destroy the query literal here???

        auto unifIt2 = getSideEffectIterator(unifIt1, [](ELEMENT_TYPE(decltype(unifIt1)) unif) {
            std::cerr << "\t\tSLQueryResult:" << std::endl;
            std::cerr << "\t\t\tClause: " << unif.clause->toString() << std::endl;
            std::cerr << "\t\t\tLiteral: " << unif.literal->toString() << std::endl;
        });

        // Annotate each result with the currently selected literal
        auto unifIt3 = pushPairIntoRightIterator(lit, unifIt2);

        return pvi(unifIt3);
    });

    // Use a VirtualIterator here because only the specialization of getFlattenedIterator for VirtualIterator<VirtualIterator<T>> is lazy enough
    // (without "pvi" we get output from the getSideEffectIterator() at this point, even if we do not use the result!)
    auto it5 = getFlattenedIterator(pvi(it4));

    auto it6 = getMappingIteratorKnownRes<Clause*>(it5, [premise](std::pair<Literal*,SLQueryResult> arg) {
        Clause* cl1 = premise;
        Literal* lit1 = arg.first;            // a < b

        Clause* cl2 = arg.second.clause;
        Literal* lit2 = arg.second.literal;   // b < c

        // TODO: assumption: no duplicated literals in cl1 cl2
        int len1 = cl1->length();
        int len2 = cl2->length();
        int nlen = len1 + len2 - 1;

        Inference* inf = new Inference2(Inference::THEORY_INFERENCE_RULE_TRANSITIVITY, cl1, cl2);
        Unit::InputType inpType = (Unit::InputType)max(cl1->inputType(), cl2->inputType());  // ??? (copied from ForwardSubsumptionAndResolution::generateSubsumptionResolutionClause)
        Clause* res = new(nlen) Clause(nlen, inpType, inf);

        auto s = arg.second.substitution;
        TermList t1 = s->applyToQuery(*lit1->nthArgument(0));
        TermList t2 = s->applyToResult(*lit2->nthArgument(1));
        Literal* lit = Literal::create2(pred_int_less, true, t1, t2);   // a < c

        (*res)[0] = lit;

        // TODO: do we have to obey some invariant on the order of literals in clauses?
        int next = 1;
        for (int i = 0; i < len1; ++i) {
            Literal* curr = (*cl1)[i];
            if (curr != lit1) {
                (*res)[next] = s->applyToQuery(curr);
                next += 1;
            }
        }
        // we should have skipped exactly one literal (namely lit1)
        ASS(next == 1 + (len1 - 1));
        for (int i = 0; i < len2; ++i) {
            Literal* curr = (*cl2)[i];
            if (curr != lit2) {
                (*res)[next] = s->applyToResult(curr);
                next += 1;
            }
        }
        ASS(next == 1 + (len1 - 1) + (len2 - 1));

        res->setAge(std::max(cl1->age(), cl2->age()) + 1);
        res->setPenalty(cl1->penalty() + cl2->penalty() + 5);

        return res;
    });

    auto finalIt = it6;
    auto printIt = getSideEffectIterator(finalIt, [](ELEMENT_TYPE(decltype(finalIt)) x) -> void {
        std::cerr << "GENERATE: " << x->toString() << std::endl;
    });

    // TODO: why do we get output if we never use the iterator?
    // => FlattenedIterator is not lazy enough, unless it operates on VirtualIterator<VirtualIterator<T>>!

    // return ClauseIterator::getEmpty();  // NOTE: uncommenting this disables the transitivity rule
    return pvi(printIt);
}


Clause* IrreflexivityISE::simplify(Clause* c)
{
    CALL("IrreflexivityISE::simplify");

    std::cerr << "IrreflexivityISE::simplify on " << c->toString() << std::endl;

    static unsigned const pred_int_less = env.signature->getInterpretingSymbol(Theory::INT_LESS);
    // std::vector<int> skip;   // TODO: should probably use vampire's own types instead of std::vector? (because of custom allocator)
    Stack<int> skip;

    for (int i = 0; i < c->length(); ++i) {
        Literal const* lit = c->literals()[i];

        if (lit->isPositive()
            && lit->functor() == pred_int_less
            && *lit->nthArgument(0) == *lit->nthArgument(1)) {

            skip.push(i);
        }
    }

    std::cerr << "\tSkip literals with indices: [ ";
    for (int k : skip) {
        std::cerr << k << ' ';
    }
    std::cerr << "]" << std::endl;

    if (skip.size() > 0) {
        int newLen = c->length() - skip.size();
        Inference* inf = new Inference1(Inference::THEORY_INFERENCE_RULE_IRREFLEXIVITY, c);
        Clause* res = new(newLen) Clause(newLen, c->inputType(), inf);

        /*
        // TODO: wrong! we need to count downwards, because skip.back() contains the highest index to skip. (but the alternative solution in the next paragraph is probably better anyways)
        for (int i = 0, j = 0; j < newLen; ++i, ++j) {
            while (!skip.empty() && skip.back() == i) {
                skip.pop_back();
                ++i;
            }
            res[j] = c[i];
        }
        */

        int i = 0;
        int j = 0;
        skip.push(c->length());  // the following loop copies literals before every skipped index. We add c->length() to make it also copy the final part.
        for (int k : skip) {
            int n = k - i;
            // std::cerr << i << ' ' << j << ' ' << k << ' ' << n << std::endl;
            std::memcpy(res->literals() + j, c->literals() + i, n * sizeof(Literal*));
            j += n;
            i += n + 1;
        }
        // std::cerr << i << ' ' << j << std::endl;
        ASS_EQ(j, newLen);
        ASS_EQ(i, c->length() + 1);

        std:: cerr << "\tres = " << res->toString() << std::endl;
        return res;
    }
    else {
        return c;
    }
}


bool IrreflexivityFSE::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
    CALL("IrreflexivityFSE::perform");

    std::cerr << "IrreflexivityFSE::perform on " << cl->toString() << std::endl;

    // just reuse the other function for now (should be extracted into a top-level function later)
    IrreflexivityISE ise;

    Clause* res = ise.simplify(cl);
    if (res == cl) {
        replacement = res;
        premises = ClauseIterator::getEmpty();  // ???
        return true;
    } else {
        replacement = nullptr;
        return false;
    }
}
