#include "TheoryRuleAttempt.hpp"

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

    _subtermIndex = static_cast<SuperpositionSubtermIndex*>(
        _salg->getIndexManager()->request(SUPERPOSITION_SUBTERM_SUBST_TREE));
}

void TransitivityRuleExperiment::detach()
{
    CALL("TransitivityRuleExperiment::detach");

    _subtermIndex = nullptr;
    _salg->getIndexManager()->release(SUPERPOSITION_SUBTERM_SUBST_TREE);

    GeneratingInferenceEngine::detach();
}

namespace {

// // template <typename T>
// struct DebugPrintFn
// {
//     DebugPrintFn() {}
//     DECL_RETURN_TYPE(Clause*);
//     OWN_RETURN_TYPE operator()(Clause* cl)
//     {
//         CALL("DebugPrintFn::operator()");
//         std::cerr << cl->toString() << std::endl;
//         return cl;
//     }
// };

template <typename Inner, typename ElementType=ELEMENT_TYPE(Inner), typename Function>
MappingIterator<Inner,std::function<ElementType(ElementType)>,ElementType>
getSideEffectIterator(Inner it, Function f) {
    auto fn = std::function<ElementType(ElementType)>([f] (ElementType el) {
        f(el);
        return el;
    });
    return getMappingIteratorKnownRes<ElementType>(it, fn);
}

}

ClauseIterator TransitivityRuleExperiment::generateClauses(Clause* premise)
{
    CALL("TransitivityRuleExperiment::generateClauses");

    // TODO
    // Plan:
    // 1. Match given clause against "x < y".
    // 2. Search active clause set for a clause of form "y < z".
    // 3. Return clause: "x < z".

    std::cerr << "\nTransitivityRuleExperiment::generateClauses:\n";
    std::cerr << "Given: " << premise->toString() << std::endl;

    static unsigned const pred_int_less = env.signature->getInterpretingSymbol(Theory::INT_LESS);

    auto it1 = premise->getSelectedLiteralIterator();
    // auto it2 = getMappingIteratorKnownRes<Literal*>(it1, [](Literal* lit) {
    //         std::cerr << "Selected literal: " << lit->toString() << std::endl;
    //         return lit;
    //     });
    auto it2 = getSideEffectIterator(it1, [](Literal* lit) -> void {
        std::cerr << "Selected literal: " << lit->toString() << std::endl;
        std::cerr << "\tFunctor: " << lit->functor() << std::endl;
        std::cerr << "\tFunction name: " << lit->functionName() << std::endl;
        std::cerr << "\tPredicate name: " << lit->predicateName() << std::endl;
        std::cerr << "\tsecond argument: " << lit->nthArgument(1)->toString() << std::endl;
    });

    // Filter iterator to positive literals of form "x < y"
    // NOTE:
    // This is easy here, since we just need to compare the outermost predicate symbol.
    // The question is how we can properly generalize this matching for other theory rules.
    auto it3 = getFilteredIterator(it2, [](Literal* lit) -> bool {
        return lit->isPositive()
            && (lit->functor() == pred_int_less);
    });


    using LiteralIterator = VirtualIterator<Literal*>;

    auto it4 = getMappingIteratorKnownRes<VirtualIterator<std::pair<Literal*,TermQueryResult>>>(it3, [this](Literal* lit) {
        // Here: lit = $less(t1, t2).
        // Goal: match against $less(t3, t4) such that there is a unification of t2 and t3.
        TermList* t2 = lit->nthArgument(1);

        std::cerr << "\tFinding unifications for: " << t2->toString() << std::endl;
        auto unifs = _subtermIndex->getUnifications(*t2);
        while (unifs.hasNext()) {
            auto unif = unifs.next();
            std::cerr << "\tUnification result:" << std::endl;
            std::cerr << "\t\tClause: " << unif.clause->toString() << std::endl;
            std::cerr << "\t\tLiteral: " << unif.literal->toString() << std::endl;
            std::cerr << "\t\tTerm: " << unif.term.toString() << std::endl;
            // std::cerr << "\t\tSubstitution: " << unif.substitution->toString() << std::endl;
            // std::cerr << "\t\tConstraints: " << unif.constraints->toString() << std::endl;
        }

        // TODO
        // This isn't quite right.
        // We only want to match the LHS of the other term, but as it is now it will also match the right-hand side.
        // (we probably need a different index type, or add some constraints; something we want to do eventually anyways for more efficient matching)

        // All unifications with t2
        auto unifIt1 = _subtermIndex->getUnifications(*t2);

        // Filter to positive literals of form "t < u"
        auto unifIt2 = getFilteredIterator(unifIt1, [](TermQueryResult unif) -> bool {
            Literal* l = unif.literal;
            return l->isPositive()
                && (l->functor() == pred_int_less)
                && (unif.term == *l->nthArgument(0));  // only match the left argument
        });

        // Annotate each result with the currently selected literal
        auto unifIt3 = pushPairIntoRightIterator(lit, unifIt2);

        return pvi(unifIt3);
    });

    auto it5 = getFlattenedIterator(it4);

    auto it6 = getMappingIteratorKnownRes<Clause*>(it5, [premise](std::pair<Literal*,TermQueryResult> arg) {
        Clause* cl1 = premise;
        Literal* lit1 = arg.first;

        Clause* cl2 = arg.second.clause;
        Literal* lit2 = arg.second.literal;

        int len1 = cl1->length();
        int len2 = cl2->length();
        int nlen = len1 + len2 - 1;

        Inference* inf = new Inference2(Inference::THEORY_INFERENCE_RULE, cl1, cl2);
        Unit::InputType inpType = (Unit::InputType)max(cl1->inputType(), cl2->inputType());  // ??? (copied from ForwardSubsumptionAndResolution::generateSubsumptionResolutionClause)
        Clause* res = new(nlen) Clause(nlen, inpType, inf);

        // TODO: We have to apply the substitution to t1, t2!!
        auto s = arg.second.substitution;
        TermList t1 = *lit1->nthArgument(0);
        TermList t2 = *lit2->nthArgument(1);
        Literal* lit = Literal::create2(pred_int_less, true, t1, t2);

        (*res)[0] = lit;

        int next = 1;
        for (int i = 0; i < len1; ++i) {
            Literal* curr = (*cl1)[i];
            if (curr != lit1) {
                (*res)[next] = curr;
                next += 1;
            }
        }
        // we should have skipped exactly one literal (namely lit1)
        ASS(next == 1 + (len1 - 1));
        for (int i = 0; i < len2; ++i) {
            Literal* curr = (*cl2)[i];
            if (curr != lit2) {
                (*res)[next] = curr;
                next += 1;
            }
        }
        ASS(next == 1 + (len1 - 1) + (len2 - 1));

        res->setAge(std::max(cl1->age(), cl2->age()));  // TODO ???

        return res;
    });

    auto finalIt = it6;
    auto printIt = getSideEffectIterator(finalIt, [](ELEMENT_TYPE(decltype(finalIt)) x) -> void {
        std::cerr << "ITERATOR ELEMENT: " << x->toString() << std::endl;
        // std::cerr << "ITERATOR ELEMENT: " << x.first->toString() << " / " << x.second.literal->toString() << std::endl;
    });

    // // Just for debugging
    // while (printIt.hasNext()) {
    //     printIt.next();
    // }
    // std::cerr << std::endl;

    return pvi(printIt);
    // return ClauseIterator::getEmpty();
}
