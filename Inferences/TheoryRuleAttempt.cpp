#include "TheoryRuleAttempt.hpp"

#include "Kernel/Signature.hpp"
#include "Indexing/IndexManager.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

using namespace Kernel;
using namespace Inferences;
using namespace Saturation;

void TransitivityRuleExperiment::attach(SaturationAlgorithm* salg)
{
    CALL("TransitivityRuleExperiment::attach");

    GeneratingInferenceEngine::attach(salg);
    // TODO: Get necessary indexing stuff from _salg->getIndexManager()
    // _salg->getIndexManager()->request( /* TODO */ );
}

void TransitivityRuleExperiment::detach()
{
    CALL("TransitivityRuleExperiment::detach");

    // TODO: release indexing stuff here
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

    // env.signature
    std::cerr << "\nTransitivityRuleExperiment::generateClauses:\n";
    std::cerr << "Given: " << premise->toString() << std::endl;

    // unsigned less_pred = env.signature->addInterpretedPredicate(Theory::INT_LESS
    static unsigned const pred_int_less = env.signature->getInterpretingSymbol(Theory::INT_LESS);

    auto it1 = premise->getSelectedLiteralIterator();
    // auto it2 = getMappingIterator(it1, DebugPrintFn());
    // auto it2 = getMappingIteratorKnownRes<Literal*>(it1, [](Literal* lit) {
    //         std::cerr << "Selected literal: " << lit->toString() << std::endl;
    //         return lit;
    //     });
    auto it2 = getSideEffectIterator(it1, [](Literal* lit) -> void {
        std::cerr << "Selected literal: " << lit->toString() << std::endl;
        std::cerr << "\tFunctor: " << lit->functor() << std::endl;
        std::cerr << "\tFunction name: " << lit->functionName() << std::endl;
        std::cerr << "\tPredicate name: " << lit->predicateName() << std::endl;
    });

    // Filter iterator to positive literals of form "x < y"
    // NOTE:
    // This is easy here, since we just need to compare the outermost predicate symbol.
    // The question is how we can properly generalize this matching for other theory rules.
    auto it3 = getFilteredIterator(it2, [](Literal* lit) -> bool {
        return lit->isPositive() && (lit->functor() == pred_int_less);
    });

    auto printIt = it3;
    while (printIt.hasNext()) {
        auto x = printIt.next();
        std::cerr << "ITERATOR ELEMENT: " << x->toString() << std::endl;
    }

    // auto it2 = premise->

    std::cerr << std::endl;

    // return pvi(it2);
    return ClauseIterator::getEmpty();
}
