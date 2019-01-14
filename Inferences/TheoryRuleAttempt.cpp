#include "TheoryRuleAttempt.hpp"

#include "Indexing/IndexManager.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

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

ClauseIterator TransitivityRuleExperiment::generateClauses(Clause* premise)
{
    CALL("TransitivityRuleExperiment::generateClauses");

    std::cerr << "\nTransitivityRuleExperiment::generateClauses:\n";
    std::cerr << "Given: " << premise->toString() << '\n';
    std::cerr << std::endl;

    // TODO
    // 1. Match given clause against "x < y".
    // 2. Search active clause set for a clause of form "y < z".
    // 3. Return clause: "x < z".
    return ClauseIterator::getEmpty();
}
