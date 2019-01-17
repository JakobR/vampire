#ifndef THEORYRULEATTEMPT_HPP
#define THEORYRULEATTEMPT_HPP

#include "InferenceEngine.hpp"
#include "Indexing/TermIndex.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;


/**
 * As a first attempt, we chose to implement
 * the following rule for transitivity:
 *
 *     t < u   u < v
 *    ---------------
 *         t < v
 *
 * Should be a GeneratingInferenceEngine, since we cannot
 * discard the premises.
 *
 * To find out more about how to use the indexing and unification,
 * I have now implemented the following extended version:
 *
 *     t < u \/ C     v < w \/ D     uθ = vθ
 *    ---------------------------------------
 *               tθ < wθ \/ Cθ \/ Dθ
 *
 * (when "t<u" is a selected literal in "t<u \/ C")
 */
class TransitivityRuleExperiment
    : public GeneratingInferenceEngine
{
    public:
        CLASS_NAME(TransitivityRuleExperiment);
        USE_ALLOCATOR(TransitivityRuleExperiment);

        void attach(SaturationAlgorithm* salg);
        void detach();

        ClauseIterator generateClauses(Clause* premise);


    private:
        SuperpositionSubtermIndex* _supSubtermIndex;
        SuperpositionLHSIndex* _supLHSIndex;
        DemodulationSubtermIndex* _demSubtermIndex;
        DemodulationLHSIndex* _demLHSIndex;
};


}

#endif /* !THEORYRULEATTEMPT_HPP */
