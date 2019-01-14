#ifndef THEORYRULEATTEMPT_HPP
#define THEORYRULEATTEMPT_HPP


#include "InferenceEngine.hpp"


namespace Inferences {

    using namespace Kernel;
    using namespace Indexing;
    using namespace Saturation;

    /*
     * As a first attempt, we chose to implement
     * the following rule for transitivity:
     *
     *     x < y   y < z
     *    ---------------
     *         x < z
     *
     * Should be a GeneratingInferenceEngine, since we cannot
     * discard the premises.
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
    };

}



#endif /* !THEORYRULEATTEMPT_HPP */
