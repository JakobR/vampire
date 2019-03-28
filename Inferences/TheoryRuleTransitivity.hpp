#ifndef THEORYRULETRANSITIVITY_HPP
#define THEORYRULETRANSITIVITY_HPP

#include "Inferences/InferenceEngine.hpp"
#include "Inferences/ForwardSubsumptionDemodulation.hpp"
#include "Indexing/LiteralIndex.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;



class TheoryRuleTransitivity
  : public GeneratingInferenceEngine
{
  public:
    CLASS_NAME(TheoryRuleTransitivity);
    USE_ALLOCATOR(TheoryRuleTransitivity);

    void attach(SaturationAlgorithm* salg) override;
    void detach() override;

    ClauseIterator generateClauses(Clause* premise) override;

  private:
    // The GeneratingLiteralIndex indexes clauses by their selected literals
    RequestedIndex<GeneratingLiteralIndex, GENERATING_SUBST_TREE> _index;

    unsigned pred_int_less;
};



}

#endif /* !THEORYRULETRANSITIVITY_HPP */
