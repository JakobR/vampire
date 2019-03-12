#ifndef FORWARDSUBSUMPTIONDEMODULATION_HPP
#define FORWARDSUBSUMPTIONDEMODULATION_HPP

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;


/**
 * Combines subsumption and demodulation into a forward simplifying rule.
 *
 * Simplified version without substitutions for clauses C, D:
 *
 *      C \/ D[s]   C \/ s = t
 *      ----------------------
 *            C \/ D[t]
 */
class ForwardSubsumptionDemodulation
  : public ForwardSimplificationEngine
{
  public:
    CLASS_NAME(ForwardSubsumptionDemodulation);
    USE_ALLOCATOR(ForwardSubsumptionDemodulation);

    void attach(SaturationAlgorithm* salg) override;
    void detach() override;
    bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;
  private:
    /** Simplification unit index */
    UnitClauseLiteralIndex* _unitIndex;
    FwSubsSimplifyingLiteralIndex* _fwIndex;
};


}

#endif /* !FORWARDSUBSUMPTIONDEMODULATION_HPP */
