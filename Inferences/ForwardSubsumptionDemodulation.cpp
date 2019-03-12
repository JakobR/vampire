#include "ForwardSubsumptionDemodulation.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/LiteralMiniIndex.hpp"
#include "Indexing/IndexManager.hpp"

using namespace Kernel;
using namespace Inferences;
using namespace Saturation;

void ForwardSubsumptionDemodulation::attach(SaturationAlgorithm* salg)
{
  CALL("ForwardSubsumptionDemodulation::attach");
  ForwardSimplificationEngine::attach(salg);
  _unitIndex = static_cast<UnitClauseLiteralIndex*>(
    _salg->getIndexManager()->request(SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE));
  _fwIndex = static_cast<FwSubsSimplifyingLiteralIndex*>(
    _salg->getIndexManager()->request(FW_SUBSUMPTION_SUBST_TREE));
}

void ForwardSubsumptionDemodulation::detach()
{
  CALL("ForwardSubsumptionDemodulation::detach");
  _unitIndex = nullptr;
  _fwIndex = nullptr;
  _salg->getIndexManager()->release(SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE);
  _salg->getIndexManager()->release(FW_SUBSUMPTION_SUBST_TREE);
  ForwardSimplificationEngine::detach();
}

bool ForwardSubsumptionDemodulation::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  CALL("ForwardSubsumptionDemodulation::perform");

  // TODO
  return false;
}
