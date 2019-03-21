#ifndef FORWARDSUBSUMPTIONDEMODULATION_HPP
#define FORWARDSUBSUMPTIONDEMODULATION_HPP

#include "InferenceEngine.hpp"
#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;


template <typename Index, Indexing::IndexType type>
class RequestedIndex
{
  public:
    CLASS_NAME(RequestedIndex);
    USE_ALLOCATOR(RequestedIndex);

    RequestedIndex() { }
    RequestedIndex(SaturationAlgorithm* salg) { attach(salg); }

    // Disallow copying
    RequestedIndex(RequestedIndex const&) = delete;
    RequestedIndex& operator=(RequestedIndex const&) = delete;

    // Moving transfers ownership of the index
    RequestedIndex(RequestedIndex&& other)
      : _index{std::exchange(other._index, nullptr)}
      , _saturationAlgorithm{std::exchange(other._saturationAlgorithm, nullptr)}
    { }

    // Moving transfers ownership of the index
    RequestedIndex& operator=(RequestedIndex&& other) {
      detach();
      _index = std::exchange(other._index, nullptr);
      _saturationAlgorithm = std::exchange(other._saturationAlgorithm, nullptr);
      return *this;
    }

    ~RequestedIndex() { detach(); }

    void attach(SaturationAlgorithm* salg) {
      ASS(!_index);
      ASS(!_saturationAlgorithm);
      _saturationAlgorithm = salg;
      _index = dynamic_cast<Index*>(_saturationAlgorithm->getIndexManager()->request(type));
      ASS(_index != nullptr);
    }

    void detach() {
      _index = nullptr;
      if (_saturationAlgorithm) {
        _saturationAlgorithm->getIndexManager()->release(type);
        _saturationAlgorithm = nullptr;
      }
    }

    Index& operator*() const { return *_index; }
    Index* operator->() const { return _index; }

  private:
    Index* _index = nullptr;
    SaturationAlgorithm* _saturationAlgorithm = nullptr;
};


/**
 * Combines subsumption and demodulation into a forward simplifying rule.
 *
 * Simplified version without substitutions for clauses C, D:
 *
 *      s = t \/ C   L[s] \/ C \/ D
 *      ---------------------------
 *            C \/ D[t]
 *
 *
 *
 *      l = r \/ C        L[lΘ] \/ CΘ \/ D
 *      ----------------------------------
 *              L[rΘ] \/ CΘ \/ D
 *
 *
 *
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
    RequestedIndex<FwSubsSimplifyingLiteralIndex, FW_SUBSUMPTION_SUBST_TREE> _fwIndex;

    void testSomeStuff();
};


}

#endif /* !FORWARDSUBSUMPTIONDEMODULATION_HPP */
