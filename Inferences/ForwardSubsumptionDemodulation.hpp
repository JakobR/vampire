#ifndef FORWARDSUBSUMPTIONDEMODULATION_HPP
#define FORWARDSUBSUMPTIONDEMODULATION_HPP

#include "Lib/STL.hpp"
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
      : _index{exchange(other._index, nullptr)}
      , _saturationAlgorithm{exchange(other._saturationAlgorithm, nullptr)}
    { }

    // Moving transfers ownership of the index
    RequestedIndex& operator=(RequestedIndex&& other) {
      detach();
      _index = exchange(other._index, nullptr);
      _saturationAlgorithm = exchange(other._saturationAlgorithm, nullptr);
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

    // detach() may be called multiple times (manually and by destructor)
    void detach() {
      _index = nullptr;
      if (_saturationAlgorithm) {
        _saturationAlgorithm->getIndexManager()->release(type);
        _saturationAlgorithm = nullptr;
      }
    }

    Index& operator*() const { return *_index; }
    Index* operator->() const { return _index; }
    Index* get() const { return _index; }

  private:
    Index* _index = nullptr;
    SaturationAlgorithm* _saturationAlgorithm = nullptr;
};

template <typename Index>
class RequestedIndex2
{
  public:
    CLASS_NAME(RequestedIndex2);
    USE_ALLOCATOR(RequestedIndex2);

    RequestedIndex2() { }

    // Disallow copying
    RequestedIndex2(RequestedIndex2 const&) = delete;
    RequestedIndex2& operator=(RequestedIndex2 const&) = delete;

    // Moving transfers ownership of the index
    RequestedIndex2(RequestedIndex2&& other)
      : _index{exchange(other._index, nullptr)}
      , _type{other._type}
      , _saturationAlgorithm{exchange(other._saturationAlgorithm, nullptr)}
    { }

    // Moving transfers ownership of the index
    RequestedIndex2& operator=(RequestedIndex2&& other) {
      detach();
      _index = exchange(other._index, nullptr);
      _type = other._type;
      _saturationAlgorithm = exchange(other._saturationAlgorithm, nullptr);
      return *this;
    }

    ~RequestedIndex2() { detach(); }

    void attach(SaturationAlgorithm* salg, Indexing::IndexType type) {
      ASS(!_index);
      ASS(!_saturationAlgorithm);
      _saturationAlgorithm = salg;
      _type = type;
      _index = dynamic_cast<Index*>(_saturationAlgorithm->getIndexManager()->request(type));
      ASS(_index != nullptr);
    }

    // detach() may be called multiple times (manually and by destructor)
    void detach() {
      _index = nullptr;
      if (_saturationAlgorithm != nullptr) {
        _saturationAlgorithm->getIndexManager()->release(_type);
        _saturationAlgorithm = nullptr;
      }
    }

    Index& operator*() const { return *_index; }
    Index* operator->() const { return _index; }
    Index* get() const { return _index; }

  private:
    Index* _index = nullptr;
    Indexing::IndexType _type;
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
    RequestedIndex2<LiteralIndex> _index;

    bool _preorderedOnly;
    bool _performRedundancyCheck;

    void testSomeStuff();
};


}

#endif /* !FORWARDSUBSUMPTIONDEMODULATION_HPP */
