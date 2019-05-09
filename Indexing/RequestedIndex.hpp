#ifndef REQUESTEDINDEX_HPP
#define REQUESTEDINDEX_HPP

#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Lib/Allocator.hpp"
#include "Lib/STL.hpp"

namespace Indexing {


template <typename Index>
class RequestedIndex final
{
  public:
    CLASS_NAME(RequestedIndex);
    USE_ALLOCATOR(RequestedIndex);

    RequestedIndex()
    { }

    // Disallow copying
    RequestedIndex(RequestedIndex const&) = delete;
    RequestedIndex& operator=(RequestedIndex const&) = delete;

    // Moving transfers ownership of the index
    RequestedIndex(RequestedIndex&& other)
      : _index{exchange(other._index, nullptr)}
      , _type{other._type}
      , _indexManager{exchange(other._indexManager, nullptr)}
    { }

    // Moving transfers ownership of the index
    RequestedIndex& operator=(RequestedIndex&& other)
    {
      release();  // need to release this index before overwriting fields with the other
      _index = exchange(other._index, nullptr);
      _type = other._type;
      _indexManager = exchange(other._indexManager, nullptr);
      return *this;
    }

    ~RequestedIndex()
    {
      release();
    }

    void request(IndexManager* indexManager, IndexType type)
    {
      ASS(!_index);
      ASS(!_indexManager);
      _indexManager = indexManager;
      _type = type;
      _index = dynamic_cast<Index*>(_indexManager->request(type));
      ASS(_index != nullptr);  // if this fails, the wrong index type was requested
    }

    // NOTE: release() might be called multiple times (manually and by destructor)
    void release()
    {
      _index = nullptr;
      if (_indexManager != nullptr) {
        _indexManager->release(_type);
        _indexManager = nullptr;
      }
    }

    Index& operator*() const { return *_index; }
    Index* operator->() const { return _index; }
    Index* get() const { return _index; }

  private:
    Index* _index = nullptr;
    IndexType _type;
    IndexManager* _indexManager = nullptr;
};


}

#endif /* !REQUESTEDINDEX_HPP */
