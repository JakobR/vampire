#ifndef VECTOR_MAP_HPP
#define VECTOR_MAP_HPP

#include <cstdint>
#include <vector>

namespace subsat { // TODO: remove namespace once I separate out Var/Lit from subsat.hpp

/// Get index by calling a member function 'index()'.
template <typename Key>
struct IndexMember {
  using key_type = Key;
#if __cplusplus >= 201703L
  using index_type = std::invoke_result_t<decltype(&key_type::index), Key>;
#else
  // std::invoke_result_t is only defined for C++17 and later,
  // while std::result_of is deprecated in C++17 and later
  using index_type = typename std::result_of<decltype(&key_type::index)(Key)>::type;
#endif
  index_type operator()(Key key) const
  {
    return key.index();
  }
};

/// The type itself is already the index.
template <typename Integer>
struct IndexIdentity {
  Integer operator()(Integer key) const noexcept
  {
    return key;
  }
};

/// Allows to defines a default indexing method for types.
template <typename Key>
struct DefaultIndex;

template <>
struct DefaultIndex<std::uint32_t> {
  using type = IndexIdentity<std::uint32_t>;
};

template <typename Key>
using DefaultIndex_t = typename DefaultIndex<Key>::type;

/// Vector-based map with type-safe indexing.
template <
    typename Key,
    typename T,
    typename Allocator = std::allocator<T>,
    typename Indexing = DefaultIndex_t<Key>>
class vector_map {
public:
  using key_type = Key;
  using value_type = T;
  using indexing_type = Indexing;
  using allocator_type = Allocator;
  using vector_type = std::vector<value_type, Allocator>;
  using reference = value_type&;
  using const_reference = value_type const&;
  using size_type = typename vector_type::size_type;
  using iterator = typename vector_type::iterator;
  using const_iterator = typename vector_type::const_iterator;

  reference operator[](key_type key)
  {
    size_type const idx = index(key);
    assert(idx < size());
    return m_data[idx];
  }

  const_reference operator[](key_type key) const
  {
    size_type const idx = index(key);
    assert(idx < size());
    return m_data[idx];
  }

  void reserve(size_type new_cap) { m_data.reserve(new_cap); }
  size_type size() const noexcept { return m_data.size(); }

  iterator begin() noexcept { return m_data.begin(); }
  const_iterator begin() const noexcept { return m_data.begin(); }
  const_iterator cbegin() const noexcept { return m_data.cbegin(); }
  iterator end() noexcept { return m_data.end(); }
  const_iterator end() const noexcept { return m_data.end(); }
  const_iterator cend() const noexcept { return m_data.cend(); }

  // TODO: a map-like iterator would be nice. need to extend Index with the backward conversion.

  void clear() noexcept { m_data.clear(); }

  void push_back(T const& value) { m_data.push_back(value); }
  void push_back(T&& value) { m_data.push_back(std::move(value)); }

  template <typename... Args>
  reference emplace_back(Args&&... args)
  {
#if __cplusplus >= 201703L
    return m_data.emplace_back(std::forward<Args>(args)...);
#else
    m_data.emplace_back(std::forward<Args>(args)...);
    return m_data.back();
#endif
  }

  void resize(size_type count) { m_data.resize(count); }
  void resize(size_type count, value_type const& value) { m_data.resize(count, value); }

private:
  size_type index(Key key) const
  {
    indexing_type index;
    return index(key);
  }

private:
  vector_type m_data;
};

} // namespace subsat

#endif /* !VECTOR_MAP_HPP */
