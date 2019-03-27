#ifndef STL_HPP
#define STL_HPP

#include <unordered_map>
#include <unordered_set>
#include <vector>
#include "Lib/STLAllocator.hpp"

namespace Lib {


template< typename Key
        , typename T
        , typename Hash = std::hash<Key>
        , typename KeyEqual = std::equal_to<Key>
        >
using v_unordered_map = std::unordered_map<Key, T, Hash, KeyEqual, STLAllocator<std::pair<const Key, T>>>;


template< typename Key
        , typename Hash = std::hash<Key>
        , typename KeyEqual = std::equal_to<Key>
        >
using v_unordered_set = std::unordered_set<Key, Hash, KeyEqual, STLAllocator<Key>>;


template< typename T >
using v_vector = std::vector<T, STLAllocator<T>>;


}  // namespace Lib

#endif /* !STL_HPP */
