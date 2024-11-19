/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file PartialOrdering.hpp
 * Defines class PartialOrdering.
 */

#ifndef __PartialOrdering__
#define __PartialOrdering__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Ordering.hpp"

namespace Kernel {

using namespace Lib;

using Result = Ordering::Result;

enum class PoComp : uint8_t {
  UNKNOWN,
  GREATER,
  EQUAL,
  LESS,
  NGEQ,
  NLEQ,
  INCOMPARABLE,
};

class PartialOrdering
{
public:
  PartialOrdering();
  PartialOrdering(const PartialOrdering& other);
  ~PartialOrdering();
  PartialOrdering& operator=(const PartialOrdering& other) = delete;

  bool get(TermList lhs, TermList rhs, Ordering::Result& res) const;
  bool set(Ordering::Constraint con);

  // Returns if PO contains full incomparaibility yet.
  // Useful to discard branches when reasoning over ground terms.
  bool hasIncomp() const { return _hasIncomp; }

  std::string to_string() const;

private:
  size_t idx_of_elem(TermList t) const;
  size_t idx_of_elem_ext(TermList t);
  PoComp idx_of(size_t x, size_t y) const;
  PoComp idx_of_safe(size_t x, size_t y) const;
  bool set_idx_of(size_t x, size_t y, PoComp v);
  bool set_idx_of_safe(size_t x, size_t y, PoComp v);

  bool set_inferred(size_t x, size_t y, PoComp result);
  bool set_inferred_loop(size_t x, size_t y, PoComp rel);
  bool set_inferred_loop_inc(size_t x, size_t y, PoComp wkn);
  bool set_inferred_loop_eq(size_t x, size_t y);

  Map<TermList,size_t> _nodes;
  size_t _size;
  PoComp* _array;
  bool _hasIncomp;
};

};

#endif /* __PartialOrdering__ */