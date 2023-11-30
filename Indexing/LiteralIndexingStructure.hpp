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
 * @file LiteralIndexingStructure.hpp
 * Defines class LiteralIndexingStructure.
 */


#ifndef __LiteralIndexingStructure__
#define __LiteralIndexingStructure__

#include "Forwards.hpp"
#include "Index.hpp"
#include "Kernel/MismatchHandler.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Shell/Options.hpp"

namespace Indexing {

class LiteralIndexingStructure {
public:
  virtual ~LiteralIndexingStructure() {}

  virtual void insert(Literal* lit, Clause* cls) = 0;
  virtual void remove(Literal* lit, Clause* cls) = 0;

  virtual VirtualIterator<SLQueryResult> getAll() { NOT_IMPLEMENTED; }
  virtual VirtualIterator<SLQueryResult> getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual VirtualIterator<LQueryRes<AbstractingUnifier*>> getUwa(Literal* lit, bool complementary, Options::UnificationWithAbstraction uwa, bool fixedPointIteration) = 0;
  virtual VirtualIterator<SLQueryResult> getGeneralizations(Literal* lit, bool complementary, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual VirtualIterator<SLQueryResult> getInstances(Literal* lit, bool complementary, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual VirtualIterator<SLQueryResult> getVariants(Literal* lit, bool complementary, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }

  virtual size_t getUnificationCount(Literal* lit, bool complementary)
  {
    return countIteratorElements(getUnifications(lit, complementary, false));
  }

};

};

#endif /* __LiteralIndexingStructure__ */
