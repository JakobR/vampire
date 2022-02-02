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
 * @file RefutationSeekerFSE.hpp
 * Defines class RefutationSeekerFSE.
 */


#ifndef __RefutationSeekerFSE__
#define __RefutationSeekerFSE__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class RefutationSeekerFSE
: public ForwardSimplificationEngine
{
public:
  CLASS_NAME(RefutationSeekerFSE);
  USE_ALLOCATOR(RefutationSeekerFSE);

  void attach(SaturationAlgorithm* salg);
  void detach();
  void perform(Clause* cl, ForwardSimplificationPerformer* simplPerformer);
private:
  /** Simplification unit index */
  UnitClauseLiteralIndex* _index;
};

};
#endif /* __RefutationSeekerFSE__ */
