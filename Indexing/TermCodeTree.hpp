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
 * @file TermCodeTree.hpp
 * Defines class TermCodeTree.
 */

#ifndef __TermCodeTree__
#define __TermCodeTree__

#include "Forwards.hpp"

#include "Indexing/Index.hpp"
#include "Lib/Allocator.hpp"
#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Hash.hpp"
#include "Lib/List.hpp"
#include "Lib/Recycled.hpp"
#include "Lib/Stack.hpp"
#include "Lib/TriangularArray.hpp"
#include "Lib/Vector.hpp"
#include "Lib/VirtualIterator.hpp"


#include "CodeTree.hpp"


namespace Indexing {

using namespace Lib;
using namespace Kernel;

class TermCodeTree : public CodeTree 
{
protected:
  static void onCodeOpDestroying(CodeOp* op);
  
public:
  TermCodeTree();
  
  using TermInfo = TermLiteralClause;


  void insert(TermInfo* ti);
  void remove(const TermInfo& ti);
  
private:
  struct RemovingTermMatcher
  : public RemovingMatcher
  {
  public:
    void init(FlatTerm* ft_, TermCodeTree* tree_, Stack<CodeOp*>* firstsInBlocks_);

  };
  
public:
  struct TermMatcher
  : public Matcher
  {
    TermMatcher();

    void init(CodeTree* tree, TermList t);
    void reset();
    
    TermInfo* next();
    
    USE_ALLOCATOR(TermMatcher);
  };

};

};

#endif // __TermCodeTree__
