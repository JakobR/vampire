
/*
 * File MLMatcher.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file MLMatcher.hpp
 * Defines class MLMatcher with methods
 * supporting multiliteral matching.
 */


#ifndef __MLMatcher__
#define __MLMatcher__

#include "Clause.hpp"
#include "Forwards.hpp"
#include <unordered_map>
#include <vector>

namespace Kernel {

using namespace Lib;

class MLMatcher
{
  public:

    using LiteralVector = std::vector<Literal*, STLAllocator<Literal*>>;
    using BindingsMap = std::unordered_map<unsigned, TermList, std::hash<unsigned>, std::equal_to<unsigned>, STLAllocator<std::pair<const unsigned, TermList>>>;

  private:
    // TODO I don't know if using outMatchedAlts/outBindings together with resolvedLit works properly, so this is private for now
    static bool canBeMatchedImpl(
      Literal** baseLits,
      unsigned baseLen,
      Clause* instance,
      LiteralList** alts,
      Literal* resolvedLit,
      bool multiset,
      LiteralVector* outMatchedAlts = nullptr,
      BindingsMap* outBindings = nullptr);

  public:

    static bool canBeMatched(Literal** baseLits, unsigned baseLen, Clause* instance, LiteralList** alts, bool multiset, LiteralVector* outMatchedAlts = nullptr, BindingsMap* outBindings = nullptr)
    {
      return canBeMatchedImpl(baseLits, baseLen, instance, alts, nullptr, multiset, outMatchedAlts, outBindings);
    }

    static bool canBeMatched(Literal** baseLits, unsigned baseLen, Clause* instance, LiteralList** alts, Literal* resolvedLit, bool multiset)
    {
      return canBeMatchedImpl(baseLits, baseLen, instance, alts, resolvedLit, multiset);
    }

    static bool canBeMatched(Clause* base,                         Clause* instance, LiteralList** alts, Literal* resolvedLit)
    {
      // Note: we need multiset matching for subsumption, but for subsumption resolution it is not necessary
      return canBeMatchedImpl(base->literals(), base->length(), instance, alts, resolvedLit, resolvedLit == nullptr);
    }

    // static bool canBeMatched(Clause* base, DArray<LiteralList*>& matches);


  // private:
  //   template<class T, class U>
  //   static void orderLiterals(T& base, U& alts, DArray<Literal*>& baseOrd, DArray<LiteralList*>& altsOrd);
};


};

#endif /* __MLMatcher__ */
