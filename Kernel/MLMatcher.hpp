
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
#include <unordered_set>
#include <vector>

namespace Kernel {

using namespace Lib;

// struct MatchingData;

// TODO: Remove all static stuff from MLMatcher implementation.
// Then, if static stuff really helps to save allocations for performance, make one shared MLMatcher instance.
class MLMatcher
{
  public:

    using LiteralVector = std::vector<Literal*, STLAllocator<Literal*>>;

    // TODO: Move these declarations (also v_vector) to some file called Lib/STL.h (or just to forwards.hpp?)
    template< typename Key
            , typename Hash = std::hash<Key>
            , typename KeyEqual = std::equal_to<Key>
    > using v_unordered_set = std::unordered_set<Key, Hash, KeyEqual, STLAllocator<Key>>;

    template< typename Key
            , typename T
            , typename Hash = std::hash<Key>
            , typename KeyEqual = std::equal_to<Key>
    > using v_unordered_map = std::unordered_map<Key, T, Hash, KeyEqual, STLAllocator<std::pair<const Key, T>>>;

    using BindingsMap = std::unordered_map<unsigned, TermList, std::hash<unsigned>, std::equal_to<unsigned>, STLAllocator<std::pair<const unsigned, TermList>>>;

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


    /**
     * Initialize matcher to the given match problem.
     * The matcher will be valid after calling this function (unless it throws an exception).
     */
    static void initMatcher(
      Literal** baseLits,
      unsigned baseLen,
      Clause* instance,
      LiteralList** alts,  // TODO: note precondition: all literals in alts must appear in instance
      Literal* resolvedLit,
      bool multiset);

    /**
     * Return true if a match was found, false if no more matches are possible.
     * May only be called if the matcher is valid.
     * If false is returned, the matcher is invalidated after the call.
     */
    static bool nextMatch();

    // Return the alts which are currently matched by some base literal.
    // May only be called after nextMatch() has returned true.
    static v_unordered_set<Literal*> getMatchedAlts();

    // Return the variable bindings due to the current match.
    // May only be called after nextMatch() has returned true.
    static v_unordered_map<unsigned, TermList> getBindings();

    /*
    class MLMatch
    {
      public:
        MLMatch(MatchingData* md);
        ~MLMatch();

        MLMatch() = delete;
        MLMatch(MLMatch const&) = delete;
        MLMatch(MLMatch&&) = delete;
        MLMatch& operator=(MLMatch const&) = delete;
        MLMatch& operator=(MLMatch&&) = delete;

        v_unordered_set<Literal*> getMatchedAlts();
        v_unordered_map<unsigned, TermList> getBindings();
      private:
        MatchingData* md;
    };

    class MLMatchIterator
    {
      public:
        MLMatchIterator(
          Literal** baseLits,
          unsigned baseLen,
          Clause* instance,
          LiteralList** alts,
          Literal* resolvedLit,
          bool multiset);

        ~MLMatchIterator();

        // Calling hasNext() or next() invalidates all previously returned MLMatch instances
        bool hasNext();
        MLMatch next();

        MLMatchIterator() = delete;
        MLMatchIterator(MLMatchIterator const&) = delete;
        MLMatchIterator(MLMatchIterator&&) = delete;
        MLMatchIterator& operator=(MLMatchIterator const&) = delete;
        MLMatchIterator& operator=(MLMatchIterator&&) = delete;

      private:
        MatchingData* md;
    };

    // NOTE: only one MLMatchIterator and one MLMatch can be active at the same time.
    static MLMatchIterator enumerateMatchings(Literal** baseLits, unsigned baseLen, Clause* instance, LiteralList** alts, bool multiset);
    */

  private:
    // It's unclear if using outMatchedAlts/outBindings together with resolvedLit works properly, so this is private for now
    static bool canBeMatchedImpl(
      Literal** baseLits,
      unsigned baseLen,
      Clause* instance,
      LiteralList** alts,  // TODO: note precondition: all literals in alts must appear in instance
      Literal* resolvedLit,
      bool multiset,
      LiteralVector* outMatchedAlts = nullptr,
      BindingsMap* outBindings = nullptr);
    // TODO: Take something that's easier to use than LiteralLists** for alts.
    // TODO: Since I do not actually need the correct order in outMatchedAlts, we can also construct a set and return that. Then we don't have to track original base indices anymore.
};


};

#endif /* __MLMatcher__ */
