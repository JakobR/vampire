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
#include "Lib/STL.hpp"

namespace Kernel {

using namespace Lib;


class MLMatcher
{
  private:
    // TODO:
    // Maybe split construction and initialization.
    // This allows users to keep a single instance around and reinitialize it whenever needed without having to reallocate memory.

    /**
     * Initializes the matcher to the given match problem.
     * The matcher will be in a valid (but unmatched) state.
     *
     * Preconditions:
     * - All literals in 'alts' must appear in 'instance'.
     * - If resolvedLit is not null, multiset must be false. (Hypothesis; not 100% sure if the matching algorithm breaks in that case)
     */
    MLMatcher(Literal** baseLits,
              unsigned baseLen,
              Clause* instance,
              LiteralList** alts,
              Literal* resolvedLit,
              bool multiset);

  public:
    MLMatcher(Literal** baseLits,
              unsigned baseLen,
              Clause* instance,
              LiteralList** alts,
              bool multiset)
      : MLMatcher(baseLits, baseLen, instance, alts, nullptr, multiset = false)
    { }

    MLMatcher(Clause* base,
              Clause* instance,
              LiteralList** alts,
              bool multiset)
      : MLMatcher(base->literals(), base->length(), instance, alts, multiset = false)
    { }

    MLMatcher(Literal** baseLits,
              unsigned baseLen,
              Clause* instance,
              LiteralList** alts,
              Literal* resolvedLit)
      : MLMatcher(baseLits, baseLen, instance, alts, resolvedLit, resolvedLit == nullptr)
      // NOTE: we need multiset matching for subsumption, but for subsumption resolution it is not necessary
    { }

    MLMatcher(Clause* base,
              Clause* instance,
              LiteralList** alts,
              Literal* resolvedLit)
      : MLMatcher(base->literals(), base->length(), instance, alts, resolvedLit)
    { }

    ~MLMatcher();

    /**
     * Find the next match.
     * May only be called if the matcher is in a valid state.
     * Return value:
     * - True if a match was found. The matcher is now in a valid and matched state.
     * - False if no more matches are possible. The matcher is now in an invalid state.
     */
    bool nextMatch();

    /**
     * Return the alts which are currently matched by some base literal.
     * May only be called in a matched state (i.e., after nextMatch() has returned true).
     */
    v_unordered_set<Literal*> getMatchedAlts();

    /**
     * Return the variable bindings due to the current match.
     * May only be called in a matched state (i.e., after nextMatch() has returned true).
     */
    v_unordered_map<unsigned, TermList> getBindings();

    // Disallow copy/move because the internal implementation still uses pointers to the underlying storage.
    // TODO: we *could* implement the move operations at least, by moving the unique_ptr.
    MLMatcher() = delete;
    MLMatcher(MLMatcher const&) = delete;
    MLMatcher(MLMatcher&&) = delete;
    MLMatcher& operator=(MLMatcher const&) = delete;
    MLMatcher& operator=(MLMatcher&&) = delete;

  private:
    class Impl;
    std::unique_ptr<Impl> m_impl;

  public:
    // Helper functions for compatibility to previous code. These are working with a shared static instance of MLMatcher::Impl.
    static bool canBeMatched(Clause* base,                         Clause* instance, LiteralList** alts, Literal* resolvedLit)
    {
      return canBeMatched(base->literals(), base->length(), instance, alts, resolvedLit);
    }

    static bool canBeMatched(Literal** baseLits, unsigned baseLen, Clause* instance, LiteralList** alts, Literal* resolvedLit)
    {
      return canBeMatchedImpl(baseLits, baseLen, instance, alts, resolvedLit, resolvedLit == nullptr);
    }

    static bool canBeMatched(Clause* base,                         Clause* instance, LiteralList** alts, bool multiset = false)
    {
      return canBeMatched(base->literals(), base->length(), instance, alts, multiset);
    }

    static bool canBeMatched(Literal** baseLits, unsigned baseLen, Clause* instance, LiteralList** alts, bool multiset = false)
    {
      return canBeMatchedImpl(baseLits, baseLen, instance, alts, nullptr, multiset);
    }

  private:
    static bool canBeMatchedImpl(Literal** baseLits, unsigned baseLen, Clause* instance, LiteralList** alts, Literal* resolvedLit, bool multiset);
};


};

#endif /* __MLMatcher__ */
