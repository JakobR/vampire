#ifndef __MLMatcher2__
#define __MLMatcher2__

#include "Clause.hpp"
#include "Forwards.hpp"
#include "Lib/STL.hpp"

namespace Kernel {

using namespace Lib;


class MLMatcher2
{
  private:
    /**
     * Initializes the matcher to the given match problem.
     * The matcher will be in a valid (but unmatched) state.
     *
     * Preconditions:
     * - All literals in 'alts' must appear in 'instance'.
     * - If resolvedLit is not null, multiset must be false. (Hypothesis; not 100% sure if the matching algorithm breaks in that case)
     */
    MLMatcher2(Literal** baseLits,
               unsigned baseLen,
               Clause* instance,
               LiteralList** alts,
               Literal* resolvedLit,
               bool multiset);

  public:
    MLMatcher2(Literal** baseLits,
               unsigned baseLen,
               Clause* instance,
               LiteralList** alts,
               bool multiset)
      : MLMatcher2(baseLits, baseLen, instance, alts, nullptr, multiset)
    { }

    MLMatcher2(Clause* base,
               Clause* instance,
               LiteralList** alts,
               bool multiset)
      : MLMatcher2(base->literals(), base->length(), instance, alts, multiset)
    { }

    MLMatcher2(Literal** baseLits,
               unsigned baseLen,
               Clause* instance,
               LiteralList** alts,
               Literal* resolvedLit)
      : MLMatcher2(baseLits, baseLen, instance, alts, resolvedLit, resolvedLit == nullptr)
      // NOTE: we need multiset matching for subsumption, but for subsumption resolution it is not necessary
    { }

    MLMatcher2(Clause* base,
               Clause* instance,
               LiteralList** alts,
               Literal* resolvedLit)
      : MLMatcher2(base->literals(), base->length(), instance, alts, resolvedLit)
    { }

    ~MLMatcher2();

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
    MLMatcher2() = delete;
    MLMatcher2(MLMatcher2 const&) = delete;
    MLMatcher2(MLMatcher2&&) = delete;
    MLMatcher2& operator=(MLMatcher2 const&) = delete;
    MLMatcher2& operator=(MLMatcher2&&) = delete;

  private:
    class Impl;
    std::unique_ptr<Impl> m_impl;

  public:
    // Helper functions for compatibility to previous code. These are working with a shared static instance of MLMatcherImpl.
    static bool canBeMatched(Clause* base,                         Clause* instance, LiteralList** alts, Literal* resolvedLit)
    {
      return canBeMatched(base->literals(), base->length(), instance, alts, resolvedLit, resolvedLit == nullptr);
    }
  private:
    static bool canBeMatched(Literal** baseLits, unsigned baseLen, Clause* instance, LiteralList** alts, Literal* resolvedLit, bool multiset);
};


};

#endif /* __MLMatcher2__ */
