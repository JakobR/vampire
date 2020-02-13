/*
 * File MLMatcher2.hpp.
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

#ifndef __MLMatcher2__
#define __MLMatcher2__

#include "Clause.hpp"
#include "Forwards.hpp"
#include "Lib/STL.hpp"

namespace Kernel {

using namespace Lib;


struct MLMatch2Stats
{
  int numBacktracked = 0;
  int numSteps = 0;
  int numMatches = 0;
};

inline std::ostream& operator<<(std::ostream& os, MLMatch2Stats const& stats)
{
  os << "{ \"backtracked\": " << stats.numBacktracked
     << ", \"steps\": " << stats.numSteps
     << ", \"matches\": " << stats.numMatches
     << " }";
  return os;
}


class MLMatcher2 final
{
  public:
    /**
     * Constructs an MLMatcher2 and puts it in an invalid state.
     */
    MLMatcher2();

    ~MLMatcher2();

    /**
     * Initializes the matcher to the given match problem.
     * The matcher will be in a valid (but unmatched) state.
     *
     * MLMatcher2 solves the FSD-Match-Problem:
     * - One positive equality of the baseLits is selected for demodulation, and
     * - All other literals are (multiset-)matched to the given alts from the instance
     *   (may involve a uniform substitution from base to alts/instance).
     *
     * Preconditions:
     * - baseLits must have length baseLen
     * - alts must have length baseLen (for 0 <= bi < baseLen, the literal baseLits[bi] will be matched against the alternatives in the list alts[bi])
     * - All literals in 'alts' must appear in 'instance'
     * - 'instance' must not have duplicate literals (during normal operation this is ensured by Inferences::DuplicateLiteralRemovalISE)
     */
    void init(Literal* baseLits[],
              unsigned baseLen,
              Clause* instance,
              LiteralList const* const alts[]);

    void init(Clause* base, Clause* instance, LiteralList const* const alts[])
    {
      init(base->literals(), base->length(), instance, alts);
    }

    /**
     * Finds the next match.
     * May only be called if the matcher is in a valid state.
     * Return value:
     * - True if a match was found. The matcher is now in a valid and matched state.
     * - False if no more matches are possible. The matcher is now in an invalid state.
     */
    bool nextMatch();

    /**
     * Returns the equality literal from base that was selected for demodulation.
     * May only be called in a matched state (i.e., after nextMatch() has returned true).
     * May return nullptr in case of subsumption (i.e., complete multiset match).
     */
    Literal* getEqualityForDemodulation() const;

    /**
     * Returns a bitmap that indicates which alts are currently matched by some base literal.
     * May only be called in a matched state (i.e., after nextMatch() has returned true).
     *
     * After the function returns:
     * outMatchedBitmap[i] == true iff instance[i] is matched by some literal of base
     *
     * The given vector will be cleared before operating on it.
     */
    void getMatchedAltsBitmap(v_vector<bool>& outMatchedBitmap) const;

    /**
     * Returns the variable bindings due to the current match.
     * May only be called in a matched state (i.e., after nextMatch() has returned true).
     */
    void getBindings(v_unordered_map<unsigned, TermList>& outBindings) const;

    MLMatch2Stats getStats() const;

    // Disallow copy because the internal implementation still uses pointers to the underlying storage and it seems hard to untangle that.
    MLMatcher2(MLMatcher2 const&) = delete;
    MLMatcher2& operator=(MLMatcher2 const&) = delete;

    // Moving works by moving the pointer m_impl
    MLMatcher2(MLMatcher2&&) = default;
    MLMatcher2& operator=(MLMatcher2&&) = default;

  private:
    class Impl;
    std::unique_ptr<Impl> m_impl;
};


};

#endif /* __MLMatcher2__ */
