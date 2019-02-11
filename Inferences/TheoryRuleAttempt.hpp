#ifndef THEORYRULEATTEMPT_HPP
#define THEORYRULEATTEMPT_HPP

#include "InferenceEngine.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/TermIndex.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;


/**
 * As a first attempt, we chose to implement
 * the following rule for transitivity:
 *
 *     t < u   u < v
 *    ---------------
 *         t < v
 *
 * Should be a GeneratingInferenceEngine, since we cannot
 * discard the premises.
 *
 * To find out more about how to use the indexing and unification,
 * I have now implemented the following extended version:
 *
 *     t < u \/ C     v < w \/ D     uθ = vθ
 *    ---------------------------------------
 *               tθ < wθ \/ Cθ \/ Dθ
 *
 * (when "t<u" is a selected literal in "t<u \/ C")
 */
class TransitivityRuleExperiment
    : public GeneratingInferenceEngine
{
    public:
        CLASS_NAME(TransitivityRuleExperiment);
        USE_ALLOCATOR(TransitivityRuleExperiment);

        void attach(SaturationAlgorithm* salg) override;
        void detach() override;

        ClauseIterator generateClauses(Clause* premise) override;


    private:
        SuperpositionSubtermIndex* _supSubtermIndex;
        SuperpositionLHSIndex* _supLHSIndex;
        DemodulationSubtermIndex* _demSubtermIndex;
        DemodulationLHSIndex* _demLHSIndex;

        GeneratingLiteralIndex* _glIndex;
        SimplifyingLiteralIndex* _slIndex;
        FwSubsSimplifyingLiteralIndex* _fwsslIndex;
        UnitClauseLiteralIndex* _suclIndex;   // there's a simplifying and a generating version
        UnitClauseLiteralIndex* _guclIndex;
        NonUnitClauseLiteralIndex* _nuclIndex;
        RewriteRuleIndex* _rrIndex;
};

/*
 * TODO
 * --show_theory_axioms doesn't print all axioms that are added.
 *
 * Make sure that we add no axioms when we set --theory_axioms off.
 * (also check value "some")
 *
 * options: --evaluation off or so??
 * two parts: normalizing (in preprocessing), simplification (during saturation)
 *
 * Goal: to have full control over theory reasoning
 * => do this off the master branch so we can merge it in when it's done
 */

/*
 * vampire options:
 * prioritize axioms vs hypothesis (which do you trust more?)
 */

/*
 * Replace all theory axioms by inference rules in clausal orientation:
 * Only difference here is that we get a penalty.
 * => see how the penalty changes the proofs
 *
 * For a first version, just add the penalty to TheoryAxioms.cpp
 * Also output penalty so we can use it for proof visualization.
 */

class IrreflexivityISE
: public ImmediateSimplificationEngine
{
    public:
        CLASS_NAME(IrreflexivityISE);
        USE_ALLOCATOR(IrreflexivityISE);

        Clause* simplify(Clause* c) override;
};

class IrreflexivityFSE
: public ForwardSimplificationEngine
{
    public:
        CLASS_NAME(IrreflexivityFSE);
        USE_ALLOCATOR(IrreflexivityFSE);

        bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;
};



}

#endif /* !THEORYRULEATTEMPT_HPP */
