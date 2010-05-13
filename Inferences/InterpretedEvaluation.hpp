/**
 * @file InterpretedEvaluation.hpp
 * Defines class InterpretedEvaluation.
 */


#ifndef __InterpretedEvaluation__
#define __InterpretedEvaluation__

#include "../Forwards.hpp"

#include "../Lib/DHMap.hpp"

#include "../Kernel/Theory.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class InterpretedEvaluation
: public ImmediateSimplificationEngine
{
public:
  Clause* simplify(Clause* cl);
private:
  int getInterpretedFunction(Term* t);
  int getInterpretedPredicate(Literal* lit);
  bool isInterpretedConstant(Term* t);

  InterpretedType interpretConstant(Term* t);
  InterpretedType interpretConstant(TermList t);
  Term* getRepresentation(InterpretedType val);

  Term* interpretFunction(int fnIndex, TermList* args);
  bool interpretPredicate(int predIndex, TermList* args);
  bool evaluateLiteral(Literal* lit, bool& constant, Literal*& res, bool& constantTrue);

  DHMap<InterpretedType, Term*> _constants;
};

};

#endif /* __InterpretedEvaluation__ */
