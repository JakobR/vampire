
/*
 * File ForwardSubsumptionAndResolution.cpp.
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
 * @file ForwardSubsumptionAndResolution.cpp
 * Implements class ForwardSubsumptionAndResolution.
 */


#include <vector>
#include "Lib/STLAllocator.hpp"

#include "Lib/VirtualIterator.hpp"
#include "Lib/DArray.hpp"
#include "Lib/List.hpp"
#include "Lib/Comparison.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/TimeCounter.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/MLMatcher.hpp"
#include "Kernel/ColorHelper.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/LiteralMiniIndex.hpp"
#include "Indexing/IndexManager.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"

#include "ForwardSubsumptionAndResolution.hpp"

extern bool reporting;

namespace Inferences
{
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void ForwardSubsumptionAndResolution::attach(SaturationAlgorithm* salg)
{
  CALL("ForwardSubsumptionAndResolution::attach");
  ForwardSimplificationEngine::attach(salg);
  _unitIndex=static_cast<UnitClauseLiteralIndex*>(
    _salg->getIndexManager()->request(SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE) );
  _fwIndex=static_cast<FwSubsSimplifyingLiteralIndex*>(
    _salg->getIndexManager()->request(FW_SUBSUMPTION_SUBST_TREE) );
}

void ForwardSubsumptionAndResolution::detach()
{
  CALL("ForwardSubsumptionAndResolution::detach");
  _unitIndex=0;
  _fwIndex=0;
  _salg->getIndexManager()->release(SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE);
  _salg->getIndexManager()->release(FW_SUBSUMPTION_SUBST_TREE);
  ForwardSimplificationEngine::detach();
}


struct ClauseMatches
{
  CLASS_NAME(ForwardSubsumptionAndResolution::ClauseMatches);
  USE_ALLOCATOR(ClauseMatches);

  ClauseMatches(const ClauseMatches&) = delete;
  ClauseMatches(ClauseMatches&&) = delete;
  ClauseMatches& operator=(const ClauseMatches&) = delete;
  ClauseMatches& operator=(ClauseMatches&&) = delete;

public:
  Clause* _cl;
  unsigned _zeroCnt;  // how many literals of cl do not have any matches yet

  // array of LiteralList* of length cl->length;
  // stores for each literal of cl the literals matched with it
  // (should be: std::vector<std::vector<Literal*>>; but this can't be used immediately because _matches will be passed to MLMatcher)
  LiteralList** _matches;

  ClauseMatches(Clause* cl) : _cl(cl), _zeroCnt(cl->length())
  {
    // std::vector<int, STLAllocator<int>> vec;
    // vec.push_back(0);

    unsigned clen=_cl->length();
    _matches = static_cast<LiteralList**>(ALLOC_KNOWN(clen*sizeof(void*), "Inferences::ClauseMatches"));
    for(unsigned i=0;i<clen;i++) {
      _matches[i] = nullptr;
    }
  }

  ~ClauseMatches()
  {
    unsigned clen=_cl->length();
    for(unsigned i=0;i<clen;i++) {
      LiteralList::destroy(_matches[i]);
    }
    DEALLOC_KNOWN(_matches, clen*sizeof(void*), "Inferences::ClauseMatches");
  }

  void addMatch(Literal* baseLit, Literal* instLit)
  {
    addMatch(_cl->getLiteralPosition(baseLit), instLit);
  }

  void addMatch(unsigned bpos, Literal* instLit)
  {
    if(!_matches[bpos]) {
      _zeroCnt--;
    }
    LiteralList::push(instLit, _matches[bpos]);
  }

  void fillInMatches(LiteralMiniIndex* miniIndex)
  {
    // note that _cl here is mcl (the candidate clause that might simplify the new clause; the literals of the new clause are in the miniIndex)
    unsigned blen = _cl->length();

    for(unsigned bi=0; bi<blen; bi++) {
      LiteralMiniIndex::InstanceIterator instIt(*miniIndex, (*_cl)[bi], false);
      while(instIt.hasNext()) {
        // matches is a literal from the new clause which is an instance of the literal bi of mcl
        Literal* matched=instIt.next();
        addMatch(bi, matched);
      }
    }
  }

  bool anyNonMatched() { return _zeroCnt; }



  class ZeroMatchLiteralIterator
  {
  public:
    ZeroMatchLiteralIterator(ClauseMatches* cm)
    : _lits(cm->_cl->literals()), _mlists(cm->_matches), _remaining(cm->_cl->length())
    {
      if(cm->_zeroCnt == 0) {
	_remaining = 0;
      }
    }
    bool hasNext()
    {
      while(_remaining>0 && *_mlists) {
	_lits++; _mlists++; _remaining--;
      }
      return _remaining;
    }
    Literal* next()
    {
      _remaining--;
      _mlists++;
      return *(_lits++);
    }
  private:
    Literal** _lits;
    LiteralList** _mlists;
    unsigned _remaining;
  };




};


typedef Stack<ClauseMatches*> CMStack;

/*
bool isSubsumed(Clause* cl, CMStack& cmStore)
{
  CALL("isSubsumed");

  CMStack::Iterator csit(cmStore);
  while(csit.hasNext()) {
    ClauseMatches* clmatches;
    clmatches=csit.next();
    Clause* mcl=clmatches->_cl;

    if(clmatches->anyNonMatched()) {
      continue;
    }

    if(MLMatcher::canBeMatched(mcl,cl,clmatches->_matches,true)) {
      return true;
    }
  }
  return false;
}
*/

Clause* ForwardSubsumptionAndResolution::generateSubsumptionResolutionClause(Clause* cl, Literal* lit, Clause* baseClause)
{
  CALL("ForwardSubsumptionAndResolution::generateSubsumptionResolutionClause");
  int clen = cl->length();
  int nlen = clen-1;

  Inference* inf = new Inference2(Inference::SUBSUMPTION_RESOLUTION, cl, baseClause);
  Unit::InputType inpType = (Unit::InputType)
  	max(cl->inputType(), baseClause->inputType());

  Clause* res = new(nlen) Clause(nlen, inpType, inf);

  int next = 0;
  bool found=false;
  for(int i=0;i<clen;i++) {
    Literal* curr=(*cl)[i];
    //As we will apply subsumption resolution after duplicate literal
    //deletion, the same literal should never occur twice.
    ASS(curr!=lit || !found);
    if(curr!=lit || found) {
	(*res)[next++] = curr;
    } else {
      found=true;
    }
  }

  res->setAge(cl->age());

  return res;
}

bool checkForSubsumptionResolution(Clause* cl, ClauseMatches* cms, Literal* resLit)
{
  Clause* mcl=cms->_cl;
  unsigned mclen=mcl->length();

  ClauseMatches::ZeroMatchLiteralIterator zmli(cms);
  if(zmli.hasNext()) {
    while(zmli.hasNext()) {
      Literal* bl=zmli.next();
//      if( !resLit->couldBeInstanceOf(bl, true) ) {
      if( ! MatchingUtils::match(bl, resLit, true) ) {
	return false;
      }
    }
  } else {
    bool anyResolvable=false;
    for(unsigned i=0;i<mclen;i++) {
//      if(resLit->couldBeInstanceOf((*mcl)[i], true)) {
      if( MatchingUtils::match((*mcl)[i], resLit, true) ) {
	anyResolvable=true;
	break;
      }
    }
    if(!anyResolvable) {
      return false;
    }
  }

  return MLMatcher::canBeMatched(mcl,cl,cms->_matches,resLit);
}

bool ForwardSubsumptionAndResolution::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  CALL("ForwardSubsumptionAndResolution::perform");

  // QUESTION:
  // Why do we store the ClauseMatch instances with Clause::setAux?
  // It seems that we never access those values again,
  // so the aux storage is basically used as a boolean flag (via Clause::hasAux).
  // This means we can remove the variable cmStore too, right?
  // And every ClauseMatches is destroyed after its own loop iteration.
  // => not true, we iterate over cmStore later


  Clause* resolutionClause=0;

  unsigned clen=cl->length();
  if(clen==0) {
    return false;
  }

  TimeCounter tc_fs(TC_FORWARD_SUBSUMPTION);

  bool result = false;

  // discard all previous aux values (so after this, hasAux() returns false for any clause).
  Clause::requestAux();

  static CMStack cmStore(64);
  ASS(cmStore.isEmpty());

  // If there is a unit clause u that's more general than a literal in cl,
  // then cl is subsumed by u and we can delete cl.
  //
  // C \/ s        t
  // ---------------
  // (delete C \/ s)
  //
  // if s = tΘ
  for(unsigned li=0;li<clen;li++) {
    SLQueryResultIterator rit=_unitIndex->getGeneralizations( (*cl)[li], false, false);
    while(rit.hasNext()) {
      Clause* premise=rit.next().clause;

      // if there's an aux, it means we already checked this clause.
      if(premise->hasAux()) {
        continue;
      }

      // set aux to nullptr (now hasAux() will return true) to indicate we have checked it
      premise->setAux(nullptr);

      if(ColorHelper::compatible(cl->color(), premise->color()) ) {
        // Done with subsumption
        premises = pvi( getSingletonIterator(premise) );
        env.statistics->forwardSubsumed++;
        result = true;
        goto fin;
      }
    }
  }

  {  // (new scope required because the goto above would otherwise skip over variable initialization)

    // Initialize miniIndex with literals in the clause cl
    LiteralMiniIndex miniIndex(cl);

    for(unsigned li=0;li<clen;li++) {
      // generalizations of a literal in cl
      SLQueryResultIterator rit = _fwIndex->getGeneralizations( (*cl)[li], false, false);

      // cl = C \/ l      where l = cl[li]
      // mcl = D \/ r     where l = rΘ

      while(rit.hasNext()) {
        SLQueryResult res = rit.next();
        Clause* mcl = res.clause;
        if(mcl->hasAux()) {
          // we've already checked this clause
          continue;
        }
        if (_fwIndex->isSecondBest(res.clause, res.literal)) {
          continue;
        }
        unsigned mlen = mcl->length();
        ASS_G(mlen,1);  // we've already checked all candidate unit clauses above

        ClauseMatches* cms = new ClauseMatches(mcl);
        mcl->setAux(cms);   // mark clause as checked
        cmStore.push(cms);
        //      cms->addMatch(res.literal, (*cl)[li]);
        //      cms->fillInMatches(&miniIndex, res.literal, (*cl)[li]);
        cms->fillInMatches(&miniIndex);
        // cms contains:
        // For each literal L of mcl, all literals L' of cl such that L' is an instance of L  (or, L is a generalization of L').

        if(cms->anyNonMatched()) {
          continue;
        }

        if (MLMatcher::canBeMatched(mcl, cl, cms->_matches, true)
            && ColorHelper::compatible(cl->color(), mcl->color())
            ) {
          // Done with subsumption (cl is subsumed, so replacement stays empty because we just delete cl)
          premises = pvi( getSingletonIterator(mcl) );
          env.statistics->forwardSubsumed++;
          result = true;
          goto fin;
        }
      }
    }

    // done with forward subsumption; so the time counter is stopped
    tc_fs.stop();




    // Below here seems to be the resolution part.
    // So if subsumptionResolution is false, we only check for subsumption and stop before checking for resolution?
    if(!_subsumptionResolution) {
      goto fin;
    }

    {
      TimeCounter tc_fsr(TC_FORWARD_SUBSUMPTION_RESOLUTION);

      for(unsigned li=0;li<clen;li++) {
        Literal* resLit=(*cl)[li];
        SLQueryResultIterator rit=_unitIndex->getGeneralizations( resLit, true, false);
        while(rit.hasNext()) {
          Clause* mcl=rit.next().clause;
          if(ColorHelper::compatible(cl->color(), mcl->color())) {
            resolutionClause=generateSubsumptionResolutionClause(cl,resLit,mcl);
            env.statistics->forwardSubsumptionResolution++;
            premises = pvi( getSingletonIterator(mcl) );
            replacement = resolutionClause;
            result = true;
            goto fin;
          }
        }
      }

      {
        CMStack::Iterator csit(cmStore);
        while(csit.hasNext()) {
          ClauseMatches* cms=csit.next();
          for(unsigned li=0;li<clen;li++) {
            Literal* resLit=(*cl)[li];
            if(checkForSubsumptionResolution(cl, cms, resLit) && ColorHelper::compatible(cl->color(), cms->_cl->color()) ) {
              resolutionClause=generateSubsumptionResolutionClause(cl,resLit,cms->_cl);
              env.statistics->forwardSubsumptionResolution++;
              premises = pvi( getSingletonIterator(cms->_cl) );
              replacement = resolutionClause;
              result = true;
              goto fin;
            }
          }
        }
      }

      for(unsigned li=0;li<clen;li++) {
        Literal* resLit=(*cl)[li];	//resolved literal
        SLQueryResultIterator rit=_fwIndex->getGeneralizations( resLit, true, false);
        while(rit.hasNext()) {
          SLQueryResult res=rit.next();
          Clause* mcl=res.clause;

          if(mcl->hasAux()) {
            //we have already examined this clause
            continue;
          }
          if (_fwIndex->isSecondBest(res.clause, res.literal)) {
            continue;
          }

          ClauseMatches* cms=new ClauseMatches(mcl);
          res.clause->setAux(cms);
          cmStore.push(cms);
          cms->fillInMatches(&miniIndex);

          if(checkForSubsumptionResolution(cl, cms, resLit) && ColorHelper::compatible(cl->color(), cms->_cl->color())) {
            resolutionClause=generateSubsumptionResolutionClause(cl,resLit,cms->_cl);
            env.statistics->forwardSubsumptionResolution++;
            premises = pvi( getSingletonIterator(cms->_cl) );
            replacement = resolutionClause;
            result = true;
            goto fin;
          }

        }
      }
    }
  }

fin:
  Clause::releaseAux();
  while(cmStore.isNonEmpty()) {
    delete cmStore.pop();
  }
  return result;
}

}
