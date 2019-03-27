/*
 * File MLMatcher.cpp.
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
 * @file MLMatcher.cpp
 * Implements class MLMatcher.
 */

#include "Lib/Backtrackable.hpp"
#include "Lib/BacktrackIterators.hpp"
#include "Lib/BinaryHeap.hpp"
#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Hash.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaarrays.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/Stack.hpp"
#include "Lib/TriangularArray.hpp"

#include "Clause.hpp"
#include "Matcher.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"

#include "MLMatcher.hpp"

#if VDEBUG
#include <iostream>
#include "Test/Output.hpp"
#endif

#define TRACE_LONG_MATCHING 0
#if TRACE_LONG_MATCHING
#include "Lib/Timer.hpp"
#endif

namespace Kernel
{

using namespace Lib;

typedef DHMap<unsigned,unsigned, IdentityHash> UUMap;


/**
 * Binder that stores bindings into a specified array. To be used
 * with MatchingUtils template methods.
 */
struct ArrayStoringBinder
{
  ArrayStoringBinder(TermList* arr, UUMap& v2pos)
  : _arr(arr), _v2pos(v2pos) {}

  bool bind(unsigned var, TermList term)
  {
    _arr[_v2pos.get(var)]=term;
    return true;
  }

  void specVar(unsigned var, TermList term)
  { ASSERTION_VIOLATION; }
private:
  TermList* _arr;
  UUMap& _v2pos;
};

bool createLiteralBindings(Literal* baseLit, LiteralList* alts, Clause* instCl, Literal* resolvedLit,
    unsigned*& boundVarData, TermList**& altBindingPtrs, TermList*& altBindingData)
{
  CALL("createLiteralBindings");

  static UUMap variablePositions;
  static BinaryHeap<unsigned,Int> varNums;
  variablePositions.reset();
  varNums.reset();

  VariableIterator bvit(baseLit);
  while(bvit.hasNext()) {
    unsigned var=bvit.next().var();
    varNums.insert(var);
  }

  unsigned nextPos=0;
  while(!varNums.isEmpty()) {
    unsigned var=varNums.pop();
    while(!varNums.isEmpty() && varNums.top()==var) {
      varNums.pop();
    }
    if(variablePositions.insert(var,nextPos)) {
      *(boundVarData++)=var;
      nextPos++;
    }
  }
  unsigned numVars=nextPos;

  LiteralList::Iterator ait(alts);
  while(ait.hasNext()) {
    //handle multiple matches in equality!
    Literal* alit=ait.next();
    if(alit==resolvedLit) {
      continue;
    }
    if(alit->isEquality()) {
      //we must try both possibilities
      if(MatchingUtils::matchArgs(baseLit,alit)) {
        ArrayStoringBinder binder(altBindingData, variablePositions);
        MatchingUtils::matchArgs(baseLit,alit,binder);
        *altBindingPtrs=altBindingData;
        altBindingPtrs++;
        altBindingData+=numVars;
        if(resolvedLit) {
          new(altBindingData++) TermList((size_t)0);
        } else {
          // add index of the literal in instance clause at the end of the binding sequence
          new(altBindingData++) TermList((size_t)instCl->getLiteralPosition(alit));
        }
      }
      if(MatchingUtils::matchReversedArgs(baseLit, alit)) {
        ArrayStoringBinder binder(altBindingData, variablePositions);
        MatchingUtils::matchTerms(*baseLit->nthArgument(0),*alit->nthArgument(1),binder);
        MatchingUtils::matchTerms(*baseLit->nthArgument(1),*alit->nthArgument(0),binder);

        *altBindingPtrs=altBindingData;
        altBindingPtrs++;
        altBindingData+=numVars;
        if(resolvedLit) {
          new(altBindingData++) TermList((size_t)0);
        } else {
          // add index of the literal in instance clause at the end of the binding sequence
          new(altBindingData++) TermList((size_t)instCl->getLiteralPosition(alit));
        }
      }

    } else {
      if(numVars) {
        ArrayStoringBinder binder(altBindingData, variablePositions);
        ALWAYS(MatchingUtils::matchArgs(baseLit,alit,binder));
      }

      *altBindingPtrs=altBindingData;
      altBindingPtrs++;
      altBindingData+=numVars;
      if(resolvedLit) {
        new(altBindingData++) TermList((size_t)0);
      } else {
        // add index of the literal in instance clause at the end of the binding sequence
        new(altBindingData++) TermList((size_t)instCl->getLiteralPosition(alit));
      }
    }
  }
  if(resolvedLit && resolvedLit->complementaryHeader()==baseLit->header()) {
    if(!baseLit->arity() || MatchingUtils::matchArgs(baseLit,resolvedLit)) {
      if(numVars) {
        ArrayStoringBinder binder(altBindingData, variablePositions);
        MatchingUtils::matchArgs(baseLit,resolvedLit,binder);
      }
      *altBindingPtrs=altBindingData;
      altBindingPtrs++;
      altBindingData+=numVars;
      new(altBindingData++) TermList((size_t)1);
    }
    if(baseLit->isEquality() && MatchingUtils::matchReversedArgs(baseLit, resolvedLit)) {
      ArrayStoringBinder binder(altBindingData, variablePositions);
      MatchingUtils::matchTerms(*baseLit->nthArgument(0),*resolvedLit->nthArgument(1),binder);
      MatchingUtils::matchTerms(*baseLit->nthArgument(1),*resolvedLit->nthArgument(0),binder);

      *altBindingPtrs=altBindingData;
      altBindingPtrs++;
      altBindingData+=numVars;
      new(altBindingData++) TermList((size_t)1);
    }

  }
  return true;
}

struct MatchingData {
  unsigned len;
  unsigned* varCnts;
  unsigned** boundVarNums;
  /**
   * TermList[] corresponding to an alternative contains binding
   * for each variable of the base literal, and then one element
   * identifying the alternative literal itself.
   */
  TermList*** altBindings;
  TriangularArray<unsigned>* remaining;
  unsigned* nextAlts;

  TriangularArray<pair<int,int>* >* intersections;

  Literal** bases;
  LiteralList** alts;
  Clause* instance;
  Literal* resolvedLit;

  unsigned* boundVarNumStorage;
  TermList** altBindingPtrStorage;
  TermList* altBindingStorage;
  pair<int,int>* intersectionStorage;

  enum InitResult {
    OK,
    MUST_BACKTRACK,
    NO_ALTERNATIVE
  };

  std::vector<unsigned, STLAllocator<unsigned>> currentAlts;
  std::vector<unsigned, STLAllocator<unsigned>> originalBaseIndex;
  unsigned timestamp = 0;

  unsigned getRemainingInCurrent(unsigned bi)
  {
    return remaining->get(bi,bi);
  }
  unsigned getAltRecordIndex(unsigned bi, unsigned alti)
  {
    return static_cast<unsigned>(altBindings[bi][alti][varCnts[bi]].content());
  }

  /**
   * Return true if binding @b b1Index -th base literal that binds variables
   * to terms stored in @b i1Bindings is compatible to binding @b b2Index -th
   * base literal that binds variables to terms stored in
   * @b altBindings[b2Index][i2AltIndex] .
   */
  bool compatible(unsigned b1Index, TermList* i1Bindings,
                  unsigned b2Index, unsigned i2AltIndex, pair<int,int>* iinfo)
  {
    CALL("MatchingData::compatible");

    TermList* i2Bindings=altBindings[b2Index][i2AltIndex];

    while(iinfo->first!=-1) {
      if(i1Bindings[iinfo->first]!=i2Bindings[iinfo->second]) {
        return false;
      }
      iinfo++;
    }
    return true;
  }

  bool bindAlt(unsigned bIndex, unsigned altIndex)
  {
    TermList* curBindings=altBindings[bIndex][altIndex];
    for(unsigned i=bIndex+1; i<len; i++) {
      if(!isInitialized(i)) {
        break;
      }
      pair<int,int>* iinfo=getIntersectInfo(bIndex, i);
      unsigned remAlts=remaining->get(i,bIndex);

      if(iinfo->first!=-1) {
        for(unsigned ai=0;ai<remAlts;ai++) {
          if(!compatible(bIndex,curBindings,i,ai,iinfo)) {
            remAlts--;
            std::swap(altBindings[i][ai], altBindings[i][remAlts]);
            ai--;
          }
        }
      }
      if(remAlts==0) {
        return false;
      }
      remaining->set(i,bIndex+1,remAlts);
    }
    currentAlts[bIndex] = altIndex;
    return true;
  }

  pair<int,int>* getIntersectInfo(unsigned b1, unsigned b2)
  {
    ASS_L(b1, b2);
    pair<int,int>* res=intersections->get(b2,b1);
    if( res ) {
      return res;
    }
    intersections->set(b2,b1, intersectionStorage);
    res=intersectionStorage;

    unsigned b1vcnt=varCnts[b1];
    unsigned b2vcnt=varCnts[b2];
    unsigned* b1vn=boundVarNums[b1];
    unsigned* b1vnStop=boundVarNums[b1]+b1vcnt;
    unsigned* b2vn=boundVarNums[b2];
    unsigned* b2vnStop=boundVarNums[b2]+b2vcnt;

    int b1VarIndex=0;
    int b2VarIndex=0;
    while(true) {
      while(b1vn!=b1vnStop && *b1vn<*b2vn) { b1vn++; b1VarIndex++; }
      if(b1vn==b1vnStop) { break; }
      while(b2vn!=b2vnStop && *b1vn>*b2vn) { b2vn++; b2VarIndex++; }
      if(b2vn==b2vnStop) { break; }
      if(*b1vn==*b2vn) {
        intersectionStorage->first=b1VarIndex;
        intersectionStorage->second=b2VarIndex;
        intersectionStorage++;

        b1vn++; b1VarIndex++;
        b2vn++; b2VarIndex++;
        if(b1vn==b1vnStop || b2vn==b2vnStop) { break; }
      }
    }

    intersectionStorage->first=-1;
    intersectionStorage++;

    return res;
  }

  bool isInitialized(unsigned bIndex) {
    return boundVarNums[bIndex];
  }

  InitResult ensureInit(unsigned bIndex)
  {
    CALL("MatchingData::ensureInit");

    if(!isInitialized(bIndex)) {
      boundVarNums[bIndex]=boundVarNumStorage;
      altBindings[bIndex]=altBindingPtrStorage;
      ALWAYS(createLiteralBindings(bases[bIndex], alts[bIndex], instance, resolvedLit,
                                   boundVarNumStorage, altBindingPtrStorage, altBindingStorage));
      varCnts[bIndex]=boundVarNumStorage-boundVarNums[bIndex];

      unsigned altCnt = altBindingPtrStorage - altBindings[bIndex];
      if (altCnt == 0) {
        return NO_ALTERNATIVE;
      }
      remaining->set(bIndex, 0, altCnt);

      unsigned remAlts=0;
      for(unsigned pbi=0;pbi<bIndex;pbi++) {  // pbi ~ previous base index
        pair<int,int>* iinfo=getIntersectInfo(pbi, bIndex);
        remAlts=remaining->get(bIndex, pbi);

        if(iinfo->first!=-1) {
          TermList* pbBindings=altBindings[pbi][nextAlts[pbi]-1];
          for(unsigned ai=0;ai<remAlts;ai++) {
            if(!compatible(pbi, pbBindings, bIndex, ai, iinfo)) {
              remAlts--;
              std::swap(altBindings[bIndex][ai], altBindings[bIndex][remAlts]);
              ai--;
            }
          }
        }
        remaining->set(bIndex,pbi+1,remAlts);
      }
      if(bIndex>0 && remAlts==0) {
        return MUST_BACKTRACK;
      }
    }
    return OK;
  }

};


static DArray<Literal*> s_baseLits(32);
static DArray<LiteralList*> s_altsArr(32);

static DArray<unsigned> s_varCnts(32);
static DArray<unsigned*> s_boundVarNums(32);
static DArray<TermList**> s_altPtrs(32);
static TriangularArray<unsigned> s_remaining(32);
static TriangularArray<pair<int,int>* > s_intersections(32);
static DArray<unsigned> s_nextAlts(32);


static DArray<unsigned> s_boundVarNumData(64);
static DArray<TermList*> s_altBindingPtrs(128);
static DArray<TermList> s_altBindingsData(256);
static DArray<pair<int,int> > s_intersectionData(128);

static MatchingData s_matchingData;

MatchingData* getMatchingData(Literal** baseLits0, unsigned baseLen, Clause* instance, LiteralList** alts, Literal* resolvedLit)
{
  CALL("getMatchingData");

  s_baseLits.initFromArray(baseLen,baseLits0);
  s_altsArr.initFromArray(baseLen,alts);

  s_varCnts.ensure(baseLen);
  s_boundVarNums.init(baseLen,0);
  s_altPtrs.ensure(baseLen);
  s_remaining.setSide(baseLen);
  s_nextAlts.ensure(baseLen);

  s_intersections.setSide(baseLen);
  s_intersections.zeroAll();

  //number of base literals that have zero alternatives
  //(not counting the resolved literal)
  unsigned zeroAlts=0;
  //number of base literals that have at most one alternative
  //(not counting the resolved literal)
  unsigned singleAlts=0;
  size_t baseLitVars=0;
  size_t altCnt=0;
  size_t altBindingsCnt=0;

  unsigned mostDistVarsLit=0;
  unsigned mostDistVarsCnt=s_baseLits[0]->getDistinctVars();

  s_matchingData.originalBaseIndex.resize(baseLen);
  for (unsigned i = 0; i < baseLen; ++i) {
    s_matchingData.originalBaseIndex[i] = i;
  }

  // Helper function to swap base literals at indices i and j
  auto swapLits = [] (int i, int j) {
    std::swap(s_baseLits[i], s_baseLits[j]);
    std::swap(s_altsArr[i], s_altsArr[j]);
    std::swap(s_matchingData.originalBaseIndex[i], s_matchingData.originalBaseIndex[j]);
  };

  // Reorder base literals to try and reduce backtracking
  // Order:
  // 1. base literals with zero alternatives
  // 2. base literals with one alternative
  // 3. from the remaining base literals the one with the most distinct variables
  // 4. the rest
  for(unsigned i=0;i<baseLen;i++) {
    unsigned distVars = s_baseLits[i]->getDistinctVars();

    baseLitVars+=distVars;
    unsigned currAltCnt=0;
    LiteralList::Iterator ait(s_altsArr[i]);
    while(ait.hasNext()) {
      currAltCnt++;
      if(ait.next()->commutative()) {
        currAltCnt++;
      }
    }
    altCnt += currAltCnt+2; //the +2 is for the resolved literal (it can be commutative)
    altBindingsCnt += (distVars+1)*(currAltCnt+2);

    ASS_LE(zeroAlts, singleAlts);
    ASS_LE(singleAlts, i);
    if(currAltCnt==0) {
      if(zeroAlts!=i) {
        if(singleAlts!=zeroAlts) {
          swapLits(singleAlts, zeroAlts);
        }
        swapLits(i, zeroAlts);
        if(mostDistVarsLit==singleAlts) {
          mostDistVarsLit=i;
        }
      }
      zeroAlts++;
      singleAlts++;
    }
    else if(currAltCnt==1 && !(resolvedLit && resolvedLit->couldBeInstanceOf(s_baseLits[i], true)) ) {
      if(singleAlts!=i) {
        swapLits(i, singleAlts);
        if(mostDistVarsLit==singleAlts) {
          mostDistVarsLit=i;
        }
      }
      singleAlts++;
    }
    else if(i>0 && mostDistVarsCnt<distVars) {
      mostDistVarsLit=i;
      mostDistVarsCnt=distVars;
    }
  }
  if (mostDistVarsLit > singleAlts) {
    swapLits(mostDistVarsLit, singleAlts);
  }

  s_boundVarNumData.ensure(baseLitVars);
  s_altBindingPtrs.ensure(altCnt);
  s_altBindingsData.ensure(altBindingsCnt);
  s_intersectionData.ensure((baseLitVars+baseLen)*baseLen);

  s_matchingData.len=baseLen;
  s_matchingData.varCnts=s_varCnts.array();
  s_matchingData.boundVarNums=s_boundVarNums.array();
  s_matchingData.altBindings=s_altPtrs.array();
  s_matchingData.remaining=&s_remaining;
  s_matchingData.nextAlts=s_nextAlts.array();
  s_matchingData.intersections=&s_intersections;


  s_matchingData.bases=s_baseLits.array();
  s_matchingData.alts=s_altsArr.array();
  s_matchingData.instance=instance;
  s_matchingData.resolvedLit=resolvedLit;

  s_matchingData.boundVarNumStorage=s_boundVarNumData.array();
  s_matchingData.altBindingPtrStorage=s_altBindingPtrs.array();
  s_matchingData.altBindingStorage=s_altBindingsData.array();
  s_matchingData.intersectionStorage=s_intersectionData.array();

  s_matchingData.currentAlts.clear();
  s_matchingData.currentAlts.resize(baseLen);

  return &s_matchingData;
}


bool MLMatcher::canBeMatchedImpl(Literal** baseLits,
                                 unsigned baseLen,
                                 Clause* instance,
                                 LiteralList** alts,
                                 Literal* resolvedLit,
                                 bool multiset,
                                 LiteralVector* outMatchedAlts,
                                 BindingsMap* outBindings)
{
  CALL("MLMatcher::canBeMatched");

  if (resolvedLit) {
    // Untested if using outMatchedAlts/outBindings together with resolvedLit works properly
    ASS(!outMatchedAlts);
    ASS(!outBindings);
    // NOTE(JR): I think using resolvedLit together with multiset does not work since there's only two match records in that case.
    // However, I was not able to find a concrete error, so maybe I've missed something.
    ASS(!multiset);
  }

  /*
  std::cerr << "Entering MLMatcher::canBeMatched with:\n";
  for (unsigned j = 0; j < baseLen; ++j) {
    std::cerr << "\tbase = " << baseLits[j]->toString() << std::endl;

    LiteralList* a = alts[j];
    while (LiteralList::isNonEmpty(a)) {
      std::cerr << "\t alt = " << a->head()->toString() << std::endl;
      a = a->tail();
    }
  }
  std::cerr << "\tinstance = " << instance->toNiceString() << std::endl;
  // */


  MatchingData* md = getMatchingData(baseLits, baseLen, instance, alts, resolvedLit);
  ASS(md);
  unsigned instLen = instance->length();

  static DArray<unsigned> matchRecord(32);
  unsigned matchRecordLen = resolvedLit ? 2 : instLen;
  matchRecord.init(matchRecordLen, 0xFFFFFFFF);
  // What is the matchRecord?
  //   Index is retrieved by getAltRecordIndex:  md->getAltRecordIndex(currBLit, md->nextAlts[currBLit])
  //   The index is the position of the alt literal in 'instance'
  //   Value is compared to currBLit, so it should refer to a base literal
  //
  // So from currBLit we get a record index, and the record is a base literal again???
  //
  // Hypothesis:
  //   The match record tracks for each literal of the instance which base literal is matched to it.
  //   This means it is only necessary for multiset matching (because each instance literal can only be used once for matching).
  //   (Except when resolvedLit is set... then there's only two match records? whatever, I don't care about that case right now)


  unsigned matchedLen=md->len;

  md->nextAlts[0]=0;
  unsigned currBLit=0;

  int counter=0;

  /*
  auto printDebugInfo = [&]() {

    std::cerr << "MLMatcher::canBeMatched: counter = " << counter << std::endl;
    std::cerr << "                         currBLit = " << currBLit << std::endl;

    for (unsigned i = 0; i < md->len; ++i) {
      std::cerr << "\tbases[" << i << "] = " << md->bases[i]->toString() << std::endl;
    }

    for (unsigned i = 0; i < md->len; ++i) {
      std::cerr << "\tnextAlts[" << i << "] = " << md->nextAlts[i] << std::endl;
    }

    for (unsigned i = 0; i < md->len; ++i) {
      std::cerr << "\tcurrentAlts[" << i << "] = " << md->currentAlts[i] << std::endl;
    }

    for (unsigned bi = 0; bi < md->len; ++bi) {
      unsigned alti = 0;
      if (md->altBindings) {
        if (md->altBindings[bi]) {
          if (md->altBindings[bi][alti]) {
            unsigned ri = md->getAltRecordIndex(bi, alti);
            std::cerr << "\tgetAltRecordIndex(" << bi << ", " << alti << ") = " << ri << std::endl;
            if (ri < instance->length()) {
              Literal* lit = (*instance)[ri];
              std::cerr << "\tinstance[" << ri << "] = " << lit->toString() << std::endl;
            }
            if (ri < matchRecordLen) {
              unsigned mr = matchRecord[ri];
              std::cerr << "\tmatchRecord[" << ri << "] = " << mr << std::endl;
            }
          }
        }
      }
    }

    for (unsigned i = 0; i < matchRecordLen; ++i) {
      std::cerr << "\tmatchRecord[" << i << "] = " << matchRecord[i] << std::endl;
    }
  }; // */

binding_start:
  while(true) {
    // printDebugInfo();
    MatchingData::InitResult ires=md->ensureInit(currBLit);
    if(ires!=MatchingData::OK) {
      if(ires==MatchingData::MUST_BACKTRACK) {
        currBLit--;
        continue;
      } else {
        ASS_EQ(ires,MatchingData::NO_ALTERNATIVE);
        return false;
      }
    }

    unsigned maxAlt = md->getRemainingInCurrent(currBLit);
    while (md->nextAlts[currBLit] < maxAlt &&
           (
             // Reject the alternative (in nextAlt) if at least one of the following holds:
             // 1. We are multiset matching and the alt is already matched to a base literal
             ( multiset && matchRecord[md->getAltRecordIndex(currBLit, md->nextAlts[currBLit])] < currBLit )
             // 2. The current variable bindings are not compatible with the alternative
             || !md->bindAlt(currBLit, md->nextAlts[currBLit])
           )
          ) {
      md->nextAlts[currBLit]++;
    }

    if(md->nextAlts[currBLit] < maxAlt) {
      // Got a suitable alternative in nextAlt
      unsigned matchRecordIndex=md->getAltRecordIndex(currBLit, md->nextAlts[currBLit]);
      for(unsigned i=0;i<matchRecordLen;i++) {
        if(matchRecord[i]==currBLit) {
          matchRecord[i]=0xFFFFFFFF;
        }
      }
      if(matchRecord[matchRecordIndex]>currBLit) {
        matchRecord[matchRecordIndex]=currBLit;
      }
      md->nextAlts[currBLit]++;
      currBLit++;
      if(currBLit==matchedLen) { break; }
      md->nextAlts[currBLit]=0;
    } else {
      // No alt left for currBLit, backtrack
      ASS_GE(md->nextAlts[currBLit], maxAlt);
      if(currBLit==0) { return false; }
      currBLit--;
    }

    counter++;
    if(counter==50000) {
      counter=0;
      if(env.timeLimitReached()) {
        throw TimeLimitExceededException();
      }
    }

  } // while (true)

  if(resolvedLit && matchRecord[1]>=matchedLen) {
    currBLit--;
    goto binding_start;
  }

  // printDebugInfo();

  /*
  std::cerr << "\tFOUND MATCHING:\n";

  std::unordered_map<unsigned, TermList, std::hash<unsigned>, std::equal_to<unsigned>, STLAllocator<std::pair<const unsigned, TermList>>> bindings;

  for (unsigned bi = 0; bi < md->len; ++bi) {
    // ASS_EQ(md->nextAlts[bi], 1);  // if this fails, maybe we should use alti = nextAlts[bi] - 1
    ASS_EQ(md->nextAlts[bi], md->currentAlts[bi] + 1);  // NOTE: If this is always true, we can remove currentAlts and use nextAlts-1 instead. (even if it's not true, nextAlts-1 might be the correct choice anyways.)
    // TODO: find an example where nextAlt isn't 1 at the end and check if this is doing the correct thing
    // E.g. this from hamming2:
    // Entering MLMatcher::canBeMatched with:
    //    base = hammingWeight(l17_rEnd(sK3),t1) != hammingWeight(l17_rEnd(s(sK3)),t1)
    //     alt = hammingWeight(l17_rEnd(sK3),t1) != hammingWeight(l17_rEnd(s(sK3)),t1)
    //    base = hammingWeight(l17_rEnd(X0),t1) = hammingWeight(l17_rEnd(X0),t2)
    //     alt = hammingWeight(l17_rEnd(X3),t1) = hammingWeight(l17_rEnd(X3),t2)
    //     alt = hammingWeight(l17_rEnd(X2),t1) = hammingWeight(l17_rEnd(X2),t2)
    //    base = hammingWeight(l17_rEnd(X1),t1) = hammingWeight(l17_rEnd(X1),t2)
    //     alt = hammingWeight(l17_rEnd(X3),t1) = hammingWeight(l17_rEnd(X3),t2)
    //     alt = hammingWeight(l17_rEnd(X2),t1) = hammingWeight(l17_rEnd(X2),t2)
    //    instance = hammingWeight(l17_rEnd(sK3),t1) != hammingWeight(l17_rEnd(s(sK3)),t1) | hammingWeight(l17_rEnd(X2),t1) = hammingWeight(l17_rEnd(X2),t2) | 'Sub'(s(sK3),s(sK0(X2,s(sK3)))) | hammingWeight(l17_rEnd(X3),t1) = hammingWeight(l17_rEnd(X3),t2)
    Literal* b = md->bases[bi];
    std::cerr << "\t\tbase = " << b->toString() << std::endl;
    unsigned alti = md->nextAlts[bi] - 1;
    unsigned i = md->getAltRecordIndex(bi, alti);
    Literal* a = (*instance)[i];
    std::cerr << "\t\t alt = " << a->toString() << std::endl;
    std::cerr << "\t\t vars:\n";
    for (unsigned vi = 0; vi < md->varCnts[bi]; ++vi) {
      TermList t = md->altBindings[bi][alti][vi];
      std::cerr << "\t\t\t " << vi << " -> " << t << std::endl;
      // std::cerr << "\t\t\t " << vi << " -> " << t.content();
      // if (t.content() != 0) {
      //   std::cerr << " / " << t;
      // }
      // std::cerr << std::endl;
    }
  }

  std::cerr << "\tBINDINGS:\n";
  for (auto [v,t] : bindings) {
    std::cerr << "\t\t" << TermList(v, false) << " -> " << t << std::endl;
  }
  // */

  // Return matched literals, if requested.
  // TODO: We don't actually need the right order in ForwardSubsumptionDemodulation. So we could remove the originalBaseIndex.
  if (outMatchedAlts) {
    outMatchedAlts->resize(md->len, nullptr);
    ASS_EQ(md->len, outMatchedAlts->size());
    for (unsigned bi = 0; bi < md->len; ++bi) {
      unsigned obi = md->originalBaseIndex[bi];
      ASS_EQ(md->bases[bi], baseLits[obi]);

      unsigned alti = md->nextAlts[bi] - 1;
      ASS_EQ(alti, md->currentAlts[bi]);

      unsigned ai = md->getAltRecordIndex(bi, alti);
      (*outMatchedAlts)[obi] = (*instance)[ai];
    }
  }

  // Return variable bindings, if requested
  if (outBindings) {
    outBindings->clear();

    for (unsigned bi = 0; bi < md->len; ++bi) {
      ASS_EQ(md->nextAlts[bi], md->currentAlts[bi] + 1);  // NOTE: If this is always true, we can remove currentAlts and use nextAlts-1 instead. (even if it's not true, nextAlts-1 might be the correct choice anyways.)

      Literal* b = md->bases[bi];
      unsigned alti = md->nextAlts[bi] - 1;
      ASS_EQ(alti, md->currentAlts[bi]);

      for (unsigned vi = 0; vi < md->varCnts[bi]; ++vi) {
        // md->altBindings[bi][alti] contains bindings for the variables in b, ordered by the variable index.
        // md->boundVarNums[bi] contains the corresponding variable indices.
        unsigned var = md->boundVarNums[bi][vi];
        TermList trm = md->altBindings[bi][alti][vi];
        auto [ it, inserted ] = outBindings->insert({var, trm});
        if (!inserted) {
          ASS_EQ(it->second, trm);
        }
      }
    }
  }

  return true;
}




static DArray<unsigned> s_matchRecord(32);
static unsigned s_currBLit;
static int s_counter;
static bool s_multiset;

void MLMatcher::initMatcher(Literal** baseLits, unsigned baseLen, Clause* instance, LiteralList** alts, Literal* resolvedLit, bool multiset)
{
  CALL("MLMatcher::initMatcher");

  if (resolvedLit) {
    // NOTE(JR): I think using resolvedLit together with multiset does not work since there's only two match records in that case.
    // However, I was not able to find a concrete error, so maybe I've missed something.
    ASS(!multiset);
  }

  MatchingData* md = getMatchingData(baseLits, baseLen, instance, alts, resolvedLit);
  ASS(md);
  ASS_EQ(md, &s_matchingData);

  unsigned matchRecordLen = resolvedLit ? 2 : instance->length();
  s_matchRecord.init(matchRecordLen, 0xFFFFFFFF);
  // What is the matchRecord?
  //   Index is retrieved by getAltRecordIndex:  md->getAltRecordIndex(currBLit, md->nextAlts[currBLit])
  //   The index is the position of the alt literal in 'instance'
  //   Value is compared to currBLit, so it should refer to a base literal
  //
  // So from currBLit we get a record index, and the record is a base literal again???
  //
  // Hypothesis:
  //   The match record tracks for each literal of the instance which base literal is matched to it.
  //   This means it is only necessary for multiset matching (because each instance literal can only be used once for matching).
  //   (Except when resolvedLit is set... then there's only two match records? whatever, I don't care about that case right now)

  unsigned matchedLen = md->len;

  md->nextAlts[0] = 0;
  s_currBLit = 0;
  s_counter = 0;
  s_multiset = multiset;
}


bool MLMatcher::nextMatch()
{
  MatchingData* const md = &s_matchingData;

  while (true) {
    MatchingData::InitResult ires = md->ensureInit(s_currBLit);
    if (ires != MatchingData::OK) {
      if (ires == MatchingData::MUST_BACKTRACK) {
        s_currBLit--;
        continue;
      } else {
        ASS_EQ(ires, MatchingData::NO_ALTERNATIVE);
        return false;
      }
    }

    unsigned maxAlt = md->getRemainingInCurrent(s_currBLit);
    while (md->nextAlts[s_currBLit] < maxAlt &&
           (
             // Reject the current alternative (nextAlts[currBLit]) if
             // 1. We are multiset matching and the alt is already matched to a base literal, or
             ( s_multiset && s_matchRecord[md->getAltRecordIndex(s_currBLit, md->nextAlts[s_currBLit])] < s_currBLit )
             // 2. The current variable bindings are not compatible with the alternative
             || !md->bindAlt(s_currBLit, md->nextAlts[s_currBLit])
           )
          ) {
      md->nextAlts[s_currBLit]++;
    }

    if (md->nextAlts[s_currBLit] < maxAlt) {
      // Got a suitable alternative in nextAlt
      unsigned matchRecordIndex=md->getAltRecordIndex(s_currBLit, md->nextAlts[s_currBLit]);
      for (unsigned i = 0; i < s_matchRecord.size(); i++) {
        if (s_matchRecord[i] == s_currBLit) {
          s_matchRecord[i]=0xFFFFFFFF;
        }
      }
      if (s_matchRecord[matchRecordIndex]>s_currBLit) {
        s_matchRecord[matchRecordIndex]=s_currBLit;
      }
      md->nextAlts[s_currBLit]++;
      s_currBLit++;
      if(s_currBLit == md->len) { break; }
      md->nextAlts[s_currBLit]=0;
    } else {
      // No alt left for currBLit, backtrack
      ASS_GE(md->nextAlts[s_currBLit], maxAlt);
      if(s_currBLit==0) { return false; }
      s_currBLit--;
    }

    s_counter++;
    if(s_counter==50000) {
      s_counter=0;
      if(env.timeLimitReached()) {
        throw TimeLimitExceededException();
      }
    }

  } // while (true)

  if(md->resolvedLit && s_matchRecord[1] >= md->len) {
    s_currBLit--;
    return nextMatch();
  }

  s_currBLit--;  // prepare for next round
  return true;
}

MLMatcher::v_unordered_set<Literal*> MLMatcher::getMatchedAlts()
{
  MatchingData* md = &s_matchingData;
  ASS(!md->resolvedLit);  // Untested if using this together with resolvedLit works correctly

  v_unordered_set<Literal*> matchedAlts;
  matchedAlts.reserve(md->len);

  for (unsigned bi = 0; bi < md->len; ++bi) {
    unsigned alti = md->nextAlts[bi] - 1;
    unsigned i = md->getAltRecordIndex(bi, alti);
    Literal* matchedAlt = (*md->instance)[i];
    matchedAlts.insert(matchedAlt);
  }

  return matchedAlts;
}

MLMatcher::v_unordered_map<unsigned, TermList> MLMatcher::getBindings()
{
  MatchingData* md = &s_matchingData;
  ASS(!md->resolvedLit);  // Untested if using this together with resolvedLit works correctly

  v_unordered_map<unsigned, TermList> bindings;

  for (unsigned bi = 0; bi < md->len; ++bi) {
    Literal* b = md->bases[bi];
    unsigned alti = md->nextAlts[bi] - 1;
    for (unsigned vi = 0; vi < md->varCnts[bi]; ++vi) {
      // md->altBindings[bi][alti] contains bindings for the variables in b, ordered by the variable index.
      // md->boundVarNums[bi] contains the corresponding variable indices.
      unsigned var = md->boundVarNums[bi][vi];
      TermList trm = md->altBindings[bi][alti][vi];
      auto [ it, inserted ] = bindings.insert({var, trm});
      if (!inserted) {
        ASS_EQ(it->second, trm);
      }
    }
  }

  return bindings;
}


/*
static int activeMatchIteratorCount = 0;
static int activeMatchCount = 0;

MLMatcher::MLMatchIterator::MLMatchIterator(Literal** baseLits, unsigned baseLen, Clause* instance, LiteralList** alts, Literal* resolvedLit, bool multiset)
{
  ASS_EQ(activeMatchIteratorCount, 0);
  ++activeMatchIteratorCount;
}

MLMatcher::MLMatchIterator::~MLMatchIterator()
{
  --activeMatchIteratorCount;
}


MLMatcher::MLMatch::MLMatch(MatchingData* md)
  : md(md)
{
  ASS_EQ(activeMatchCount, 0);
  ++activeMatchCount;
}

MLMatcher::MLMatch::~MLMatch()
{
  --activeMatchCount;
}

MLMatcher::v_unordered_set<Literal*> MLMatcher::MLMatch::getMatchedAlts()
{
  v_unordered_set<Literal*> matchedAlts;
  matchedAlts.reserve(md->len);

  for (unsigned bi = 0; bi < md->len; ++bi) {
    unsigned alti = md->nextAlts[bi] - 1;
    unsigned i = md->getAltRecordIndex(bi, alti);
    Literal* matchedAlt = (*md->instance)[i];
    matchedAlts.insert(matchedAlt);
  }

  return matchedAlts;
}

MLMatcher::v_unordered_map<unsigned, TermList> MLMatcher::MLMatch::getBindings()
{
  v_unordered_map<unsigned, TermList> bindings;

  for (unsigned bi = 0; bi < md->len; ++bi) {
    Literal* b = md->bases[bi];
    unsigned alti = md->nextAlts[bi] - 1;
    for (unsigned vi = 0; vi < md->varCnts[bi]; ++vi) {
      // md->altBindings[bi][alti] contains bindings for the variables in b, ordered by the variable index.
      // md->boundVarNums[bi] contains the corresponding variable indices.
      unsigned var = md->boundVarNums[bi][vi];
      TermList trm = md->altBindings[bi][alti][vi];
      auto [ it, inserted ] = bindings.insert({var, trm});
      if (!inserted) {
        ASS_EQ(it->second, trm);
      }
    }
  }

  return bindings;
}
*/


}
