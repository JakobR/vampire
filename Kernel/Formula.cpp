/**
 *  @file Formula.cpp
 *  Implements class Formula.
 */

#include "Debug/Tracer.hpp"

#include "Lib/Exception.hpp"
#include "Lib/MultiCounter.hpp"
#include "Lib/VString.hpp"

#include "BDD.hpp"
#include "Clause.hpp"
#include "Term.hpp"
#include "Formula.hpp"
#include "SubformulaIterator.hpp"
#include "FormulaVarIterator.hpp"

using namespace Lib;

namespace Kernel {

// /**
//  * Turn literal list into a formula representing the disjunction of
//  * these literals.
//  *
//  * @since 10/10/2004 Manchester
//  */
// void Formula::makeFromLiteralList (const LiteralList& from,Formula& to)
// {
//   CALL("Formula::makeFromLiteralList");

//   if (from.isEmpty()) {
//     to = Formula(FALSE);
//     return;
//   }
//   if (from.tail().isEmpty()) {
//     to = Formula(from.head());
//     return;
//   }
//   // at least two literals
//   FormulaList fs;
//   FormulaList::makeFromLiteralList(from,fs);
//   to = Formula(OR,fs);
// } // Formula::makeFromLiteralList

// /**
//  * Construct a list of formulas from a non-empty list of literals
//  * @since 10/10/2004 Manchester
//  */
// void FormulaList::makeFromLiteralList (const LiteralList& ls,FormulaList& fs)
// {
//   CALL("FormulaList::makeFromLiteralList");

//   Lib::ListPusher<Formula> stack(fs);
//   Lib::Iterator<Literal> lits(ls);
//   while (lits.hasNext()) {
//     Formula f(lits.next());
//     stack.push(f);
//   }
// } // FormulaList::FormulaList


/**
 * Destroy the content of the formula. The destruction depends on the type
 * of this formula.
 *
 * @since 11/12/2004 Manchester, true and false added
 * @since 02/06/2007 Manchester, rewritten for new data types
 */
void Formula::destroy ()
{
  CALL ("Formula::Data::destroy");
  ASS (this);

  switch ( connective() ) {
  case LITERAL:
    delete static_cast<AtomicFormula*>(this);
    return;

  case AND:
  case OR:
    delete static_cast<JunctionFormula*>(this);
    return;

  case IMP:
  case IFF:
  case XOR:
    delete static_cast<BinaryFormula*>(this);
    return;

  case NOT:
    delete static_cast<NegatedFormula*>(this);
    return;

  case FORALL:
  case EXISTS:
    delete static_cast<QuantifiedFormula*>(this);
    return;

  case TRUE:
  case FALSE:
    delete this;
    return;

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
    return;
#endif
  }
} // Formula::Data::deref ()


// // the total number of symbols in the formula
// // a bug fixed 30/06/2001, flight Kopenhagen-Manchester
// int Formula::weight () const
// {
//   switch ( connective () ) {
//     case LITERAL:
//       return atom()->weight();

//     case AND:
//     case OR: {
//       int sz = -1;

//       for ( List* fs = args(); fs->isNonEmpty (); fs = fs->tail() )
//         sz += fs->head()->weight() + 1;

//       return sz;
//     }

//     case IMP:
//     case IFF:
//     case XOR:
//       return left()->weight() +
//              right()->weight () + 1;

//     case NOT:
//       return arg()->weight () + 1;

//     case FORALL:
//     case EXISTS:
//       return vars()->length() + arg()->weight () + 1;

//     default:
//       ASSERTION_VIOLATION;
//       return 0;
//   }
// } // Formula::weight

// /**
//  * Convert the formula to an XML element.
//  * @since 29/11/2003 Manchester
//  * @since 11/12/2004 Manchester, true and false added
//  */
// XMLElement Formula::toXML() const
// {
//   XMLElement f("formula");
//   f.addAttribute("connective",_connectiveNames[connective()]);

//   switch ( connective() ) {
//   case LITERAL:
//     f.addChild(literal()->toXML());
//     return f;

//   case AND:
//   case OR:
//     {
//       FormulaList::Iterator fs(args());
//       while (fs.hasNext()) {
// 	f.addChild(fs.next()->toXML());
//       }
//     }
//     return f;

//   case IMP:
//   case IFF:
//   case XOR:
//     f.addChild(left()->toXML());
//     f.addChild(right()->toXML());
//     return f;

//   case NOT:
//     f.addChild(uarg()->toXML());
//     return f;

//   case FORALL:
//   case EXISTS:
//     {
//       XMLElement vs("variables");
//       VarList::Iterator variables(vars());
//       while (variables.hasNext()) {
// 	vs.addChild(Term::variableToXML(variables.next()));
//       }
//       f.addChild(vs);
//       f.addChild(qarg()->toXML());
//     }
//     return f;

//   case TRUE:
//   case FALSE:
//     return f;

// #if VDEBUG
//   default:
//     ASSERTION_VIOLATION;
// #endif
//   }
// } // Formula::toXML()

/**
 * Convert the connective to a vstring.
 * @since 02/01/2004 Manchester
 */
vstring Formula::toString (Connective c)
{
  static vstring names [] =
    { "", "&", "|", "=>", "<=>", "<~>", "~", "!", "?", "$false", "$true"};
  ASS_EQ(sizeof(names)/sizeof(vstring), TRUE+1);

  return names[(int)c];
} // Formula::toString (Connective c)



/**
 * Convert the formula to a vstring using the native syntax
 *
 * @since 12/10/2002 Tbilisi, implemented as ostream output function
 * @since 09/12/2003 Manchester
 * @since 11/12/2004 Manchester, true and false added
 */
vstring Formula::toString () const
{
  CALL("Formula::toString");

  Connective c = connective();
  vstring con = toString(c);

  switch (c) {
  case LITERAL:
    return literal()->toString();

  case AND:
  case OR:
    {
      ASS (args()->length() >= 2);
      vstring result = args()->head()->toStringInScopeOf(c);
      FormulaList::Iterator arg(args()->tail());
      while (arg.hasNext()) {
	result += ' ' + con + ' ' + arg.next()->toStringInScopeOf(c);
      }
      return result;
    }

  case IMP:
  case IFF:
  case XOR:
    return left()->toStringInScopeOf(c) + ' ' + con + ' ' +
           right()->toStringInScopeOf(c);

  case NOT:
    {
      const Formula* arg = uarg();
      if (arg->connective() == LITERAL) {
	return con + arg->literal()->toString();
      }
      return con + arg->toStringInScopeOf(c);
    }

  case FORALL:
  case EXISTS:
    {
//      vstring result = "(" + con;
//      VarList::Iterator vs(vars());
//      while (vs.hasNext()) {
//	result += vstring(" ") + Term::variableToString(vs.next());
//      }
//      result += ")";
      vstring result = con + " [";
      VarList::Iterator vs(vars());
      bool first=true;
      while (vs.hasNext()) {
	if(!first) {
	  result+= ",";
	}
	result += Term::variableToString(vs.next());
	first=false;
      }
      result += "] : ";
      return result + qarg()->toStringInScopeOf(c);
    }

  case TRUE:
  case FALSE:
    return con;

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
} // Formula::toString

/**
 * True if the formula needs parentheses around itself
 * when in scope of outer.
 *
 * @since 21/09/2002 Manchester
 * @since 11/12/2004 Manchester, true and false added
 */
bool Formula::parenthesesRequired (Connective outer) const
{
  CALL("Formula::parenthesesRequired");

  switch (connective())
    {
    case LITERAL:
    case NOT:
    case FORALL:
    case EXISTS:
    case TRUE:
    case FALSE:
      return false;

    case OR:
    case AND:
    case IMP:
    case IFF:
    case XOR:
      return true;

#if VDEBUG
    default:
      ASSERTION_VIOLATION;
      return false;
#endif
    }
} // Formula::parenthesesRequired


/**
 * Convert the formula in scope of another formula
 * to a vstring using the native syntax.
 * @param outer connective of the outer formula
 * @since 09/12/2003 Manchester
 */
vstring Formula::toStringInScopeOf (Connective outer) const
{
  return parenthesesRequired(outer) ?
         vstring("(") + toString() + ")" :
         toString();
} // Formula::toStringInScopeOf


// /**
//  * True if this formula is equal to f.
//  *
//  * @since 23/12/2003 Manchester
//  * @since 11/12/2004 Manchester, true and false added
//  */
// bool Formula::equals (const Formula& f) const
// {
//   if (*this == f) {
//     return true;
//   }
//   if (connective() != f.connective()) {
//     return false;
//   }

//   switch (connective())
//     {
//     case LITERAL:
//       return literal()->equals(f.literal());

//     case AND:
//     case OR:
//       return args().equals(f.args());

//     case IMP:
//     case IFF:
//     case XOR:
//       return left().equals(f.left()) &&
//              right().equals(f.right());

//     case NOT:
//       return uarg().equals(f.uarg());

//     case FORALL:
//     case EXISTS:
//       {
// 	// first check that the variables are equal
// 	Iterator<int> vs(vars());
// 	Iterator<int> ws(f.vars());
// 	while (vs.hasNext()) {
// 	  if (! ws.hasNext()) {
// 	    return false;
// 	  }
// 	  if (vs.next() != ws.next()) {
// 	    return false;
// 	  }
// 	}
// 	if (ws.hasNext()) {
// 	  return false;
// 	}
//       }
//       // and then compare immediate subformulas
//       return qarg().equals(f.qarg());

//     case TRUE:
//     case FALSE:
//       return true;

// #if VDEBUG
//     default:
//       ASSERTION_VIOLATION;
// #endif
//     }
// }

// /**
//  * True if this list is equal to fs.
//  * @since 23/12/2003 Manchester
//  */
// bool FormulaList::equals (const FormulaList& fs) const
// {
//   if (isEmpty()) {
//     return fs.isEmpty();
//   }
//   return fs.isNonEmpty() &&
//          head().equals(fs.head()) &&
//          tail().equals(fs.tail());
// } // FormulaList::equals

/**
 * Return the list of all free variables of the formula
 *
 * Each variable in the formula is returned just once.
 *
 * @since 12/12/2004 Manchester
 */
Formula::VarList* Formula::freeVariables () const
{
  CALL("Formula::freeVariables");

  FormulaVarIterator fvi(this);
  VarList* result = VarList::empty();
  VarList::FIFO stack(result);
  while (fvi.hasNext()) {
    stack.push(fvi.next());
  }
  return result;
} // Formula::freeVariables

/**
 * Return the list of all bound variables of the formula
 *
 * If a variable is bound multiple times in the formula,
 * it appears in the list the same number of times as well.
 */
Formula::VarList* Formula::boundVariables () const
{
  CALL("Formula::boundVariables");

  VarList* res=0;
  SubformulaIterator sfit(const_cast<Formula*>(this));
  while(sfit.hasNext()) {
    Formula* sf=sfit.next();
    if(sf->connective()==FORALL || sf->connective()==EXISTS) {
      VarList* qvars=sf->vars();
      VarList* qvCopy=qvars->copy();
      res=VarList::concat(qvCopy, res);
    }
  }
  return res;
}

/**
 * Add into @c acc numbers of all atoms in the formula.
 *
 * As we are collecting atoms, for negative literals we insert their
 * complements.
 */
void Formula::collectAtoms(Stack<Literal*>& acc)
{
  CALL("Formula::collectPredicates");

  SubformulaIterator sfit(this);
  while(sfit.hasNext()) {
    Formula* sf = sfit.next();
    if(sf->connective()==LITERAL) {
      Literal* l = sf->literal();
      acc.push(Literal::positiveLiteral(l));
    }
  }
}

/**
 * Add into @c acc numbers of all predicates in the formula.
 */
void Formula::collectPredicates(Stack<unsigned>& acc)
{
  CALL("Formula::collectPredicates");

  SubformulaIterator sfit(this);
  while(sfit.hasNext()) {
    Formula* sf = sfit.next();
    if(sf->connective()==LITERAL) {
      acc.push(sf->literal()->functor());
    }
  }
}

void Formula::collectPredicatesWithPolarity(Stack<pair<unsigned,int> >& acc, int polarity)
{
  CALL("Formula::collectPredicatesWithPolarity");

  switch (connective()) {
    case LITERAL:
    {
      Literal* l=literal();
      int pred = l->functor();
      acc.push(make_pair(pred, l->isPositive() ? polarity : -polarity));
      return;
    }

    case AND:
    case OR: {
      FormulaList::Iterator fs(args());
      while (fs.hasNext()) {
	fs.next()->collectPredicatesWithPolarity(acc,polarity);
      }
      return;
    }

    case IMP:
      left()->collectPredicatesWithPolarity(acc,-polarity);
      right()->collectPredicatesWithPolarity(acc,polarity);
      return;

    case NOT:
      uarg()->collectPredicatesWithPolarity(acc,-polarity);
      return;

    case IFF:
    case XOR:
      left()->collectPredicatesWithPolarity(acc,0);
      right()->collectPredicatesWithPolarity(acc,0);
      return;

    case FORALL:
    case EXISTS:
      qarg()->collectPredicatesWithPolarity(acc,polarity);
      return;

    case TRUE:
    case FALSE:
      return;

#if VDEBUG
    default:
      ASSERTION_VIOLATION;
      return;
#endif
  }
}


/**
 * Compute the weight of the formula: the number of connectives plus the
 * weight of all atoms.
 * @since 23/03/2008 Torrevieja
 */
unsigned Formula::weight() const
{
  CALL("Formula::weight");

  unsigned result=0;

  SubformulaIterator fs(const_cast<Formula*>(this));
  while (fs.hasNext()) {
    const Formula* f = fs.next();
    switch (f->connective()) {
    case LITERAL:
      result += f->literal()->weight();
      break;
    default:
      result++;
      break;
    }
  }
  return result;
} // Formula::weight

Formula* JunctionFormula::generalJunction(Connective c, FormulaList* args)
{
  if(!args) {
    if(c==AND) {
      return new Formula(true);
    }
    else {
      ASS_EQ(c,OR);
      return new Formula(false);
    }
  }
  if(!args->tail()) {
    return FormulaList::pop(args);
  }
  return new JunctionFormula(c, args);
}

/**
 * Return color of the formula
 *
 * We do not store the color of the formula, so it gets
 * computed again each time the function is called.
 */
Color Formula::getColor()
{
  CALL("Formula::getColor");

  SubformulaIterator si(this);
  while(si.hasNext()) {
    Formula* f=si.next();
    if(f->connective()!=LITERAL) {
      continue;
    }

    if(f->literal()->color()!=COLOR_TRANSPARENT) {
      return f->literal()->color();
    }
  }
  return COLOR_TRANSPARENT;
}

/**
 * Return true iff the formula is Skip for the purpose of
 * symbol elimination
 */
bool Formula::getSkip()
{
  CALL("Formula::getColor");

  SubformulaIterator si(this);
  while(si.hasNext()) {
    Formula* f=si.next();
    if(f->connective()!=LITERAL) {
      continue;
    }

    if(!f->literal()->skip()) {
      return false;
    }
  }
  return true;
}

Formula* Formula::trueFormula()
{
  CALL("Formula::trueFormula");

  static Formula* res = new Formula(true);
  return res;
}

Formula* Formula::falseFormula()
{
  CALL("Formula::falseFormula");

  static Formula* res = new Formula(false);
  return res;
}

Formula* Formula::fromTerm(TermList ts)
{
  CALL("Formula::fromTerm(TermList*)");
  TermList tru;
  tru.setTerm(Term::createFormula(new Formula(true)));
  Literal *l = Literal::createEquality(true, ts, tru, Sorts::SRT_BOOL);
  return new AtomicFormula(l);
}

/**
 * Creates a formula of the form $ite(c, a, b), where a, b, c are formulas
 * @since 16/04/2015 Gothenburg
 */
Formula* Formula::createITE(Formula* condition, Formula* thenArg, Formula* elseArg)
{
  CALL("Formula::createITE");
  TermList thenTerm(Term::createFormula(thenArg));
  TermList elseTerm(Term::createFormula(elseArg));
  TermList iteTerm(Term::createITE(condition, thenTerm, elseTerm));
  return Formula::fromTerm(iteTerm);
}

/**
 * Creates a formula of the form $let(lhs := rhs, body), where body is a formula
 * and lhs and rhs form a binding for a function
 * @since 16/04/2015 Gothenburg
 */
Formula* Formula::createTermLet(TermList lhs, TermList rhs, Formula* body)
{
  CALL("Formula::createTermLet");
  TermList bodyTerm(Term::createFormula(body));
  TermList letTerm(Term::createLet(lhs, rhs, bodyTerm));
  return Formula::fromTerm(letTerm);
}

/**
 * Creates a formula of the form $let(lhs := rhs, body), where body is a formula
 * and lhs and rhs form a binding for a predicate
 * @since 16/04/2015 Gothenburg
 */
Formula* Formula::createFormulaLet(Literal* lhs, Formula* rhs, Formula* body)
{
  CALL("Formula::createFormulaLet");
  TermList bodyTerm(Term::createFormula(body));
  TermList function(lhs);
  TermList functionBody(Term::createFormula(rhs));
  TermList letTerm(Term::createLet(function, functionBody, bodyTerm));
  return Formula::fromTerm(letTerm);
}

Formula* Formula::quantify(Formula* f)
{
  Set<unsigned> vars;
  FormulaVarIterator fvit( f );
  while(fvit.hasNext()) {
    vars.insert(fvit.next());
  }

  //we have to quantify the formula
  VarList* varLst=0;
  Set<unsigned>::Iterator vit(vars);
  while(vit.hasNext()) {
    VarList::push(vit.next(), varLst);
  }
  if(varLst) {
    f=new QuantifiedFormula(FORALL, varLst, f);
  }
  return f;
}


/**
 * Return formula equal to @b cl 
 * that has all variables quantified
 */
Formula* Formula::fromClause(Clause* cl)
{
  CALL("Formula::fromClause");
  
  FormulaList* resLst=0;
  unsigned clen=cl->length();
  for(unsigned i=0;i<clen;i++) {
    Formula* lf=new AtomicFormula((*cl)[i]);
    FormulaList::push(lf, resLst);
  }

  Formula* res=JunctionFormula::generalJunction(OR, resLst);
  
  Set<unsigned> vars;
  FormulaVarIterator fvit( res );
  while(fvit.hasNext()) {
    vars.insert(fvit.next());
  }

  //we have to quantify the formula
  VarList* varLst=0;
  Set<unsigned>::Iterator vit(vars);
  while(vit.hasNext()) {
    VarList::push(vit.next(), varLst);
  }
  if(varLst) {
    res=new QuantifiedFormula(FORALL, varLst, res);
  }

  return res;
}

/*
  THIS IS USEFUL
  switch (connective()) {
  case LITERAL:
  case AND:
  case OR:
  case IMP:
  case IFF:
  case XOR:
  case NOT:
  case FORALL:
  case EXISTS:
  case TRUE:
  case FALSE:
#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
*/

std::ostream& operator<< (ostream& out, const Formula& f)
{
  CALL("operator <<(ostream&, const Formula&)");
  return out << f.toString();
}

std::ostream& operator<< (ostream& out, const Formula* f)
{
  CALL("operator <<(ostream&, const Formula&)");
  return out << f->toString();
}

}
