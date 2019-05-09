/*
 * TermBuilder.cpp
 * Copyright (C) 2019 Jakob Rath <git@jakobrath.eu>
 *
 * Distributed under terms of the MIT license.
 */


#include "Kernel/Term.hpp"
#include "Lib/Environment.hpp"


// Playing with building terms/literals in C++ with a more intuitive notation
namespace TermBuilder
{

using namespace Kernel;

class TermBuilder
{
  public:
    TermBuilder(Term* t)
      : t{t}
    { }

    TermBuilder(TermList t)
      : t{t}
    { }

    operator TermList() const
    {
      return t;
    }

  private:
    TermList t;
};

class LiteralBuilder
{
  public:
    LiteralBuilder(Literal* lit)
      : lit{lit}
    { }

    operator Literal*() const
    {
      return lit;
    }

  private:
    Literal* lit;
};

TermBuilder var(unsigned i)
{
  return {TermList(i, false)};
}

TermList term(TermBuilder tb)
{
  return tb;
}

TermList term(Term* t)
{
  return TermList(t);
}

TermList term(TermList t)
{
  return t;
}

TermBuilder operator+(TermBuilder const& t1, TermBuilder const& t2)
{
  unsigned const fn = env.signature->getInterpretingSymbol(Theory::INT_PLUS);
  return {Term::create2(fn, t1, t2)};
}

// problematic! (type is too general)
template <typename T1, typename T2>
LiteralBuilder operator<(T1 t1, T2 t2)
{
  unsigned const pred = env.signature->getInterpretingSymbol(Theory::INT_LESS);
  return {Literal::create2(pred, true, term(t1), term(t2))};
}

LiteralBuilder operator!(LiteralBuilder const& l)
{
  return {Literal::complementaryLiteral(l)};
}

template <unsigned Arity>
class FnBuilder
{
  public:
    FnBuilder(unsigned fn)
      : fn{fn}
    { }

    // Args may contain values of types TermBuilder, Term*, and TermList (also mixed)
    template <typename...Args, typename std::enable_if<sizeof...(Args) == Arity>::type* = nullptr>
    TermBuilder operator()(Args... args) const
    {
      std::array<TermList, Arity> const ts{term(args)...};
      return {Term::create(fn, Arity, ts.data())};
    }

    static FnBuilder fresh(char const* prefix, char const* suffix = nullptr)
    {
      unsigned fn = env.signature->addFreshFunction(Arity, prefix, suffix);
      return {fn};
    }

  private:
    unsigned fn;
};

static TermBuilder const x = var(0);
static TermBuilder const y = var(1);
static TermBuilder const z = var(2);

}  // namespace TermBuilder



void testSomeStuff()
{

  {
    using namespace TermBuilder;
    TermList xpx = x + x;
    TermList xpxpy = x + (x + y);

    // auto h = FnBuilder<1>(env.signature->addFreshFunction(1, "h"));
    // auto g = FnBuilder<2>(env.signature->addFreshFunction(2, "g"));
    auto h = FnBuilder<1>::fresh("h");
    auto g = FnBuilder<2>::fresh("g");

    auto hx = h(x);
    auto hhx = h(h(x));
    auto hhx2 = h(hx);

    TermList gx = g(x, x);
    TermList ggh = g(gx, h(hx));

    Literal* blup = hx < ggh;
  }

  /* // old FSD stuff
  unsigned csym = env.signature->addFreshFunction(0, "c");
  unsigned f = env.signature->addFreshFunction(1, "f");
  unsigned g = env.signature->addFreshFunction(2, "g");
  unsigned P = env.signature->addFreshPredicate(1, "P");
  unsigned Q = env.signature->addFreshPredicate(1, "Q");
  unsigned R = env.signature->addFreshPredicate(1, "R");

  TermList x(0, false);
  TermList y(1, false);
  TermList fx(Term::create1(f, x));
  TermList ffx(Term::create1(f, fx));
  TermList fffx(Term::create1(f, ffx));
  TermList gx(Term::create2(g, x, x));
  TermList g2x(Term::create2(g, gx, gx));
  TermList g3x(Term::create2(g, g2x, g2x));
  TermList g4x(Term::create2(g, g3x, g3x));

  TermList c(Term::create(csym, 0, nullptr));
  TermList fc(Term::create1(f, c));
  TermList ffc(Term::create1(f, fc));
  TermList fffc(Term::create1(f, ffc));
  TermList gc(Term::create2(g, c, c));
  TermList g2c(Term::create2(g, gc, gc));
  TermList g3c(Term::create2(g, g2c, g2c));
  TermList g4c(Term::create2(g, g3c, g3c));

  Literal* fffxEQfx = Literal::createEquality(true, fffx, fx, Sorts::SRT_DEFAULT);
  Literal* Pgx = Literal::create1(P, true, gx);
  Literal* Pg2x = Literal::create1(P, true, g2x);
  Literal* Qfffc = Literal::create1(Q, true, fffc);
  Literal* Pgc = Literal::create1(P, true, gc);
  Literal* Pg2c = Literal::create1(P, true, g2c);
  Literal* Pg4c = Literal::create1(P, true, g4c);
  Literal* Ry = Literal::create1(R, true, y);

  Clause* mcl = [&]() {
    LiteralStack lits;
    lits.push(fffxEQfx);
    // This literal needs to be large, otherwise it won't be indexed by the subsumption index.
    // NOTE: Maybe we should make a new index which skips equality literals when selecting the "best" literal
    // (however, we could have the case that one equality is used for demodulation but another equality subsumes part of the given clause)
    lits.push(Pg2x);
    return Clause::fromStack(lits, Unit::AXIOM, new Inference(Inference::THEORY));
  }();

  Clause* cl = [&]() {
    LiteralStack lits;
    lits.push(Qfffc);
    lits.push(Pg2c);
    lits.push(Pg4c);  // (!)
    lits.push(Ry);
    return Clause::fromStack(lits, Unit::AXIOM, new Inference(Inference::THEORY));
  }();

  std::cerr << "Clause mcl:\t" << mcl->toNiceString() << std::endl;
  std::cerr << "Clause cl:\t" << cl->toNiceString() << std::endl;

  // _index->handleClause(mcl, true);


  Clause* replacement = nullptr;
  ClauseIterator premises;
  if (perform(cl, replacement, premises)) {
    std::cerr << "testSomeStuff: success!" << std::endl;
  } else {
    std::cerr << "testSomeStuff: fail!" << std::endl;
  }


  std::cerr << "exiting" << std::endl;
  std::exit(27);
  // */
}

