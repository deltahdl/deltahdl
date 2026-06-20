#pragma once

#include <memory>
#include <string>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"

namespace delta {

// §F.5.6.1 defines neutral satisfaction in the presence of local variables. Its
// opening sentence is the governing rule: the rules defining neutral
// satisfaction are identical to those without local variables (§F.5.3.1, a
// satisfied dependency), but with the understanding that the underlying
// properties may carry local variables. The mechanical difference is that the
// satisfaction relation threads a local variable context L_0 -- the function
// assigning a value to each live local variable name, modelled by §F.5.5's
// LocalContext -- alongside the word. This file carries the unclocked layer,
// where that threading is observable:
//
//   * the property forms gain a local variable declaration ( t v ; P ), absent
//     from §F.5.3.1's no-local-variable property model, whose rule strips the
//     declared name from the context: w, L_0 |= ( t v ; P ) iff w, L_0\v |= P;
//   * the sequence-bearing forms strong(R), weak(R), and ( R |-> P ) decide
//     their sequence operand with §F.5.5's four-way relation w, L_0, L_1 |== R
//     instead of §F.5.2's context-free tight satisfaction, and the implication
//     feeds each output context L_1 produced by the antecedent into the
//     consequent;
//   * the entry point w |= P starts the recursion from the empty context {},
//     mirroring §F.5.6.1's "w |= Q iff w, {} |= Q".
//
// The clocked column (w, L_0 |= Q iff w, L_0 |= T^p(Q, 1) and the clocked
// top-level property U) is the no-local-variable rule of §F.5.3.1 with the
// context threaded inertly: T^p (§F.5.1.2) rewrites a ClockedProperty, whose
// model carries no local variable forms, so it can neither introduce nor
// consume a binding. That column adds no observable local-variable rule beyond
// this layer and is left to §F.5.3.1.

// §F.3.2 production P with local variables: the property forms §F.5.6.1 threads
// a context through. It mirrors §F.5.3.1's PropertyExpr and adds the local
// variable declaration ( t v ; P ).
struct LvProperty {
  enum class Kind {
    kStrong,        // strong ( R )
    kWeak,          // weak ( R )
    kParen,         // ( P )
    kNot,           // not P
    kImplication,   // ( R |-> P )
    kOr,            // ( P1 or P2 )
    kAnd,           // ( P1 and P2 )
    kNexttime,      // ( nexttime P )
    kUntil,         // ( P1 until P2 )
    kAcceptOn,      // ( accept_on ( b ) P )
    kLocalVarDecl,  // ( t v ; P )
  };

  Kind kind = Kind::kStrong;
  std::shared_ptr<const SequenceExpr>
      sequence;                                // R for strong/weak/implication
  std::shared_ptr<const BooleanExpr> boolean;  // b for accept_on
  std::shared_ptr<const LvProperty> lhs;       // sub-property / first operand
  std::shared_ptr<const LvProperty> rhs;       // second operand
  std::string local_var_type;                  // t, for the declaration form
  std::string local_var_name;                  // v, for the declaration form
};

std::shared_ptr<const LvProperty> LvStrong(
    std::shared_ptr<const SequenceExpr> r);
std::shared_ptr<const LvProperty> LvWeak(std::shared_ptr<const SequenceExpr> r);
std::shared_ptr<const LvProperty> LvParen(
    std::shared_ptr<const LvProperty> inner);
std::shared_ptr<const LvProperty> LvNot(
    std::shared_ptr<const LvProperty> inner);
std::shared_ptr<const LvProperty> LvImplication(
    std::shared_ptr<const SequenceExpr> antecedent,
    std::shared_ptr<const LvProperty> consequent);
std::shared_ptr<const LvProperty> LvOr(std::shared_ptr<const LvProperty> a,
                                       std::shared_ptr<const LvProperty> b);
std::shared_ptr<const LvProperty> LvAnd(std::shared_ptr<const LvProperty> a,
                                        std::shared_ptr<const LvProperty> b);
std::shared_ptr<const LvProperty> LvNexttime(
    std::shared_ptr<const LvProperty> inner);
std::shared_ptr<const LvProperty> LvUntil(std::shared_ptr<const LvProperty> a,
                                          std::shared_ptr<const LvProperty> b);
std::shared_ptr<const LvProperty> LvAcceptOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const LvProperty> inner);
std::shared_ptr<const LvProperty> LvLocalVarDecl(
    std::string type, std::string name, std::shared_ptr<const LvProperty> body);

// §F.3.2 production T (unclocked top-level property) with local variables: a
// bare property, a disable iff guard, a parenthesized top-level property, and
// the local variable declaration ( t v ; T ).
struct LvTopLevelProperty {
  enum class Kind {
    kProperty,      // P
    kDisableIff,    // disable iff ( b ) P
    kParen,         // ( T )
    kLocalVarDecl,  // ( t v ; T )
  };

  Kind kind = Kind::kProperty;
  std::shared_ptr<const BooleanExpr> disable_condition;  // b for disable iff
  std::shared_ptr<const LvProperty> property;            // P
  std::shared_ptr<const LvTopLevelProperty> inner;  // T for ( T )/decl body
  std::string local_var_type;                       // t, for declaration
  std::string local_var_name;                       // v, for declaration
};

std::shared_ptr<const LvTopLevelProperty> LvTopProperty(
    std::shared_ptr<const LvProperty> p);
std::shared_ptr<const LvTopLevelProperty> LvTopDisableIff(
    std::shared_ptr<const BooleanExpr> b, std::shared_ptr<const LvProperty> p);
std::shared_ptr<const LvTopLevelProperty> LvTopParen(
    std::shared_ptr<const LvTopLevelProperty> inner);
std::shared_ptr<const LvTopLevelProperty> LvTopLocalVarDecl(
    std::string type, std::string name,
    std::shared_ptr<const LvTopLevelProperty> body);

// §F.5.6.1: neutral satisfaction w, L_0 |= P of a property under an input local
// variable context.
bool NeutrallySatisfiesWithLocals(const Word& word, const LvProperty& property,
                                  const LocalContext& context);

// §F.5.6.1: the entry rule "w |= Q iff w, {} |= Q" -- neutral satisfaction with
// no live local variables starts the recursion from the empty context.
bool NeutrallySatisfiesWithLocals(const Word& word, const LvProperty& property);

// §F.5.6.1: neutral satisfaction w, L_0 |= T of an (unclocked) top-level
// property.
bool NeutrallySatisfiesTopLevelWithLocals(const Word& word,
                                          const LvTopLevelProperty& top,
                                          const LocalContext& context);

// §F.5.6.1: the disabling relation w, L_0 |=^d T. A bare property is never
// disabled; a disable iff guard is disabled when its condition first holds on a
// word for which the guarded property holds under a T^omega completion but not
// under a _|_^omega one; a declaration strips its name and a parenthesis is
// transparent.
bool DisablesTopLevelWithLocals(const Word& word, const LvTopLevelProperty& top,
                                const LocalContext& context);

// §F.5.6.1: "T is said to pass on w, L_0 if w, L_0 |= T", "T is said to be
// disabled on w, L_0 if w, L_0 |=^d T", and "T is said to fail on w, L_0 if T
// neither passes nor is disabled on w, L_0." Pass and disabled are mutually
// exclusive.
bool PassesTopLevelWithLocals(const Word& word, const LvTopLevelProperty& top,
                              const LocalContext& context);
bool IsDisabledTopLevelWithLocals(const Word& word,
                                  const LvTopLevelProperty& top,
                                  const LocalContext& context);
bool FailsTopLevelWithLocals(const Word& word, const LvTopLevelProperty& top,
                             const LocalContext& context);

}  // namespace delta
