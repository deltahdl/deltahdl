#pragma once

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "elaborator/annex_f_notation.h"

namespace delta {

// §F.3.2 fixes the abstract grammars used by the rest of Annex F. It lists
// seven productions -- the unclocked sequence R, the clocked sequence S, the
// unclocked property P, the clocked property Q, the unclocked top-level
// property T, the clocked top-level property U, and the assertion A -- and,
// in the property productions, states that the sequence operands shall be
// nondegenerate. This file models the grammar so the rewrite rules (§F.5.1.1)
// and tight satisfaction (§F.5.2) can share a single sequence representation,
// and so the nondegeneracy requirement can be checked against §F.5.2.

// §F.3.2 intro: b denotes a Boolean expression. The sequence-rewrite rule
// §F.5.1.1 forms !c and c & b, so the Boolean model carries negation and
// conjunction in addition to the constant 1 and atomic propositions.
struct BooleanExpr {
  enum class Kind : std::uint8_t {
    kTrue,  // the constant 1
    kAtom,  // a named atomic proposition
    kNot,   // !operand
    kAnd,   // operand_a && operand_b
  };

  Kind kind = Kind::kTrue;
  std::string atom;  // valid when kind == kAtom
  std::shared_ptr<const BooleanExpr> operand_a;
  std::shared_ptr<const BooleanExpr> operand_b;
};

std::shared_ptr<const BooleanExpr> BoolTrue();
std::shared_ptr<const BooleanExpr> BoolAtom(std::string name);
std::shared_ptr<const BooleanExpr> BoolNot(
    std::shared_ptr<const BooleanExpr> a);
std::shared_ptr<const BooleanExpr> BoolAnd(
    std::shared_ptr<const BooleanExpr> a, std::shared_ptr<const BooleanExpr> b);

bool BooleanExprEqual(const BooleanExpr& lhs, const BooleanExpr& rhs);

// §F.3.2 productions R (unclocked sequence) and S (clocked sequence). One node
// type carries both because S differs from R only by the presence of a clock
// form. The kZeroOrMoreRepeat kind is not a §F.3.2 primitive; it is the
// [*0:$] shape produced by the §F.5.1.1 rewrite of a Boolean and is included
// so a rewritten sequence remains representable.
struct SequenceExpr {
  enum class Kind : std::uint8_t {
    kBoolean,           // b
    kLocalVarDecl,      // ( t v [ = e ]; R )
    kLocalVarSampling,  // ( 1, v = e )
    kParen,             // ( R )
    kConcat,            // ( R ##1 R )
    kFusion,            // ( R ##0 R )
    kOr,                // ( R or R )
    kIntersect,         // ( R intersect R )
    kFirstMatch,        // first_match ( R )
    kNullRepeat,        // R [* 0 ]
    kUnboundedRepeat,   // R [* 1:$ ]
    kClock,             // @( b ) R
    kZeroOrMoreRepeat,  // R [* 0:$ ] (rewrite output, not a §F.3.2 primitive)
  };

  Kind kind = Kind::kBoolean;
  std::shared_ptr<const BooleanExpr> boolean;  // kBoolean guard / kClock event
  std::shared_ptr<const SequenceExpr> lhs;     // first operand / child
  std::shared_ptr<const SequenceExpr> rhs;     // second operand
  std::string local_var_type;                  // t, for declaration forms
  std::string local_var_name;                  // v, for var forms
};

// Factories for each §F.3.2 sequence form.
std::shared_ptr<const SequenceExpr> SeqBoolean(
    std::shared_ptr<const BooleanExpr> b);
std::shared_ptr<const SequenceExpr> SeqLocalVarDecl(
    std::string type, std::string name,
    std::shared_ptr<const SequenceExpr> rest);
std::shared_ptr<const SequenceExpr> SeqLocalVarSampling(std::string name);
std::shared_ptr<const SequenceExpr> SeqParen(
    std::shared_ptr<const SequenceExpr> inner);
std::shared_ptr<const SequenceExpr> SeqConcat(
    std::shared_ptr<const SequenceExpr> a,
    std::shared_ptr<const SequenceExpr> b);
std::shared_ptr<const SequenceExpr> SeqFusion(
    std::shared_ptr<const SequenceExpr> a,
    std::shared_ptr<const SequenceExpr> b);
std::shared_ptr<const SequenceExpr> SeqOr(
    std::shared_ptr<const SequenceExpr> a,
    std::shared_ptr<const SequenceExpr> b);
std::shared_ptr<const SequenceExpr> SeqIntersect(
    std::shared_ptr<const SequenceExpr> a,
    std::shared_ptr<const SequenceExpr> b);
std::shared_ptr<const SequenceExpr> SeqFirstMatch(
    std::shared_ptr<const SequenceExpr> inner);
std::shared_ptr<const SequenceExpr> SeqNullRepeat(
    std::shared_ptr<const SequenceExpr> inner);
std::shared_ptr<const SequenceExpr> SeqUnboundedRepeat(
    std::shared_ptr<const SequenceExpr> inner);
std::shared_ptr<const SequenceExpr> SeqZeroOrMoreRepeat(
    std::shared_ptr<const SequenceExpr> inner);
std::shared_ptr<const SequenceExpr> SeqClock(
    std::shared_ptr<const BooleanExpr> event,
    std::shared_ptr<const SequenceExpr> inner);

bool SequenceExprEqual(const SequenceExpr& lhs, const SequenceExpr& rhs);

// §F.3.2: S is distinguished from R by the @( b ) clock form. A sequence is
// clocked iff a clock appears anywhere within it.
bool ContainsClock(const SequenceExpr& seq);

// The seven left-hand sides of the §F.3.2 "::=" rules.
enum class GrammarProduction : std::uint8_t {
  kUnclockedSequence,          // R
  kClockedSequence,            // S
  kUnclockedProperty,          // P
  kClockedProperty,            // Q
  kUnclockedTopLevelProperty,  // T
  kClockedTopLevelProperty,    // U
  kAssertion,                  // A
};

// §F.3.3 assigns each abstract-syntax production a notation letter. This links
// §F.3.2's productions to §F.3.3's metavariable conventions: the category a
// production carries is exactly the one §F.3.3 records for its letter.
NotationCategory CategoryOfProduction(GrammarProduction production);

// One right-hand-side alternative of a §F.3.2 production: the descriptive name
// from the grammar comment and the operand symbols it composes.
struct GrammarForm {
  std::string label;
  std::vector<std::string> operands;
};

// The complete list of alternatives §F.3.2 gives for a production, in source
// order.
std::vector<GrammarForm> ProductionForms(GrammarProduction production);

// §F.3.2: in the strong/weak "sequence" forms of P, "each instance of R ...
// shall be a nondegenerate unclocked sequence" and "R shall not be tightly
// satisfied by the empty word"; the Q production states the same for its
// clocked sequence S. This check enforces both clauses for such an operand by
// deferring to §F.5.2's nondegeneracy and tight-satisfaction definitions.
bool SequenceOperandSatisfiesNondegeneracyRequirement(const SequenceExpr& seq);

}  // namespace delta
