#include "elaborator/sequence_match_class.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/sequence_degeneracy.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

constexpr uint64_t kInfinite = UINT64_MAX;
constexpr int kMaxInstanceDepth = 16;

// The lengths, in ticks, the matches of a sequence can have, from `lo` to
// `hi`, kInfinite where unbounded; `none` where it admits no match.
struct LengthRange {
  uint64_t lo = 0;
  uint64_t hi = 0;
  bool none = false;
};

LengthRange NoMatch() { return {0, 0, true}; }

uint64_t Add(uint64_t a, uint64_t b) {
  return a == kInfinite || b == kInfinite ? kInfinite : a + b;
}

uint64_t Less1(uint64_t a) { return a == kInfinite ? kInfinite : a - 1; }

uint64_t Multiply(uint64_t a, uint64_t b) {
  if (a == 0 || b == 0) return 0;
  return a == kInfinite || b == kInfinite ? kInfinite : a * b;
}

LengthRange RangeOfBody(const SeqLinearBody& body,
                        const PropertyRegistry& registry, int depth);

// §16.9.2: the lengths an operand's repetition gives it, each repetition of
// a boolean one tick: `[*min:max]` from min to max ticks, a goto or
// nonconsecutive repetition at least min ticks with no bound above, and an
// operand with none one tick.
LengthRange RangeOfRepetition(const SeqRepetition& rep, LengthRange one) {
  if (rep.kind == SeqRepetition::Kind::kNone) return one;
  uint64_t max = rep.max == SeqCycleDelay::kUnbounded ? kInfinite : rep.max;
  if (rep.kind != SeqRepetition::Kind::kConsecutive) max = kInfinite;
  if (one.none) return rep.min == 0 ? LengthRange{0, 0, false} : NoMatch();
  return {Multiply(rep.min, one.lo), Multiply(max, one.hi), false};
}

// One operand: an instance of a named sequence is the declaration's body,
// any other operand a boolean, one tick.
LengthRange RangeOfOperand(const Expr* operand,
                           const PropertyRegistry& registry, int depth) {
  LengthRange one{1, 1, false};
  if (operand == nullptr || depth >= kMaxInstanceDepth) return one;
  if (operand->kind != ExprKind::kIdentifier &&
      operand->kind != ExprKind::kCall) {
    return one;
  }
  std::string_view name =
      operand->kind == ExprKind::kCall ? operand->callee : operand->text;
  const ModuleItem* decl = registry.Find(name);
  if (decl == nullptr || decl->kind != ModuleItemKind::kSequenceDecl ||
      decl->seq_linear.operands.empty()) {
    return one;
  }
  return RangeOfBody(decl->seq_linear, registry, depth + 1);
}

// §16.7 and §16.9.2.1: the operand appended to the chain `total` after the
// delay `delay`: `##0` fuses the two, which an operand admitting only the
// empty match cannot join, and an operand admitting the empty match joins
// only by its nonempty matches; `##n` for n at least 1 adds n - 1 ticks
// between them.
LengthRange Append(LengthRange total, const SeqCycleDelay& delay,
                   LengthRange operand) {
  if (total.none || operand.none) return NoMatch();
  if (delay.min == 0 && delay.max == 0) {
    if (total.hi == 0 || operand.hi == 0) return NoMatch();
    return {
        std::max<uint64_t>(total.lo, 1) + std::max<uint64_t>(operand.lo, 1) - 1,
        Less1(Add(total.hi, operand.hi)), false};
  }
  uint64_t gap_lo = delay.min == 0 ? 0 : delay.min - 1;
  uint64_t gap_hi =
      delay.max == SeqCycleDelay::kUnbounded ? kInfinite : delay.max;
  if (gap_hi != kInfinite && gap_hi > 0) --gap_hi;
  return {Add(Add(total.lo, gap_lo), operand.lo),
          Add(Add(total.hi, gap_hi), operand.hi), false};
}

// The chain of one body: its operands under their delays, a leading delay
// standing for a true boolean before it.
LengthRange RangeOfChain(const SeqLinearBody& body,
                         const PropertyRegistry& registry, int depth) {
  LengthRange total{0, 0, false};
  bool leading = body.delays[0].min > 0 || body.delays[0].max > 0;
  if (leading) total = {1, 1, false};
  for (size_t i = 0; i < body.operands.size(); ++i) {
    LengthRange operand = RangeOfRepetition(
        body.repetitions[i], RangeOfOperand(body.operands[i], registry, depth));
    if (i == 0 && !leading) {
      total = operand;
    } else {
      total = Append(total, body.delays[i], operand);
    }
  }
  return total;
}

// §16.9.6: the operands of an intersect match over the same ticks, so the
// lengths are those they have in common; §16.9.5: an and ends at the later
// end point, so the lengths are the longer's.
LengthRange Intersect(LengthRange a, LengthRange b) {
  if (a.none || b.none) return NoMatch();
  LengthRange out{std::max(a.lo, b.lo), std::min(a.hi, b.hi), false};
  if (out.lo > out.hi) return NoMatch();
  return out;
}

LengthRange Conjoin(LengthRange a, LengthRange b) {
  if (a.none || b.none) return NoMatch();
  return {std::max(a.lo, b.lo), std::max(a.hi, b.hi), false};
}

// §16.9.7: an or matches where either operand does.
LengthRange Alternate(LengthRange a, LengthRange b) {
  if (a.none) return b;
  if (b.none) return a;
  return {std::min(a.lo, b.lo), std::max(a.hi, b.hi), false};
}

LengthRange RangeOfConjunction(const SeqLinearBody& body,
                               const PropertyRegistry& registry, int depth) {
  LengthRange range = RangeOfChain(body, registry, depth);
  for (const SeqLinearBody& other : body.intersects) {
    range = Intersect(range, RangeOfChain(other, registry, depth));
  }
  for (const SeqLinearBody& conjunct : body.conjuncts) {
    LengthRange other = RangeOfChain(conjunct, registry, depth);
    for (const SeqLinearBody& inner : conjunct.intersects) {
      other = Intersect(other, RangeOfChain(inner, registry, depth));
    }
    range = Conjoin(range, other);
  }
  return range;
}

LengthRange RangeOfBody(const SeqLinearBody& body,
                        const PropertyRegistry& registry, int depth) {
  if (body.operands.empty()) return NoMatch();
  LengthRange range = RangeOfConjunction(body, registry, depth);
  for (const SeqLinearBody& alt : body.alternatives) {
    range = Alternate(range, RangeOfConjunction(alt, registry, depth));
  }
  return range;
}

SequenceMatchClass ClassOfRange(LengthRange range) {
  if (range.none) return SequenceMatchClass::kAdmitsNoMatch;
  if (range.hi == 0) return SequenceMatchClass::kAdmitsOnlyEmpty;
  if (range.lo == 0) return SequenceMatchClass::kAdmitsBothEmptyAndNonempty;
  return SequenceMatchClass::kAdmitsAtLeastOneNonempty;
}

// What the class breaches in the context, as the report says it.
std::string_view Where(SequenceUsageContext ctx) {
  switch (ctx) {
    case SequenceUsageContext::kAsProperty:
      return "a sequence used as a property";
    case SequenceUsageContext::kOverlappingImplicationAntecedent:
      return "the antecedent of |->";
    case SequenceUsageContext::kNonoverlappingImplicationAntecedent:
      return "the antecedent of |=>";
  }
  return "";
}

std::string_view Rule(SequenceUsageContext ctx) {
  switch (ctx) {
    case SequenceUsageContext::kAsProperty:
      return "shall be nondegenerate and admit no empty match";
    case SequenceUsageContext::kOverlappingImplicationAntecedent:
      return "shall be nondegenerate";
    case SequenceUsageContext::kNonoverlappingImplicationAntecedent:
      return "shall admit at least one match";
  }
  return "";
}

std::string_view Admits(SequenceMatchClass m) {
  switch (m) {
    case SequenceMatchClass::kAdmitsNoMatch:
      return "admits no match";
    case SequenceMatchClass::kAdmitsOnlyEmpty:
      return "admits only empty matches";
    case SequenceMatchClass::kAdmitsBothEmptyAndNonempty:
      return "admits an empty match";
    case SequenceMatchClass::kAdmitsAtLeastOneNonempty:
      return "admits a nonempty match";
  }
  return "";
}

std::string Breach(SequenceUsageContext ctx, SequenceMatchClass m) {
  return std::string(Where(ctx)) + " " + std::string(Admits(m)) + "; it " +
         std::string(Rule(ctx));
}

void CheckUsage(const ModuleItem* seq, SequenceUsageContext ctx, SourceLoc loc,
                const PropertyRegistry& registry, DiagEngine& diag) {
  if (seq == nullptr) return;
  SequenceMatchClass m = ClassifySequenceMatches(seq, registry);
  if (IsSequenceUsageLegal(ctx, m)) return;
  diag.Error(loc, Breach(ctx, m), Subclause("16.12.22"));
}

}  // namespace

SequenceMatchClass ClassifySequenceMatches(const ModuleItem* seq,
                                           const PropertyRegistry& registry) {
  if (seq == nullptr) return SequenceMatchClass::kAdmitsAtLeastOneNonempty;
  return ClassifyBodyMatches(seq->seq_linear, registry);
}

SequenceMatchClass ClassifyBodyMatches(const SeqLinearBody& body,
                                       const PropertyRegistry& registry) {
  return ClassOfRange(RangeOfBody(body, registry, 0));
}

void ValidateSequenceUsedAsProperty(const ModuleItem* seq, SourceLoc loc,
                                    const PropertyRegistry& registry,
                                    DiagEngine& diag) {
  CheckUsage(seq, SequenceUsageContext::kAsProperty, loc, registry, diag);
}

void ValidateSequenceDegeneracy(const PropertyExprNode* node, SourceLoc loc,
                                const PropertyRegistry& registry,
                                DiagEngine& diag) {
  if (node == nullptr) return;
  if (node->kind == PropertyExprNode::Kind::kSequence) {
    CheckUsage(node->sequence, SequenceUsageContext::kAsProperty, loc, registry,
               diag);
  } else if (node->kind == PropertyExprNode::Kind::kImplication) {
    CheckUsage(node->sequence,
               node->strong
                   ? SequenceUsageContext::kNonoverlappingImplicationAntecedent
                   : SequenceUsageContext::kOverlappingImplicationAntecedent,
               loc, registry, diag);
  }
  for (const PropertyExprNode* operand : node->operands) {
    ValidateSequenceDegeneracy(operand, loc, registry, diag);
  }
}

}  // namespace delta
