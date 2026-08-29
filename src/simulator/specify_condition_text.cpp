// Renders a §30.4.4 module path condition as the text §32.4.1's SDF COND
// matching compares against. SpecifyManager::AnnotateSdfPathDelay in
// simulator/specify_register.cpp matches an SDF record to a declared path by
// its port names and by this string, so the only job here is to write a
// condition in the same spelling an SDF file writes one in. Nothing evaluates
// what is rendered: §30.5.3's activity test reads PathDelay::condition_expr
// instead, which BuildPathDelayFromDecl in simulator/specify.cpp sets from the
// same declaration.
//
// SpecifyConditionOperator gives the spelling of each operator Table 30-1
// admits, and SpecifyConditionText walks the expression; the helpers between
// them render the select, concatenation and conditional forms §30.4.4.1 names.

#include <cstddef>
#include <string>
#include <string_view>

#include "parser/ast.h"
#include "simulator/specify_internal.h"

namespace delta {

namespace {

// The spelling of an operator a state-dependent path condition may be built
// from (§30.4.4.1). An operator with no spelling here is one the condition text
// below cannot render.
std::string_view SpecifyConditionOperator(TokenKind op) {
  switch (op) {
    case TokenKind::kBang:
      return "!";
    case TokenKind::kTilde:
      return "~";
    case TokenKind::kAmpAmp:
      return "&&";
    case TokenKind::kPipePipe:
      return "||";
    case TokenKind::kEqEq:
      return "==";
    case TokenKind::kBangEq:
      return "!=";
    case TokenKind::kEqEqEq:
      return "===";
    case TokenKind::kBangEqEq:
      return "!==";
    case TokenKind::kAmp:
      return "&";
    case TokenKind::kPipe:
      return "|";
    case TokenKind::kCaret:
      return "^";
    default:
      return {};
  }
}

// The bracketed address of a bit-select or part-select, written the way an SDF
// file writes one. An SDF COND names a fixed bit, so only an address the source
// wrote as a literal is rendered: `mode[i]` and `mode[WIDTH-1]` yield nothing
// on purpose, because their addresses are not known here and no SDF file could
// name them. Elaboration is what would fold the second of those, and
// simulator/specify.cpp runs after it on an unfolded expression.
std::string SpecifyConditionIndexText(const Expr* index) {
  if (index == nullptr) return {};
  if (index->kind != ExprKind::kIntegerLiteral) return {};
  return std::to_string(index->int_val);
}

// §30.4.4.1 admits a bit-select or a part-select of a port or of a locally
// defined variable or net, so `mode[1]` renders as `mode[1]` and `mode[3:2]` as
// `mode[3:2]`. The indexed part-selects `[i +: n]` and `[i -: n]` are left
// unrendered: SDF has no such spelling, so a condition using one yields
// nothing rather than a form no COND entry could carry.
std::string SpecifyConditionSelectText(const Expr* sel) {
  if (sel->is_part_select_plus || sel->is_part_select_minus) return {};
  std::string base = SpecifyConditionText(sel->base);
  std::string index = SpecifyConditionIndexText(sel->index);
  if (base.empty() || index.empty()) return {};
  if (sel->index_end == nullptr) return base + "[" + index + "]";
  std::string index_end = SpecifyConditionIndexText(sel->index_end);
  if (index_end.empty()) return {};
  return base + "[" + index + ":" + index_end + "]";
}

// Table 30-1 lists the concatenation operator, so `{a, b}` renders as `{a, b}`.
// An empty concatenation and one whose operands cannot all be rendered both
// yield nothing.
std::string SpecifyConditionConcatText(const Expr* cat) {
  if (cat->elements.empty()) return {};
  std::string out = "{";
  for (std::size_t i = 0; i < cat->elements.size(); ++i) {
    std::string element = SpecifyConditionText(cat->elements[i]);
    if (element.empty()) return {};
    if (i != 0) out += ", ";
    out += element;
  }
  return out + "}";
}

// Table 30-1 lists the replication operator, so `{2{a}}` renders as `{2{a}}`.
// The replication count is a constant expression (§11.4.12.1) and is rendered
// by the same rule the select addresses follow: only a literal count is
// written, because nothing here folds an expression to a number.
std::string SpecifyConditionReplicateText(const Expr* rep) {
  std::string count = SpecifyConditionIndexText(rep->repeat_count);
  std::string body = SpecifyConditionConcatText(rep);
  if (count.empty() || body.empty()) return {};
  return "{" + count + body + "}";
}

// Table 30-1 lists the conditional operator, so `c ? a : b` renders with the
// same spacing the binary operators use, which is the spacing
// JoinSdfCondTokens in simulator/sdf_parser.cpp gives the SDF side.
std::string SpecifyConditionTernaryText(const Expr* cond) {
  std::string test = SpecifyConditionText(cond->condition);
  std::string on_true = SpecifyConditionText(cond->true_expr);
  std::string on_false = SpecifyConditionText(cond->false_expr);
  if (test.empty() || on_true.empty() || on_false.empty()) return {};
  return test + " ? " + on_true + " : " + on_false;
}

}  // namespace

// §32.4.1: render a module path's condition as the text an SDF COND condition
// is compared against. Backannotation matches a conditional delay to a specify
// path by names *and* condition, so the condition a state-dependent path was
// declared with has to travel with the path in a comparable form.
//
// The forms of §30.4.4.1 that still yield no text are an operator outside
// Table 30-1, a select whose address is not a literal, an indexed part-select,
// and every other expression kind. A condition that yields no text is
// indistinguishable here from an unconditional path, both being the empty
// string, so an SDF record with no COND matches such a path. The declaration
// side does not share that ambiguity: PathDelay::condition_expr holds the
// expression itself, and SpecifyManager::AddPathDelay in
// simulator/specify_register.cpp reads it.
std::string SpecifyConditionText(const Expr* cond) {
  if (cond == nullptr) return {};
  switch (cond->kind) {
    case ExprKind::kIdentifier:
      return std::string(cond->text);
    case ExprKind::kIntegerLiteral:
      return std::to_string(cond->int_val);
    case ExprKind::kUnary: {
      std::string_view op = SpecifyConditionOperator(cond->op);
      std::string operand = SpecifyConditionText(cond->lhs);
      if (op.empty() || operand.empty()) return {};
      return std::string(op) + operand;
    }
    case ExprKind::kBinary: {
      std::string_view op = SpecifyConditionOperator(cond->op);
      std::string lhs = SpecifyConditionText(cond->lhs);
      std::string rhs = SpecifyConditionText(cond->rhs);
      if (op.empty() || lhs.empty() || rhs.empty()) return {};
      return lhs + " " + std::string(op) + " " + rhs;
    }
    case ExprKind::kSelect:
      return SpecifyConditionSelectText(cond);
    case ExprKind::kConcatenation:
      return SpecifyConditionConcatText(cond);
    case ExprKind::kReplicate:
      return SpecifyConditionReplicateText(cond);
    case ExprKind::kTernary:
      return SpecifyConditionTernaryText(cond);
    default:
      return {};
  }
}

}  // namespace delta
