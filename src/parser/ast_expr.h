#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "common/types.h"
#include "lexer/token.h"

namespace delta {

struct Expr;
struct Stmt;
struct ModuleItem;
struct ModuleDecl;
struct SpecifyItem;
struct BindDirective;
struct ClassMember;

enum class ExprKind : uint8_t {
  kIntegerLiteral,
  kRealLiteral,
  kTimeLiteral,
  kStringLiteral,
  kUnbasedUnsizedLiteral,
  kIdentifier,
  kSystemCall,
  kUnary,
  kBinary,
  kTernary,
  kConcatenation,
  kReplicate,
  kSelect,
  kMemberAccess,
  kCall,
  kAssignmentPattern,
  kCast,
  kTypeRef,
  kPostfixUnary,
  kInside,
  kStreamingConcat,
  kMinTypMax,
  kTagged,
};

struct Expr {
  ExprKind kind;
  SourceRange range;

  std::string_view text;
  std::string_view scope_prefix;
  uint64_t int_val = 0;
  double real_val = 0.0;

  TokenKind op = TokenKind::kEof;
  Expr* lhs = nullptr;
  Expr* rhs = nullptr;

  Expr* condition = nullptr;
  Expr* true_expr = nullptr;
  Expr* false_expr = nullptr;

  std::string_view callee;
  std::vector<Expr*> args;
  std::vector<std::string_view> arg_names;

  Expr* base = nullptr;
  Expr* index = nullptr;
  Expr* index_end = nullptr;
  bool is_part_select_plus = false;
  bool is_part_select_minus = false;
  bool has_param_spec = false;
  // kMemberAccess only: true when the operator was `::` (scope resolution),
  // false when it was `.` (member access). Lets the elaborator distinguish
  // `pkg::x` from `obj.x` (§26.3 / §23.7.1).
  bool is_scope_resolution = false;

  Expr* with_expr = nullptr;
  bool with_has_parens = false;

  // 18.7: for a randomize() with { constraint_block } call, the captured inline
  // constraint block. Its top-level relations (and dist/soft/if-else forms) are
  // scanned into a throwaway constraint ClassMember exactly as an in-class
  // constraint block is, so the simulator can apply them alongside the object's
  // own constraints. Null for any other call, including a plain randomize().
  ClassMember* inline_constraint = nullptr;

  // 18.7: the identifier_list of a restricted inline constraint block -- the
  // names inside the parentheses of `randomize() with ( a, b ) { ... }`. In a
  // restricted block only these names resolve as the object's random variables;
  // all others resolve in the calling scope. with_has_parens records that the
  // parenthesized form was used (so an empty list still marks a restricted
  // block); this vector holds the listed names. Empty for an unrestricted
  // block.
  std::vector<std::string_view> with_restrict_ids;

  std::vector<Expr*> elements;
  Expr* repeat_count = nullptr;

  // §10.9: the key of each keyed element of an assignment pattern, in the order
  // the elements were written, and empty for a positional one. Syntax 10-5
  // writes a key as an expression -- `array_pattern_key ::= constant_expression
  // | assignment_pattern_key` -- so a key is held as one, and `N-1` is as much
  // a key as `3` is. The two spellings that are not expressions,
  // `assignment_pattern_key ::= simple_type | default`, are held as an
  // identifier node carrying the keyword, which is a spelling no member name
  // and no index can be confused with. A key written as a single name or
  // literal therefore has that name or literal as its node's text, which is
  // what a reader matching a key against a member name or an associative
  // array's string index wants.
  std::vector<Expr*> pattern_keys;

  bool is_parenthesized = false;

  // §12.6: set on a kIdentifier produced from the `. variable_identifier`
  // pattern form, distinguishing a pattern identifier that binds a new variable
  // from a bare identifier used as a constant expression pattern. Parsing drops
  // the leading dot, so this flag is the only record that the identifier came
  // from a binding position.
  bool is_pattern_binding = false;
};

// §11.5: an operand is "simple" iff it is not parenthesized AND is a primary
// (as defined in A.8.4). The example given is `1'b1 - 2'b00 + (1'b1 + 1'b1)`,
// where `1'b1 - 2'b00` (binary, not a primary) and `(1'b1 + 1'b1)`
// (parenthesized) are operands but not simple operands.
inline bool IsSimpleOperand(const Expr* e) {
  if (e == nullptr) return false;
  if (e->is_parenthesized) return false;
  switch (e->kind) {
    case ExprKind::kIntegerLiteral:
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral:
    case ExprKind::kStringLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
    case ExprKind::kIdentifier:
    case ExprKind::kSelect:
    case ExprKind::kMemberAccess:
    case ExprKind::kCall:
    case ExprKind::kSystemCall:
    case ExprKind::kConcatenation:
    case ExprKind::kReplicate:
    case ExprKind::kAssignmentPattern:
    case ExprKind::kCast:
    case ExprKind::kStreamingConcat:
    case ExprKind::kTypeRef:
    case ExprKind::kTagged:
      return true;
    case ExprKind::kUnary:
    case ExprKind::kBinary:
    case ExprKind::kTernary:
    case ExprKind::kPostfixUnary:
    case ExprKind::kInside:
    case ExprKind::kMinTypMax:
      return false;
  }
  return false;
}

// §11.8.1: decimal numbers are signed, and based numbers are unsigned except
// where the s notation is used in the base specifier, as in 4'sd12. The text an
// Expr carries for a literal is its source spelling, which is where the base
// specifier is: the apostrophe separates the decimal form from the based form,
// and the character after the apostrophe decides the based one.
inline bool IsSignedLiteral(std::string_view text) {
  auto tick = text.find('\'');
  if (tick == std::string_view::npos) return true;
  if (tick + 1 >= text.size()) return false;
  char c = text[tick + 1];
  return c == 's' || c == 'S';
}

struct Attribute {
  std::string_view name;
  Expr* value = nullptr;
  SourceLoc loc;
};

}  // namespace delta
