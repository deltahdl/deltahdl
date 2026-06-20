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

  Expr* with_expr = nullptr;
  bool with_has_parens = false;

  std::vector<Expr*> elements;
  Expr* repeat_count = nullptr;
  std::vector<std::string_view> pattern_keys;

  bool is_parenthesized = false;
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

struct Attribute {
  std::string_view name;
  Expr* value = nullptr;
  SourceLoc loc;
};

}  // namespace delta
