#pragma once

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/source_loc.h"
#include "lexer/token.h"

namespace delta {

struct Expr;
struct Stmt;
struct ModuleItem;
struct ModuleDecl;
struct SpecifyItem;
struct BindDirective;
struct ClassMember;
struct PropertyExprNode;
struct DataType;
struct EventExpr;
struct ConstraintDistItem;

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

struct Attribute {
  std::string_view name;
  Expr* value = nullptr;
  SourceLoc loc;
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
  bool has_arg_list = false;

  Expr* base = nullptr;
  Expr* index = nullptr;
  Expr* index_end = nullptr;
  bool is_part_select_plus = false;
  bool is_part_select_minus = false;
  bool has_param_spec = false;
  bool is_scope_resolution = false;

  Expr* with_expr = nullptr;
  bool with_has_parens = false;

  ClassMember* inline_constraint = nullptr;

  std::vector<std::string_view> with_restrict_ids;

  std::vector<Expr*> elements;
  Expr* repeat_count = nullptr;
  bool is_pattern_replication = false;

  std::vector<Expr*> pattern_keys;

  bool is_parenthesized = false;

  bool is_pattern_binding = false;
  bool is_coverage_event_sample = false;

  PropertyExprNode* property_actual = nullptr;
  PropertyExprNode* sequence_reading = nullptr;
  const std::vector<EventExpr>* sampled_clock = nullptr;
  const std::vector<ConstraintDistItem>* dist_items = nullptr;

  DataType* type_value = nullptr;
  std::vector<Attribute> attrs;
  Expr* stream_range = nullptr;
};

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

inline bool IsSignedLiteral(std::string_view text) {
  auto tick = text.find('\'');
  if (tick == std::string_view::npos) return true;
  if (tick + 1 >= text.size()) return false;
  char c = text[tick + 1];
  return c == 's' || c == 'S';
}

}  // namespace delta
