#include <cmath>
#include <format>
#include <optional>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaboration/const_eval.h"
#include "elaboration/elaborator.h"
#include "elaboration/type_eval.h"
#include "parser/ast.h"

namespace delta {

void Elaborator::ValidateArrayInitPattern(const ModuleItem* item) {
  if (!item->init_expr || item->unpacked_dims.empty()) return;
  if (item->init_expr->kind != ExprKind::kAssignmentPattern) return;
  if (item->init_expr->repeat_count) return;           // replication form
  if (!item->init_expr->pattern_keys.empty()) return;  // named form

  const auto* dim = item->unpacked_dims[0];
  if (!dim) return;  // dynamic array

  std::optional<int64_t> dim_size;
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
    auto left = ConstEvalInt(dim->lhs);
    auto right = ConstEvalInt(dim->rhs);
    if (left && right) {
      dim_size = std::abs(*left - *right) + 1;
    }
  } else {
    dim_size = ConstEvalInt(dim);
  }
  if (!dim_size) return;

  auto count = static_cast<int64_t>(item->init_expr->elements.size());
  if (count != *dim_size) {
    diag_.Error(item->loc,
                std::format("assignment pattern has {} elements, but array "
                            "dimension requires {}",
                            count, *dim_size));
  }
}

// --- §6 validation helpers ---

static std::string_view ExprIdent(const Expr* e) {
  if (!e) return {};
  if (e->kind == ExprKind::kIdentifier) return e->text;
  return {};
}

static void CollectProcTargets(const Stmt* s,
                               std::unordered_set<std::string_view>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    auto name = ExprIdent(s->lhs);
    if (!name.empty()) out.insert(name);
  }
  for (auto* sub : s->stmts) CollectProcTargets(sub, out);
  CollectProcTargets(s->then_branch, out);
  CollectProcTargets(s->else_branch, out);
  CollectProcTargets(s->body, out);
  CollectProcTargets(s->for_body, out);
  for (auto& ci : s->case_items) CollectProcTargets(ci.body, out);
}

static bool IsRealType(DataTypeKind k) {
  return k == DataTypeKind::kReal || k == DataTypeKind::kShortreal ||
         k == DataTypeKind::kRealtime;
}

using TypeMap = std::unordered_map<std::string_view, DataTypeKind>;

static void CheckRealSelectNode(const Expr* e, const TypeMap& types,
                                DiagEngine& diag) {
  auto name = ExprIdent(e->base);
  if (!name.empty()) {
    auto it = types.find(name);
    if (it != types.end() && IsRealType(it->second)) {
      diag.Error(e->range.start, "bit-select on real type is illegal");
      return;
    }
  }
  if (!e->index) return;
  auto idx = ExprIdent(e->index);
  if (idx.empty()) return;
  auto it = types.find(idx);
  if (it != types.end() && IsRealType(it->second)) {
    diag.Error(e->range.start, "real type used as index is illegal");
  }
}

static void CheckRealSelect(const Expr* e, const TypeMap& types,
                            DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSelect && e->base) {
    CheckRealSelectNode(e, types, diag);
  }
  CheckRealSelect(e->lhs, types, diag);
  CheckRealSelect(e->rhs, types, diag);
  CheckRealSelect(e->base, types, diag);
  CheckRealSelect(e->index, types, diag);
}

static bool ExprContainsIdent(const Expr* e, std::string_view name) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier && e->text == name) return true;
  if (ExprContainsIdent(e->lhs, name)) return true;
  return ExprContainsIdent(e->rhs, name);
}

void Elaborator::ValidateEdgeOnReal(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kAlwaysBlock) return;
  for (const auto& ev : item->sensitivity) {
    if (ev.edge == Edge::kNone) continue;
    auto name = ExprIdent(ev.signal);
    if (name.empty()) continue;
    auto it = var_types_.find(name);
    if (it != var_types_.end() && IsRealType(it->second)) {
      diag_.Error(item->loc, "edge event on real type is illegal");
    }
  }
}

void Elaborator::ValidateItemConstraints(const ModuleItem* item) {
  bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                 item->kind == ModuleItemKind::kInitialBlock;
  if (is_proc && item->body) {
    CollectProcTargets(item->body, proc_assign_targets_);
  }
  ValidateEdgeOnReal(item);
  if (item->kind == ModuleItemKind::kContAssign) {
    CheckRealSelect(item->assign_rhs, var_types_, diag_);
  }
}

void Elaborator::ValidateMixedAssignments() {
  for (const auto& [name, loc] : cont_assign_targets_) {
    if (proc_assign_targets_.count(name) != 0) {
      diag_.Error(loc, std::format("variable '{}' has both continuous and "
                                   "procedural assignments",
                                   name));
    }
  }
}

void Elaborator::ValidateSpecparamInParams(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kParamDecl) continue;
    if (!item->init_expr) continue;
    for (const auto& sp : specparam_names_) {
      if (ExprContainsIdent(item->init_expr, sp)) {
        diag_.Error(item->loc,
                    std::format("parameter references specparam '{}'", sp));
        break;
      }
    }
  }
}

void Elaborator::ValidateModuleConstraints(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    ValidateItemConstraints(item);
  }
  ValidateMixedAssignments();
  ValidateSpecparamInParams(decl);
  ValidateEnumAssignments(decl);
}

// §6.19 enum validation helpers

static int64_t ParseLiteralWidth(std::string_view txt) {
  auto apos = txt.find('\'');
  if (apos == std::string_view::npos || apos == 0) return 0;
  int64_t width = 0;
  for (size_t i = 0; i < apos; ++i) {
    if (txt[i] < '0' || txt[i] > '9') return 0;
    width = width * 10 + (txt[i] - '0');
  }
  return width;
}

static bool LiteralHasXZ(std::string_view txt) {
  auto apos = txt.find('\'');
  if (apos == std::string_view::npos) return false;
  return txt.substr(apos + 1).find_first_of("xXzZ") != std::string_view::npos;
}

static bool ExprContainsXZ(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kIntegerLiteral && LiteralHasXZ(e->text)) {
    return true;
  }
  if (ExprContainsXZ(e->lhs)) return true;
  if (ExprContainsXZ(e->rhs)) return true;
  for (const auto* elem : e->elements) {
    if (ExprContainsXZ(elem)) return true;
  }
  return ExprContainsXZ(e->repeat_count);
}

bool Elaborator::ValidateEnumLiteral(const EnumMember& member,
                                     uint32_t base_width, bool is_2state) {
  if (member.value->kind == ExprKind::kIntegerLiteral) {
    auto width = ParseLiteralWidth(member.value->text);
    if (width > 0) {
      if (width != static_cast<int64_t>(base_width)) {
        diag_.Error(member.value->range.start,
                    std::format("enum literal width {} does not match "
                                "base type width {}",
                                width, base_width));
      }
    }
  }
  bool has_xz = ExprContainsXZ(member.value);
  if (has_xz && is_2state) {
    diag_.Error(member.value->range.start,
                "x/z value in 2-state enum is illegal");
  }
  return has_xz;
}

void Elaborator::ValidateEnumDecl(const DataType& dtype, SourceLoc loc) {
  auto base_width = EvalTypeWidth(dtype, typedefs_);
  bool is_2state = !Is4stateType(dtype, typedefs_);
  bool prev_had_xz = false;

  for (const auto& member : dtype.enum_members) {
    if (!member.value) {
      if (prev_had_xz) {
        diag_.Error(loc,
                    std::format("unassigned enum member '{}' follows member "
                                "with x/z value",
                                member.name));
      }
      prev_had_xz = false;
      continue;
    }
    prev_had_xz = ValidateEnumLiteral(member, base_width, is_2state);
  }
}

// §6.19.3/§6.19.4 enum assignment validation

void Elaborator::TrackEnumVariable(const ModuleItem* item) {
  if (item->data_type.kind == DataTypeKind::kEnum) {
    enum_var_names_.insert(item->name);
    for (const auto& m : item->data_type.enum_members) {
      enum_member_names_.insert(m.name);
    }
    return;
  }
  if (item->data_type.kind != DataTypeKind::kNamed) return;
  auto it = typedefs_.find(item->data_type.type_name);
  if (it != typedefs_.end() && it->second.kind == DataTypeKind::kEnum) {
    enum_var_names_.insert(item->name);
  }
}

static bool IsCompoundAssignOp(TokenKind op) {
  switch (op) {
    case TokenKind::kPlusEq:
    case TokenKind::kMinusEq:
    case TokenKind::kStarEq:
    case TokenKind::kSlashEq:
    case TokenKind::kPercentEq:
    case TokenKind::kAmpEq:
    case TokenKind::kPipeEq:
    case TokenKind::kCaretEq:
    case TokenKind::kLtLtEq:
    case TokenKind::kGtGtEq:
    case TokenKind::kLtLtLtEq:
    case TokenKind::kGtGtGtEq:
      return true;
    default:
      return false;
  }
}

void Elaborator::CheckEnumAssignStmt(const Stmt* s) {
  auto name = ExprIdent(s->lhs);
  if (name.empty()) return;
  if (enum_var_names_.count(name) == 0) return;
  if (s->rhs && s->rhs->kind == ExprKind::kBinary &&
      IsCompoundAssignOp(s->rhs->op)) {
    diag_.Error(s->range.start,
                "compound assignment to enum variable without cast");
    return;
  }
  if (!s->rhs) return;
  if (s->rhs->kind == ExprKind::kIdentifier) return;
  if (s->rhs->kind == ExprKind::kCast) return;
  diag_.Error(s->range.start, "integer assigned to enum variable without cast");
}

void Elaborator::WalkStmtsForEnumAssign(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl) {
    if (s->var_decl_type.kind == DataTypeKind::kNamed) {
      auto it = typedefs_.find(s->var_decl_type.type_name);
      if (it != typedefs_.end() && it->second.kind == DataTypeKind::kEnum) {
        enum_var_names_.insert(s->var_name);
      }
    }
  }
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckEnumAssignStmt(s);
  }
  for (auto* sub : s->stmts) WalkStmtsForEnumAssign(sub);
  WalkStmtsForEnumAssign(s->then_branch);
  WalkStmtsForEnumAssign(s->else_branch);
  WalkStmtsForEnumAssign(s->body);
  WalkStmtsForEnumAssign(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForEnumAssign(ci.body);
}

void Elaborator::ValidateEnumAssignments(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForEnumAssign(item->body);
    }
  }
}

}  // namespace delta
