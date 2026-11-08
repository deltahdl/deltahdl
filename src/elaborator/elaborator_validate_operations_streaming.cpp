#include <cstdint>
#include <format>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/bit_stream_width.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/elaborator_validate_operations.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

bool ElaboratorOperationRules::ConcatContainsStringElement(const Expr* expr) {
  if (!expr) return false;
  if (expr->kind == ExprKind::kIdentifier) {
    auto it = var_types_.find(expr->text);
    return it != var_types_.end() && it->second == DataTypeKind::kString;
  }
  if (expr->kind == ExprKind::kStringLiteral) return true;
  if (expr->kind == ExprKind::kConcatenation) {
    for (const auto* elem : expr->elements) {
      if (ConcatContainsStringElement(elem)) return true;
    }
  }
  return false;
}

void ElaboratorOperationRules::CheckStringConcatLvalue(const Expr* lhs) {
  if (!lhs) return;
  if (lhs->kind != ExprKind::kConcatenation) return;
  if (ConcatContainsStringElement(lhs)) {
    diag_.Error(lhs->range.start,
                "string concatenation is not allowed on the left-hand side "
                "of an assignment",
                Subclause("11.4.12.2"));
  }
}

void ElaboratorOperationRules::WalkStmtsForStringConcatLvalue(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign || s->kind == StmtKind::kAssign ||
      s->kind == StmtKind::kForce) {
    CheckStringConcatLvalue(s->lhs);
  }
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { WalkStmtsForStringConcatLvalue(sub); });
}

void ElaboratorOperationRules::ValidateStringConcatLvalue(
    const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForStringConcatLvalue(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckStringConcatLvalue(item->assign_lhs);
    }
  }
}

static bool ClassHasHiddenMember(const ClassDecl* cls);

namespace {

void CheckStreamingConcatOperand(
    const Expr* elem, DiagEngine& diag,
    const std::unordered_map<std::string_view, std::string_view>&
        class_var_types,
    const std::unordered_map<std::string_view, DataTypeKind>& var_types,
    CompilationUnit* unit) {
  if (elem && elem->kind == ExprKind::kIdentifier && elem->text != "this") {
    auto it = class_var_types.find(elem->text);
    if (it != class_var_types.end() &&
        ClassHasHiddenMember(FindClassDecl(it->second, unit))) {
      diag.Error(elem->range.start,
                 std::format("class handle '{}' is illegal as a streaming "
                             "concatenation operand: its class has local "
                             "or protected members",
                             elem->text),
                 Subclause("11.4.14.1"));
    }
  }
  if (elem && elem->kind == ExprKind::kIdentifier) {
    auto vt = var_types.find(elem->text);
    if (vt != var_types.end()) {
      auto k = vt->second;
      if (IsRealType(k) || k == DataTypeKind::kEvent ||
          k == DataTypeKind::kChandle || k == DataTypeKind::kVirtualInterface) {
        diag.Error(elem->range.start,
                   std::format("'{}' is not a bit-stream type and cannot "
                               "be a streaming concatenation operand",
                               elem->text),
                   Subclause("11.4.14.1"));
      }
    }
  }
}

void CheckStreamingSliceSize(const Expr* slice, DiagEngine& diag,
                             const ScopeMap& param_scope) {
  if (!slice) return;
  std::optional<int64_t> value = ConstEvalInt(slice, param_scope);
  if (value && *value <= 0) {
    diag.Error(slice->range.start,
               "streaming slice_size shall be a positive constant",
               Subclause("11.4.14.2"));
  }
}

bool IsUnpackedTaggedUnion(const DataType* type, const TypedefMap& typedefs) {
  if (type->kind == DataTypeKind::kNamed) {
    auto it = typedefs.find(type->type_name);
    if (it == typedefs.end()) return false;
    type = &it->second;
  }
  return type->kind == DataTypeKind::kUnion && type->is_tagged &&
         !type->is_packed;
}

void CheckTaggedUnionStreamOperand(
    const Expr* elem,
    const std::unordered_map<std::string_view, const DataType*>& types,
    const TypedefMap& typedefs, DiagEngine& diag) {
  if (elem->kind != ExprKind::kIdentifier) return;
  auto it = types.find(elem->text);
  if (it == types.end() || !IsUnpackedTaggedUnion(it->second, typedefs)) return;
  diag.Error(elem->range.start,
             std::format("'{}' is not a bit-stream type and cannot be a "
                         "streaming concatenation operand",
                         elem->text),
             Subclause("11.4.14.1"));
}

void ReportStreamsNestedInTarget(const Expr* target, DiagEngine& diag) {
  if (target->kind != ExprKind::kStreamingConcat) return;
  for (const Expr* elem : target->elements) {
    if (elem->kind != ExprKind::kStreamingConcat) continue;
    diag.Error(elem->range.start,
               "a streaming concatenation written as a target holds no "
               "streaming concatenation among its stream expressions",
               Subclause("A.8.5"));
    ReportStreamsNestedInTarget(elem, diag);
  }
}

}  // namespace

void ElaboratorOperationRules::WalkExprForStreamingContext(
    const Expr* expr, bool is_valid_context) {
  if (!expr) return;
  if (expr->kind == ExprKind::kStreamingConcat) {
    if (!is_valid_context) {
      diag_.Error(expr->range.start,
                  "streaming concatenation shall not be used as an operand "
                  "of an expression other than an assignment or bit-stream "
                  "cast",
                  Subclause("11.4.14"));
    }

    for (auto* elem : expr->elements) {
      CheckStreamingConcatOperand(elem, diag_, class_var_types_, var_types_,
                                  unit_);
      CheckTaggedUnionStreamOperand(elem, stream_operand_types_, typedefs_,
                                    diag_);
      WalkExprForStreamingContext(elem, true);
    }

    CheckStreamingSliceSize(expr->lhs, diag_, streaming_slice_size_scope_);

    WalkExprForStreamingContext(expr->lhs, false);
    return;
  }
  if (expr->kind == ExprKind::kCast) {
    WalkExprForStreamingContext(expr->lhs, true);
    return;
  }
  if (expr->kind == ExprKind::kBinary && expr->op == TokenKind::kEq) {
    ReportStreamsNestedInTarget(expr->lhs, diag_);
    WalkExprForStreamingContext(expr->lhs, true);
    WalkExprForStreamingContext(expr->rhs, true);
    return;
  }

  WalkExprForStreamingContext(expr->lhs, false);
  WalkExprForStreamingContext(expr->rhs, false);
  WalkExprForStreamingContext(expr->condition, false);
  WalkExprForStreamingContext(expr->true_expr, false);
  WalkExprForStreamingContext(expr->false_expr, false);
  for (auto* elem : expr->elements) WalkExprForStreamingContext(elem, false);
  for (auto* arg : expr->args) WalkExprForStreamingContext(arg, false);
}

void ElaboratorOperationRules::CheckStreamingSourceTargetType(const Expr* lhs,
                                                              const Expr* rhs) {
  if (!lhs || !rhs) return;
  if (rhs->kind != ExprKind::kStreamingConcat) return;
  if (lhs->kind == ExprKind::kStreamingConcat) return;
  if (lhs->kind != ExprKind::kIdentifier) return;
  auto it = var_types_.find(lhs->text);
  if (it == var_types_.end()) return;
  auto k = it->second;
  bool not_bitstream = IsRealType(k) || k == DataTypeKind::kEvent ||
                       k == DataTypeKind::kChandle ||
                       k == DataTypeKind::kVirtualInterface;
  if (not_bitstream) {
    diag_.Error(lhs->range.start,
                "target of a streaming concatenation source assignment must "
                "be a bit-stream type",
                Subclause("11.4.14"));
  }
}

void ElaboratorOperationRules::CheckStreamingUnpackSourceType(const Expr* lhs,
                                                              const Expr* rhs) {
  if (!lhs || !rhs) return;
  if (lhs->kind != ExprKind::kStreamingConcat) return;
  if (rhs->kind == ExprKind::kStreamingConcat) return;
  if (rhs->kind != ExprKind::kIdentifier) return;
  auto it = var_types_.find(rhs->text);
  if (it == var_types_.end()) return;
  auto k = it->second;
  bool not_bitstream = IsRealType(k) || k == DataTypeKind::kEvent ||
                       k == DataTypeKind::kChandle ||
                       k == DataTypeKind::kVirtualInterface;
  if (not_bitstream) {
    diag_.Error(rhs->range.start,
                "source of a streaming concatenation unpack must be a "
                "bit-stream type or another streaming concatenation",
                Subclause("11.4.14.3"));
  }
}

void ElaboratorOperationRules::WalkStmtsForStreamingContext(const Stmt* s) {
  if (!s) return;
  bool is_assign = s->kind == StmtKind::kBlockingAssign ||
                   s->kind == StmtKind::kNonblockingAssign ||
                   s->kind == StmtKind::kAssign || s->kind == StmtKind::kForce;
  if (is_assign) {
    CheckStreamingSourceTargetType(s->lhs, s->rhs);
    CheckStreamingUnpackSourceType(s->lhs, s->rhs);
    ReportStreamsNestedInTarget(s->lhs, diag_);
  }
  ForEachChildExpr(s, [&](const Expr* e) {
    bool assigned = (is_assign && (e == s->lhs || e == s->rhs)) ||
                    (s->kind == StmtKind::kReturn && e == s->expr) ||
                    (s->kind == StmtKind::kVarDecl && e == s->var_init);
    WalkExprForStreamingContext(e, assigned);
  });
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { WalkStmtsForStreamingContext(sub); });
}

void ElaboratorOperationRules::ValidateStreamingConcatContext(
    const ModuleDecl* decl) {
  stream_operand_types_.clear();
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl)
      stream_operand_types_[item->name] = &item->data_type;
  }
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForStreamingContext(item->body);
    }
    if (item->kind == ModuleItemKind::kVarDecl ||
        item->kind == ModuleItemKind::kNetDecl)
      WalkExprForStreamingContext(item->init_expr, true);
    for (const Stmt* s : item->func_body_stmts) WalkStmtsForStreamingContext(s);
    if (item->kind == ModuleItemKind::kContAssign) {
      WalkExprForStreamingContext(item->assign_lhs, true);
      WalkExprForStreamingContext(item->assign_rhs, true);
      CheckStreamingSourceTargetType(item->assign_lhs, item->assign_rhs);
      CheckStreamingUnpackSourceType(item->assign_lhs, item->assign_rhs);
      ReportStreamsNestedInTarget(item->assign_lhs, diag_);
    }
  }
}

static bool ClassHasHiddenMember(const ClassDecl* cls) {
  if (!cls) return false;
  for (const auto* m : cls->members) {
    if (m && (m->is_local || m->is_protected)) return true;
  }
  return false;
}

static uint32_t CastTargetSimpleWidth(std::string_view t) {
  if (t == "byte") return 8;
  if (t == "shortint") return 16;
  if (t == "int" || t == "integer") return 32;
  if (t == "longint") return 64;
  if (t == "bit" || t == "logic" || t == "reg") return 1;
  return 0;
}

namespace {

struct BitStreamCast {
  const Expr* expr;
  std::string_view target;
};

struct BitStreamCastCtx {
  DiagEngine& diag;
  const std::unordered_set<std::string_view>& class_names;
  const std::unordered_map<std::string_view, std::string_view>& class_var_types;
  const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
      var_array_info;
  const TypedefMap& typedefs;
  const std::unordered_map<std::string_view, uint32_t>& unpacked_typedef_widths;
  const std::unordered_map<std::string_view, const DataType*>& var_decl_types;
  CompilationUnit* unit;
};

uint32_t BitStreamDestinationWidth(std::string_view target,
                                   const BitStreamCastCtx& ctx) {
  if (uint32_t simple = CastTargetSimpleWidth(target)) return simple;
  auto unpacked = ctx.unpacked_typedef_widths.find(target);
  if (unpacked != ctx.unpacked_typedef_widths.end()) return unpacked->second;
  auto td = ctx.typedefs.find(target);
  if (td == ctx.typedefs.end()) return 0;
  return BitStreamTypeWidth(td->second, ctx.typedefs);
}

uint32_t UnpackedOperandWidth(std::string_view name,
                              const BitStreamCastCtx& ctx) {
  auto var_it = ctx.var_array_info.find(name);
  if (var_it != ctx.var_array_info.end()) {
    const auto& info = var_it->second;
    if (info.is_dynamic || info.is_assoc) return 0;
    return info.unpacked_size * info.elem_width;
  }
  auto decl = ctx.var_decl_types.find(name);
  if (decl == ctx.var_decl_types.end()) return 0;
  const DataType* type = decl->second;
  for (int hops = 0; hops < 8 && type->kind == DataTypeKind::kNamed; ++hops) {
    auto td = ctx.typedefs.find(type->type_name);
    if (td == ctx.typedefs.end()) return 0;
    type = &td->second;
  }
  if (type->kind != DataTypeKind::kStruct || type->is_packed) return 0;
  return BitStreamTypeWidth(*type, ctx.typedefs);
}

bool CheckBitStreamCastClassSource(const BitStreamCast& cast,
                                   const BitStreamCastCtx& ctx) {
  const Expr* expr = cast.expr;
  if (expr->lhs && expr->lhs->kind == ExprKind::kIdentifier &&
      expr->lhs->text != "this" && ctx.class_names.count(cast.target) == 0) {
    auto it = ctx.class_var_types.find(expr->lhs->text);
    if (it != ctx.class_var_types.end()) {
      const auto* cls = FindClassDecl(it->second, ctx.unit);
      if (ClassHasHiddenMember(cls)) {
        ctx.diag.Error(expr->range.start,
                       std::format("class handle '{}' is illegal as a "
                                   "bit-stream cast source: its class has "
                                   "local or protected members",
                                   expr->lhs->text),
                       Subclause("6.24.3"));
        return true;
      }
    }
  }
  return false;
}

void CheckBitStreamCastUnpackedOperand(const BitStreamCast& cast,
                                       const BitStreamCastCtx& ctx) {
  const Expr* expr = cast.expr;
  if (expr->lhs->kind != ExprKind::kIdentifier) return;
  uint32_t src_width = UnpackedOperandWidth(expr->lhs->text, ctx);
  if (src_width == 0) return;
  uint32_t dst_width = BitStreamDestinationWidth(cast.target, ctx);
  if (dst_width == 0) return;
  if (src_width == dst_width) return;
  ctx.diag.Error(expr->range.start,
                 std::format("bit-stream cast between fixed-size types of "
                             "different sizes ({} bits to {} bits) with an "
                             "unpacked operand is illegal",
                             src_width, dst_width),
                 Subclause("6.24.3"));
}

}  // namespace

void ElaboratorOperationRules::CheckBitStreamCastExpr(const Expr* expr) {
  if (!expr || expr->kind != ExprKind::kCast) return;
  auto target = expr->text;
  if (target.empty()) return;

  if (assoc_typedef_names_.count(target) > 0) {
    diag_.Error(expr->range.start,
                std::format("associative array type '{}' is illegal as a "
                            "bit-stream cast destination",
                            target),
                Subclause("6.24.3"));
    return;
  }

  BitStreamCast cast{expr, target};
  BitStreamCastCtx ctx{diag_,
                       class_names_,
                       class_var_types_,
                       var_array_info_,
                       typedefs_,
                       fixed_unpacked_typedef_widths_,
                       bit_stream_var_types_,
                       unit_};

  if (CheckBitStreamCastClassSource(cast, ctx)) {
    return;
  }

  if (!expr->lhs) return;

  auto dst_unpacked_it = fixed_unpacked_typedef_widths_.find(target);
  if (dst_unpacked_it != fixed_unpacked_typedef_widths_.end()) {
    uint32_t src_width = expr->lhs->kind == ExprKind::kIdentifier
                             ? UnpackedOperandWidth(expr->lhs->text, ctx)
                             : 0;
    if (src_width == 0) src_width = InferExprWidth(expr->lhs, typedefs_);
    if (src_width > 0 && src_width != dst_unpacked_it->second) {
      diag_.Error(expr->range.start,
                  std::format("bit-stream cast between fixed-size types of "
                              "different sizes ({} bits to {} bits) with an "
                              "unpacked destination is illegal",
                              src_width, dst_unpacked_it->second),
                  Subclause("6.24.3"));
      return;
    }
  }

  CheckBitStreamCastUnpackedOperand(cast, ctx);
}

void ElaboratorOperationRules::WalkExprForBitStreamCast(const Expr* expr) {
  if (!expr) return;
  CheckBitStreamCastExpr(expr);
  WalkExprForBitStreamCast(expr->lhs);
  WalkExprForBitStreamCast(expr->rhs);
  WalkExprForBitStreamCast(expr->base);
  WalkExprForBitStreamCast(expr->index);
  WalkExprForBitStreamCast(expr->index_end);
  WalkExprForBitStreamCast(expr->condition);
  WalkExprForBitStreamCast(expr->true_expr);
  WalkExprForBitStreamCast(expr->false_expr);
  for (const auto* elem : expr->elements) WalkExprForBitStreamCast(elem);
  for (const auto* arg : expr->args) WalkExprForBitStreamCast(arg);
}

void ElaboratorOperationRules::WalkStmtsForBitStreamCast(const Stmt* s) {
  if (!s) return;
  WalkExprForBitStreamCast(s->lhs);
  WalkExprForBitStreamCast(s->rhs);
  WalkExprForBitStreamCast(s->expr);
  WalkExprForBitStreamCast(s->condition);
  ForEachChildStmt(s,
                   [&](Stmt* const& sub) { WalkStmtsForBitStreamCast(sub); });
}

void ElaboratorOperationRules::ValidateBitStreamCast(const ModuleDecl* decl) {
  bit_stream_var_types_.clear();
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl && item->unpacked_dims.empty())
      bit_stream_var_types_[item->name] = &item->data_type;
  }
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForBitStreamCast(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      WalkExprForBitStreamCast(item->assign_lhs);
      WalkExprForBitStreamCast(item->assign_rhs);
    }
    if (item->kind == ModuleItemKind::kVarDecl) {
      WalkExprForBitStreamCast(item->init_expr);
    }
  }
}

}  // namespace delta
