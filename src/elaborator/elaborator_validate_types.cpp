#include <cmath>
#include <format>
#include <optional>
#include <unordered_map>
#include <unordered_set>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

void Elaborator::ValidateModuleConstraints(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    ValidateItemConstraints(item);
  }
  ValidatePackageImportRules(decl);
  ValidateScopeRules(decl);
  ValidateMixedAssignments();
  ValidateInputPortAssignments(decl);
  ValidateMatchesPatternIntegral(decl);
  ValidateMatchesCaseSelectorType(decl);
  ValidateMatchesIfPredicateType(decl);
  ValidateDisableTargets(decl);
  ValidateProceduralNetAssign();
  ValidateDynamicArrayNba(decl);
  ValidateArrayQueryOnDynamicType(decl);
  ValidateArrayQueryOnVariableDim(decl);
  ValidateRandomSeedType(decl);
  ValidatePlaOutputTerms(decl);
  ValidatePlaAscendingOrder(decl);
  ValidateBitsCallRestrictions(decl);
  ValidateAutomaticVarProcWrites(decl);
  ValidateJumpStatements(decl);
  ValidateForeachLoops(decl);
  ValidateContAssignConstSelect(decl);
  ValidatePartSelectBounds(decl);
  ValidateSpecparamInParams(decl);
  ValidateSpecparamInDeclRange(decl);
  ValidateEnumAssignments(decl);
  ValidateConstAssignments(decl);
  ValidateArrayAssignments(decl);
  ValidateAssocArraySlices(decl);
  ValidateAssocWildcardTraversal(decl);
  ValidateAssocTraversalArgType(decl);
  ValidateArrayOrderingMethods(decl);
  ValidateClassIndexSelect(decl);
  ValidateStringIndexSelect(decl);
  ValidateIntegralIndexSelect(decl);
  ValidateAssocConcatTarget(decl);
  ValidateAssocOperandInExpr(decl);
  ValidateArrayPatternElemType(decl);
  ValidateReplicateTargetingArray(decl);
  ValidateArrayElementPartSelect(decl);
  ValidateUnpackedArrayConcatNesting(decl);
  ValidateClassHandleOps(decl);
  ValidateChandleOps(decl);
  ValidateVirtualInterfaceOps(decl);
  ValidateEventOps(decl);
  ValidateVirtualInterfaceClocking(decl);
  ValidateInterfaceObjectAccess(decl);

  ValidateDeferredAssertionActions(decl);
  ValidateAggregateComparisons(decl);
  ValidateTypeRefComparisons(decl);
  ValidateTypeRefArgs(decl);
  ValidateTaggedUnionMembers(decl);
  ValidateRealOperatorRestrictions(decl);
  ValidateAssignInExprRestrictions(decl);
  ValidateUnsizedInConcat(decl);
  ValidateSelectOnConcatLvalue(decl);
  ValidateReplicateLvalue(decl);
  ValidateStringConcatLvalue(decl);
  ValidateReplicateMultiplier(decl);
  ValidateStreamingConcatContext(decl);
  ValidateBitStreamCast(decl);
  ValidateSubroutineCallArgs(decl);
  ValidateArrayArgTypes(decl);
  ValidateLocalProtectedAccess(decl);
  ValidateParameterizedScopeResolution(decl);
  ValidateTypeParamScopeUsage(decl);
  ValidateTypeParamScopePrefixResolvesToClass(decl);
  ValidateStaticMethodBodies(decl);
  ValidateClassMethodBodies(decl);
  ValidateThisUsage(decl);

  if (decl->has_timeunit && decl->has_timeprecision) {
    int unit_order =
        EffectiveTimeOrder(decl->time_unit, decl->time_unit_magnitude);
    int prec_order =
        EffectiveTimeOrder(decl->time_prec, decl->time_prec_magnitude);
    if (prec_order > unit_order) {
      diag_.Error(decl->range.start,
                  "time precision is less precise than the time unit");
    }
  }
}

namespace {

void ClassifyTimescaleElement(bool el_has_unit, bool el_has_prec,
                              bool cu_fallback_unit, bool cu_fallback_prec,
                              SourceLoc loc, bool& any_specified,
                              bool& any_unspecified,
                              SourceLoc& unspecified_loc) {
  bool has_unit = el_has_unit || cu_fallback_unit;
  bool has_prec = el_has_prec || cu_fallback_prec;
  if (has_unit && has_prec) {
    any_specified = true;
  } else {
    if (!any_unspecified) unspecified_loc = loc;
    any_unspecified = true;
  }
}

}  // namespace

void Elaborator::ValidateTimescaleConsistency() {
  bool cu_unit = unit_->has_preproc_timescale || unit_->has_cu_timeunit;
  bool cu_prec = unit_->has_preproc_timescale || unit_->has_cu_timeprecision;
  bool any_specified = false;
  bool any_unspecified = false;
  SourceLoc unspecified_loc;
  auto inspect = [&](bool el_has_unit, bool el_has_prec, SourceLoc loc) {
    ClassifyTimescaleElement(el_has_unit, el_has_prec, cu_unit, cu_prec, loc,
                             any_specified, any_unspecified, unspecified_loc);
  };

  for (const auto* mod : unit_->modules)
    inspect(mod->has_timeunit, mod->has_timeprecision, mod->range.start);
  for (const auto* iface : unit_->interfaces)
    inspect(iface->has_timeunit, iface->has_timeprecision, iface->range.start);
  for (const auto* prog : unit_->programs)
    inspect(prog->has_timeunit, prog->has_timeprecision, prog->range.start);

  if (any_specified && any_unspecified) {
    diag_.Error(unspecified_loc,
                "some design elements specify time unit and precision while "
                "others do not");
  }
}

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

static bool ExprContainsHierarchicalRef(const Expr* e);

static bool AnyScalarChildContainsHierarchicalRef(const Expr* e) {
  const Expr* const kChildren[] = {
      e->lhs,       e->rhs,       e->base,       e->index,       e->index_end,
      e->condition, e->true_expr, e->false_expr, e->repeat_count};
  for (const Expr* child : kChildren) {
    if (ExprContainsHierarchicalRef(child)) return true;
  }
  return false;
}

static bool ExprContainsHierarchicalRef(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kMemberAccess) return true;
  if (e->kind == ExprKind::kIdentifier && !e->scope_prefix.empty()) return true;
  if (AnyScalarChildContainsHierarchicalRef(e)) return true;
  for (const auto* a : e->args) {
    if (ExprContainsHierarchicalRef(a)) return true;
  }
  for (const auto* elem : e->elements) {
    if (ExprContainsHierarchicalRef(elem)) return true;
  }
  return false;
}

static std::string_view FindConstVarRef(
    const Expr* e, const std::unordered_set<std::string_view>& const_names);

static std::string_view FindConstVarRefInScalarChildren(
    const Expr* e, const std::unordered_set<std::string_view>& const_names) {
  const Expr* const kChildren[] = {
      e->lhs,       e->rhs,       e->base,       e->index,       e->index_end,
      e->condition, e->true_expr, e->false_expr, e->repeat_count};
  for (const Expr* child : kChildren) {
    if (auto n = FindConstVarRef(child, const_names); !n.empty()) return n;
  }
  return {};
}

static std::string_view FindConstVarRef(
    const Expr* e, const std::unordered_set<std::string_view>& const_names) {
  if (!e) return {};
  if (e->kind == ExprKind::kIdentifier && e->scope_prefix.empty() &&
      const_names.count(e->text)) {
    return e->text;
  }
  if (auto n = FindConstVarRefInScalarChildren(e, const_names); !n.empty())
    return n;
  for (const auto* a : e->args) {
    if (auto n = FindConstVarRef(a, const_names); !n.empty()) return n;
  }
  for (const auto* elem : e->elements) {
    if (auto n = FindConstVarRef(elem, const_names); !n.empty()) return n;
  }
  return {};
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
  if (!dtype.enum_base_name.empty()) {
    auto it = typedefs_.find(dtype.enum_base_name);
    if (it != typedefs_.end()) {
      auto k = it->second.kind;
      bool integer_atom =
          k == DataTypeKind::kByte || k == DataTypeKind::kShortint ||
          k == DataTypeKind::kInt || k == DataTypeKind::kLongint ||
          k == DataTypeKind::kInteger || k == DataTypeKind::kTime;
      bool integer_vector = k == DataTypeKind::kLogic ||
                            k == DataTypeKind::kReg || k == DataTypeKind::kBit;
      if (!integer_atom && !integer_vector) {
        diag_.Error(loc, std::format("enum base type '{}' is not an "
                                     "integer_atom_type or integer_vector_type",
                                     dtype.enum_base_name));
      } else if (integer_atom && dtype.packed_dim_left != nullptr) {
        diag_.Error(loc,
                    std::format("packed dimension not permitted on enum base "
                                "type '{}' that denotes an integer_atom_type",
                                dtype.enum_base_name));
      }
    }
  }

  auto base_width = EvalTypeWidth(dtype, typedefs_);
  bool is_2state = !Is4stateType(dtype, typedefs_);
  bool prev_had_xz = false;

  uint64_t max_val =
      dtype.is_signed
          ? (base_width > 0 ? (1ULL << (base_width - 1)) - 1 : 0)
          : (base_width < 64 ? (1ULL << base_width) - 1 : UINT64_MAX);
  int64_t signed_min = (dtype.is_signed && base_width > 0 && base_width < 64)
                           ? -(1LL << (base_width - 1))
                           : INT64_MIN;

  std::unordered_set<std::string_view> seen_names;
  std::unordered_set<int64_t> seen_values;
  int64_t next_val = 0;

  for (const auto& member : dtype.enum_members) {
    if (!member.range_start) {
      if (!seen_names.insert(member.name).second) {
        diag_.Error(
            loc, std::format("duplicate enum member name '{}'", member.name));
      } else if (enum_member_names_.count(member.name)) {
        diag_.Error(loc,
                    std::format("enum member name '{}' is already declared "
                                "in this scope",
                                member.name));
      }
    }

    if (member.value) {
      if (ExprContainsHierarchicalRef(member.value)) {
        diag_.Error(member.value->range.start,
                    "hierarchical name not allowed in enum named constant "
                    "value");
      }
      auto const_name = FindConstVarRef(member.value, const_names_);
      if (!const_name.empty()) {
        diag_.Error(member.value->range.start,
                    std::format("const variable '{}' not allowed in enum named "
                                "constant value",
                                const_name));
      }
    }

    if (!member.value) {
      if (prev_had_xz) {
        diag_.Error(loc,
                    std::format("unassigned enum member '{}' follows member "
                                "with x/z value",
                                member.name));
      }
      prev_had_xz = false;
    } else {
      prev_had_xz = ValidateEnumLiteral(member, base_width, is_2state);
      if (!prev_had_xz) {
        auto v = ConstEvalInt(member.value);
        if (v) {
          bool out_of_range = false;
          if (dtype.is_signed) {
            out_of_range =
                *v < signed_min || *v > static_cast<int64_t>(max_val);
          } else {
            out_of_range = *v < 0 || (base_width < 64 &&
                                      static_cast<uint64_t>(*v) > max_val);
          }
          if (out_of_range) {
            diag_.Error(member.value->range.start,
                        std::format("enum member '{}' value {} is outside the "
                                    "representable range of the base type",
                                    member.name, *v));
          }
          next_val = *v;
        }
      }
    }

    int64_t count = 1;
    if (member.range_start) {
      auto n = ConstEvalInt(member.range_start).value_or(0);
      if (member.range_end) {
        auto m = ConstEvalInt(member.range_end).value_or(0);
        // Table 6-10: for the name[N:M] form, both bounds shall be
        // non-negative integral numbers.
        if (n < 0 || m < 0) {
          diag_.Error(loc, std::format("enum range bounds of '{}' shall be "
                                       "non-negative integral numbers",
                                       member.name));
        }
        count = (m >= n) ? (m - n + 1) : (n - m + 1);
      } else {
        // Table 6-10: for the name[N] form, N shall be a positive integral
        // number.
        if (n < 1) {
          diag_.Error(loc, std::format("enum range count of '{}' shall be a "
                                       "positive integral number",
                                       member.name));
        }
        count = n;
      }
      if (count < 1) count = 1;
    }

    if (!prev_had_xz) {
      for (int64_t i = 0; i < count; ++i) {
        if (!seen_values.insert(next_val + i).second) {
          diag_.Error(
              loc, std::format("duplicate enum member value {}", next_val + i));
        }
      }
    }

    next_val += count;
    if (!prev_had_xz && next_val > 0 &&
        static_cast<uint64_t>(next_val) > max_val &&
        &member != &dtype.enum_members.back()) {
      diag_.Error(loc,
                  "enum auto-increment exceeds maximum representable "
                  "value of base type");
    }
  }
}

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

void Elaborator::CheckEnumCallArguments(const Expr* call) {
  if (!call || call->kind != ExprKind::kCall) return;
  // Restrict to free-function calls: a member/method receiver could share a
  // name with a module function and must not be matched here.
  if (call->lhs && call->lhs->kind != ExprKind::kIdentifier) return;
  auto it = func_decls_.find(call->callee);
  if (it == func_decls_.end() || it->second == nullptr) return;
  const ModuleItem* fn = it->second;
  // Positional binding only; a named association is left for the general
  // argument-binding path and is not second-guessed by the strong-typing rule.
  for (auto name : call->arg_names) {
    if (!name.empty()) return;
  }
  size_t count = std::min(call->args.size(), fn->func_args.size());
  for (size_t i = 0; i < count; ++i) {
    const DataType& formal = fn->func_args[i].data_type;
    bool formal_is_enum = formal.kind == DataTypeKind::kEnum;
    if (!formal_is_enum && formal.kind == DataTypeKind::kNamed) {
      auto t = typedefs_.find(formal.type_name);
      formal_is_enum =
          t != typedefs_.end() && t->second.kind == DataTypeKind::kEnum;
    }
    if (!formal_is_enum) continue;
    const Expr* actual = call->args[i];
    if (!actual) continue;
    // Mirror the assignment rule: a bare name (an enum member or another enum
    // of the same family) and an explicit cast are accepted; a plain integral
    // value is rejected because it is not a member of the enumeration.
    if (actual->kind == ExprKind::kIdentifier) continue;
    if (actual->kind == ExprKind::kCast) continue;
    diag_.Error(actual->range.start,
                "integer value passed to enum argument without cast");
  }
}

void Elaborator::WalkExprForEnumCalls(const Expr* e) {
  if (!e) return;
  CheckEnumCallArguments(e);
  WalkExprForEnumCalls(e->lhs);
  WalkExprForEnumCalls(e->rhs);
  WalkExprForEnumCalls(e->condition);
  WalkExprForEnumCalls(e->true_expr);
  WalkExprForEnumCalls(e->false_expr);
  WalkExprForEnumCalls(e->base);
  WalkExprForEnumCalls(e->index);
  WalkExprForEnumCalls(e->index_end);
  for (auto* a : e->args) WalkExprForEnumCalls(a);
  for (auto* el : e->elements) WalkExprForEnumCalls(el);
}

void Elaborator::WalkStmtsForEnumAssign(const Stmt* s) {
  if (!s) return;
  WalkExprForEnumCalls(s->rhs);
  WalkExprForEnumCalls(s->expr);
  WalkExprForEnumCalls(s->condition);
  if (s->kind == StmtKind::kVarDecl) {
    bool is_enum = false;
    if (s->var_decl_type.kind == DataTypeKind::kEnum) {
      enum_var_names_.insert(s->var_name);
      is_enum = true;
    } else if (s->var_decl_type.kind == DataTypeKind::kNamed) {
      auto it = typedefs_.find(s->var_decl_type.type_name);
      if (it != typedefs_.end() && it->second.kind == DataTypeKind::kEnum) {
        enum_var_names_.insert(s->var_name);
        is_enum = true;
      }
    }
    if (is_enum && s->var_init && s->var_init->kind != ExprKind::kIdentifier &&
        s->var_init->kind != ExprKind::kCast) {
      diag_.Error(s->range.start,
                  "integer assigned to enum variable without cast");
    }
  }
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckEnumAssignStmt(s);
  }
  if (s->kind == StmtKind::kExprStmt && s->expr &&
      s->expr->kind == ExprKind::kPostfixUnary) {
    auto name = ExprIdent(s->expr->lhs);
    if (!name.empty() && enum_var_names_.count(name) != 0) {
      diag_.Error(s->range.start,
                  "increment/decrement of enum variable without cast");
    }
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
    if (item->kind == ModuleItemKind::kVarDecl &&
        enum_var_names_.count(item->name) != 0 && item->init_expr &&
        item->init_expr->kind != ExprKind::kIdentifier &&
        item->init_expr->kind != ExprKind::kCast) {
      diag_.Error(item->loc, "integer assigned to enum variable without cast");
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForEnumAssign(item->body);
    }
  }
}

void Elaborator::WalkStmtsForConstAssign(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    if (s->lhs && s->lhs->kind == ExprKind::kIdentifier) {
      if (const_names_.count(s->lhs->text)) {
        diag_.Error(s->range.start,
                    std::format("assignment to constant '{}'", s->lhs->text));
      }
    }
  }
  for (auto* sub : s->stmts) WalkStmtsForConstAssign(sub);
  WalkStmtsForConstAssign(s->then_branch);
  WalkStmtsForConstAssign(s->else_branch);
  WalkStmtsForConstAssign(s->body);
  WalkStmtsForConstAssign(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForConstAssign(ci.body);
}

void Elaborator::ValidateConstAssignments(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForConstAssign(item->body);
    }
  }
}

static uint32_t InferTypeRefExprWidth(const Expr* expr,
                                      const RtlirModule* mod) {
  if (!expr) return 0;
  switch (expr->kind) {
    case ExprKind::kIdentifier:
      for (const auto& v : mod->variables) {
        if (v.name == expr->text) return v.width;
      }
      return 0;
    case ExprKind::kIntegerLiteral:
      return ExtractLiteralWidth(expr->text);
    case ExprKind::kBinary: {
      uint32_t lw = InferTypeRefExprWidth(expr->lhs, mod);
      uint32_t rw = InferTypeRefExprWidth(expr->rhs, mod);
      return std::max(lw, rw);
    }
    case ExprKind::kTernary: {
      uint32_t tw = InferTypeRefExprWidth(expr->true_expr, mod);
      uint32_t fw = InferTypeRefExprWidth(expr->false_expr, mod);
      return std::max(tw, fw);
    }
    case ExprKind::kConcatenation: {
      uint32_t total = 0;
      for (const auto* el : expr->elements) {
        total += InferTypeRefExprWidth(el, mod);
      }
      return total;
    }
    case ExprKind::kUnary:
      return InferTypeRefExprWidth(expr->lhs, mod);
    default:
      return 0;
  }
}

static bool InferTypeRefExprSigned(const Expr* expr, const RtlirModule* mod) {
  if (!expr) return false;
  switch (expr->kind) {
    case ExprKind::kIdentifier:
      for (const auto& v : mod->variables) {
        if (v.name == expr->text) return v.is_signed;
      }
      return false;
    case ExprKind::kBinary:
      return InferTypeRefExprSigned(expr->lhs, mod) &&
             InferTypeRefExprSigned(expr->rhs, mod);
    case ExprKind::kTernary:
      return InferTypeRefExprSigned(expr->true_expr, mod) &&
             InferTypeRefExprSigned(expr->false_expr, mod);
    case ExprKind::kConcatenation:
      return false;
    case ExprKind::kUnary:
      return InferTypeRefExprSigned(expr->lhs, mod);
    default:
      return false;
  }
}

void Elaborator::ResolveTypeRef(ModuleItem* item, const RtlirModule* mod) {
  if (!item->data_type.type_ref_expr) return;
  auto* ref = item->data_type.type_ref_expr;
  CheckTypeRefArgInner(ref, item->loc);
  if (ref->kind != ExprKind::kIdentifier) {
    uint32_t w = InferTypeRefExprWidth(ref, mod);
    item->data_type.kind = DataTypeKind::kLogic;
    if (w > 1) {
      auto* left = arena_.Create<Expr>();
      left->kind = ExprKind::kIntegerLiteral;
      left->int_val = static_cast<int64_t>(w - 1);
      auto* right = arena_.Create<Expr>();
      right->kind = ExprKind::kIntegerLiteral;
      right->int_val = 0;
      item->data_type.packed_dim_left = left;
      item->data_type.packed_dim_right = right;
    }
    item->data_type.is_signed = InferTypeRefExprSigned(ref, mod);
    item->data_type.type_ref_expr = nullptr;
    return;
  }

  for (const auto& v : mod->variables) {
    if (v.name != ref->text) continue;
    item->data_type.kind = var_types_[ref->text];
    item->data_type.is_signed = v.is_signed;

    if (v.width > 1 && (item->data_type.kind == DataTypeKind::kLogic ||
                        item->data_type.kind == DataTypeKind::kBit ||
                        item->data_type.kind == DataTypeKind::kReg)) {
      auto* left = arena_.Create<Expr>();
      left->kind = ExprKind::kIntegerLiteral;
      left->int_val = static_cast<int64_t>(v.width - 1);
      auto* right = arena_.Create<Expr>();
      right->kind = ExprKind::kIntegerLiteral;
      right->int_val = 0;
      item->data_type.packed_dim_left = left;
      item->data_type.packed_dim_right = right;
    }
    item->data_type.type_ref_expr = nullptr;
    return;
  }
  auto it = var_types_.find(ref->text);
  if (it != var_types_.end()) {
    item->data_type.kind = it->second;
    item->data_type.type_ref_expr = nullptr;
  }
}

const ClassDecl* FindClassDecl(std::string_view name,
                               const CompilationUnit* unit) {
  for (const auto* cls : unit->classes) {
    if (cls->name == name) return cls;
  }
  return nullptr;
}

static const ModuleItem* FindClassTypedef(const ClassDecl* cls,
                                          std::string_view member_name) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kTypedef && m->name == member_name) {
      return m->typedef_item;
    }
  }
  return nullptr;
}

bool Elaborator::ResolveParameterizedType(DataType& dtype) {
  if (dtype.scope_name.empty() || dtype.type_params.empty()) return false;
  const auto* cls = FindClassDecl(dtype.scope_name, unit_);
  if (!cls) return false;

  std::unordered_map<std::string_view, const DataType*> subst;
  for (size_t i = 0; i < cls->params.size() && i < dtype.type_params.size();
       ++i) {
    subst[cls->params[i].first] = &dtype.type_params[i];
  }

  // The scope resolution operator applied to a specialization may name a type
  // parameter of the class directly, or a member typedef whose aliased type is
  // one of those parameters. Resolve a direct type-parameter reference first;
  // otherwise look through a member typedef to the parameter it aliases.
  std::string_view param_name = dtype.type_name;
  if (!subst.count(param_name)) {
    const auto* td = FindClassTypedef(cls, dtype.type_name);
    if (!td) return false;
    param_name = td->typedef_type.type_name;
  }

  auto it = subst.find(param_name);
  if (it == subst.end()) return false;
  const DataType& resolved = *it->second;
  dtype.kind = resolved.kind;
  dtype.is_signed = resolved.is_signed;
  dtype.packed_dim_left = resolved.packed_dim_left;
  dtype.packed_dim_right = resolved.packed_dim_right;
  dtype.extra_packed_dims = resolved.extra_packed_dims;
  dtype.type_name = resolved.type_name;
  dtype.scope_name = {};
  dtype.type_params.clear();
  return true;
}

void Elaborator::ValidatePackedStructDefaults(const DataType& dtype,
                                              SourceLoc loc) {
  if (dtype.kind != DataTypeKind::kStruct || !dtype.is_packed) return;
  for (const auto& m : dtype.struct_members) {
    if (m.init_expr) {
      diag_.Error(loc,
                  "members of packed structures shall not be assigned "
                  "individual default member values");
      return;
    }
  }
}

void Elaborator::ValidateUnpackedStructWithUnionDefaults(const DataType& dtype,
                                                         SourceLoc loc) {
  if (dtype.kind != DataTypeKind::kStruct || dtype.is_packed) return;
  bool has_union_member = false;
  for (const auto& m : dtype.struct_members) {
    if (m.type_kind == DataTypeKind::kUnion) has_union_member = true;
  }
  if (!has_union_member) return;
  for (const auto& m : dtype.struct_members) {
    if (m.init_expr) {
      diag_.Error(loc,
                  "members of unpacked structures containing a union shall "
                  "not be assigned individual default member values");
      return;
    }
  }
}

void Elaborator::ValidateStructMemberDefaultsConstant(const DataType& dtype,
                                                      SourceLoc loc) {
  if (dtype.kind != DataTypeKind::kStruct) return;

  if (dtype.is_packed) return;

  for (const auto& m : dtype.struct_members) {
    if (m.type_kind == DataTypeKind::kUnion) return;
  }
  for (const auto& m : dtype.struct_members) {
    if (m.init_expr && !IsConstantExpr(m.init_expr, cu_param_scope_)) {
      diag_.Error(loc,
                  "struct member default value must be a constant expression");
      return;
    }
  }
}

void Elaborator::ValidateVoidMembers(const DataType& dtype, SourceLoc loc) {
  bool allow_void = (dtype.kind == DataTypeKind::kUnion && dtype.is_tagged);
  for (const auto& m : dtype.struct_members) {
    if (m.type_kind == DataTypeKind::kVoid && !allow_void) {
      diag_.Error(loc, "void member is only allowed in tagged unions");
      return;
    }
  }
}

void Elaborator::ValidateRandQualifiers(const DataType& dtype, SourceLoc loc) {
  bool allow_rand = (dtype.kind == DataTypeKind::kStruct && !dtype.is_packed);
  for (const auto& m : dtype.struct_members) {
    if ((m.is_rand || m.is_randc) && !allow_rand) {
      diag_.Error(loc,
                  "random qualifier is only allowed in unpacked structures");
      return;
    }
  }
}

void Elaborator::ValidatePackedDimRequiresPackedKeyword(const DataType& dtype,
                                                        SourceLoc loc) {
  if (dtype.kind != DataTypeKind::kStruct && dtype.kind != DataTypeKind::kUnion)
    return;
  if (!dtype.packed_dim_left) return;
  if (dtype.is_packed || dtype.is_soft) return;
  const char* kw = (dtype.kind == DataTypeKind::kStruct) ? "struct" : "union";
  diag_.Error(
      loc,
      std::format("packed dimension on {} requires the packed keyword", kw));
}

static bool IsLegalPackedMemberType(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kBit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kInteger:
    case DataTypeKind::kTime:
    case DataTypeKind::kEnum:
    case DataTypeKind::kStruct:
    case DataTypeKind::kUnion:
    case DataTypeKind::kNamed:
    case DataTypeKind::kImplicit:
      return true;
    default:
      return false;
  }
}

void Elaborator::ValidatePackedStructMemberTypes(const DataType& dtype,
                                                 SourceLoc loc) {
  if (!dtype.is_packed && !dtype.is_soft) return;
  if (dtype.kind != DataTypeKind::kStruct && dtype.kind != DataTypeKind::kUnion)
    return;
  const char* container = (dtype.kind == DataTypeKind::kStruct)
                              ? "packed structure"
                              : "packed union";
  for (const auto& m : dtype.struct_members) {
    if (!IsLegalPackedMemberType(m.type_kind)) {
      diag_.Error(loc, std::format("type of member '{}' is not allowed in a {}",
                                   m.name, container));
    }
  }
}

void Elaborator::ValidateChandleInUnion(const DataType& dtype, SourceLoc loc) {
  if (dtype.kind != DataTypeKind::kUnion) return;
  if (dtype.is_tagged) return;
  for (const auto& m : dtype.struct_members) {
    if (m.type_kind == DataTypeKind::kChandle) {
      diag_.Error(loc, "chandle type can only be used in tagged unions");
      return;
    }
    if (m.type_kind == DataTypeKind::kString) {
      diag_.Error(loc, "string type can only be used in tagged unions");
      return;
    }
    if (m.type_kind == DataTypeKind::kEvent) {
      diag_.Error(loc, "event type can only be used in tagged unions");
      return;
    }
  }
}

void Elaborator::ValidateVirtualInterfaceInUnion(const DataType& dtype,
                                                 SourceLoc loc) {
  if (dtype.kind != DataTypeKind::kUnion) return;
  for (const auto& m : dtype.struct_members) {
    if (m.type_kind == DataTypeKind::kVirtualInterface) {
      diag_.Error(loc,
                  "virtual interface cannot be used as a member of a union");
      return;
    }
  }
}

void Elaborator::ValidatePackedUnion(const DataType& dtype, SourceLoc loc) {
  if (dtype.kind != DataTypeKind::kUnion) return;
  if (!dtype.is_packed && !dtype.is_soft) return;
  if (dtype.struct_members.empty()) return;

  if (!dtype.is_soft && !dtype.is_tagged) {
    uint32_t first_w = EvalStructMemberWidth(dtype.struct_members[0]);
    for (size_t i = 1; i < dtype.struct_members.size(); ++i) {
      uint32_t w = EvalStructMemberWidth(dtype.struct_members[i]);
      if (w != first_w) {
        diag_.Error(loc,
                    std::format("packed union member '{}' has width {} but "
                                "first member '{}' has width {}",
                                dtype.struct_members[i].name, w,
                                dtype.struct_members[0].name, first_w));
      }
    }
  }
}

static bool HasPredefinedWidth(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kInteger:
    case DataTypeKind::kTime:
      return true;
    default:
      return false;
  }
}

void Elaborator::ValidatePackedDimRange(const DataType& dtype, SourceLoc loc) {
  if (dtype.packed_dim_left && ExprContainsXZ(dtype.packed_dim_left)) {
    diag_.Error(loc, "packed dimension range shall not contain x or z");
  }
  if (dtype.packed_dim_right && ExprContainsXZ(dtype.packed_dim_right)) {
    diag_.Error(loc, "packed dimension range shall not contain x or z");
  }
  for (const auto& [left, right] : dtype.extra_packed_dims) {
    if (ExprContainsXZ(left) || ExprContainsXZ(right)) {
      diag_.Error(loc, "packed dimension range shall not contain x or z");
    }
  }
}

void Elaborator::ValidateUnpackedDimRange(const std::vector<Expr*>& dims,
                                          SourceLoc loc) {
  for (const auto* dim : dims) {
    if (!dim) continue;
    if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
      if (ExprContainsXZ(dim->lhs) || ExprContainsXZ(dim->rhs)) {
        diag_.Error(loc, "unpacked dimension range shall not contain x or z");
      }
    } else if (ExprContainsXZ(dim)) {
      diag_.Error(loc, "unpacked dimension range shall not contain x or z");
    }
  }
}

void Elaborator::ValidatePackedDimOnPredefinedType(const DataType& dtype,
                                                   SourceLoc loc) {
  if (!HasPredefinedWidth(dtype.kind)) return;
  if (!dtype.packed_dim_left) return;
  diag_.Error(loc,
              "integer type with predefined width shall not have packed "
              "array dimensions");
}

static bool IsAllowedPackedElementKind(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
    case DataTypeKind::kString:
    case DataTypeKind::kChandle:
    case DataTypeKind::kEvent:
    case DataTypeKind::kVoid:
    case DataTypeKind::kVirtualInterface:
      return false;
    default:
      return true;
  }
}

void Elaborator::ValidatePackedDimOnDisallowedType(const DataType& dtype,
                                                   SourceLoc loc) {
  if (!dtype.packed_dim_left) return;
  if (IsAllowedPackedElementKind(dtype.kind)) return;
  diag_.Error(loc,
              "packed array element type must be a single-bit type, "
              "enum, or packed aggregate");
}

}  // namespace delta
