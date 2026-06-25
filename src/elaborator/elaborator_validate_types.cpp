#include <cmath>
#include <format>
#include <functional>
#include <initializer_list>
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

static void CheckModuleTimescaleOrder(const ModuleDecl* decl,
                                      DiagEngine& diag) {
  if (!decl->has_timeunit || !decl->has_timeprecision) return;
  int unit_order =
      EffectiveTimeOrder(decl->time_unit, decl->time_unit_magnitude);
  int prec_order =
      EffectiveTimeOrder(decl->time_prec, decl->time_prec_magnitude);
  if (prec_order > unit_order) {
    diag.Error(decl->range.start,
               "time precision is less precise than the time unit");
  }
}

void Elaborator::ValidateModuleConstraints(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    ValidateItemConstraints(item);
  }
  // The bulk of module-level validation is an ordered series of independent
  // single-element checks. Two of them inspect elaborator-wide state rather
  // than the module declaration and must run in their original positions, so
  // the dispatch is driven by an ordered table of pointer-to-member checks; a
  // null decl-check entry is the cursor for the next no-argument check. This
  // keeps the dispatch (and its exact execution order) in one place while
  // staying well under the per-function statement budget.
  using DeclCheck = void (Elaborator::*)(const ModuleDecl*);
  using PlainCheck = void (Elaborator::*)();
  static constexpr DeclCheck kDeclChecks[] = {
      &Elaborator::ValidatePackageImportRules,
      &Elaborator::ValidateScopeRules,
      nullptr,  // ValidateMixedAssignments
      &Elaborator::ValidateInputPortAssignments,
      &Elaborator::ValidateMatchesPatternIntegral,
      &Elaborator::ValidateMatchesCaseSelectorType,
      &Elaborator::ValidateMatchesIfPredicateType,
      &Elaborator::ValidateDisableTargets,
      nullptr,  // ValidateProceduralNetAssign
      &Elaborator::ValidateDynamicArrayNba,
      &Elaborator::ValidateArrayQueryOnDynamicType,
      &Elaborator::ValidateArrayQueryOnVariableDim,
      &Elaborator::ValidateRandomSeedType,
      &Elaborator::ValidatePlaOutputTerms,
      &Elaborator::ValidatePlaAscendingOrder,
      &Elaborator::ValidateBitsCallRestrictions,
      &Elaborator::ValidateAutomaticVarProcWrites,
      &Elaborator::ValidateJumpStatements,
      &Elaborator::ValidateForeachLoops,
      &Elaborator::ValidateContAssignConstSelect,
      &Elaborator::ValidatePartSelectBounds,
      &Elaborator::ValidateSpecparamInParams,
      &Elaborator::ValidateSpecparamInDeclRange,
      &Elaborator::ValidateEnumAssignments,
      &Elaborator::ValidateConstAssignments,
      &Elaborator::ValidateArrayAssignments,
      &Elaborator::ValidateAssocArraySlices,
      &Elaborator::ValidateAssocWildcardTraversal,
      &Elaborator::ValidateAssocTraversalArgType,
      &Elaborator::ValidateArrayOrderingMethods,
      &Elaborator::ValidateClassIndexSelect,
      &Elaborator::ValidateStringIndexSelect,
      &Elaborator::ValidateIntegralIndexSelect,
      &Elaborator::ValidateAssocConcatTarget,
      &Elaborator::ValidateAssocOperandInExpr,
      &Elaborator::ValidateArrayPatternElemType,
      &Elaborator::ValidateReplicateTargetingArray,
      &Elaborator::ValidateArrayElementPartSelect,
      &Elaborator::ValidateUnpackedArrayConcatNesting,
      &Elaborator::ValidateClassHandleOps,
      &Elaborator::ValidateChandleOps,
      &Elaborator::ValidateVirtualInterfaceOps,
      &Elaborator::ValidateEventOps,
      &Elaborator::ValidateVirtualInterfaceClocking,
      &Elaborator::ValidateInterfaceObjectAccess,
      &Elaborator::ValidateDeferredAssertionActions,
      &Elaborator::ValidateAggregateComparisons,
      &Elaborator::ValidateTypeRefComparisons,
      &Elaborator::ValidateTypeRefArgs,
      &Elaborator::ValidateTaggedUnionMembers,
      &Elaborator::ValidateRealOperatorRestrictions,
      &Elaborator::ValidateAssignInExprRestrictions,
      &Elaborator::ValidateUnsizedInConcat,
      &Elaborator::ValidateSelectOnConcatLvalue,
      &Elaborator::ValidateReplicateLvalue,
      &Elaborator::ValidateStringConcatLvalue,
      &Elaborator::ValidateReplicateMultiplier,
      &Elaborator::ValidateStreamingConcatContext,
      &Elaborator::ValidateBitStreamCast,
      &Elaborator::ValidateSubroutineCallArgs,
      &Elaborator::ValidateArrayArgTypes,
      &Elaborator::ValidateLocalProtectedAccess,
      &Elaborator::ValidateParameterizedScopeResolution,
      &Elaborator::ValidateTypeParamScopeUsage,
      &Elaborator::ValidateTypeParamScopePrefixResolvesToClass,
      &Elaborator::ValidateStaticMethodBodies,
      &Elaborator::ValidateClassMethodBodies,
      &Elaborator::ValidateThisUsage,
  };
  // No-argument checks, consumed in order at each null table entry.
  static constexpr PlainCheck kPlainChecks[] = {
      &Elaborator::ValidateMixedAssignments,
      &Elaborator::ValidateProceduralNetAssign,
  };
  size_t plain_idx = 0;
  for (DeclCheck check : kDeclChecks) {
    if (check) {
      (this->*check)(decl);
    } else {
      (this->*kPlainChecks[plain_idx++])();
    }
  }
  CheckModuleTimescaleOrder(decl, diag_);
}

namespace {

// State for the §3.14.2.3 timescale-consistency scan: the compilation-unit
// fallback timescale (used when a design element omits its own) plus the
// running record of whether any element was fully specified or unspecified.
struct TimescaleScan {
  bool cu_fallback_unit = false;
  bool cu_fallback_prec = false;
  bool any_specified = false;
  bool any_unspecified = false;
  SourceLoc unspecified_loc;
};

void ClassifyTimescaleElement(bool el_has_unit, bool el_has_prec, SourceLoc loc,
                              TimescaleScan& scan) {
  bool has_unit = el_has_unit || scan.cu_fallback_unit;
  bool has_prec = el_has_prec || scan.cu_fallback_prec;
  if (has_unit && has_prec) {
    scan.any_specified = true;
  } else {
    if (!scan.any_unspecified) scan.unspecified_loc = loc;
    scan.any_unspecified = true;
  }
}

}  // namespace

void Elaborator::ValidateTimescaleConsistency() {
  TimescaleScan scan;
  scan.cu_fallback_unit =
      unit_->has_preproc_timescale || unit_->has_cu_timeunit;
  scan.cu_fallback_prec =
      unit_->has_preproc_timescale || unit_->has_cu_timeprecision;
  auto inspect = [&](bool el_has_unit, bool el_has_prec, SourceLoc loc) {
    ClassifyTimescaleElement(el_has_unit, el_has_prec, loc, scan);
  };

  for (const auto* mod : unit_->modules)
    inspect(mod->has_timeunit, mod->has_timeprecision, mod->range.start);
  for (const auto* iface : unit_->interfaces)
    inspect(iface->has_timeunit, iface->has_timeprecision, iface->range.start);
  for (const auto* prog : unit_->programs)
    inspect(prog->has_timeunit, prog->has_timeprecision, prog->range.start);

  if (scan.any_specified && scan.any_unspecified) {
    diag_.Error(scan.unspecified_loc,
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

static void CheckEnumBaseType(const DataType& dtype, SourceLoc loc,
                              const TypedefMap& typedefs, DiagEngine& diag) {
  if (dtype.enum_base_name.empty()) return;
  auto it = typedefs.find(dtype.enum_base_name);
  if (it == typedefs.end()) return;
  auto k = it->second.kind;
  bool integer_atom = k == DataTypeKind::kByte ||
                      k == DataTypeKind::kShortint || k == DataTypeKind::kInt ||
                      k == DataTypeKind::kLongint ||
                      k == DataTypeKind::kInteger || k == DataTypeKind::kTime;
  bool integer_vector = k == DataTypeKind::kLogic || k == DataTypeKind::kReg ||
                        k == DataTypeKind::kBit;
  if (!integer_atom && !integer_vector) {
    diag.Error(loc, std::format("enum base type '{}' is not an "
                                "integer_atom_type or integer_vector_type",
                                dtype.enum_base_name));
  } else if (integer_atom && dtype.packed_dim_left != nullptr) {
    diag.Error(loc, std::format("packed dimension not permitted on enum base "
                                "type '{}' that denotes an integer_atom_type",
                                dtype.enum_base_name));
  }
}

static void CheckEnumMemberName(
    const EnumMember& member, SourceLoc loc,
    std::unordered_set<std::string_view>& seen_names,
    const std::unordered_set<std::string_view>& declared, DiagEngine& diag) {
  if (member.range_start) return;
  if (!seen_names.insert(member.name).second) {
    diag.Error(loc,
               std::format("duplicate enum member name '{}'", member.name));
  } else if (declared.count(member.name)) {
    diag.Error(loc, std::format("enum member name '{}' is already declared "
                                "in this scope",
                                member.name));
  }
}

static void CheckEnumMemberValueRefs(
    const EnumMember& member,
    const std::unordered_set<std::string_view>& const_names, DiagEngine& diag) {
  if (!member.value) return;
  if (ExprContainsHierarchicalRef(member.value)) {
    diag.Error(member.value->range.start,
               "hierarchical name not allowed in enum named constant "
               "value");
  }
  auto const_name = FindConstVarRef(member.value, const_names);
  if (!const_name.empty()) {
    diag.Error(member.value->range.start,
               std::format("const variable '{}' not allowed in enum named "
                           "constant value",
                           const_name));
  }
}

static int64_t ComputeEnumRangeCount(const EnumMember& member, SourceLoc loc,
                                     DiagEngine& diag) {
  if (!member.range_start) return 1;
  auto n = ConstEvalInt(member.range_start).value_or(0);
  int64_t count = 1;
  if (member.range_end) {
    auto m = ConstEvalInt(member.range_end).value_or(0);
    // Table 6-10: for the name[N:M] form, both bounds shall be
    // non-negative integral numbers.
    if (n < 0 || m < 0) {
      diag.Error(loc, std::format("enum range bounds of '{}' shall be "
                                  "non-negative integral numbers",
                                  member.name));
    }
    count = (m >= n) ? (m - n + 1) : (n - m + 1);
  } else {
    // Table 6-10: for the name[N] form, N shall be a positive integral
    // number.
    if (n < 1) {
      diag.Error(loc, std::format("enum range count of '{}' shall be a "
                                  "positive integral number",
                                  member.name));
    }
    count = n;
  }
  return count < 1 ? 1 : count;
}

// Representable range of an enum base type (§6.19, Table 6-10).
struct EnumBaseRange {
  bool is_signed = false;
  uint32_t base_width = 0;
  uint64_t max_val = 0;
  int64_t signed_min = 0;
};

static EnumBaseRange ComputeEnumBaseRange(const DataType& dtype,
                                          uint32_t base_width) {
  EnumBaseRange range;
  range.is_signed = dtype.is_signed;
  range.base_width = base_width;
  range.max_val =
      dtype.is_signed
          ? (base_width > 0 ? (1ULL << (base_width - 1)) - 1 : 0)
          : (base_width < 64 ? (1ULL << base_width) - 1 : UINT64_MAX);
  range.signed_min = (dtype.is_signed && base_width > 0 && base_width < 64)
                         ? -(1LL << (base_width - 1))
                         : INT64_MIN;
  return range;
}

static bool EnumValueOutOfRange(int64_t v, const EnumBaseRange& range) {
  if (range.is_signed) {
    return v < range.signed_min || v > static_cast<int64_t>(range.max_val);
  }
  return v < 0 ||
         (range.base_width < 64 && static_cast<uint64_t>(v) > range.max_val);
}

static void CheckEnumDuplicateValues(int64_t start, int64_t count,
                                     std::unordered_set<int64_t>& seen,
                                     SourceLoc loc, DiagEngine& diag) {
  for (int64_t i = 0; i < count; ++i) {
    if (!seen.insert(start + i).second) {
      diag.Error(loc, std::format("duplicate enum member value {}", start + i));
    }
  }
}

// Const-evaluates an explicitly-valued enum member, reports an out-of-range
// value, and updates the running auto-increment cursor. Called only after the
// member's literal width/x-z checks have passed.
static void CheckEnumMemberValueInRange(const EnumMember& member,
                                        const EnumBaseRange& range,
                                        int64_t& next_val, DiagEngine& diag) {
  auto v = ConstEvalInt(member.value);
  if (!v) return;
  if (EnumValueOutOfRange(*v, range)) {
    diag.Error(member.value->range.start,
               std::format("enum member '{}' value {} is outside the "
                           "representable range of the base type",
                           member.name, *v));
  }
  next_val = *v;
}

void Elaborator::ValidateEnumDecl(const DataType& dtype, SourceLoc loc) {
  CheckEnumBaseType(dtype, loc, typedefs_, diag_);
  auto base_width = EvalTypeWidth(dtype, typedefs_);
  bool is_2state = !Is4stateType(dtype, typedefs_);
  bool prev_had_xz = false;
  EnumBaseRange range = ComputeEnumBaseRange(dtype, base_width);
  std::unordered_set<std::string_view> seen_names;
  std::unordered_set<int64_t> seen_values;
  int64_t next_val = 0;
  for (const auto& member : dtype.enum_members) {
    CheckEnumMemberName(member, loc, seen_names, enum_member_names_, diag_);
    CheckEnumMemberValueRefs(member, const_var_names_, diag_);
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
        CheckEnumMemberValueInRange(member, range, next_val, diag_);
      }
    }
    int64_t count = ComputeEnumRangeCount(member, loc, diag_);
    if (!prev_had_xz) {
      CheckEnumDuplicateValues(next_val, count, seen_values, loc, diag_);
    }
    next_val += count;
    if (!prev_had_xz && next_val > 0 &&
        static_cast<uint64_t>(next_val) > range.max_val &&
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

// §6.19.5/§6.19.6: the first, last, next, and prev enumeration methods return a
// value of the same enumeration type, so assigning their result to an enum
// variable requires no cast. Recognizes both the no-parens member access
// (c.next) and the explicit call form (c.next()). The num/name methods return
// int/string and are intentionally excluded.
static bool IsEnumTypedMethodResult(const Expr* e) {
  if (!e) return false;
  const Expr* member = e;
  if (e->kind == ExprKind::kCall && e->lhs &&
      e->lhs->kind == ExprKind::kMemberAccess) {
    member = e->lhs;
  }
  if (member->kind != ExprKind::kMemberAccess) return false;
  if (!member->rhs || member->rhs->kind != ExprKind::kIdentifier) return false;
  std::string_view m = member->rhs->text;
  return m == "first" || m == "last" || m == "next" || m == "prev";
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
  if (IsEnumTypedMethodResult(s->rhs)) return;
  diag_.Error(s->range.start, "integer assigned to enum variable without cast");
}

static bool FormalIsEnumType(const DataType& formal,
                             const TypedefMap& typedefs) {
  if (formal.kind == DataTypeKind::kEnum) return true;
  if (formal.kind != DataTypeKind::kNamed) return false;
  auto t = typedefs.find(formal.type_name);
  return t != typedefs.end() && t->second.kind == DataTypeKind::kEnum;
}

static bool CallUsesNamedArgs(const Expr* call) {
  // Positional binding only; a named association is left for the general
  // argument-binding path and is not second-guessed by the strong-typing rule.
  for (auto name : call->arg_names) {
    if (!name.empty()) return true;
  }
  return false;
}

static void CheckEnumActualArg(const Expr* actual, DiagEngine& diag) {
  if (!actual) return;
  // Mirror the assignment rule: a bare name (an enum member or another enum
  // of the same family) and an explicit cast are accepted; a plain integral
  // value is rejected because it is not a member of the enumeration.
  if (actual->kind == ExprKind::kIdentifier) return;
  if (actual->kind == ExprKind::kCast) return;
  diag.Error(actual->range.start,
             "integer value passed to enum argument without cast");
}

void Elaborator::CheckEnumCallArguments(const Expr* call) {
  if (!call || call->kind != ExprKind::kCall) return;
  // Restrict to free-function calls: a member/method receiver could share a
  // name with a module function and must not be matched here.
  if (call->lhs && call->lhs->kind != ExprKind::kIdentifier) return;
  auto it = func_decls_.find(call->callee);
  if (it == func_decls_.end() || it->second == nullptr) return;
  const ModuleItem* fn = it->second;
  if (CallUsesNamedArgs(call)) return;
  size_t count = std::min(call->args.size(), fn->func_args.size());
  for (size_t i = 0; i < count; ++i) {
    if (!FormalIsEnumType(fn->func_args[i].data_type, typedefs_)) continue;
    CheckEnumActualArg(call->args[i], diag_);
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

// True when a data type denotes an enumeration, either directly or via a
// typedef name.
static bool DataTypeIsEnum(const DataType& dtype, const TypedefMap& typedefs) {
  if (dtype.kind == DataTypeKind::kEnum) return true;
  if (dtype.kind != DataTypeKind::kNamed) return false;
  auto it = typedefs.find(dtype.type_name);
  return it != typedefs.end() && it->second.kind == DataTypeKind::kEnum;
}

// An initializer/RHS that is acceptable for an enum target without a cast:
// a bare name (enum member or sibling enum) or an explicit cast.
static bool IsBareEnumAssignable(const Expr* e) {
  return e && (e->kind == ExprKind::kIdentifier || e->kind == ExprKind::kCast);
}

namespace {

// True when a procedural statement declares an enum variable (Stmt-level
// var_decl) — used to register the name and screen its initializer.
bool StmtDeclaresEnumVar(const Stmt* s, const TypedefMap& typedefs) {
  return s->kind == StmtKind::kVarDecl &&
         DataTypeIsEnum(s->var_decl_type, typedefs);
}

// True when a statement is a blocking or nonblocking assignment.
bool StmtIsProceduralAssign(const Stmt* s) {
  return s->kind == StmtKind::kBlockingAssign ||
         s->kind == StmtKind::kNonblockingAssign;
}

// True when a statement is a bare ++/-- expression statement.
bool StmtIsPostfixIncDec(const Stmt* s) {
  return s->kind == StmtKind::kExprStmt && s->expr &&
         s->expr->kind == ExprKind::kPostfixUnary;
}

// Reports an unguarded ++/-- on an enum variable (callers ensure the statement
// is a postfix unary expression statement).
void CheckEnumIncDecStmt(const Stmt* s,
                         const std::unordered_set<std::string_view>& enum_vars,
                         DiagEngine& diag) {
  auto name = ExprIdent(s->expr->lhs);
  if (!name.empty() && enum_vars.count(name) != 0) {
    diag.Error(s->range.start,
               "increment/decrement of enum variable without cast");
  }
}

}  // namespace

void Elaborator::WalkStmtsForEnumAssign(const Stmt* s) {
  if (!s) return;
  WalkExprForEnumCalls(s->rhs);
  WalkExprForEnumCalls(s->expr);
  WalkExprForEnumCalls(s->condition);
  if (StmtDeclaresEnumVar(s, typedefs_)) {
    enum_var_names_.insert(s->var_name);
    if (s->var_init && !IsBareEnumAssignable(s->var_init)) {
      diag_.Error(s->range.start,
                  "integer assigned to enum variable without cast");
    }
  } else if (StmtIsProceduralAssign(s)) {
    CheckEnumAssignStmt(s);
  } else if (StmtIsPostfixIncDec(s)) {
    CheckEnumIncDecStmt(s, enum_var_names_, diag_);
  }
  for (const Stmt* branch :
       {s->then_branch, s->else_branch, s->body, s->for_body}) {
    WalkStmtsForEnumAssign(branch);
  }
  for (auto* sub : s->stmts) WalkStmtsForEnumAssign(sub);
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
