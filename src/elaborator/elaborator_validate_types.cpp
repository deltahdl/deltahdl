#include <cmath>
#include <format>
#include <optional>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

void Elaborator::ValidateModuleConstraints(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    ValidateItemConstraints(item);
  }
  ValidateMixedAssignments();
  ValidateProceduralNetAssign();
  ValidateContAssignConstSelect(decl);
  ValidateSpecparamInParams(decl);
  ValidateEnumAssignments(decl);
  ValidateConstAssignments(decl);
  ValidateArrayAssignments(decl);
  ValidateUnpackedArrayConcatNesting(decl);
  ValidateClassHandleOps(decl);
  ValidateChandleOps(decl);
  ValidateAggregateComparisons(decl);
  ValidateRealOperatorRestrictions(decl);
  ValidateAssignInExprRestrictions(decl);
  ValidateSubroutineCallArgs(decl);
  ValidateLocalProtectedAccess(decl);
  ValidateStaticMethodBodies(decl);
  ValidateThisUsage(decl);
  // §3.14: Precision shall be at least as precise as the time unit.
  if (decl->has_timeunit && decl->has_timeprecision) {
    if (static_cast<int>(decl->time_prec) > static_cast<int>(decl->time_unit)) {
      diag_.Error(decl->range.start,
                  "time precision is less precise than the time unit");
    }
  }
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

  // §6.19: Compute max representable value for overflow detection.
  uint64_t max_val = dtype.is_signed
                         ? (base_width > 0 ? (1ULL << (base_width - 1)) - 1 : 0)
                         : (base_width < 64 ? (1ULL << base_width) - 1
                                            : UINT64_MAX);

  std::unordered_set<std::string_view> seen_names;
  std::unordered_set<int64_t> seen_values;
  int64_t next_val = 0;

  for (const auto& member : dtype.enum_members) {
    // §6.19: Enum member names shall be unique.
    if (!seen_names.insert(member.name).second) {
      diag_.Error(loc,
                  std::format("duplicate enum member name '{}'", member.name));
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
        if (v) next_val = *v;
      }
    }

    // §6.19: Enum member values shall be unique.
    if (!prev_had_xz) {
      if (!seen_values.insert(next_val).second) {
        diag_.Error(loc,
                    std::format("duplicate enum member value {}", next_val));
      }
    }

    // §6.19: Auto-increment past max representable value is an error.
    ++next_val;
    if (!prev_had_xz && next_val > 0 &&
        static_cast<uint64_t>(next_val) > max_val &&
        &member != &dtype.enum_members.back()) {
      diag_.Error(loc, "enum auto-increment exceeds maximum representable "
                       "value of base type");
    }
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

// --- §6.20.6: Const assignment validation ---

void Elaborator::WalkStmtsForConstAssign(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    if (s->lhs && s->lhs->kind == ExprKind::kIdentifier) {
      if (const_names_.count(s->lhs->text)) {
        diag_.Error(
            s->range.start,
            std::format("assignment to const variable '{}'", s->lhs->text));
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

// --- Type resolution (§6.23, §6.25) ---

void Elaborator::ResolveTypeRef(ModuleItem* item, const RtlirModule* mod) {
  if (!item->data_type.type_ref_expr) return;
  auto* ref = item->data_type.type_ref_expr;
  if (ref->kind != ExprKind::kIdentifier) {
    // For complex expressions, infer width from expression.
    item->data_type.kind = DataTypeKind::kLogic;
    item->data_type.type_ref_expr = nullptr;
    return;
  }
  // Look up the referenced variable's type in the module.
  for (const auto& v : mod->variables) {
    if (v.name != ref->text) continue;
    item->data_type.kind = var_types_[ref->text];
    item->data_type.is_signed = v.is_signed;
    item->data_type.type_ref_expr = nullptr;
    return;
  }
  auto it = var_types_.find(ref->text);
  if (it != var_types_.end()) {
    item->data_type.kind = it->second;
    item->data_type.type_ref_expr = nullptr;
  }
}

// §6.25: Find a ClassDecl by name in the compilation unit.
const ClassDecl* FindClassDecl(std::string_view name,
                               const CompilationUnit* unit) {
  for (const auto* cls : unit->classes) {
    if (cls->name == name) return cls;
  }
  return nullptr;
}

// §6.25: Find a typedef member inside a class declaration.
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
  const auto* td = FindClassTypedef(cls, dtype.type_name);
  if (!td) return false;
  // Build substitution map: param_name → provided type.
  std::unordered_map<std::string_view, const DataType*> subst;
  for (size_t i = 0; i < cls->params.size() && i < dtype.type_params.size();
       ++i) {
    subst[cls->params[i].first] = &dtype.type_params[i];
  }
  // The typedef references a type parameter (e.g. typedef T my_type).
  auto it = subst.find(td->typedef_type.type_name);
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

// §7.2.2: Packed struct members shall not have individual default values.
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

// §7.2.2: Members of unpacked structures containing a union shall not be
// assigned individual default member values.
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

// §7.2, footnote 20: void struct_union_member only within tagged unions.
void Elaborator::ValidateVoidMembers(const DataType& dtype, SourceLoc loc) {
  bool allow_void = (dtype.kind == DataTypeKind::kUnion && dtype.is_tagged);
  for (const auto& m : dtype.struct_members) {
    if (m.type_kind == DataTypeKind::kVoid && !allow_void) {
      diag_.Error(loc, "void member is only allowed in tagged unions");
      return;
    }
  }
}

// §7.2, footnote 20: random_qualifier only within unpacked structures.
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

// §7.2.1: Only packed data types and integer data types shall be legal in
// packed structures.
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

// §7.3: Dynamic types and chandle types can only be used in tagged unions.
void Elaborator::ValidateChandleInUnion(const DataType& dtype, SourceLoc loc) {
  if (dtype.kind != DataTypeKind::kUnion) return;
  if (dtype.is_tagged) return;
  for (const auto& m : dtype.struct_members) {
    if (m.type_kind == DataTypeKind::kChandle) {
      diag_.Error(loc, "chandle type can only be used in tagged unions");
      return;
    }
  }
}

// §7.3.1: Validate packed union member constraints.
void Elaborator::ValidatePackedUnion(const DataType& dtype, SourceLoc loc) {
  if (dtype.kind != DataTypeKind::kUnion) return;
  if (!dtype.is_packed && !dtype.is_soft) return;
  if (dtype.struct_members.empty()) return;

  // Hard packed union: all members must be the same width.
  if (!dtype.is_soft) {
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

// §7.4.1: Integer types with predefined widths shall not have packed array
// dimensions.
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

void Elaborator::ValidatePackedDimOnPredefinedType(const DataType& dtype,
                                                   SourceLoc loc) {
  if (!HasPredefinedWidth(dtype.kind)) return;
  if (!dtype.packed_dim_left) return;
  diag_.Error(loc,
              "integer type with predefined width shall not have packed "
              "array dimensions");
}

}  // namespace delta
