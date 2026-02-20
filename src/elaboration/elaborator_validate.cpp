#include <cmath>
#include <format>
#include <optional>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaboration/const_eval.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "elaboration/type_eval.h"
#include "parser/ast.h"

namespace delta {

// §5.11: Check if an assignment pattern is a replication or named form.
static bool IsArrayPatternSpecial(const Expr* init) {
  if (init->repeat_count) return true;
  if (init->elements.size() == 1 &&
      init->elements[0]->kind == ExprKind::kReplicate)
    return true;
  return !init->pattern_keys.empty();
}

static std::optional<int64_t> ComputeDimSize(const Expr* dim) {
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
    auto left = ConstEvalInt(dim->lhs);
    auto right = ConstEvalInt(dim->rhs);
    if (left && right) return std::abs(*left - *right) + 1;
    return std::nullopt;
  }
  return ConstEvalInt(dim);
}

void Elaborator::ValidateArrayInitPattern(const ModuleItem* item) {
  if (!item->init_expr || item->unpacked_dims.empty()) return;
  if (item->init_expr->kind != ExprKind::kAssignmentPattern) return;
  if (IsArrayPatternSpecial(item->init_expr)) return;

  const auto* dim = item->unpacked_dims[0];
  if (!dim) return;
  auto dim_size = ComputeDimSize(dim);
  if (!dim_size) return;

  auto count = static_cast<int64_t>(item->init_expr->elements.size());
  if (count != *dim_size) {
    diag_.Error(item->loc,
                std::format("assignment pattern has {} elements, but array "
                            "dimension requires {}",
                            count, *dim_size));
  }
}

// §10.9.2: Type key strings that are valid in assignment patterns.
static bool IsTypeKeyword(std::string_view key) {
  return key == "int" || key == "integer" || key == "logic" || key == "reg" ||
         key == "byte" || key == "shortint" || key == "longint" ||
         key == "bit" || key == "real" || key == "shortreal" || key == "string";
}

static void CheckPatternKeys(const ModuleItem* item,
                             const std::vector<StructMember>& members,
                             DiagEngine& diag) {
  std::unordered_set<std::string_view> member_names;
  for (const auto& m : members) member_names.insert(m.name);
  std::unordered_set<std::string_view> seen;
  for (auto key : item->init_expr->pattern_keys) {
    if (key == "default" || IsTypeKeyword(key)) continue;
    if (!member_names.count(key)) {
      diag.Error(item->loc,
                 std::format("'{}' is not a member of the struct", key));
    }
    if (!seen.insert(key).second) {
      diag.Error(item->loc,
                 std::format("duplicate member key '{}' in pattern", key));
    }
  }
}

void Elaborator::ValidateStructInitPattern(const ModuleItem* item) {
  if (!item->init_expr) return;
  if (item->init_expr->kind != ExprKind::kAssignmentPattern) return;
  if (item->init_expr->pattern_keys.empty()) return;
  const auto& members = item->data_type.struct_members;
  if (!members.empty()) {
    CheckPatternKeys(item, members, diag_);
    return;
  }
  if (item->data_type.kind != DataTypeKind::kNamed) return;
  auto td = typedefs_.find(item->data_type.type_name);
  if (td == typedefs_.end() || td->second.struct_members.empty()) return;
  CheckPatternKeys(item, td->second.struct_members, diag_);
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

static bool IsChandleVar(const Expr* e, const TypeMap& types) {
  auto name = ExprIdent(e);
  if (name.empty()) return false;
  auto it = types.find(name);
  return it != types.end() && it->second == DataTypeKind::kChandle;
}

void Elaborator::ValidateChandleContAssign(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kContAssign) return;
  if (IsChandleVar(item->assign_lhs, var_types_) ||
      IsChandleVar(item->assign_rhs, var_types_)) {
    diag_.Error(item->loc, "chandle cannot be used in continuous assignment");
  }
}

void Elaborator::ValidateChandleSensitivity(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kAlwaysBlock) return;
  for (const auto& ev : item->sensitivity) {
    if (IsChandleVar(ev.signal, var_types_)) {
      diag_.Error(item->loc, "chandle cannot appear in event expression");
    }
  }
}

// §6.6.8: interconnect nets cannot appear in continuous assignments.
void Elaborator::ValidateInterconnectContAssign(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kContAssign) return;
  if (!item->assign_lhs || item->assign_lhs->kind != ExprKind::kIdentifier) {
    return;
  }
  if (interconnect_names_.count(item->assign_lhs->text)) {
    diag_.Error(item->loc,
                "interconnect net cannot be used in continuous assignment");
  }
}

void Elaborator::ValidateItemConstraints(const ModuleItem* item) {
  bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                 item->kind == ModuleItemKind::kInitialBlock;
  if (is_proc && item->body) {
    CollectProcTargets(item->body, proc_assign_targets_);
  }
  ValidateEdgeOnReal(item);
  ValidateChandleContAssign(item);
  ValidateChandleSensitivity(item);
  ValidateInterconnectContAssign(item);
  if (item->kind == ModuleItemKind::kContAssign) {
    CheckRealSelect(item->assign_rhs, var_types_, diag_);
    // §10.3.4: (highz0, highz1) and (highz1, highz0) are illegal.
    if (item->drive_strength0 == 1 && item->drive_strength1 == 1) {
      diag_.Error(item->loc,
                  "drive strength (highz0, highz1) is illegal");
    }
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

// §13.4.1/§13.4.4: Check function body for illegal return/fork constructs.
static void CheckFuncBodyStmt(const Stmt* s, bool is_void, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kReturn && s->expr && is_void) {
    diag.Error(s->range.start, "void function returns a value");
  }
  if (s->kind == StmtKind::kFork && s->join_kind != TokenKind::kKwJoinNone) {
    diag.Error(s->range.start,
               "only fork/join_none is permitted inside a function");
  }
  for (auto* sub : s->stmts) CheckFuncBodyStmt(sub, is_void, diag);
  CheckFuncBodyStmt(s->then_branch, is_void, diag);
  CheckFuncBodyStmt(s->else_branch, is_void, diag);
  CheckFuncBodyStmt(s->body, is_void, diag);
  CheckFuncBodyStmt(s->for_body, is_void, diag);
  for (auto& ci : s->case_items) CheckFuncBodyStmt(ci.body, is_void, diag);
}

void Elaborator::ValidateFunctionBody(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kFunctionDecl) return;
  bool is_void = (item->return_type.kind == DataTypeKind::kVoid);
  for (auto* s : item->func_body_stmts) {
    CheckFuncBodyStmt(s, is_void, diag_);
  }
}

void Elaborator::ValidateModuleConstraints(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    ValidateItemConstraints(item);
  }
  ValidateMixedAssignments();
  ValidateSpecparamInParams(decl);
  ValidateEnumAssignments(decl);
  ValidateConstAssignments(decl);
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
static const ClassDecl* FindClassDecl(std::string_view name,
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

}  // namespace delta
