#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_array_shape.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/index_value_kind.h"
#include "elaborator/net_data_type.h"
#include "elaborator/queue_dim.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// §7.4/§7.8 — the two array operands of a single assignment: the left-hand and
// right-hand tracked arrays (`l`/`r`) together with the identifier expressions
// that named them (`lhs`/`rhs`) and the source location of the assignment. The
// shape/element compatibility checks all act on this one assignment entity, so
// they take it as a unit rather than threading the five values separately.
struct ArrayAssignPair {
  const Elaborator::VarArrayInfo& l;
  const Elaborator::VarArrayInfo& r;
  const Expr* lhs;
  const Expr* rhs;
  SourceLoc loc;
};

// True when both tracked arrays are fixed-size, equally ranked, and have more
// than one unpacked dimension -- the precondition for a faster-varying
// dimension size comparison.
bool BothFixedMultiDim(const Elaborator::VarArrayInfo& l,
                       const Elaborator::VarArrayInfo& r) {
  return !l.is_dynamic && !r.is_dynamic && !l.is_assoc && !r.is_assoc &&
         l.dim_sizes.size() == r.dim_sizes.size() && l.dim_sizes.size() > 1;
}

// Emits the faster-varying dimension size-mismatch diagnostic for dimension
// `i` of the two tracked arrays.
void ReportFasterVaryingDimMismatchAt(const ArrayAssignPair& p, size_t i,
                                      DiagEngine& diag) {
  diag.Error(p.loc,
             std::format("faster-varying array dimension size mismatch in "
                         "assignment ('{}' dim {} is {}, '{}' dim {} is {})",
                         p.lhs->text, i, p.l.dim_sizes[i], p.rhs->text, i,
                         p.r.dim_sizes[i]),
             Subclause("7.6"));
}

// Reports the first faster-varying (non-leftmost) unpacked dimension whose
// size differs between the two fixed-size arrays. Returns true (with a
// diagnostic emitted) when a mismatch is found, mirroring the early return of
// the caller.
bool ReportFasterVaryingDimMismatch(const ArrayAssignPair& p,
                                    DiagEngine& diag) {
  if (!BothFixedMultiDim(p.l, p.r)) return false;
  for (size_t i = 1; i < p.l.dim_sizes.size(); ++i) {
    if (p.l.dim_sizes[i] != p.r.dim_sizes[i]) {
      ReportFasterVaryingDimMismatchAt(p, i, diag);
      return true;
    }
  }
  return false;
}

// §7.6 — the slowest-varying (leftmost) dimension of a dynamic array or queue
// may differ in kind and its size is not known until run time, but every
// faster-varying dimension shall still meet the §6.22.2 equivalence
// requirement, which for a fixed dimension means an identical declared size.
// The leftmost dynamic/queue dimension contributes no entry to `dim_sizes`, so
// when both arrays have a dynamic/queue leftmost dimension backed by a full
// complement of fixed faster dimensions, `dim_sizes` holds exactly those faster
// dimensions and comparing the two vectors element-wise enforces the rule for
// that declaration shape. The both-fixed shape is handled separately, and the
// leftmost dimension is intentionally left uncompared here.
bool ReportFasterVaryingDimMismatchVarOuter(const ArrayAssignPair& p,
                                            DiagEngine& diag) {
  const Elaborator::VarArrayInfo& l = p.l;
  const Elaborator::VarArrayInfo& r = p.r;
  bool l_var_outer = (l.is_dynamic || l.is_queue) && !l.is_assoc;
  bool r_var_outer = (r.is_dynamic || r.is_queue) && !r.is_assoc;
  if (!l_var_outer || !r_var_outer) return false;
  if (l.num_unpacked_dims != r.num_unpacked_dims) return false;
  if (l.num_unpacked_dims < 2) return false;
  if (l.dim_sizes.size() != l.num_unpacked_dims - 1) return false;
  if (r.dim_sizes.size() != r.num_unpacked_dims - 1) return false;
  for (size_t i = 0; i < l.dim_sizes.size(); ++i) {
    if (l.dim_sizes[i] != r.dim_sizes[i]) {
      diag.Error(
          p.loc,
          std::format("faster-varying array dimension size mismatch in "
                      "assignment ('{}' dim {} is {}, '{}' dim {} is {})",
                      p.lhs->text, i + 1, l.dim_sizes[i], p.rhs->text, i + 1,
                      r.dim_sizes[i]),
          Subclause("7.6"));
      return true;
    }
  }
  return false;
}

// Reports an associativity / associative-index-type mismatch between two
// tracked arrays. Returns true (with a diagnostic emitted) when found.
bool ReportAssocKindMismatch(const Elaborator::VarArrayInfo& l,
                             const Elaborator::VarArrayInfo& r, SourceLoc loc,
                             DiagEngine& diag) {
  if (l.is_assoc != r.is_assoc) {
    diag.Error(loc,
               "associative array cannot be assigned to or from a "
               "non-associative array",
               Subclause("7.9.9"));
    return true;
  }
  if (l.is_assoc && r.is_assoc && l.assoc_index_type != r.assoc_index_type) {
    diag.Error(loc, "associative array index type mismatch in assignment",
               Subclause("7.9.9"));
    return true;
  }
  return false;
}

// Reports a mismatch in the number of unpacked dimensions between two tracked
// arrays. Returns true (with a diagnostic emitted) when found.
bool ReportUnpackedDimCountMismatch(const ArrayAssignPair& p,
                                    DiagEngine& diag) {
  if (p.l.num_unpacked_dims != p.r.num_unpacked_dims) {
    diag.Error(p.loc,
               std::format("array assignment requires the same number of "
                           "unpacked dimensions ('{}' has {}, '{}' has {})",
                           p.lhs->text, p.l.num_unpacked_dims, p.rhs->text,
                           p.r.num_unpacked_dims),
               Subclause("7.6"));
    return true;
  }
  return false;
}

// Reports an element-type mismatch between two tracked arrays. Returns true
// (with a diagnostic emitted) when found.
bool ReportElementTypeMismatch(const ArrayAssignPair& p, DiagEngine& diag) {
  if (!ElementTypesEquivalent(
          {p.l.elem_type, p.l.elem_width, p.l.elem_is_signed,
           p.l.elem_is_4state, p.l.elem_type_name},
          {p.r.elem_type, p.r.elem_width, p.r.elem_is_signed,
           p.r.elem_is_4state, p.r.elem_type_name})) {
    diag.Error(p.loc,
               std::format("array element type mismatch in assignment "
                           "('{}' vs '{}')",
                           p.lhs->text, p.rhs->text),
               Subclause("7.6"));
    return true;
  }
  return false;
}

// Reports a fixed-size element-count mismatch between two tracked arrays.
// Returns true (with a diagnostic emitted) when found.
bool ReportFixedSizeMismatch(const ArrayAssignPair& p, DiagEngine& diag) {
  if (p.l.unpacked_size > 0 && !p.l.is_dynamic && p.r.unpacked_size > 0 &&
      !p.r.is_dynamic && p.l.unpacked_size != p.r.unpacked_size) {
    diag.Error(p.loc,
               std::format("array size mismatch: '{}' has {} elements but "
                           "'{}' has {}",
                           p.lhs->text, p.l.unpacked_size, p.rhs->text,
                           p.r.unpacked_size),
               Subclause("7.6"));
    return true;
  }
  return false;
}

// Validates the kind/shape compatibility of two tracked arrays in an
// assignment (associativity, index type, dimension count, element type, and
// fixed-size element count). Returns true (with a diagnostic emitted) when the
// first incompatibility is found, mirroring the caller's early returns.
bool ReportArrayShapeMismatch(const ArrayAssignPair& p, DiagEngine& diag) {
  if (ReportAssocKindMismatch(p.l, p.r, p.loc, diag)) return true;
  if (ReportUnpackedDimCountMismatch(p, diag)) return true;
  if (ReportElementTypeMismatch(p, diag)) return true;
  if (ReportFixedSizeMismatch(p, diag)) return true;
  return false;
}

using ArrayInfos =
    std::unordered_map<std::string_view, Elaborator::VarArrayInfo>;

// The arrays an assignment's operands may name: those a procedural block or a
// subroutine declares, which hide the module's own, and the module's. A name
// the block declares as no array hides a module array just the same.
struct ArrayScope {
  const ArrayInfos& module;
  std::unordered_map<std::string_view, std::optional<Elaborator::VarArrayInfo>>
      local = {};

  [[nodiscard]] const Elaborator::VarArrayInfo* Find(
      std::string_view name) const {
    auto lit = local.find(name);
    if (lit != local.end()) return lit->second ? &*lit->second : nullptr;
    auto mit = module.find(name);
    return mit != module.end() ? &mit->second : nullptr;
  }
};

// What judging the assignments of a module reads besides the arrays in scope.
struct ArrayAssignScan {
  const std::unordered_set<std::string_view>& packed_array_vars;
  const TypeShapeTables& tables;
  const std::unordered_set<std::string_view>& aggregate_typedefs;
  DiagEngine& diag;
};

// §7.4.5: the number of elements the slice `sel` takes, when its bounds or its
// width are literals; nullopt otherwise.
std::optional<uint32_t> ConstantSliceWidth(const Expr* sel) {
  if (sel->is_part_select_plus || sel->is_part_select_minus) {
    auto width = ConstEvalInt(sel->index_end);
    if (!width) return std::nullopt;
    return static_cast<uint32_t>(*width);
  }
  auto left = ConstEvalInt(sel->index);
  auto right = ConstEvalInt(sel->index_end);
  if (!left || !right) return std::nullopt;
  return static_cast<uint32_t>(std::abs(*left - *right) + 1);
}

// §7.4.4 and §7.4.5: the array an operand of an assignment stands for. A
// tracked array named alone is itself; one selected by index through some of
// its dimensions is the subarray those leave, and one whose last select is a
// slice is that slice, each described as the whole array is. A subarray or
// slice is described only where every dimension it keeps has a fixed size the
// declaration states and the slice's width is a literal; nullopt for anything
// else, including an element or a select inside one. `root` is set to the
// array's name.
std::optional<Elaborator::VarArrayInfo> OperandArrayInfo(
    const Expr* e, const ArrayScope& arrays, const Expr*& root) {
  const Expr* last = e->kind == ExprKind::kSelect ? e : nullptr;
  size_t selects = 0;
  // A select standing as a side of an assignment always has a base; only a
  // value range of `inside` is written as a select without one.
  for (; e->kind == ExprKind::kSelect; e = e->base) ++selects;
  if (e->kind != ExprKind::kIdentifier) return std::nullopt;
  const Elaborator::VarArrayInfo* found = arrays.Find(e->text);
  if (found == nullptr) return std::nullopt;
  root = e;
  const Elaborator::VarArrayInfo& whole = *found;
  if (selects == 0) return whole;
  const auto& shape = whole.unpacked_shape;
  bool sliced = last->index_end != nullptr;
  size_t kept = sliced ? selects - 1 : selects;
  if (kept >= shape.size()) return std::nullopt;
  std::vector<std::optional<uint32_t>> sizes(
      shape.begin() + static_cast<std::ptrdiff_t>(kept), shape.end());
  if (sliced) sizes.front() = ConstantSliceWidth(last);
  Elaborator::VarArrayInfo part = whole;
  part.dim_sizes.clear();
  for (const std::optional<uint32_t>& size : sizes) {
    if (!size) return std::nullopt;
    part.dim_sizes.push_back(*size);
  }
  part.unpacked_size = part.dim_sizes.front();
  part.num_unpacked_dims = static_cast<uint32_t>(part.dim_sizes.size());
  part.is_dynamic = false;
  part.is_assoc = false;
  part.is_queue = false;
  part.elements_are_queues = false;
  part.declared_dims.clear();
  part.unpacked_shape = sizes;
  return part;
}

}  // namespace

namespace {

void CheckArrayOperands(const Expr* lhs, const Expr* rhs, SourceLoc loc,
                        const ArrayScope& arrays, const ArrayAssignScan& scan) {
  if (!lhs || !rhs) return;
  const Expr* lhs_root = nullptr;
  const Expr* rhs_root = nullptr;
  auto l = OperandArrayInfo(lhs, arrays, lhs_root);
  auto r = OperandArrayInfo(rhs, arrays, rhs_root);
  if (!l || !r) {
    if (l && rhs->kind == ExprKind::kIdentifier &&
        scan.packed_array_vars.count(rhs->text)) {
      scan.diag.Error(
          loc,
          std::format("packed array '{}' cannot be directly assigned to "
                      "unpacked array '{}' without an explicit cast",
                      rhs->text, lhs_root->text),
          Subclause("7.6"));
    }
    return;
  }
  const ArrayAssignPair kPair{*l, *r, lhs_root, rhs_root, loc};

  if (ReportArrayShapeMismatch(kPair, scan.diag)) return;
  if (ReportFasterVaryingDimMismatch(kPair, scan.diag)) return;
  if (ReportFasterVaryingDimMismatchVarOuter(kPair, scan.diag)) return;
}

// A declaration assignment is an assignment to the variable declared, so
// §7.6 judges its initializer as it would the same right-hand side.
void CheckInitializer(std::string_view name, const Expr* init, SourceLoc loc,
                      const ArrayScope& arrays, const ArrayAssignScan& scan) {
  Expr target;
  target.kind = ExprKind::kIdentifier;
  target.text = name;
  CheckArrayOperands(&target, init, loc, arrays, scan);
}

// §7.4 to §7.10: an array a procedural block or a subroutine declares,
// described as Elaborator::TrackVarArrayInfo describes a module's. Its sizes
// are those its dimensions state as literals; one sized by a parameter is
// left unsized, so that no count is compared for it.
Elaborator::VarArrayInfo DeclaredArrayInfo(const DataType& type,
                                           const std::vector<Expr*>& dims,
                                           const ArrayAssignScan& scan) {
  const TypedefMap& typedefs = scan.tables.typedefs;
  Elaborator::VarArrayInfo info;
  info.elem_type = ElementKindThroughTypedefs(type, typedefs);
  info.elem_type_name = ElementTypeIdentity(type, typedefs);
  info.elem_width = EvalTypeWidth(type, typedefs);
  info.elem_is_signed = IsSignedType(type, typedefs);
  info.elem_is_4state = Is4stateType(type, typedefs);
  info.num_unpacked_dims = static_cast<uint32_t>(dims.size());
  info.unpacked_shape =
      UnpackedShapeOf(type, dims, scan.aggregate_typedefs, ScopeMap{});
  const Expr* first = dims.front();
  info.is_dynamic = first == nullptr;
  info.is_queue = first != nullptr && IsQueueDim(first);
  info.is_assoc = !info.is_dynamic && !info.is_queue &&
                  !IsFixedSizeUnpackedDim(first, scan.tables);
  info.unpacked_size = static_cast<uint32_t>(
      info.is_dynamic ? 0 : ComputeDimSize(first).value_or(0));
  for (const std::optional<uint32_t>& size : info.unpacked_shape) {
    if (size) info.dim_sizes.push_back(*size);
  }
  return info;
}

// Records what a declaration makes of `name` in the block that declares it.
void Declare(std::string_view name, const DataType& type,
             const std::vector<Expr*>& dims, ArrayScope& arrays,
             const ArrayAssignScan& scan) {
  if (dims.empty()) {
    arrays.local[name] = std::nullopt;
  } else {
    arrays.local[name] = DeclaredArrayInfo(type, dims, scan);
  }
}

void WalkArrayAssignments(const Stmt* s, ArrayScope& arrays,
                          const ArrayAssignScan& scan) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl) {
    Declare(s->var_name, s->var_decl_type, s->var_unpacked_dims, arrays, scan);
    if (s->var_init != nullptr) {
      CheckInitializer(s->var_name, s->var_init, s->range.start, arrays, scan);
    }
  }
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckArrayOperands(s->lhs, s->rhs, s->range.start, arrays, scan);
  }
  // §7.6 states the shape and element-type compatibility an array assignment
  // requires and names no statement the requirement is suspended in, so this
  // descends every link ForEachChildStmt in elaborator_validate_internal.h
  // names and names no link itself. It wrote out six of the thirteen, so
  // `fork a = b; join` and `assert (1) a = b;` were judged in neither form
  // while the same `a = b;` one level up was reported.
  ForEachChildStmt(s, [&arrays, &scan](Stmt* const& sub) {
    WalkArrayAssignments(sub, arrays, scan);
  });
}

// A subroutine's arguments are declarations of its own, as its body's are.
void WalkSubroutine(const ModuleItem* item, const ArrayInfos& module,
                    const ArrayAssignScan& scan) {
  ArrayScope arrays{module};
  for (const FunctionArg& arg : item->func_args) {
    Declare(arg.name, arg.data_type, arg.unpacked_dims, arrays, scan);
  }
  for (const Stmt* s : item->func_body_stmts) {
    WalkArrayAssignments(s, arrays, scan);
  }
}

}  // namespace

void Elaborator::ValidateArrayAssignments(const ModuleDecl* decl) {
  const TypeShapeTables kShapeTables{typedefs_, td_array_dims_, class_names_};
  const ArrayAssignScan kScan{packed_array_vars_, kShapeTables,
                              aggregate_typedef_names_, diag_};
  const ArrayScope kModuleScope{var_array_info_};
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckArrayOperands(item->assign_lhs, item->assign_rhs, item->loc,
                         kModuleScope, kScan);
    }
    if (item->kind == ModuleItemKind::kVarDecl && item->init_expr != nullptr) {
      CheckInitializer(item->name, item->init_expr, item->loc, kModuleScope,
                       kScan);
    }
    if (IsProceduralItemKind(item->kind)) {
      ArrayScope arrays{var_array_info_};
      WalkArrayAssignments(item->body, arrays, kScan);
    }
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      WalkSubroutine(item, var_array_info_, kScan);
    }
  }
}

bool IsSliceSelect(const Expr* e) {
  if (!e || e->kind != ExprKind::kSelect) return false;
  return e->is_part_select_plus || e->is_part_select_minus || e->index_end;
}

static void CheckAssocSliceExpr(
    const Expr* e, const std::unordered_set<std::string_view>& assoc_names,
    DiagEngine& diag) {
  if (!e) return;
  if (IsSliceSelect(e) && e->base && e->base->kind == ExprKind::kIdentifier) {
    if (assoc_names.count(e->base->text)) {
      diag.Error(e->range.start, "slice is not allowed on an associative array",
                 Subclause("7.4.6"));
    }
  }
  CheckAssocSliceExpr(e->lhs, assoc_names, diag);
  CheckAssocSliceExpr(e->rhs, assoc_names, diag);
  CheckAssocSliceExpr(e->base, assoc_names, diag);
  CheckAssocSliceExpr(e->index, assoc_names, diag);
  CheckAssocSliceExpr(e->index_end, assoc_names, diag);
  CheckAssocSliceExpr(e->condition, assoc_names, diag);
  CheckAssocSliceExpr(e->true_expr, assoc_names, diag);
  CheckAssocSliceExpr(e->false_expr, assoc_names, diag);
  for (const auto* elem : e->elements) {
    CheckAssocSliceExpr(elem, assoc_names, diag);
  }
}

static void WalkStmtsForAssocSlice(
    const Stmt* s, const std::unordered_set<std::string_view>& assoc_names,
    DiagEngine& diag) {
  if (!s) return;
  CheckAssocSliceExpr(s->lhs, assoc_names, diag);
  CheckAssocSliceExpr(s->rhs, assoc_names, diag);
  CheckAssocSliceExpr(s->expr, assoc_names, diag);
  CheckAssocSliceExpr(s->condition, assoc_names, diag);
  // §7.8 gives an associative array no slice, the rule the report names
  // §7.4.6 for, and neither clause conditions it on the statement the slice is
  // written in, so this descends every link ForEachChildStmt in
  // elaborator_validate_internal.h names and names no link itself. It wrote out
  // six of the thirteen, so `fork x = aa[1:2]; join` and a slice written in a
  // randcase item were never looked at.
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtsForAssocSlice(sub, assoc_names, diag);
  });
}

void Elaborator::ValidateAssocArraySlices(const ModuleDecl* decl) {
  std::unordered_set<std::string_view> assoc_names;
  for (const auto& [name, info] : var_array_info_) {
    if (info.is_assoc) assoc_names.insert(name);
  }
  if (assoc_names.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckAssocSliceExpr(item->assign_lhs, assoc_names, diag_);
      CheckAssocSliceExpr(item->assign_rhs, assoc_names, diag_);
    }
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForAssocSlice(item->body, assoc_names, diag_);
    }
  }
}

static bool IsTraversalMethod(std::string_view name) {
  return name == "first" || name == "last" || name == "next" || name == "prev";
}

// The subclause of IEEE 1800-2023 stating the wildcard restriction for one
// associative array traversal method. §7.9.4 First(), §7.9.5 Last(), §7.9.6
// Next() and §7.9.7 Prev() each bar their own method from an associative array
// with a wildcard index type. The caller has already answered
// IsTraversalMethod, so `name` is one of the four.
static std::string_view TraversalMethodSubclause(std::string_view name) {
  if (name == "first") return "7.9.4";
  if (name == "last") return "7.9.5";
  if (name == "next") return "7.9.6";
  return "7.9.7";
}

// §7.8.1 — array manipulation methods (§7.12) that yield an index value or an
// array of index values. A wildcard-indexed associative array may not be used
// with these, since its keys have no stable index domain to return. This
// includes unique_index, which returns an array of the qualifying indices.
static bool IsIndexReturningMethod(std::string_view name) {
  return name == "find_index" || name == "find_first_index" ||
         name == "find_last_index" || name == "unique_index";
}

// §7.8.1 — true when `idx` is a nonintegral index expression for a wildcard
// associative array: one whose value is real, whatever its form
// (KindOfIndexValue). (A string literal is not nonintegral here; it is cast to
// an equivalent-width bit vector.)
bool IsNonintegralIndex(const Expr* idx, const TypeMap& var_types) {
  if (!idx) return false;
  return KindOfIndexValue(idx, var_types) == IndexValueKind::kReal;
}

static void CheckWildcardTraversalExpr(
    const Expr* e, const std::unordered_set<std::string_view>& wildcard_names,
    const TypeMap& var_types, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kCall && e->base &&
      e->base->kind == ExprKind::kIdentifier && IsTraversalMethod(e->callee) &&
      wildcard_names.count(e->base->text)) {
    // §7.8.1 bars foreach and the §7.12 methods that return an index, not
    // these four. Each traversal method's own subclause states the rule, so
    // the report names the one belonging to the method it rejected.
    diag.Error(e->range.start,
               std::format("'{}' is not allowed on wildcard associative "
                           "array '{}'",
                           e->callee, e->base->text),
               Subclause(TraversalMethodSubclause(e->callee)));
  }
  // §7.8.1 — an array-locator method (e.g. `aa.find_index with (...)`) parses
  // as a member access whose receiver is the array and whose member is the
  // method name. Reject the index-returning locators on a wildcard array.
  if (e->kind == ExprKind::kMemberAccess && e->lhs &&
      e->lhs->kind == ExprKind::kIdentifier && e->rhs &&
      IsIndexReturningMethod(e->rhs->text) &&
      wildcard_names.count(e->lhs->text)) {
    diag.Error(e->range.start,
               std::format("'{}' is not allowed on wildcard associative "
                           "array '{}'",
                           e->rhs->text, e->lhs->text),
               Subclause("7.8.1"));
  }
  // §7.8.1 — a wildcard index must be integral; a real (nonintegral) value used
  // to index the array is illegal.
  if (e->kind == ExprKind::kSelect && e->base &&
      e->base->kind == ExprKind::kIdentifier &&
      IsNonintegralIndex(e->index, var_types) &&
      wildcard_names.count(e->base->text)) {
    diag.Error(e->index->range.start,
               std::format("nonintegral index is not allowed on wildcard "
                           "associative array '{}'",
                           e->base->text),
               Subclause("7.8.1"));
  }
  CheckWildcardTraversalExpr(e->lhs, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(e->rhs, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(e->base, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(e->index, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(e->index_end, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(e->condition, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(e->true_expr, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(e->false_expr, wildcard_names, var_types, diag);
  for (const auto* elem : e->elements) {
    CheckWildcardTraversalExpr(elem, wildcard_names, var_types, diag);
  }
}

static void WalkStmtsForWildcardTraversal(
    const Stmt* s, const std::unordered_set<std::string_view>& wildcard_names,
    const TypeMap& var_types, DiagEngine& diag) {
  if (!s) return;
  // §7.8.1 — a wildcard-indexed associative array may not drive a foreach loop.
  std::string_view foreach_array;
  if (s->kind == StmtKind::kForeach && s->expr) {
    // The array's own identifier: the name itself, or the last member of the
    // chain Parser::ParseForeachArrayId reads a hierarchical name into.
    if (s->expr->kind == ExprKind::kIdentifier) {
      foreach_array = s->expr->text;
    } else if (s->expr->kind == ExprKind::kMemberAccess && s->expr->rhs) {
      foreach_array = s->expr->rhs->text;
    }
  }
  if (!foreach_array.empty() && wildcard_names.count(foreach_array)) {
    diag.Error(s->range.start,
               std::format("wildcard associative array '{}' may not be used in "
                           "a foreach loop",
                           foreach_array),
               Subclause("7.8.1"));
  }
  CheckWildcardTraversalExpr(s->lhs, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(s->rhs, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(s->expr, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(s->condition, wildcard_names, var_types, diag);
  // §7.8.1 bars a wildcard-indexed associative array from a foreach loop, from
  // the §7.12 methods that return an index and from a nonintegral index, and
  // names no statement the prohibition is lifted in, so this descends every
  // link ForEachChildStmt in elaborator_validate_internal.h names and names no
  // link itself. It wrote out six of the thirteen, so
  // `fork foreach (aa[i]) ; join` and `assert (1) else x = aa[1.5];`
  // elaborated clean.
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtsForWildcardTraversal(sub, wildcard_names, var_types, diag);
  });
}

void Elaborator::ValidateAssocWildcardTraversal(const ModuleDecl* decl) {
  std::unordered_set<std::string_view> wildcard_names;
  for (const auto& [name, info] : var_array_info_) {
    if (info.is_assoc && info.assoc_index_type == "*")
      wildcard_names.insert(name);
  }
  if (wildcard_names.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckWildcardTraversalExpr(item->assign_lhs, wildcard_names, var_types_,
                                 diag_);
      CheckWildcardTraversalExpr(item->assign_rhs, wildcard_names, var_types_,
                                 diag_);
    }
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForWildcardTraversal(item->body, wildcard_names, var_types_,
                                    diag_);
    }
  }
}

// Section 7.9.8 -- the argument passed to one of the four associative-array
// traversal methods (first/last/next/prev) shall be assignment compatible with
// the array's index type. A string-indexed array therefore requires a string
// argument and an integral-indexed array requires an integral argument; the two
// categories are not assignment compatible with each other. A narrower integral
// argument is still assignment compatible -- the resulting truncation is
// resolved at run time and is not flagged during elaboration.
enum class AssocKeyCategory : std::uint8_t {
  kOther,
  kStringKey,
  kIntegralKey,
  kWildcard
};

static AssocKeyCategory ClassifyAssocKey(std::string_view index_type,
                                         const TypedefMap& typedefs) {
  if (index_type == "string") return AssocKeyCategory::kStringKey;
  auto builtin_integral = [](std::string_view t) {
    return t == "bit" || t == "logic" || t == "reg" || t == "byte" ||
           t == "shortint" || t == "int" || t == "longint" || t == "integer" ||
           t == "time";
  };
  if (builtin_integral(index_type)) return AssocKeyCategory::kIntegralKey;
  auto it = typedefs.find(index_type);
  if (it != typedefs.end() && IsIntegralType(it->second.kind))
    return AssocKeyCategory::kIntegralKey;
  return AssocKeyCategory::kOther;
}

static bool TraversalArgIsString(const Expr* arg, const TypeMap& var_types) {
  if (!arg || arg->kind != ExprKind::kIdentifier) return false;
  auto it = var_types.find(arg->text);
  return it != var_types.end() && it->second == DataTypeKind::kString;
}

static bool TraversalArgIsIntegral(const Expr* arg, const TypeMap& var_types) {
  if (!arg || arg->kind != ExprKind::kIdentifier) return false;
  auto it = var_types.find(arg->text);
  return it != var_types.end() && IsIntegralType(it->second);
}

// Reports a traversal-method call (`arr.first(x)` etc.) whose argument type is
// not assignment compatible with the associative array's index category. Only
// the call node itself is examined; child expressions are walked by the caller.
static void CheckTraversalCallSite(
    const Expr* e,
    const std::unordered_map<std::string_view, AssocKeyCategory>& assoc_keys,
    const TypeMap& var_types, DiagEngine& diag) {
  // `arr.first(x)` parses as a kCall whose lhs is the member access `arr.first`
  // and whose args hold the traversal argument.
  if (e->kind != ExprKind::kCall || !e->lhs ||
      e->lhs->kind != ExprKind::kMemberAccess || e->args.empty()) {
    return;
  }
  const Expr* access = e->lhs;
  if (!access->lhs || access->lhs->kind != ExprKind::kIdentifier ||
      !access->rhs || access->rhs->kind != ExprKind::kIdentifier ||
      !IsTraversalMethod(access->rhs->text)) {
    return;
  }
  auto array_name = access->lhs->text;
  auto method = access->rhs->text;
  auto it = assoc_keys.find(array_name);
  if (it == assoc_keys.end()) return;
  // §7.9.4 First(), §7.9.5 Last(), §7.9.6 Next() and §7.9.7 Prev() each bar
  // their own method from an associative array with a wildcard index type, so
  // the report names the subclause belonging to the method it rejected rather
  // than the clause the four sit under.
  if (it->second == AssocKeyCategory::kWildcard) {
    diag.Error(e->range.start,
               std::format("traversal method '{}' shall not be used on the "
                           "wildcard-indexed associative array '{}'",
                           method, array_name),
               Subclause(TraversalMethodSubclause(method)));
    return;
  }
  const Expr* arg = e->args[0];
  bool wrong = (it->second == AssocKeyCategory::kStringKey &&
                TraversalArgIsIntegral(arg, var_types)) ||
               (it->second == AssocKeyCategory::kIntegralKey &&
                TraversalArgIsString(arg, var_types));
  if (wrong) {
    diag.Error(arg ? arg->range.start : e->range.start,
               std::format("traversal method '{}' argument is not "
                           "assignment compatible with the index type of "
                           "associative array '{}'",
                           method, array_name),
               Subclause("7.9.8"));
  }
}

static void CheckTraversalArgTypeExpr(
    const Expr* e,
    const std::unordered_map<std::string_view, AssocKeyCategory>& assoc_keys,
    const TypeMap& var_types, DiagEngine& diag) {
  if (!e) return;
  CheckTraversalCallSite(e, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(e->lhs, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(e->rhs, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(e->base, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(e->index, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(e->index_end, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(e->condition, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(e->true_expr, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(e->false_expr, assoc_keys, var_types, diag);
  for (const auto* a : e->args)
    CheckTraversalArgTypeExpr(a, assoc_keys, var_types, diag);
  for (const auto* el : e->elements)
    CheckTraversalArgTypeExpr(el, assoc_keys, var_types, diag);
}

static void WalkStmtsForTraversalArgType(
    const Stmt* s,
    const std::unordered_map<std::string_view, AssocKeyCategory>& assoc_keys,
    const TypeMap& var_types, DiagEngine& diag) {
  if (!s) return;
  CheckTraversalArgTypeExpr(s->lhs, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(s->rhs, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(s->expr, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(s->condition, assoc_keys, var_types, diag);
  // §7.9.8 requires a traversal method's argument to be assignment compatible
  // with the array's index type, and §7.9.4 through §7.9.7 bar the four methods
  // on a wildcard-indexed array; neither rule is conditioned on the statement
  // the call is written in, so this descends every link ForEachChildStmt in
  // elaborator_validate_internal.h names and names no link itself. It wrote out
  // six of the thirteen, so `fork status = aa.first(s); join` and the same call
  // written in a randsequence production code block went unchecked.
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtsForTraversalArgType(sub, assoc_keys, var_types, diag);
  });
}

void Elaborator::ValidateAssocTraversalArgType(const ModuleDecl* decl) {
  std::unordered_map<std::string_view, AssocKeyCategory> assoc_keys;
  for (const auto& [name, info] : var_array_info_) {
    if (!info.is_assoc) continue;
    if (info.assoc_index_type == "*") {
      assoc_keys[name] = AssocKeyCategory::kWildcard;
      continue;
    }
    auto cat = ClassifyAssocKey(info.assoc_index_type, typedefs_);
    if (cat != AssocKeyCategory::kOther) assoc_keys[name] = cat;
  }
  if (assoc_keys.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckTraversalArgTypeExpr(item->assign_lhs, assoc_keys, var_types_,
                                diag_);
      CheckTraversalArgTypeExpr(item->assign_rhs, assoc_keys, var_types_,
                                diag_);
    }
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body)
      WalkStmtsForTraversalArgType(item->body, assoc_keys, var_types_, diag_);
  }
}

}  // namespace delta
